import ATK.NSIdent
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# ATK — Navier–Stokes: estimativas trilineares no lado de Fourier

Camada 22 do ataque a B3 (unicidade fraca–forte, passo U-7). Sem imersão de Sobolev (que não
está na Mathlib): todas as estimativas são feitas no lado de Fourier, com Cauchy–Schwarz com
pesos `w₁ = 1 + ‖ξ‖` e a integrabilidade de `w₄⁻¹` em `ℝ³`.

* `tri_bound`: para `F, G, H ≥ 0` em `L²`,
  `∫∫ F(ξ) G(η) H(ξ − η) w₁(η)⁻¹ w₁(ξ − η)⁻¹ ≤ (I₄ ‖F‖² + ‖G‖² ‖H‖²)/2`
  (média aritmético-geométrica e `w₁(η)⁻² w₁(ζ)⁻² ≤ (w₄(η)⁻¹ + w₄(ζ)⁻¹)/2`);
* `integrable_Psi`: o integrando trilinear `‖ξ‖ ‖f(ξ)‖ ‖g(η)‖ ‖h(ξ − η)‖` é integrável no produto
  para `f, g, h` com `w₁ ‖·‖ ∈ L²` (isto é, em `H¹`);
* `integral_inner_Nl_cancel`: `∫ ⟪d, N(b, d)⟫ = 0` para `b` de divergência nula e `d`
  hermitiana (a simetria `ξ ↦ η − ξ`);
* `norm_integral_inner_Nl_le`: `|∫ ⟪d, N(d, f)⟫| ≤ 2π A I₄ ‖d‖²` para `d` de divergência nula e
  `‖f‖ ≤ A w₅⁻¹` (usa `⟪ξ, d(η)⟫ = ⟪ξ − η, d(η)⟫`).

**CLOSED_MATH continua false.**
-/

open MeasureTheory Filter Set ComplexConjugate
open scoped InnerProductSpace Real

namespace ATK.NSTrilinear

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSL2 ATK.NSSimetria

/-! ### Integrais no produto `ℝ³ × ℝ³` -/

section Prod

variable {φ ψ : E3 → ℝ}

theorem integrable_fst_mul_sub (hφm : Measurable φ) (hψm : Measurable ψ) (hφ : Integrable φ)
    (hψ : Integrable ψ) :
    Integrable (fun p : E3 × E3 => φ p.1 * ψ (p.1 - p.2)) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : E3 × E3 => φ p.1 * ψ (p.1 - p.2))
      (volume.prod volume) :=
    ((hφm.comp measurable_fst).mul
      (hψm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  refine (integrable_prod_iff hm).mpr ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
  · exact (hψ.comp_sub_left ξ).const_mul (φ ξ)
  · have e : (fun ξ => ∫ η, ‖φ ξ * ψ (ξ - η)‖) = fun ξ => ‖φ ξ‖ * ∫ η, ‖ψ η‖ := by
      funext ξ
      simp_rw [norm_mul]
      rw [integral_const_mul]
      congr 1
      exact integral_sub_left_eq_self (fun η => ‖ψ η‖) volume ξ
    rw [e]
    exact hφ.norm.mul_const _

theorem integral_fst_mul_sub (hφm : Measurable φ) (hψm : Measurable ψ) (hφ : Integrable φ)
    (hψ : Integrable ψ) :
    ∫ p : E3 × E3, φ p.1 * ψ (p.1 - p.2) ∂(volume.prod volume) = (∫ ξ, φ ξ) * ∫ ξ, ψ ξ := by
  rw [integral_prod _ (integrable_fst_mul_sub hφm hψm hφ hψ), ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  try dsimp only
  rw [integral_const_mul]
  congr 1
  exact integral_sub_left_eq_self ψ volume ξ

theorem integrable_snd_mul_sub (hφm : Measurable φ) (hψm : Measurable ψ) (hφ : Integrable φ)
    (hψ : Integrable ψ) :
    Integrable (fun p : E3 × E3 => φ p.2 * ψ (p.1 - p.2)) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : E3 × E3 => φ p.2 * ψ (p.1 - p.2))
      (volume.prod volume) :=
    ((hφm.comp measurable_snd).mul
      (hψm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  refine (integrable_prod_iff' hm).mpr ⟨Eventually.of_forall fun η => ?_, ?_⟩
  · exact (hψ.comp_sub_right η).const_mul (φ η)
  · have e : (fun η => ∫ ξ, ‖φ η * ψ (ξ - η)‖) = fun η => ‖φ η‖ * ∫ ξ, ‖ψ ξ‖ := by
      funext η
      simp_rw [norm_mul]
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (fun ξ => ‖ψ ξ‖) η
    rw [e]
    exact hφ.norm.mul_const _

theorem integral_snd_mul_sub (hφm : Measurable φ) (hψm : Measurable ψ) (hφ : Integrable φ)
    (hψ : Integrable ψ) :
    ∫ p : E3 × E3, φ p.2 * ψ (p.1 - p.2) ∂(volume.prod volume) = (∫ ξ, φ ξ) * ∫ ξ, ψ ξ := by
  rw [integral_prod_symm _ (integrable_snd_mul_sub hφm hψm hφ hψ), ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  try dsimp only
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self ψ η

end Prod

/-! ### A estimativa trilinear com pesos -/

theorem w1_inv_pow4 (ξ : E3) : (w 1 ξ)⁻¹ ^ 4 = (w 4 ξ)⁻¹ := by
  unfold w
  rw [inv_pow, ← pow_mul]

theorem measurable_w_inv (m : ℕ) : Measurable fun ξ : E3 => (w m ξ)⁻¹ := by
  unfold w
  exact ((continuous_const.add continuous_norm).pow m).measurable.inv

theorem tri_pt {X Y Z W1 W2 : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hW1 : 0 ≤ W1)
    (hW2 : 0 ≤ W2) :
    X * Y * Z * (W1 * W2) ≤
      (X ^ 2 * W1 ^ 4 + X ^ 2 * W2 ^ 4) / 4 + Y ^ 2 * Z ^ 2 / 2 := by
  have h1 : (W1 * W2) ^ 2 ≤ (W1 ^ 4 + W2 ^ 4) / 2 := by
    nlinarith [sq_nonneg (W1 ^ 2 - W2 ^ 2)]
  have h2 := two_mul_le_add_sq (X * (W1 * W2)) (Y * Z)
  have h3 : X ^ 2 * (W1 * W2) ^ 2 ≤ X ^ 2 * ((W1 ^ 4 + W2 ^ 4) / 2) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg X)
  nlinarith [h2, h3]

/-- **A estimativa trilinear com pesos.** -/
theorem tri_bound {F G H : E3 → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hHm : Measurable H) (hF0 : ∀ ξ, 0 ≤ F ξ) (hG0 : ∀ ξ, 0 ≤ G ξ) (hH0 : ∀ ξ, 0 ≤ H ξ)
    (hF : Integrable fun ξ => F ξ ^ 2) (hG : Integrable fun ξ => G ξ ^ 2)
    (hH : Integrable fun ξ => H ξ ^ 2) :
    Integrable (fun p : E3 × E3 =>
        F p.1 * G p.2 * H (p.1 - p.2) * ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹))
        (volume.prod volume) ∧
      ∫ p : E3 × E3, F p.1 * G p.2 * H (p.1 - p.2) * ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹)
          ∂(volume.prod volume) ≤
        (I4 * (∫ ξ, F ξ ^ 2) + (∫ ξ, G ξ ^ 2) * ∫ ξ, H ξ ^ 2) / 2 := by
  set k : E3 → ℝ := fun ξ => (w 4 ξ)⁻¹ with hk
  have hkm : Measurable k := measurable_w_inv 4
  have hki : Integrable k := integrable_w_inv
  have hF2m : Measurable fun ξ => F ξ ^ 2 := hFm.pow_const 2
  have hG2m : Measurable fun ξ => G ξ ^ 2 := hGm.pow_const 2
  have hH2m : Measurable fun ξ => H ξ ^ 2 := hHm.pow_const 2
  have i1 : Integrable (fun p : E3 × E3 => F p.1 ^ 2 * k p.2) (volume.prod volume) :=
    hF.mul_prod hki
  have i2 : Integrable (fun p : E3 × E3 => F p.1 ^ 2 * k (p.1 - p.2)) (volume.prod volume) :=
    integrable_fst_mul_sub hF2m hkm hF hki
  have i3 : Integrable (fun p : E3 × E3 => G p.2 ^ 2 * H (p.1 - p.2) ^ 2) (volume.prod volume) :=
    integrable_snd_mul_sub hG2m hH2m hG hH
  set D : E3 × E3 → ℝ := fun p =>
    (F p.1 ^ 2 * k p.2 + F p.1 ^ 2 * k (p.1 - p.2)) / 4 + G p.2 ^ 2 * H (p.1 - p.2) ^ 2 / 2
    with hD
  have iD : Integrable D (volume.prod volume) :=
    ((i1.add i2).div_const 4).add (i3.div_const 2)
  have hpt : ∀ p : E3 × E3,
      F p.1 * G p.2 * H (p.1 - p.2) * ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹) ≤ D p := by
    intro p
    have h := tri_pt (hF0 p.1) (hG0 p.2) (hH0 (p.1 - p.2)) (inv_pos.mpr (w_pos 1 p.2)).le
      (inv_pos.mpr (w_pos 1 (p.1 - p.2))).le
    rw [w1_inv_pow4, w1_inv_pow4] at h
    rw [hD]
    dsimp only
    rw [hk]
    dsimp only
    linarith
  have hm : AEStronglyMeasurable (fun p : E3 × E3 =>
      F p.1 * G p.2 * H (p.1 - p.2) * ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹))
      (volume.prod volume) := by
    have h1 := measurable_w_inv 1
    exact ((((hFm.comp measurable_fst).mul (hGm.comp measurable_snd)).mul
      (hHm.comp (measurable_fst.sub measurable_snd))).mul
      ((h1.comp measurable_snd).mul (h1.comp (measurable_fst.sub measurable_snd)))).aestronglyMeasurable
  have hint : Integrable (fun p : E3 × E3 =>
      F p.1 * G p.2 * H (p.1 - p.2) * ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹))
      (volume.prod volume) := by
    refine iD.mono' hm (Eventually.of_forall fun p => ?_)
    have h0 : 0 ≤ F p.1 * G p.2 * H (p.1 - p.2) * ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹) := by
      have := hF0 p.1; have := hG0 p.2; have := hH0 (p.1 - p.2)
      have := (inv_pos.mpr (w_pos 1 p.2)).le; have := (inv_pos.mpr (w_pos 1 (p.1 - p.2))).le
      positivity
    rw [Real.norm_of_nonneg h0]
    exact hpt p
  refine ⟨hint, (integral_mono hint iD hpt).trans (le_of_eq ?_)⟩
  have e1 : ∫ p : E3 × E3, F p.1 ^ 2 * k p.2 ∂(volume.prod volume) =
      (∫ ξ, F ξ ^ 2) * I4 := by
    rw [integral_prod_mul (fun ξ => F ξ ^ 2) k]
    rfl
  have e2 : ∫ p : E3 × E3, F p.1 ^ 2 * k (p.1 - p.2) ∂(volume.prod volume) =
      (∫ ξ, F ξ ^ 2) * I4 := by
    rw [integral_fst_mul_sub hF2m hkm hF hki]
    rfl
  have e3 := integral_snd_mul_sub hG2m hH2m hG hH
  have i12 : Integrable (fun p : E3 × E3 => (F p.1 ^ 2 * k p.2 + F p.1 ^ 2 * k (p.1 - p.2)) / 4)
      (volume.prod volume) := (i1.add i2).div_const 4
  have i3' : Integrable (fun p : E3 × E3 => G p.2 ^ 2 * H (p.1 - p.2) ^ 2 / 2)
      (volume.prod volume) := i3.div_const 2
  show ∫ p : E3 × E3, ((F p.1 ^ 2 * k p.2 + F p.1 ^ 2 * k (p.1 - p.2)) / 4 +
    G p.2 ^ 2 * H (p.1 - p.2) ^ 2 / 2) ∂(volume.prod volume) = _
  rw [integral_add i12 i3', integral_div, integral_div, integral_add i1 i2, e1, e2, e3]
  ring

/-! ### O integrando trilinear -/

/-- `w₁ ‖f‖ ∈ L²`. -/
def H1 (f : E3 → C3) : Prop := Integrable fun ξ => (w 1 ξ * ‖f ξ‖) ^ 2

/-- `∫ (w₁ ‖f‖)²`. -/
noncomputable def nH1 (f : E3 → C3) : ℝ := ∫ ξ, (w 1 ξ * ‖f ξ‖) ^ 2

theorem nH1_nonneg (f : E3 → C3) : 0 ≤ nH1 f := integral_nonneg fun _ => sq_nonneg _

/-- O integrando trilinear `‖ξ‖ ‖f(ξ)‖ ‖g(η)‖ ‖h(ξ − η)‖`. -/
noncomputable def Psi (f g h : E3 → C3) (p : E3 × E3) : ℝ :=
  ‖p.1‖ * ‖f p.1‖ * (‖g p.2‖ * ‖h (p.1 - p.2)‖)

theorem Psi_nonneg (f g h : E3 → C3) (p : E3 × E3) : 0 ≤ Psi f g h p := by
  unfold Psi; positivity

theorem measurable_Psi {f g h : E3 → C3} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) : Measurable (Psi f g h) := by
  unfold Psi
  exact ((measurable_fst.norm.mul (hf.comp measurable_fst).norm).mul
    ((hg.comp measurable_snd).norm.mul (hh.comp (measurable_fst.sub measurable_snd)).norm))

/-- **O integrando trilinear é integrável no produto** para `f, g, h ∈ H¹`. -/
theorem integrable_Psi {f g h : E3 → C3} (hfm : Measurable f) (hgm : Measurable g)
    (hhm : Measurable h) (hf : H1 f) (hg : H1 g) (hh : H1 h) :
    Integrable (Psi f g h) (volume.prod volume) ∧
      ∫ p, Psi f g h p ∂(volume.prod volume) ≤ (I4 * nH1 f + nH1 g * nH1 h) / 2 := by
  have hw1m : Measurable fun ξ : E3 => w 1 ξ := by
    unfold w; exact ((continuous_const.add continuous_norm).pow 1).measurable
  obtain ⟨hT, hTb⟩ := tri_bound (F := fun ξ => w 1 ξ * ‖f ξ‖) (G := fun ξ => w 1 ξ * ‖g ξ‖)
    (H := fun ξ => w 1 ξ * ‖h ξ‖) (hw1m.mul hfm.norm) (hw1m.mul hgm.norm) (hw1m.mul hhm.norm)
    (fun ξ => mul_nonneg (w_pos 1 ξ).le (norm_nonneg _))
    (fun ξ => mul_nonneg (w_pos 1 ξ).le (norm_nonneg _))
    (fun ξ => mul_nonneg (w_pos 1 ξ).le (norm_nonneg _)) hf hg hh
  have hpt : ∀ p : E3 × E3, Psi f g h p ≤
      w 1 p.1 * ‖f p.1‖ * (w 1 p.2 * ‖g p.2‖) * (w 1 (p.1 - p.2) * ‖h (p.1 - p.2)‖) *
        ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹) := by
    intro p
    have e : w 1 p.1 * ‖f p.1‖ * (w 1 p.2 * ‖g p.2‖) * (w 1 (p.1 - p.2) * ‖h (p.1 - p.2)‖) *
        ((w 1 p.2)⁻¹ * (w 1 (p.1 - p.2))⁻¹) =
        w 1 p.1 * ‖f p.1‖ * (‖g p.2‖ * ‖h (p.1 - p.2)‖) := by
      have h1 := (w_pos 1 p.2).ne'
      have h2 := (w_pos 1 (p.1 - p.2)).ne'
      field_simp
    rw [e]
    unfold Psi
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (norm_le_w1 p.1) (norm_nonneg _))
      (by positivity)
  have hint : Integrable (Psi f g h) (volume.prod volume) :=
    hT.mono' (measurable_Psi hfm hgm hhm).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (Psi_nonneg f g h p)]; exact hpt p)
  refine ⟨hint, (integral_mono hint hT hpt).trans ?_⟩
  unfold nH1
  exact hTb

/-! ### O termo não linear em `L²` -/

theorem aesm_sub_left {g : E3 → C3} (hg : AEStronglyMeasurable g volume) (ξ : E3) :
    AEStronglyMeasurable (fun η => g (ξ - η)) volume :=
  hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)

theorem integrable_Nl_L2 {f g : E3 → C3} (hf : MemLp f 2) (hg : MemLp g 2) (ξ : E3) :
    Integrable fun η => ⟪cpx ξ, f η⟫_ℂ • g (ξ - η) := by
  have hm : AEStronglyMeasurable (fun η => ⟪cpx ξ, f η⟫_ℂ • g (ξ - η)) volume :=
    (AEStronglyMeasurable.inner (𝕜 := ℂ) (aestronglyMeasurable_const (b := cpx ξ))
      hf.aestronglyMeasurable).smul (aesm_sub_left hg.aestronglyMeasurable ξ)
  refine ((integrable_norm_mul_sub hf hg ξ).const_mul ‖ξ‖).mono' hm
    (Eventually.of_forall fun η => ?_)
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_inner_cpx_le ξ _) (norm_nonneg _)

theorem measurable_Nl {f g : E3 → C3} (hf : Measurable f) (hg : Measurable g) :
    Measurable (Nl f g) := by
  have hm : StronglyMeasurable fun p : E3 × E3 => ⟪cpx p.1, f p.2⟫_ℂ • g (p.1 - p.2) :=
    ((Measurable.inner (𝕜 := ℂ) (ATK.NSPicard.continuous_cpx.measurable.comp measurable_fst)
      (hf.comp measurable_snd)).smul (hg.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  have h : Measurable fun ξ => ∫ η, ⟪cpx ξ, f η⟫_ℂ • g (ξ - η) :=
    (hm.integral_prod_right' (ν := (volume : Measure E3))).measurable
  unfold Nl
  exact h.const_smul (((2 * π : ℝ) * Complex.I : ℂ))

/-- `N(f, f) − N(g, g) = N(f − g, f) + N(g, f − g)`. -/
theorem Nl_split {f g : E3 → C3} (hf : MemLp f 2) (hg : MemLp g 2) (ξ : E3) :
    Nl f f ξ - Nl g g ξ = Nl (f - g) f ξ + Nl g (f - g) ξ := by
  have hd : MemLp (f - g) 2 := hf.sub hg
  unfold Nl
  rw [← smul_sub, ← smul_add, ← integral_sub (integrable_Nl_L2 hf hf ξ) (integrable_Nl_L2 hg hg ξ),
    ← integral_add (integrable_Nl_L2 hd hf ξ) (integrable_Nl_L2 hg hd ξ)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Pi.sub_apply, inner_sub_right, sub_smul, smul_sub]
  abel

theorem norm_Nl_le_L2 {f : E3 → C3} (hf : MemLp f 2) (ξ : E3) :
    ‖Nl f f ξ‖ ≤ 2 * π * ‖ξ‖ * ∫ η, ‖f η‖ ^ 2 := by
  refine (norm_Nl_le ξ (integrable_norm_mul_sub hf hf ξ)).trans
    (mul_le_mul_of_nonneg_left ((integral_norm_mul_sub_le hf hf ξ).trans (le_of_eq ?_))
      (by positivity))
  exact Real.mul_self_sqrt (integral_nonneg fun _ => sq_nonneg _)

/-- `∫ η, Psi f g h (ξ, η) = ‖ξ‖ ‖f ξ‖ ∫ ‖g(η)‖ ‖h(ξ − η)‖`. -/
theorem integral_Psi_right (f g h : E3 → C3) (ξ : E3) :
    ∫ η, Psi f g h (ξ, η) = ‖ξ‖ * ‖f ξ‖ * ∫ η, ‖g η‖ * ‖h (ξ - η)‖ := by
  unfold Psi
  exact integral_const_mul (‖ξ‖ * ‖f ξ‖) (fun η => ‖g η‖ * ‖h (ξ - η)‖)

theorem norm_mul_Nl_le {d f g : E3 → C3} (hf : MemLp f 2) (hg : MemLp g 2) (ξ : E3) :
    ‖d ξ‖ * ‖Nl f g ξ‖ ≤ 2 * π * ∫ η, Psi d f g (ξ, η) := by
  rw [integral_Psi_right]
  calc ‖d ξ‖ * ‖Nl f g ξ‖ ≤ ‖d ξ‖ * (2 * π * ‖ξ‖ * ∫ η, ‖f η‖ * ‖g (ξ - η)‖) :=
        mul_le_mul_of_nonneg_left (norm_Nl_le ξ (integrable_norm_mul_sub hf hg ξ)) (norm_nonneg _)
    _ = 2 * π * (‖ξ‖ * ‖d ξ‖ * ∫ η, ‖f η‖ * ‖g (ξ - η)‖) := by ring

theorem norm_inner_Nl_le {d f g : E3 → C3} (hf : MemLp f 2) (hg : MemLp g 2) (ξ : E3) :
    ‖⟪d ξ, Nl f g ξ⟫_ℂ‖ ≤ 2 * π * ∫ η, Psi d f g (ξ, η) :=
  (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (norm_mul_Nl_le hf hg ξ)

theorem integrable_inner_Nl {d f g : E3 → C3} (hdm : Measurable d) (hfm : Measurable f)
    (hgm : Measurable g) (hf : MemLp f 2) (hg : MemLp g 2) (hP : Integrable (Psi d f g)
      (volume.prod volume)) : Integrable fun ξ => ⟪d ξ, Nl f g ξ⟫_ℂ :=
  (hP.integral_prod_left.const_mul (2 * π)).mono'
    (Measurable.inner (𝕜 := ℂ) hdm (measurable_Nl hfm hgm)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => norm_inner_Nl_le hf hg ξ)

/-! ### Cancelamento -/

/-- `⟪ξ, b(η)⟫ ⟪d(ξ), d(ξ − η)⟫`. -/
noncomputable def Ftri2 (b d : E3 → C3) (p : E3 × E3) : ℂ :=
  ⟪cpx p.1, b p.2⟫_ℂ * ⟪d p.1, d (p.1 - p.2)⟫_ℂ

/-- Para cada `η` com `⟪η, b(η)⟫ = 0`, a integral em `ξ` é nula (simetria `ξ ↦ η − ξ`). -/
theorem integral_Ftri2_eq_zero {b d : E3 → C3} (hdh : Herm d) (η : E3)
    (hbη : ⟪cpx η, b η⟫_ℂ = 0) : ∫ ξ, Ftri2 b d (ξ, η) = 0 := by
  set G : E3 → ℂ := fun p => ⟪cpx p, b η⟫_ℂ * ⟪d (p + η), d p⟫_ℂ with hG
  have h1 : ∀ ξ, Ftri2 b d (ξ, η) = G (ξ - η) := by
    intro ξ
    simp only [Ftri2, hG, sub_add_cancel, ATK.NSEnergia.cpx_sub, inner_sub_left, hbη, sub_zero]
  have h2 : ∀ ξ, G (-ξ) = -Ftri2 b d (ξ, η) := by
    intro ξ
    have e1 : -ξ + η = -(ξ - η) := by abel
    simp only [hG, Ftri2, cpx_neg, inner_neg_left]
    rw [e1, hdh, hdh ξ, ATK.NSEnergia.inner_cj3_cj3]
    ring
  have h3 : ∫ ξ, Ftri2 b d (ξ, η) = -∫ ξ, Ftri2 b d (ξ, η) := by
    calc ∫ ξ, Ftri2 b d (ξ, η) = ∫ ξ, G (ξ - η) := integral_congr_ae (Eventually.of_forall h1)
      _ = ∫ p, G p := integral_sub_right_eq_self G η
      _ = ∫ ξ, G (-ξ) := (integral_neg_eq_self G volume).symm
      _ = ∫ ξ, -Ftri2 b d (ξ, η) := integral_congr_ae (Eventually.of_forall h2)
      _ = -∫ ξ, Ftri2 b d (ξ, η) := integral_neg _
  exact self_eq_neg.mp h3

theorem inner_Nl_eq {b d : E3 → C3} (hb : MemLp b 2) (hd : MemLp d 2) (ξ : E3) :
    ⟪d ξ, Nl b d ξ⟫_ℂ = ((2 * π : ℝ) * Complex.I : ℂ) * ∫ η, Ftri2 b d (ξ, η) := by
  unfold Nl
  rw [inner_smul_right, ← integral_inner (integrable_Nl_L2 hb hd ξ)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Ftri2, inner_smul_right]

/-- **Cancelamento**: `∫ ⟪d, N(b, d)⟫ = 0` para `b` de divergência nula e `d` hermitiana. -/
theorem integral_inner_Nl_cancel {b d : E3 → C3} (hbm : Measurable b) (hdm : Measurable d)
    (hb : MemLp b 2) (hd : MemLp d 2) (hbd : ∀ η, ⟪cpx η, b η⟫_ℂ = 0) (hdh : Herm d)
    (hint : Integrable (Psi d b d) (volume.prod volume)) :
    ∫ ξ, ⟪d ξ, Nl b d ξ⟫_ℂ = 0 := by
  have hF : Integrable (Ftri2 b d) (volume.prod volume) := by
    refine hint.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((Measurable.inner (𝕜 := ℂ) (ATK.NSPicard.continuous_cpx.measurable.comp measurable_fst)
        (hbm.comp measurable_snd)).mul (Measurable.inner (𝕜 := ℂ) (hdm.comp measurable_fst)
          (hdm.comp (measurable_fst.sub measurable_snd)))).aestronglyMeasurable
    · unfold Ftri2 Psi
      rw [norm_mul]
      calc ‖⟪cpx p.1, b p.2⟫_ℂ‖ * ‖⟪d p.1, d (p.1 - p.2)⟫_ℂ‖
          ≤ (‖p.1‖ * ‖b p.2‖) * (‖d p.1‖ * ‖d (p.1 - p.2)‖) :=
            mul_le_mul (norm_inner_cpx_le _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
              (by positivity)
        _ = ‖p.1‖ * ‖d p.1‖ * (‖b p.2‖ * ‖d (p.1 - p.2)‖) := by ring
  have e : (fun ξ => ⟪d ξ, Nl b d ξ⟫_ℂ) =
      fun ξ => ((2 * π : ℝ) * Complex.I : ℂ) * ∫ η, Ftri2 b d (ξ, η) :=
    funext fun ξ => inner_Nl_eq hb hd ξ
  rw [e, integral_const_mul]
  have hswap : ∫ ξ, ∫ η, Ftri2 b d (ξ, η) = ∫ η, ∫ ξ, Ftri2 b d (ξ, η) :=
    integral_integral_swap (f := fun ξ η => Ftri2 b d (ξ, η)) hF
  rw [hswap]
  have h0 : (fun η => ∫ ξ, Ftri2 b d (ξ, η)) = fun _ => (0 : ℂ) :=
    funext fun η => integral_Ftri2_eq_zero hdh η (hbd η)
  rw [h0, integral_zero, mul_zero]

/-! ### A estimativa do termo `N(d, f)` -/

theorem w4_inv_le_one (ζ : E3) : (w 4 ζ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_w 4 ζ)

/-- **`|∫ ⟪d, N(d, f)⟫| ≤ 2π A I₄ ‖d‖²`** para `d` de divergência nula e `‖f‖ ≤ A w₅⁻¹`. -/
theorem norm_integral_inner_Nl_le {d f : E3 → C3} (hdm : Measurable d) (hd : MemLp d 2)
    (hdd : ∀ η, ⟪cpx η, d η⟫_ℂ = 0) {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ ζ, ‖f ζ‖ ≤ A * (w 5 ζ)⁻¹) :
    ‖∫ ξ, ⟪d ξ, Nl d f ξ⟫_ℂ‖ ≤ 2 * π * (A * I4 * ∫ ξ, ‖d ξ‖ ^ 2) := by
  set k : E3 → ℝ := fun ζ => (w 4 ζ)⁻¹ with hk
  have hkm : Measurable k := measurable_w_inv 4
  have hki : Integrable k := integrable_w_inv
  have hk0 : ∀ ζ, 0 ≤ k ζ := fun ζ => (inv_pos.mpr (w_pos 4 ζ)).le
  have hk1 : ∀ ζ, k ζ ≤ 1 := w4_inv_le_one
  have hd2 : Integrable fun ξ => ‖d ξ‖ ^ 2 := integrable_sq_norm_of_memLp hd
  have hd2m : Measurable fun ξ => ‖d ξ‖ ^ 2 := hdm.norm.pow_const 2
  set P : E3 × E3 → ℝ := fun p => ‖d p.1‖ * (‖d p.2‖ * (A * k (p.1 - p.2))) with hP
  have i1 := integrable_fst_mul_sub hd2m hkm hd2 hki
  have i2 := integrable_snd_mul_sub hd2m hkm hd2 hki
  have i12 : Integrable (fun p : E3 × E3 =>
      A / 2 * (‖d p.1‖ ^ 2 * k (p.1 - p.2) + ‖d p.2‖ ^ 2 * k (p.1 - p.2)))
      (volume.prod volume) := (i1.add i2).const_mul (A / 2)
  have hPle : ∀ p : E3 × E3,
      P p ≤ A / 2 * (‖d p.1‖ ^ 2 * k (p.1 - p.2) + ‖d p.2‖ ^ 2 * k (p.1 - p.2)) := by
    intro p
    have h2 := two_mul_le_add_sq ‖d p.1‖ ‖d p.2‖
    have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hA0 (hk0 (p.1 - p.2)))
    show ‖d p.1‖ * (‖d p.2‖ * (A * k (p.1 - p.2))) ≤ _
    have e1 : ‖d p.1‖ * (‖d p.2‖ * (A * k (p.1 - p.2))) =
        2 * ‖d p.1‖ * ‖d p.2‖ * (A * k (p.1 - p.2)) / 2 := by ring
    have e2 : A / 2 * (‖d p.1‖ ^ 2 * k (p.1 - p.2) + ‖d p.2‖ ^ 2 * k (p.1 - p.2)) =
        (‖d p.1‖ ^ 2 + ‖d p.2‖ ^ 2) * (A * k (p.1 - p.2)) / 2 := by ring
    rw [e1, e2]
    linarith
  have hP0 : ∀ p : E3 × E3, 0 ≤ P p := fun p => by
    show 0 ≤ ‖d p.1‖ * (‖d p.2‖ * (A * k (p.1 - p.2)))
    have := hk0 (p.1 - p.2); positivity
  have hPm : Measurable P :=
    (hdm.comp measurable_fst).norm.mul ((hdm.comp measurable_snd).norm.mul
      (measurable_const.mul (hkm.comp (measurable_fst.sub measurable_snd))))
  have hPi : Integrable P (volume.prod volume) :=
    i12.mono' hPm.aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (hP0 p)]; exact hPle p)
  have hPint : ∫ p, P p ∂(volume.prod volume) ≤ A * I4 * ∫ ξ, ‖d ξ‖ ^ 2 := by
    refine (integral_mono hPi i12 hPle).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add i1 i2, integral_fst_mul_sub hd2m hkm hd2 hki,
      integral_snd_mul_sub hd2m hkm hd2 hki]
    show A / 2 * ((∫ ξ, ‖d ξ‖ ^ 2) * I4 + (∫ ξ, ‖d ξ‖ ^ 2) * I4) = _
    ring
  -- integrabilidade em `η` para cada `ξ`
  have hrow : ∀ ξ, Integrable fun η => ‖d η‖ * (A * k (ξ - η)) := by
    intro ξ
    refine ((hd2.add (hki.comp_sub_left ξ)).const_mul (A / 2)).mono'
      ((hdm.norm.mul (measurable_const.mul
        (hkm.comp (measurable_const.sub measurable_id)))).aestronglyMeasurable)
      (Eventually.of_forall fun η => ?_)
    have hk' := hk0 (ξ - η)
    have hk1' := hk1 (ξ - η)
    rw [Real.norm_of_nonneg (by positivity)]
    have h2 := two_mul_le_add_sq ‖d η‖ (k (ξ - η))
    have h4 : k (ξ - η) ^ 2 ≤ k (ξ - η) := by nlinarith
    show ‖d η‖ * (A * k (ξ - η)) ≤ A / 2 * (‖d η‖ ^ 2 + k (ξ - η))
    have h5 : 2 * ‖d η‖ * k (ξ - η) ≤ ‖d η‖ ^ 2 + k (ξ - η) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 hA0
    linarith
  -- cota pontual
  have hpt : ∀ ξ, ‖⟪d ξ, Nl d f ξ⟫_ℂ‖ ≤ 2 * π * ∫ η, P (ξ, η) := by
    intro ξ
    have eP : ∫ η, P (ξ, η) = ‖d ξ‖ * ∫ η, ‖d η‖ * (A * k (ξ - η)) := by
      show ∫ η, ‖d ξ‖ * (‖d η‖ * (A * k (ξ - η))) = _
      exact integral_const_mul ‖d ξ‖ (fun η => ‖d η‖ * (A * k (ξ - η)))
    rw [eP]
    have hN : ‖Nl d f ξ‖ ≤ 2 * π * ∫ η, ‖d η‖ * (A * k (ξ - η)) := by
      unfold Nl
      rw [norm_smul]
      have hI : ‖((2 * π : ℝ) * Complex.I : ℂ)‖ = 2 * π := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [hI]
      refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
        (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hrow ξ)
          (Eventually.of_forall fun η => ?_))) (by positivity)
      have e1 : ⟪cpx ξ, d η⟫_ℂ = ⟪cpx (ξ - η), d η⟫_ℂ := by
        rw [ATK.NSEnergia.cpx_sub, inner_sub_left, hdd η, sub_zero]
      dsimp only
      rw [norm_smul, e1]
      calc ‖⟪cpx (ξ - η), d η⟫_ℂ‖ * ‖f (ξ - η)‖ ≤ (‖ξ - η‖ * ‖d η‖) * (A * (w 5 (ξ - η))⁻¹) :=
            mul_le_mul (norm_inner_cpx_le _ _) (hA _) (norm_nonneg _) (by positivity)
        _ = ‖d η‖ * (A * (‖ξ - η‖ * (w 5 (ξ - η))⁻¹)) := by ring
        _ ≤ ‖d η‖ * (A * k (ξ - η)) := by
            gcongr
            exact ATK.NSEnergia.norm_mul_w5_le _
    calc ‖⟪d ξ, Nl d f ξ⟫_ℂ‖ ≤ ‖d ξ‖ * ‖Nl d f ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖d ξ‖ * (2 * π * ∫ η, ‖d η‖ * (A * k (ξ - η))) :=
          mul_le_mul_of_nonneg_left hN (norm_nonneg _)
      _ = 2 * π * (‖d ξ‖ * ∫ η, ‖d η‖ * (A * k (ξ - η))) := by ring
  refine (norm_integral_le_of_norm_le (hPi.integral_prod_left.const_mul (2 * π))
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, ← integral_prod _ hPi]
  exact mul_le_mul_of_nonneg_left hPint (by positivity)

/-! ### Normas `H¹` -/

theorem measurable_w (m : ℕ) : Measurable fun ξ : E3 => w m ξ := by
  unfold w
  exact ((continuous_const.add continuous_norm).pow m).measurable

theorem H1_of_bound {f : E3 → C3} (hfm : Measurable f) {A : ℝ} (hA : ∀ ζ, ‖f ζ‖ ≤ A * (w 5 ζ)⁻¹) :
    H1 f ∧ nH1 f ≤ A ^ 2 * I4 := by
  have hpt : ∀ ξ, (w 1 ξ * ‖f ξ‖) ^ 2 ≤ A ^ 2 * (w 4 ξ)⁻¹ := by
    intro ξ
    have h5 : w 5 ξ = w 4 ξ * w 1 ξ := w_add 4 1 ξ
    have hw1 := (w_pos 1 ξ).ne'
    have hw4 := (w_pos 4 ξ).ne'
    have h0 : 0 ≤ w 1 ξ * ‖f ξ‖ := mul_nonneg (w_pos 1 ξ).le (norm_nonneg _)
    have h1 : w 1 ξ * ‖f ξ‖ ≤ |A| * (w 4 ξ)⁻¹ := by
      calc w 1 ξ * ‖f ξ‖ ≤ w 1 ξ * (A * (w 5 ξ)⁻¹) :=
            mul_le_mul_of_nonneg_left (hA ξ) (w_pos 1 ξ).le
        _ = A * (w 4 ξ)⁻¹ := by rw [h5]; field_simp
        _ ≤ |A| * (w 4 ξ)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_abs_self A) (inv_pos.mpr (w_pos 4 ξ)).le
    have hk := w4_inv_le_one ξ
    have hk0 := (inv_pos.mpr (w_pos 4 ξ)).le
    calc (w 1 ξ * ‖f ξ‖) ^ 2 ≤ (|A| * (w 4 ξ)⁻¹) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = A ^ 2 * ((w 4 ξ)⁻¹ * (w 4 ξ)⁻¹) := by rw [mul_pow, sq_abs]; ring
      _ ≤ A ^ 2 * (w 4 ξ)⁻¹ :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hk0 hk) (sq_nonneg A)
  have hi : Integrable fun ξ => A ^ 2 * (w 4 ξ)⁻¹ := integrable_w_inv.const_mul _
  have hm : Measurable fun ξ => (w 1 ξ * ‖f ξ‖) ^ 2 :=
    ((measurable_w 1).mul hfm.norm).pow_const 2
  have hH : H1 f := hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt ξ)
  refine ⟨hH, (integral_mono hH hi hpt).trans (le_of_eq ?_)⟩
  rw [integral_const_mul]
  rfl

theorem H1_sub {f g : E3 → C3} (hfm : Measurable f) (hgm : Measurable g) (hf : H1 f)
    (hg : H1 g) : H1 (f - g) ∧ nH1 (f - g) ≤ 2 * nH1 f + 2 * nH1 g := by
  have hpt : ∀ ξ, (w 1 ξ * ‖(f - g) ξ‖) ^ 2 ≤
      2 * (w 1 ξ * ‖f ξ‖) ^ 2 + 2 * (w 1 ξ * ‖g ξ‖) ^ 2 := by
    intro ξ
    have hw := (w_pos 1 ξ).le
    have h1 : w 1 ξ * ‖(f - g) ξ‖ ≤ w 1 ξ * ‖f ξ‖ + w 1 ξ * ‖g ξ‖ := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hw
    have h0 : 0 ≤ w 1 ξ * ‖(f - g) ξ‖ := mul_nonneg hw (norm_nonneg _)
    nlinarith [sq_nonneg (w 1 ξ * ‖f ξ‖ - w 1 ξ * ‖g ξ‖)]
  have hi : Integrable fun ξ => 2 * (w 1 ξ * ‖f ξ‖) ^ 2 + 2 * (w 1 ξ * ‖g ξ‖) ^ 2 :=
    (hf.const_mul 2).add (hg.const_mul 2)
  have hm : Measurable fun ξ => (w 1 ξ * ‖(f - g) ξ‖) ^ 2 :=
    ((measurable_w 1).mul (hfm.sub hgm).norm).pow_const 2
  have hH : H1 (f - g) := hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt ξ)
  refine ⟨hH, (integral_mono hH hi hpt).trans (le_of_eq ?_)⟩
  rw [integral_add (hf.const_mul 2) (hg.const_mul 2), integral_const_mul, integral_const_mul]
  rfl

/-! ### O integrando da identidade de energia -/

/-- `φ(ξ) = 2 Re⟪(f − g)(ξ), −P(ξ)(N(f, f) − N(g, g))(ξ)⟫`. -/
noncomputable def phiE (f g : E3 → C3) (ξ : E3) : ℝ :=
  2 * (⟪f ξ - g ξ, -ATK.NSFourierBase.lp ξ (Nl f f ξ - Nl g g ξ)⟫_ℂ).re

theorem measurable_phiE {f g : E3 → C3} (hfm : Measurable f) (hgm : Measurable g) :
    Measurable (phiE f g) := by
  have h1 : Measurable fun ξ => ATK.NSFourierBase.lp ξ (Nl f f ξ - Nl g g ξ) :=
    ATK.NSIdent.measurable_lp.comp
      (measurable_id.prodMk ((measurable_Nl hfm hfm).sub (measurable_Nl hgm hgm)))
  unfold phiE
  exact measurable_const.mul (Complex.measurable_re.comp
    (Measurable.inner (𝕜 := ℂ) (hfm.sub hgm) h1.neg))

/-- **O integrando de energia**: integrável, com norma `L¹` controlada pelas normas `H¹`, e
`∫ φ ≤ 4π A I₄ ‖f − g‖²`. -/
theorem phiE_props {f g : E3 → C3} (hfm : Measurable f) (hgm : Measurable g) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ ζ, ‖f ζ‖ ≤ A * (w 5 ζ)⁻¹) (hfd : ∀ ξ, ⟪cpx ξ, f ξ⟫_ℂ = 0)
    (hfh : Herm f) (hg : MemLp g 2) (hgH : H1 g) (hgd : ∀ ξ, ⟪cpx ξ, g ξ⟫_ℂ = 0)
    (hgh : Herm g) :
    Integrable (phiE f g) ∧
      ∫ ξ, ‖phiE f g ξ‖ ≤ 2 * π * (2 * I4 * nH1 (f - g) + nH1 f ^ 2 + nH1 g ^ 2) ∧
      ∫ ξ, phiE f g ξ ≤ 4 * π * (A * I4 * ∫ ξ, ‖f ξ - g ξ‖ ^ 2) := by
  have hf2 : MemLp f 2 := ATK.NSPlancherel.memLp_two_of_bound hfm.aestronglyMeasurable
    (fun ζ => (hA ζ).trans (mul_le_mul_of_nonneg_left (w_inv_anti (by norm_num) ζ) hA0))
  have hfH : H1 f := (H1_of_bound hfm hA).1
  have hdm : Measurable (f - g) := hfm.sub hgm
  have hdH : H1 (f - g) := (H1_sub hfm hgm hfH hgH).1
  have hd2 : MemLp (f - g) 2 := hf2.sub hg
  have hdd : ∀ ξ, ⟪cpx ξ, (f - g) ξ⟫_ℂ = 0 := fun ξ => by
    rw [Pi.sub_apply, inner_sub_right, hfd, hgd, sub_zero]
  have hdh : Herm (f - g) := fun ξ => by
    rw [Pi.sub_apply, Pi.sub_apply, hfh ξ, hgh ξ, cj3_sub]
  obtain ⟨P1, B1⟩ := integrable_Psi hdm hfm hfm hdH hfH hfH
  obtain ⟨P2, B2⟩ := integrable_Psi hdm hgm hgm hdH hgH hgH
  obtain ⟨P3, -⟩ := integrable_Psi hdm hdm hfm hdH hdH hfH
  obtain ⟨P4, -⟩ := integrable_Psi hdm hgm hdm hdH hgH hdH
  -- cota pontual
  have hpt : ∀ ξ, ‖phiE f g ξ‖ ≤
      4 * π * ((∫ η, Psi (f - g) f f (ξ, η)) + ∫ η, Psi (f - g) g g (ξ, η)) := by
    intro ξ
    have h1 := norm_mul_Nl_le (d := f - g) hf2 hf2 ξ
    have h2 := norm_mul_Nl_le (d := f - g) hg hg ξ
    have h3 : ‖⟪f ξ - g ξ, -ATK.NSFourierBase.lp ξ (Nl f f ξ - Nl g g ξ)⟫_ℂ‖ ≤
        ‖(f - g) ξ‖ * (‖Nl f f ξ‖ + ‖Nl g g ξ‖) := by
      refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_left ((norm_lp_le _ _).trans (norm_sub_le _ _)) (norm_nonneg _)
    unfold phiE
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * |(⟪f ξ - g ξ, -ATK.NSFourierBase.lp ξ (Nl f f ξ - Nl g g ξ)⟫_ℂ).re|
        ≤ 2 * ‖⟪f ξ - g ξ, -ATK.NSFourierBase.lp ξ (Nl f f ξ - Nl g g ξ)⟫_ℂ‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
      _ ≤ 2 * (‖(f - g) ξ‖ * ‖Nl f f ξ‖ + ‖(f - g) ξ‖ * ‖Nl g g ξ‖) := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ 2 * (2 * π * (∫ η, Psi (f - g) f f (ξ, η)) + 2 * π * ∫ η, Psi (f - g) g g (ξ, η)) := by
          gcongr
      _ = 4 * π * ((∫ η, Psi (f - g) f f (ξ, η)) + ∫ η, Psi (f - g) g g (ξ, η)) := by ring
  have hdom : Integrable fun ξ =>
      4 * π * ((∫ η, Psi (f - g) f f (ξ, η)) + ∫ η, Psi (f - g) g g (ξ, η)) :=
    (P1.integral_prod_left.add P2.integral_prod_left).const_mul (4 * π)
  have hint : Integrable (phiE f g) :=
    hdom.mono' (measurable_phiE hfm hgm).aestronglyMeasurable (Eventually.of_forall hpt)
  refine ⟨hint, ?_, ?_⟩
  · -- a norma `L¹`
    refine (integral_mono hint.norm hdom hpt).trans ?_
    rw [integral_const_mul, integral_add P1.integral_prod_left P2.integral_prod_left,
      ← integral_prod _ P1, ← integral_prod _ P2]
    have hπ : 0 ≤ 4 * π := by positivity
    calc 4 * π * ((∫ p, Psi (f - g) f f p ∂(volume.prod volume)) +
          ∫ p, Psi (f - g) g g p ∂(volume.prod volume))
        ≤ 4 * π * ((I4 * nH1 (f - g) + nH1 f * nH1 f) / 2 +
          (I4 * nH1 (f - g) + nH1 g * nH1 g) / 2) :=
          mul_le_mul_of_nonneg_left (add_le_add B1 B2) hπ
      _ = 2 * π * (2 * I4 * nH1 (f - g) + nH1 f ^ 2 + nH1 g ^ 2) := by ring
  · -- a integral
    have hX := integrable_inner_Nl hdm hdm hfm hd2 hf2 P3
    have hY := integrable_inner_Nl hdm hgm hdm hg hd2 P4
    have hY0 : ∫ ξ, ⟪(f - g) ξ, Nl g (f - g) ξ⟫_ℂ = 0 :=
      integral_inner_Nl_cancel hgm hdm hg hd2 hgd hdh P4
    have hXb := norm_integral_inner_Nl_le hdm hd2 hdd hA0 hA
    have e : ∀ ξ, phiE f g ξ = -(2 * RCLike.re (⟪(f - g) ξ, Nl (f - g) f ξ⟫_ℂ +
        ⟪(f - g) ξ, Nl g (f - g) ξ⟫_ℂ)) := by
      intro ξ
      have hdξ : ⟪cpx ξ, f ξ - g ξ⟫_ℂ = 0 := hdd ξ
      unfold phiE
      rw [inner_neg_right, ATK.NSEnergia.inner_lp_of_div hdξ, Nl_split hf2 hg, inner_add_right]
      simp only [Complex.neg_re, RCLike.re_to_complex, Pi.sub_apply]
      ring
    have hXY : Integrable fun ξ => ⟪(f - g) ξ, Nl (f - g) f ξ⟫_ℂ +
        ⟪(f - g) ξ, Nl g (f - g) ξ⟫_ℂ := hX.add hY
    rw [integral_congr_ae (Eventually.of_forall e), integral_neg, integral_const_mul,
      integral_re hXY, integral_add hX hY, hY0, add_zero]
    have h1 := RCLike.abs_re_le_norm (∫ ξ, ⟪(f - g) ξ, Nl (f - g) f ξ⟫_ℂ)
    have h2 := neg_abs_le (RCLike.re (∫ ξ, ⟪(f - g) ξ, Nl (f - g) f ξ⟫_ℂ))
    have h3 : ∫ ξ, ‖(f - g) ξ‖ ^ 2 = ∫ ξ, ‖f ξ - g ξ‖ ^ 2 := rfl
    rw [h3] at hXb
    nlinarith [hXb, h1, h2]

end ATK.NSTrilinear

#print axioms ATK.NSTrilinear.integrable_fst_mul_sub
#print axioms ATK.NSTrilinear.integral_fst_mul_sub
#print axioms ATK.NSTrilinear.integrable_snd_mul_sub
#print axioms ATK.NSTrilinear.integral_snd_mul_sub
#print axioms ATK.NSTrilinear.w1_inv_pow4
#print axioms ATK.NSTrilinear.measurable_w_inv
#print axioms ATK.NSTrilinear.tri_pt
#print axioms ATK.NSTrilinear.tri_bound
#print axioms ATK.NSTrilinear.nH1_nonneg
#print axioms ATK.NSTrilinear.Psi_nonneg
#print axioms ATK.NSTrilinear.measurable_Psi
#print axioms ATK.NSTrilinear.integrable_Psi
#print axioms ATK.NSTrilinear.aesm_sub_left
#print axioms ATK.NSTrilinear.integrable_Nl_L2
#print axioms ATK.NSTrilinear.measurable_Nl
#print axioms ATK.NSTrilinear.Nl_split
#print axioms ATK.NSTrilinear.norm_Nl_le_L2
#print axioms ATK.NSTrilinear.integral_Psi_right
#print axioms ATK.NSTrilinear.norm_mul_Nl_le
#print axioms ATK.NSTrilinear.norm_inner_Nl_le
#print axioms ATK.NSTrilinear.integrable_inner_Nl
#print axioms ATK.NSTrilinear.integral_Ftri2_eq_zero
#print axioms ATK.NSTrilinear.inner_Nl_eq
#print axioms ATK.NSTrilinear.integral_inner_Nl_cancel
#print axioms ATK.NSTrilinear.w4_inv_le_one
#print axioms ATK.NSTrilinear.norm_integral_inner_Nl_le
#print axioms ATK.NSTrilinear.measurable_w
#print axioms ATK.NSTrilinear.H1_of_bound
#print axioms ATK.NSTrilinear.H1_sub
#print axioms ATK.NSTrilinear.measurable_phiE
#print axioms ATK.NSTrilinear.phiE_props
