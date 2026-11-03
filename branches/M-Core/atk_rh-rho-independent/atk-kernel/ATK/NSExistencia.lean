import ATK.NSReducao
import ATK.NSPressao
import ATK.NSDado
import ATK.NSPlancherel

/-!
# ATK — **Existência local** de soluções suaves de Navier–Stokes em `ℝ³` (Leray; Kato–Fujita)

Camada 9 do ataque a B3: o primeiro dos quatro enunciados clássicos de `ATK.NSReducao`,
`ExistenciaLocal`, **provado** no modelo genuíno `ATK.LigacaoNS.modeloNS`:

> todo dado admissível `(ν, u₀)` — `ν > 0`, `u₀` de Schwartz, `div u₀ = 0` — tem uma solução
> `(u, p)` **suave** em `ℝ³ × [0, T)`, `T > 0`, de `∂ₜu + (u·∇)u = νΔu − ∇p`, `div u = 0`,
> `u(·, 0) = u₀`, com energia `∫|u|²` e enstrofia `∫|∇u|²` finitas e limitadas em cada `[0, T']`.

Construção: `â₀ = 𝓕u₀` (`ATK.NSDado`); a solução branda hermitiana `a(t, ξ)` (`ATK.NSMild`,
`ATK.NSSimetria`); `u = Re ∫ e^{2πi⟪ξ,x⟫} a(t, ξ) dξ` e `p = Re ∫ e^{2πi⟪ξ,x⟫} p̂(t, ξ) dξ`, com
`p̂ = (i/2π)⟪ξ, Nl(a, a)⟫/‖ξ‖²` (`ATK.NSPressao`). A suavidade vem de `ATK.NSSuave` +
`ATK.NSTempo`; a equação, da identidade pontual em `ξ` (`identidade_amp`) e do teorema da
convolução (`ATK.NSFisico.conv_Vf`); a energia e a enstrofia, de Plancherel
(`ATK.NSPlancherel`).

Isto **não** prova B3 nem regularidade global: faltam a unicidade fraca–forte, a continuação
(critério de Leray) e a desigualdade de energia. **CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace ATK.NSExistencia

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard ATK.NSSuave ATK.NSTempo ATK.NSSimetria
  ATK.NSFisico ATK.NSPressao ATK.NSDado ATK.NSPlancherel

/-! ### A parte real -/

theorem norm_re3_le (v : C3) : ‖re3 v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  simp only [re3_apply, Real.norm_eq_abs, sq_abs]
  have := Complex.abs_re_le_norm (v k)
  nlinarith [abs_nonneg (v k).re, sq_abs (v k).re]

theorem re3_add (v w : C3) : re3 (v + w) = re3 v + re3 w := map_add re3L v w

theorem re3_sub (v w : C3) : re3 (v - w) = re3 v - re3 w := map_sub re3L v w

theorem re3_real_smul (r : ℝ) (v : C3) : re3 (r • v) = r • re3 v := map_smul re3L r v

theorem re3_sum {ι : Type*} (s : Finset ι) (f : ι → C3) : re3 (∑ i ∈ s, f i) = ∑ i ∈ s, re3 (f i) :=
  map_sum re3L f s

theorem re3_smul_of_im {c : ℂ} (hc : c.im = 0) (v : C3) : re3 (c • v) = c.re • re3 v := by
  ext k; simp [Complex.mul_re, hc]

theorem re3_smul_cpx (c : ℂ) (x : E3) : re3 (c • cpx x) = c.re • x := by
  ext k; simp [cpx, Complex.mul_re]

theorem re3_ofReal_smul (r : ℝ) (v : C3) : re3 ((r : ℂ) • v) = r • re3 v := by
  rw [re3_smul_of_im (Complex.ofReal_im r), Complex.ofReal_re]

/-- Projeção real escalar `v ↦ Re v₀`. -/
noncomputable def re0L : C3 →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) 0).restrictScalars ℝ)

theorem re0L_apply (v : C3) : re0L v = (v 0).re := rfl

/-- `dX` comuta com aplicações lineares contínuas. -/
theorem dX_clm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : C3 →L[ℝ] W)
    {g : E3 → C3} {y : E3} (hg : DifferentiableAt ℝ g y) (j : Fin 3) :
    dX j (fun z => L (g z)) y = L (dX j g y) := by
  unfold dX
  have h : HasFDerivAt (fun z => L (g z)) (L.comp (fderiv ℝ g y)) y :=
    L.hasFDerivAt.comp y hg.hasFDerivAt
  rw [h.fderiv]
  rfl

/-! ### Derivadas das fatias -/

theorem Amp.differentiableAt_fatia {T : ℝ} {c : ℕ → ℝ → E3 → C3} (hc : Amp T c) {t : ℝ}
    (ht : t ∈ Icc 0 T) (y : E3) : DifferentiableAt ℝ (fun z => V (c 0) (z, t)) y :=
  (Amp.hasFDerivAt_fatia hc ht y).differentiableAt

/-- `∂_j (L ∘ V(·, t)) = L(V[2πiξ_j c])`. -/
theorem Amp.dX_clm_V {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : C3 →L[ℝ] W)
    {T : ℝ} {c : ℕ → ℝ → E3 → C3} (hc : Amp T c) {t : ℝ} (ht : t ∈ Icc 0 T) (j : Fin 3)
    (y : E3) :
    dX j (fun z => L (V (c 0) (z, t))) y = L (V (mulC (cj j) c 0) (y, t)) := by
  rw [dX_clm L (Amp.differentiableAt_fatia hc ht y), Amp.dX_V hc ht]

/-! ### O campo, a pressão e as identidades -/

/-- O campo de velocidades `u(x, t) = Re V[a](x, t)`. -/
noncomputable def Uf (ν : ℝ) (a : ℝ → E3 → C3) : E3 × ℝ → E3 := fun q => re3 (V (ader ν a 0) q)

/-- A pressão `p(x, t) = Re V[p̂](x, t)₀`. -/
noncomputable def Pf (ν : ℝ) (a : ℝ → E3 → C3) : E3 × ℝ → ℝ := fun q => re0L (V (pk ν a 0) q)

section

variable {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3}

theorem fatia_Uf (t : ℝ) : fatia (Uf ν a) t = fun z => re3L (V (ader ν a 0) (z, t)) := rfl

theorem fatia_Pf (t : ℝ) : fatia (Pf ν a) t = fun z => re0L (V (pk ν a 0) (z, t)) := rfl

theorem integrable_amp {f : E3 → C3} (hf : AEStronglyMeasurable f) {C : ℝ}
    (hC : ∀ ξ, ‖f ξ‖ ≤ C * (w 4 ξ)⁻¹) (x : E3) : Integrable fun ξ => ex x ξ • f ξ :=
  integrable_ex_smul hf hC x

theorem BoaW.integrable_ex {f : ℝ → E3 → C3} (hf : BoaW f) (t : ℝ) (x : E3) :
    Integrable fun ξ => ex x ξ • f t ξ := by
  obtain ⟨C, -, hC⟩ := hf.bound 4
  exact integrable_ex_smul (hf.cont_s t).aestronglyMeasurable (hC t) x

/-- A identidade de Navier–Stokes, integrada contra `e^{2πi⟪ξ,x⟫}`. -/
theorem identidade_V (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E3) :
    Vf (ader ν a 1 t) x + Vf (Nl (a t) (a t)) x -
      (ν : ℂ) • ∑ j, Vf (fun ξ => cj j ξ • (cj j ξ • a t ξ)) x +
      ∑ j, (Vf (fun ξ => cj j ξ • pk ν a 0 t ξ) x 0) • cpx (e j) = 0 := by
  have hb := boaW_ader (ν := ν) ha
  have hp := amp_pk ha hmild
  -- integrabilidades
  have i1 : Integrable fun ξ => ex x ξ • ader ν a 1 t ξ := BoaW.integrable_ex (hb 1) t x
  have i2 : Integrable fun ξ => ex x ξ • Nl (a t) (a t) ξ := BoaW.integrable_ex (ha.nl ha) t x
  have hcc : ∀ j, Amp T (mulC (cj j) (mulC (cj j) (ader ν a))) :=
    fun j => ((amp_ader ha hmild).mulcj j).mulcj j
  have i3 : ∀ j, Integrable fun ξ => ex x ξ • (cj j ξ • (cj j ξ • a t ξ)) := by
    intro j
    have := (hcc j).integrable 0 ht x
    simpa [mulC, ader_zero] using this
  have i4 : ∀ j, Integrable fun ξ => ex x ξ • (cj j ξ • pk ν a 0 t ξ) :=
    fun j => (hp.mulcj j).integrable 0 ht x
  have i4' : ∀ j, Integrable fun ξ => ex x ξ • ((cj j ξ • pk ν a 0 t ξ) 0 • cpx (e j)) := by
    intro j
    have h := ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) 0).integrable_comp (i4 j)).smul_const
      (cpx (e j))
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp [smul_smul, mul_assoc]
  -- as componentes
  have e4 : ∀ j, (Vf (fun ξ => cj j ξ • pk ν a 0 t ξ) x 0) • cpx (e j) =
      ∫ ξ, ex x ξ • ((cj j ξ • pk ν a 0 t ξ) 0 • cpx (e j)) := by
    intro j
    rw [Vf_apply (i4 j) 0, ← integral_smul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp [smul_smul]
  -- a soma é a integral de `e · R`, `R = 0`
  have hR : ∀ ξ, ex x ξ • ader ν a 1 t ξ + ex x ξ • Nl (a t) (a t) ξ -
      (ν : ℂ) • ∑ j, ex x ξ • (cj j ξ • (cj j ξ • a t ξ)) +
      ∑ j, ex x ξ • ((cj j ξ • pk ν a 0 t ξ) 0 • cpx (e j)) = 0 := by
    intro ξ
    have h := identidade_amp ν a t ξ
    rw [← Finset.smul_sum, ← Finset.smul_sum, smul_comm (ν : ℂ) (ex x ξ), ← smul_add,
      ← smul_sub, ← smul_add, h, smul_zero]
  have hsum : Vf (ader ν a 1 t) x + Vf (Nl (a t) (a t)) x -
      (ν : ℂ) • ∑ j, Vf (fun ξ => cj j ξ • (cj j ξ • a t ξ)) x +
      ∑ j, (Vf (fun ξ => cj j ξ • pk ν a 0 t ξ) x 0) • cpx (e j) =
      ∫ ξ, (ex x ξ • ader ν a 1 t ξ + ex x ξ • Nl (a t) (a t) ξ -
        (ν : ℂ) • ∑ j, ex x ξ • (cj j ξ • (cj j ξ • a t ξ)) +
        ∑ j, ex x ξ • ((cj j ξ • pk ν a 0 t ξ) 0 • cpx (e j))) := by
    have j1 : Integrable fun ξ => ex x ξ • ader ν a 1 t ξ + ex x ξ • Nl (a t) (a t) ξ :=
      i1.add i2
    have j2 : Integrable fun ξ => (ν : ℂ) • ∑ j, ex x ξ • (cj j ξ • (cj j ξ • a t ξ)) :=
      (integrable_finsetSum _ fun j _ => i3 j).smul (ν : ℂ)
    have j3 : Integrable fun ξ => ex x ξ • ader ν a 1 t ξ + ex x ξ • Nl (a t) (a t) ξ -
        (ν : ℂ) • ∑ j, ex x ξ • (cj j ξ • (cj j ξ • a t ξ)) := j1.sub j2
    have j4 : Integrable fun ξ => ∑ j, ex x ξ • ((cj j ξ • pk ν a 0 t ξ) 0 • cpx (e j)) :=
      integrable_finsetSum _ fun j _ => i4' j
    rw [integral_add j3 j4, integral_sub j1 j2, integral_add i1 i2, integral_smul,
      integral_finsetSum _ fun j _ => i3 j, integral_finsetSum _ fun j _ => i4' j]
    simp only [e4]
    rfl
  rw [hsum]
  simp only [hR, integral_zero]

end

theorem continuous_fatia_V {T : ℝ} {c : ℕ → ℝ → E3 → C3} (hc : Amp T c) {t : ℝ}
    (ht : t ∈ Icc 0 T) : Continuous fun z => V (c 0) (z, t) :=
  continuous_iff_continuousAt.2 fun y => (Amp.differentiableAt_fatia hc ht y).continuousAt

theorem norm_cj_smul_le {A : ℝ} {f : E3 → C3} (hf : ∀ ξ, ‖f ξ‖ ≤ A * (w 5 ξ)⁻¹) (j : Fin 3)
    (ξ : E3) : ‖cj j ξ • f ξ‖ ≤ (2 * π * A) * (w 4 ξ)⁻¹ := by
  have hA0 : 0 ≤ A := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf 0))
    (inv_pos.mpr (w_pos 5 0))
  rw [norm_smul]
  calc ‖cj j ξ‖ * ‖f ξ‖ ≤ (2 * π * w 1 ξ) * (A * (w 5 ξ)⁻¹) :=
        mul_le_mul (norm_cj_le j ξ) (hf ξ) (norm_nonneg _) (by have := w_pos 1 ξ; positivity)
    _ = (2 * π * A) * (w 4 ξ)⁻¹ := by
        rw [show (5 : ℕ) = 4 + 1 from rfl, w_add]
        have := w_pos 4 ξ; have := w_pos 1 ξ; field_simp

theorem integral_sq_le {g : E3 → C3} (hg : AEStronglyMeasurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖g ξ‖ ≤ C * (w 4 ξ)⁻¹) : ∫ ξ, ‖g ξ‖ ^ 2 ≤ C ^ 2 * I4 := by
  have hint : Integrable fun ξ => C ^ 2 * (w 4 ξ)⁻¹ := integrable_w_inv.const_mul _
  have hpt : ∀ ξ, ‖g ξ‖ ^ 2 ≤ C ^ 2 * (w 4 ξ)⁻¹ := by
    intro ξ
    have hw := inv_pos.mpr (w_pos 4 ξ)
    have hw1 : (w 4 ξ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_w 4 ξ)
    calc ‖g ξ‖ ^ 2 ≤ (C * (w 4 ξ)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC ξ) 2
      _ = C ^ 2 * ((w 4 ξ)⁻¹ * (w 4 ξ)⁻¹) := by ring
      _ ≤ C ^ 2 * ((w 4 ξ)⁻¹ * 1) := by gcongr
      _ = C ^ 2 * (w 4 ξ)⁻¹ := by ring
  calc ∫ ξ, ‖g ξ‖ ^ 2 ≤ ∫ ξ, C ^ 2 * (w 4 ξ)⁻¹ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity) hint
          (Eventually.of_forall hpt)
    _ = C ^ 2 * I4 := by rw [integral_const_mul, I4]

section

variable {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3}

/-! ### O campo e a pressão: derivadas -/

variable (ha : BoaW a)
  (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
include ha hmild

theorem dX_Uf {t : ℝ} (ht : t ∈ Icc 0 T) (j : Fin 3) (y : E3) :
    dX j (fatia (Uf ν a) t) y = re3 (V (mulC (cj j) (ader ν a) 0) (y, t)) := by
  rw [fatia_Uf]
  exact Amp.dX_clm_V re3L (amp_ader ha hmild) ht j y

theorem lap_Uf {t : ℝ} (ht : t ∈ Icc 0 T) (x : E3) :
    lap (fatia (Uf ν a) t) x = re3 (∑ j, Vf (fun ξ => cj j ξ • (cj j ξ • a t ξ)) x) := by
  have hb := amp_ader ha hmild
  unfold lap
  rw [re3_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : dX j (fatia (Uf ν a) t) = fun y => re3L (V (mulC (cj j) (ader ν a) 0) (y, t)) :=
    funext fun y => dX_Uf ha hmild ht j y
  rw [e, Amp.dX_clm_V re3L (hb.mulcj j) ht j x]
  simp only [V, Vf, mulC, ader_zero]
  rfl

theorem deriv_Uf {t : ℝ} (ht : t ∈ Ioo 0 T) (x : E3) :
    deriv (fun s => Uf ν a (x, s)) t = re3 (Vf (ader ν a 1 t) x) := by
  have hb := amp_ader ha hmild
  have h := (re3L.hasFDerivAt (x := V (ader ν a 0) (x, t))).comp_hasDerivAt t
    (Amp.hasDerivAt_V_t hb ht x)
  exact h.deriv

theorem grad_Pf {t : ℝ} (ht : t ∈ Icc 0 T) (x : E3) :
    grad (fatia (Pf ν a) t) x =
      ∑ j, (Vf (fun ξ => cj j ξ • pk ν a 0 t ξ) x 0).re • e j := by
  have hp := amp_pk ha hmild
  unfold grad
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fatia_Pf, Amp.dX_clm_V re0L hp ht j x, re0L_apply]
  rfl

theorem real_V (hherm : ∀ t, Herm (a t)) (t : ℝ) (x : E3) :
    cj3 (Vf (a t) x) = Vf (a t) x :=
  Vf_real (hherm t) x

theorem conv_Uf (hherm : ∀ t, Herm (a t)) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E3) :
    conv (fatia (Uf ν a) t) x = re3 (Vf (Nl (a t) (a t)) x) := by
  obtain ⟨C, -, hC⟩ := ha.bound 5
  rw [← conv_Vf (ha.cont_s t) (hC t) (hdivF t) x, re3_sum]
  unfold conv
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dX_Uf ha hmild ht j x]
  have hr := real_V ha hmild hherm t x
  have him : (Vf (a t) x j).im = 0 := by
    have h := congrArg (fun u : C3 => u j) hr
    simp only [cj3_apply] at h
    exact Complex.conj_eq_iff_im.mp h
  rw [re3_smul_of_im him]
  have hm : mulC (cj j) (ader ν a) 0 t = fun ζ => cj j ζ • a t ζ := by
    funext ζ; simp [mulC, ader_zero]
  simp only [fatia, Uf, V, ader_zero, re3_apply, hm]

theorem div_Uf (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : E3) : div (fatia (Uf ν a) t) x = 0 := by
  have hb := amp_ader ha hmild
  unfold div
  simp only [dX_Uf ha hmild ht, re3_apply]
  rw [← Complex.re_sum]
  have hint : ∀ j, Integrable fun ξ => ex x ξ • mulC (cj j) (ader ν a) 0 t ξ :=
    fun j => (hb.mulcj j).integrable 0 ht x
  have h1 : ∑ j, V (mulC (cj j) (ader ν a) 0) (x, t) j =
      ∫ ξ, ∑ j, ex x ξ * mulC (cj j) (ader ν a) 0 t ξ j := by
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      exact Vf_apply (hint j) j
    · exact ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).integrable_comp (hint j)).congr
        (Eventually.of_forall fun ξ => by simp)
  rw [h1]
  have h2 : ∀ ξ, ∑ j, ex x ξ * mulC (cj j) (ader ν a) 0 t ξ j = 0 := by
    intro ξ
    simp only [mulC, ader_zero, PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    have := sum_cj_mul ξ (a t ξ)
    rw [show ∑ j, cj j ξ * a t ξ j = ∑ j, a t ξ j * cj j ξ from
      Finset.sum_congr rfl fun j _ => mul_comm _ _, this, hdivF t ξ, mul_zero, mul_zero]
  simp only [h2, integral_zero, Complex.zero_re]

/-- **A equação de Navier–Stokes** para `(u, p)` reconstruídos. -/
theorem NSEq_Uf (hherm : ∀ t, Herm (a t)) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : E3) : NSEq ν (Uf ν a) (Pf ν a) x t := by
  have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  unfold NSEq
  rw [deriv_Uf ha hmild ht x, conv_Uf ha hmild hherm hdivF ht' x, lap_Uf ha hmild ht' x,
    grad_Pf ha hmild ht' x]
  have hid := congrArg re3 (identidade_V ha hmild ht' x)
  rw [re3_add, re3_sub, re3_add, re3_ofReal_smul, re3_sum, re3_sum] at hid
  simp only [re3_smul_cpx] at hid
  have hz : re3 (0 : C3) = 0 := map_zero re3L
  rw [hz] at hid
  rw [re3_sum, ← sub_eq_zero, ← hid]
  abel

/-! ### Energia e enstrofia -/

theorem energia_Uf {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ t ξ, ‖a t ξ‖ ≤ A * (w 5 ξ)⁻¹)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x => ‖Uf ν a (x, t)‖ ^ 2) ∧ ∫ x, ‖Uf ν a (x, t)‖ ^ 2 ≤ A ^ 2 * I4 := by
  have hb := amp_ader ha hmild
  have hA4 : ∀ ξ, ‖a t ξ‖ ≤ A * (w 4 ξ)⁻¹ := fun ξ =>
    (hA t ξ).trans (mul_le_mul_of_nonneg_left (w_inv_anti (by norm_num) ξ) hA0)
  obtain ⟨hI, hE⟩ := integral_norm_sq_Vf (ha.cont_s t).aestronglyMeasurable hA4
  have eU : ∀ x, Uf ν a (x, t) = re3 (Vf (a t) x) := fun x => by
    simp [Uf, V, ader_zero]
  have hc : Continuous fun x => Uf ν a (x, t) :=
    re3L.continuous.comp (continuous_fatia_V hb ht)
  have hle : ∀ x, ‖Uf ν a (x, t)‖ ^ 2 ≤ ‖Vf (a t) x‖ ^ 2 := fun x => by
    rw [eU]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_re3_le _) 2
  have hUi : Integrable (fun x => ‖Uf ν a (x, t)‖ ^ 2) :=
    hI.mono' (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hle x)
  refine ⟨hUi, ?_⟩
  calc ∫ x, ‖Uf ν a (x, t)‖ ^ 2 ≤ ∫ x, ‖Vf (a t) x‖ ^ 2 :=
        integral_mono hUi hI hle
    _ = ∫ ξ, ‖a t ξ‖ ^ 2 := hE
    _ ≤ A ^ 2 * I4 := integral_sq_le (ha.cont_s t).aestronglyMeasurable hA0 hA4

theorem enstrofia_Uf {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ t ξ, ‖a t ξ‖ ≤ A * (w 5 ξ)⁻¹)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (gradSq (fatia (Uf ν a) t)) ∧
      ∫ x, gradSq (fatia (Uf ν a) t) x ≤ 3 * ((2 * π * A) ^ 2 * I4) := by
  have hb := amp_ader ha hmild
  set g : Fin 3 → E3 → C3 := fun j ξ => cj j ξ • a t ξ with hg
  have hgm : ∀ j, AEStronglyMeasurable (g j) := fun j =>
    ((continuous_cj j).smul (ha.cont_s t)).aestronglyMeasurable
  have hgb : ∀ j ξ, ‖g j ξ‖ ≤ (2 * π * A) * (w 4 ξ)⁻¹ := fun j ξ => norm_cj_smul_le (hA t) j ξ
  have hP := fun j => integral_norm_sq_Vf (hgm j) (hgb j)
  have eD : ∀ j x, dX j (fatia (Uf ν a) t) x = re3 (Vf (g j) x) := by
    intro j x
    rw [dX_Uf ha hmild ht j x]
    have hm : mulC (cj j) (ader ν a) 0 t = g j := by
      funext ξ; simp [mulC, ader_zero, hg]
    simp only [V, hm]
  have hle : ∀ x, gradSq (fatia (Uf ν a) t) x ≤ ∑ j, ‖Vf (g j) x‖ ^ 2 := by
    intro x
    unfold gradSq
    refine Finset.sum_le_sum fun j _ => ?_
    rw [eD]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_re3_le _) 2
  have hsumI : Integrable fun x => ∑ j, ‖Vf (g j) x‖ ^ 2 :=
    integrable_finsetSum _ fun j _ => (hP j).1
  have hcD : ∀ j, Continuous fun x => dX j (fatia (Uf ν a) t) x := by
    intro j
    have h : (fun x => dX j (fatia (Uf ν a) t) x) =
        fun x => re3L (V (mulC (cj j) (ader ν a) 0) (x, t)) :=
      funext fun x => dX_Uf ha hmild ht j x
    rw [h]
    exact re3L.continuous.comp (continuous_fatia_V (hb.mulcj j) ht)
  have hgi : Integrable (gradSq (fatia (Uf ν a) t)) := by
    refine hsumI.mono' ?_ (Eventually.of_forall fun x => ?_)
    · unfold gradSq
      exact (continuous_finsetSum _ fun j _ => ((hcD j).norm.pow 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (show 0 ≤ gradSq (fatia (Uf ν a) t) x from
        Finset.sum_nonneg fun j _ => sq_nonneg _)]
      exact hle x
  refine ⟨hgi, ?_⟩
  calc ∫ x, gradSq (fatia (Uf ν a) t) x ≤ ∫ x, ∑ j, ‖Vf (g j) x‖ ^ 2 :=
        integral_mono hgi hsumI hle
    _ = ∑ j, ∫ x, ‖Vf (g j) x‖ ^ 2 := integral_finsetSum _ fun j _ => (hP j).1
    _ = ∑ j, ∫ ξ, ‖g j ξ‖ ^ 2 := Finset.sum_congr rfl fun j _ => (hP j).2
    _ ≤ ∑ _j : Fin 3, (2 * π * A) ^ 2 * I4 :=
        Finset.sum_le_sum fun j _ => integral_sq_le (hgm j) (by positivity) (hgb j)
    _ = 3 * ((2 * π * A) ^ 2 * I4) := by simp

end

/-! ### A existência local -/

/-- **Existência local de soluções suaves de Navier–Stokes em `ℝ³`** (Leray 1934;
Kato–Fujita): o enunciado `ATK.NSReducao.ExistenciaLocal`, no modelo genuíno. -/
theorem existenciaLocal : ATK.NSReducao.ExistenciaLocal := by
  rintro ⟨ν, u₀f⟩ ⟨hν, ⟨u₀, hu₀⟩, hdiv⟩
  simp only at hν hdiv hu₀ ⊢
  subst hu₀
  obtain ⟨M, hM⟩ := ahat_dado u₀
  obtain ⟨T, hT, a, ha4, hmild, hdivF, -, hbnd, hherm⟩ :=
    existe_branda_herm hν hM (ahat_div u₀ hdiv) (ahat_herm u₀)
  have haW : BoaW a := by
    refine ⟨ha4.cont, fun m => ?_⟩
    obtain ⟨C0, -, hC0⟩ := ahat_bound u₀ m
    obtain ⟨C, hC⟩ := hbnd m C0 hC0
    refine ⟨max C 0, le_max_right _ _, fun t ξ => (hC t ξ).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_pos.mpr (w_pos m ξ)).le
  have hb := amp_ader haW hmild
  have hp := amp_pk haW hmild
  obtain ⟨A, hA0, hA⟩ := haW.bound 5
  have hsub : univ ×ˢ Ico 0 T ⊆ (univ : Set E3) ×ˢ Icc 0 T :=
    prod_mono subset_rfl Ico_subset_Icc_self
  refine ⟨T, hT, Uf ν a, Pf ν a, ?_, ?_, fun x => ?_, fun x t ht => ?_, fun x t ht => ?_,
    fun T' hT' => ?_⟩
  · exact (re3L.contDiff.comp_contDiffOn (hb.contDiffOn_V_infty hT)).mono hsub
  · exact (re0L.contDiff.comp_contDiffOn (hp.contDiffOn_V_infty hT)).mono hsub
  · have ha0 : a 0 = ahat u₀ := by
      funext ξ
      rw [hmild 0 ⟨le_rfl, hT.le⟩ ξ, heat_zero, one_smul, intervalIntegral.integral_same,
        sub_zero]
    show re3 (V (ader ν a 0) (x, 0)) = u₀ x
    simp only [V, ader_zero, ha0, Vf_ahat, re3_cpx]
  · exact NSEq_Uf haW hmild hherm hdivF ht x
  · exact div_Uf haW hmild hdivF (Ico_subset_Icc_self ht) x
  · refine ⟨A ^ 2 * I4 + 3 * ((2 * π * A) ^ 2 * I4), fun t ht => ?_⟩
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hT'.le⟩
    have hI4 := I4_nonneg
    obtain ⟨hE1, hE2⟩ := energia_Uf haW hmild hA0 hA htT
    obtain ⟨hG1, hG2⟩ := enstrofia_Uf haW hmild hA0 hA htT
    refine ⟨⟨hE1, hE2.trans ?_⟩, hG1, hG2.trans ?_⟩
    · have : 0 ≤ 3 * ((2 * π * A) ^ 2 * I4) := by positivity
      linarith
    · have : 0 ≤ A ^ 2 * I4 := by positivity
      linarith

end ATK.NSExistencia

#print axioms ATK.NSExistencia.norm_re3_le
#print axioms ATK.NSExistencia.re3_add
#print axioms ATK.NSExistencia.re3_sub
#print axioms ATK.NSExistencia.re3_real_smul
#print axioms ATK.NSExistencia.re3_sum
#print axioms ATK.NSExistencia.re3_smul_of_im
#print axioms ATK.NSExistencia.re3_smul_cpx
#print axioms ATK.NSExistencia.re3_ofReal_smul
#print axioms ATK.NSExistencia.re0L_apply
#print axioms ATK.NSExistencia.dX_clm
#print axioms ATK.NSExistencia.Amp.differentiableAt_fatia
#print axioms ATK.NSExistencia.Amp.dX_clm_V
#print axioms ATK.NSExistencia.fatia_Uf
#print axioms ATK.NSExistencia.fatia_Pf
#print axioms ATK.NSExistencia.integrable_amp
#print axioms ATK.NSExistencia.BoaW.integrable_ex
#print axioms ATK.NSExistencia.identidade_V
#print axioms ATK.NSExistencia.continuous_fatia_V
#print axioms ATK.NSExistencia.norm_cj_smul_le
#print axioms ATK.NSExistencia.integral_sq_le
#print axioms ATK.NSExistencia.dX_Uf
#print axioms ATK.NSExistencia.lap_Uf
#print axioms ATK.NSExistencia.deriv_Uf
#print axioms ATK.NSExistencia.grad_Pf
#print axioms ATK.NSExistencia.real_V
#print axioms ATK.NSExistencia.conv_Uf
#print axioms ATK.NSExistencia.div_Uf
#print axioms ATK.NSExistencia.NSEq_Uf
#print axioms ATK.NSExistencia.energia_Uf
#print axioms ATK.NSExistencia.enstrofia_Uf
#print axioms ATK.NSExistencia.existenciaLocal
