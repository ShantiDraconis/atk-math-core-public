import ATK.NSExistencia

/-!
# ATK — Navier–Stokes: a identidade de energia no lado de Fourier

Camada 10 do ataque a B3. Para amplitudes `a(t, ξ)` hermitianas e de divergência nula:

* **`integral_inner_Nl_self`**: `∫ ⟪â(ξ), N(â, â)(ξ)⟫ dξ = 0` — o termo não linear não troca
  energia (no espaço físico: `∫ u·(u·∇)u = 0`). Prova puramente do lado de Fourier: para cada
  `η`, a integral em `ξ` do integrando trilinear é igual à sua oposta (translação `ξ ↦ ξ − η`,
  reflexão `ξ ↦ −ξ`, simetria hermitiana e `⟪η, â(η)⟫ = 0`), e Fubini;
* **`inner_lp_of_div`**: o projetor de Leray é autoadjunto contra campos de divergência nula;
* **`energia_decresce`**: para a solução branda, `∫ ‖â(t)‖² ≤ ∫ ‖â(0)‖²` em `[0, T]`
  (mais precisamente `∫ ‖â(t)‖² − ∫ ‖â(0)‖² = −2 ∫₀ᵗ ∫ κ ‖â‖²`).

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Real

namespace ATK.NSEnergia

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard ATK.NSMild ATK.NSSuave ATK.NSTempo
  ATK.NSSimetria ATK.NSFisico

theorem cpx_sub (ξ η : E3) : cpx (ξ - η) = cpx ξ - cpx η := by
  ext k; simp [cpx]

theorem inner_cj3_cj3 (v v' : C3) : inner ℂ (cj3 v) (cj3 v') = inner ℂ v' v := by
  simp only [PiLp.inner_apply, cj3]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

/-! ### O termo trilinear -/

/-- O integrando trilinear `⟪ξ, f(η)⟫ ⟪f(ξ), f(ξ − η)⟫`. -/
noncomputable def Ftri (f : E3 → C3) (ξ η : E3) : ℂ :=
  inner ℂ (cpx ξ) (f η) * inner ℂ (f ξ) (f (ξ - η))

/-- Para cada `η`, a integral em `ξ` do integrando trilinear é nula. -/
theorem integral_Ftri_eq_zero {f : E3 → C3} (hh : Herm f)
    (hd : ∀ ξ, inner ℂ (cpx ξ) (f ξ) = 0) (η : E3) : ∫ ξ, Ftri f ξ η = 0 := by
  set G : E3 → ℂ := fun p => inner ℂ (cpx p) (f η) * inner ℂ (f (p + η)) (f p) with hG
  have h1 : ∀ ξ, Ftri f ξ η = G (ξ - η) := by
    intro ξ
    simp only [Ftri, hG, sub_add_cancel, cpx_sub, inner_sub_left, hd η, sub_zero]
  have h2 : ∀ ξ, G (-ξ) = -Ftri f ξ η := by
    intro ξ
    have e1 : -ξ + η = -(ξ - η) := by abel
    simp only [hG, Ftri, cpx_neg, inner_neg_left]
    rw [e1, hh, hh ξ, inner_cj3_cj3]
    ring
  have h3 : ∫ ξ, Ftri f ξ η = -∫ ξ, Ftri f ξ η := by
    calc ∫ ξ, Ftri f ξ η = ∫ ξ, G (ξ - η) := integral_congr_ae (Eventually.of_forall h1)
      _ = ∫ p, G p := integral_sub_right_eq_self G η
      _ = ∫ ξ, G (-ξ) := (integral_neg_eq_self G volume).symm
      _ = ∫ ξ, -Ftri f ξ η := integral_congr_ae (Eventually.of_forall h2)
      _ = -∫ ξ, Ftri f ξ η := integral_neg _
  exact self_eq_neg.mp h3

theorem norm_mul_w5_le (ξ : E3) : ‖ξ‖ * (w 5 ξ)⁻¹ ≤ (w 4 ξ)⁻¹ := by
  have h5 : w 5 ξ = w 4 ξ * w 1 ξ := w_add 4 1 ξ
  rw [h5, mul_inv, ← mul_assoc, mul_comm ‖ξ‖, mul_assoc]
  have h4 := inv_pos.mpr (w_pos 4 ξ)
  refine mul_le_of_le_one_right h4.le ?_
  rw [mul_inv_le_iff₀ (w_pos 1 ξ), one_mul]
  exact norm_le_w1 ξ

theorem norm_Ftri_le {f : E3 → C3} {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ ξ, ‖f ξ‖ ≤ A * (w 5 ξ)⁻¹)
    (ξ η : E3) : ‖Ftri f ξ η‖ ≤ A ^ 3 * ((w 4 ξ)⁻¹ * (w 4 η)⁻¹) := by
  have hA4 : ∀ ζ, ‖f ζ‖ ≤ A * (w 4 ζ)⁻¹ := fun ζ =>
    (hA ζ).trans (mul_le_mul_of_nonneg_left (w_inv_anti (by norm_num) ζ) hA0)
  have hA1 : ∀ ζ, ‖f ζ‖ ≤ A := fun ζ =>
    (hA ζ).trans (mul_le_of_le_one_right hA0 (inv_le_one_of_one_le₀ (one_le_w 5 ζ)))
  unfold Ftri
  rw [norm_mul]
  have e1 : ‖inner ℂ (cpx ξ) (f η)‖ ≤ ‖ξ‖ * (A * (w 4 η)⁻¹) :=
    (norm_inner_cpx_le ξ _).trans (mul_le_mul_of_nonneg_left (hA4 η) (norm_nonneg _))
  have e2 : ‖inner ℂ (f ξ) (f (ξ - η))‖ ≤ (A * (w 5 ξ)⁻¹) * A :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (hA ξ) (hA1 _) (norm_nonneg _)
      (mul_nonneg hA0 (inv_pos.mpr (w_pos 5 ξ)).le))
  have hw4 := (inv_pos.mpr (w_pos 4 η)).le
  calc ‖inner ℂ (cpx ξ) (f η)‖ * ‖inner ℂ (f ξ) (f (ξ - η))‖
      ≤ (‖ξ‖ * (A * (w 4 η)⁻¹)) * ((A * (w 5 ξ)⁻¹) * A) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
    _ = A ^ 3 * ((‖ξ‖ * (w 5 ξ)⁻¹) * (w 4 η)⁻¹) := by ring
    _ ≤ A ^ 3 * ((w 4 ξ)⁻¹ * (w 4 η)⁻¹) := by
        gcongr
        exact norm_mul_w5_le ξ

theorem integrable_Ftri {f : E3 → C3} (hc : Continuous f) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ ξ, ‖f ξ‖ ≤ A * (w 5 ξ)⁻¹) :
    Integrable (Function.uncurry (Ftri f)) ((volume : Measure E3).prod volume) := by
  have hdom : Integrable (fun p : E3 × E3 => A ^ 3 * ((w 4 p.1)⁻¹ * (w 4 p.2)⁻¹))
      ((volume : Measure E3).prod volume) :=
    (integrable_w_inv.mul_prod integrable_w_inv).const_mul _
  refine hdom.mono' ?_ (Eventually.of_forall fun p => norm_Ftri_le hA0 hA p.1 p.2)
  have hcF : Continuous (Function.uncurry (Ftri f)) := by
    unfold Function.uncurry Ftri
    have hcp : Continuous cpx := continuous_cpx
    fun_prop
  exact hcF.aestronglyMeasurable

/-- `⟪v, Nl f f ξ⟫ = 2πi ∫ ⟪ξ, f(η)⟫ ⟪v, f(ξ − η)⟫ dη`. -/
theorem inner_Nl_self {f : E3 → C3} (hc : Continuous f) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ ξ, ‖f ξ‖ ≤ A * (w 5 ξ)⁻¹) (ξ : E3) :
    inner ℂ (f ξ) (Nl f f ξ) = ((2 * π : ℝ) * Complex.I : ℂ) * ∫ η, Ftri f ξ η := by
  have hA4 : ∀ ζ, ‖f ζ‖ ≤ A * (w 4 ζ)⁻¹ := fun ζ =>
    (hA ζ).trans (mul_le_mul_of_nonneg_left (w_inv_anti (by norm_num) ζ) hA0)
  have hA1 : ∀ ζ, ‖f ζ‖ ≤ A := fun ζ =>
    (hA ζ).trans (mul_le_of_le_one_right hA0 (inv_le_one_of_one_le₀ (one_le_w 5 ζ)))
  have hint := integrable_Nl_integrand hc hc hA4 hA1 ξ
  unfold Nl
  rw [inner_smul_right, ← integral_inner hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [Ftri, inner_smul_right]

/-- **O termo não linear não troca energia**: `∫ ⟪f(ξ), N(f, f)(ξ)⟫ dξ = 0` para `f`
hermitiana, de divergência nula e de decaimento `w₅`. -/
theorem integral_inner_Nl_self {f : E3 → C3} (hc : Continuous f) (hh : Herm f)
    (hd : ∀ ξ, inner ℂ (cpx ξ) (f ξ) = 0) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ ξ, ‖f ξ‖ ≤ A * (w 5 ξ)⁻¹) :
    ∫ ξ, inner ℂ (f ξ) (Nl f f ξ) = 0 := by
  simp_rw [inner_Nl_self hc hA0 hA]
  rw [integral_const_mul, integral_integral_swap (integrable_Ftri hc hA0 hA)]
  simp [integral_Ftri_eq_zero hh hd]

/-- O projetor de Leray é autoadjunto contra campos de divergência nula. -/
theorem inner_lp_of_div {ξ : E3} {v : C3} (hv : inner ℂ (cpx ξ) v = 0) (u : C3) :
    inner ℂ v (lp ξ u) = inner ℂ v u := by
  have hv' : inner ℂ v (cpx ξ) = 0 := by rw [← inner_conj_symm, hv, map_zero]
  simp [ATK.NSFourierBase.lp, inner_sub_right, inner_smul_right, hv']


/-! ### Produtos internos de amplitudes boas -/

theorem BoaW.inner_bound {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) :
    ∃ C, 0 ≤ C ∧ ∀ s ξ, ‖inner ℂ (f s ξ) (g s ξ)‖ ≤ C * (w 4 ξ)⁻¹ := by
  obtain ⟨A, hA0, hA⟩ := hf.bound 4
  obtain ⟨B, hB0, hB⟩ := hg.bound 0
  refine ⟨A * B, mul_nonneg hA0 hB0, fun s ξ => ?_⟩
  have hw0 : (w 0 ξ)⁻¹ = 1 := by simp [w]
  have hB' : ‖g s ξ‖ ≤ B := by simpa [hw0] using hB s ξ
  have hw := (inv_pos.mpr (w_pos 4 ξ)).le
  calc ‖inner ℂ (f s ξ) (g s ξ)‖ ≤ ‖f s ξ‖ * ‖g s ξ‖ := norm_inner_le_norm _ _
    _ ≤ (A * (w 4 ξ)⁻¹) * B := mul_le_mul (hA s ξ) hB' (norm_nonneg _) (by positivity)
    _ = A * B * (w 4 ξ)⁻¹ := by ring

theorem BoaW.integrable_inner {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) (s : ℝ) :
    Integrable fun ξ => inner ℂ (f s ξ) (g s ξ) := by
  obtain ⟨C, -, hC⟩ := BoaW.inner_bound hf hg
  have hc : Continuous fun ξ => inner ℂ (f s ξ) (g s ξ) := by
    have h1 := hf.cont_s s
    have h2 := hg.cont_s s
    fun_prop
  exact (integrable_w_inv.const_mul C).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun ξ => hC s ξ)

theorem BoaW.integrable_norm_sq {f : ℝ → E3 → C3} (hf : BoaW f) (s : ℝ) :
    Integrable fun ξ => ‖f s ξ‖ ^ 2 := by
  have h := BoaW.integrable_inner hf hf s
  have e : (fun ξ => ‖f s ξ‖ ^ 2) = fun ξ => RCLike.re (inner ℂ (f s ξ) (f s ξ)) := by
    funext ξ
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  rw [e]
  exact h.re

/-! ### A energia decresce -/

theorem ader_one (ν : ℝ) (a : ℝ → E3 → C3) (t : ℝ) (ξ : E3) :
    ader ν a 1 t ξ = -((kappa ν ξ : ℝ) : ℂ) • a t ξ - lp ξ (Nl (a t) (a t) ξ) := by
  rw [ader_succ, Nk_zero, ader_zero]

section

variable {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3}

/-- `‖â(t, ξ)‖² − ‖â(0, ξ)‖² = ∫₀ᵗ 2 Re ⟪â, ∂ₜâ⟫`. -/
theorem norm_sq_sub_eq (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (ξ : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖a t ξ‖ ^ 2 - ‖a 0 ξ‖ ^ 2 =
      ∫ s in (0 : ℝ)..t, 2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re := by
  have hb := amp_ader ha hmild
  have hc1 : Continuous fun s => ader ν a 1 s ξ := (boaW_ader ha 1).cont_t ξ
  have hc0 : Continuous fun s => a s ξ := ha.cont_t ξ
  have hfd : ∀ s ∈ Icc 0 T, a s ξ = a 0 ξ + ∫ r in (0 : ℝ)..s, ader ν a 1 r ξ := by
    intro s hs
    have h := hb.deriv 0 ξ s hs
    simpa only [ader_zero] using h
  have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => ‖a r ξ‖ ^ 2)
      (2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re) s := by
    intro s hs
    have h := hasDerivAt_of_integral (T := T) (f := fun r => a r ξ) hc1 hfd
      ⟨hs.1, hs.2.trans_le ht.2⟩
    have h2 := h.norm_sq
    convert h2 using 2
    exact (real_inner_eq_re_inner ℂ (a s ξ) (ader ν a 1 s ξ)).symm
  have hcont : Continuous fun s => 2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc0.norm.pow 2).continuousOn hderiv (hcont.intervalIntegrable _ _)]
  rfl

/-- `∫ 2 Re ⟪â, ∂ₜâ⟫ dξ = −2 ∫ κ ‖â‖² ≤ 0`. -/
theorem integral_re_inner_ader_le (hν : 0 ≤ ν) (ha : BoaW a) (hherm : ∀ t, Herm (a t))
    (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) (s : ℝ) :
    ∫ ξ, 2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re ≤ 0 := by
  obtain ⟨A, hA0, hA⟩ := ha.bound 5
  have hN := ha.nl ha
  have hI1 := BoaW.integrable_inner ha (boaW_ader (ν := ν) ha 1) s
  have hI2 := BoaW.integrable_inner ha hN s
  have hpt : ∀ ξ, 2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re ≤
      -(2 * RCLike.re (inner ℂ (a s ξ) (Nl (a s) (a s) ξ))) := by
    intro ξ
    rw [ader_one, inner_sub_right, inner_lp_of_div (hdivF s ξ), inner_smul_right]
    have hk : 0 ≤ kappa ν ξ := by unfold kappa; positivity
    have h0 : 0 ≤ (inner ℂ (a s ξ) (a s ξ)).re := by
      have := inner_self_nonneg (𝕜 := ℂ) (x := a s ξ)
      simpa [RCLike.re_to_complex] using this
    simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, RCLike.re_to_complex]
    nlinarith [mul_nonneg hk h0]
  have hI1' : Integrable fun ξ => 2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re :=
    hI1.re.const_mul 2
  have hI2' : Integrable fun ξ => -(2 * RCLike.re (inner ℂ (a s ξ) (Nl (a s) (a s) ξ))) :=
    (hI2.re.const_mul 2).neg
  calc ∫ ξ, 2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re
      ≤ ∫ ξ, -(2 * RCLike.re (inner ℂ (a s ξ) (Nl (a s) (a s) ξ))) :=
        integral_mono hI1' hI2' hpt
    _ = -(2 * RCLike.re (∫ ξ, inner ℂ (a s ξ) (Nl (a s) (a s) ξ))) := by
        rw [integral_neg, integral_const_mul, integral_re hI2]
    _ = 0 := by
        rw [integral_inner_Nl_self (ha.cont_s s) (hherm s) (hdivF s) hA0 (hA s)]
        simp

/-- **A energia da solução branda decresce**: `∫ ‖â(t)‖² ≤ ∫ ‖â(0)‖²` em `[0, T]`. -/
theorem energia_decresce (hν : 0 ≤ ν) (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (hherm : ∀ t, Herm (a t)) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ ξ, ‖a t ξ‖ ^ 2 ≤ ∫ ξ, ‖a 0 ξ‖ ^ 2 := by
  set h : ℝ → E3 → ℝ := fun s ξ => 2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re with hh
  obtain ⟨C, hC0, hC⟩ := BoaW.inner_bound ha (boaW_ader (ν := ν) ha 1)
  have hint : Integrable (Function.uncurry h) ((volume.restrict (uIoc 0 t)).prod volume) := by
    have h1 : Integrable (fun _ : ℝ => 2 * C) (volume.restrict (uIoc 0 t)) :=
      integrableOn_const (by simp [uIoc])
    have hdom : Integrable (fun p : ℝ × E3 => (2 * C) * (w 4 p.2)⁻¹)
        ((volume.restrict (uIoc 0 t)).prod volume) := h1.mul_prod integrable_w_inv
    have hcont : Continuous (Function.uncurry h) := by
      have c1 := ha.cont
      have c2 := (boaW_ader (ν := ν) ha 1).cont
      simp only [hh, Function.uncurry]
      fun_prop
    refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    show ‖2 * (inner ℂ (a p.1 p.2) (ader ν a 1 p.1 p.2)).re‖ ≤ 2 * C * (w 4 p.2)⁻¹
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos two_pos]
    have := hC p.1 p.2
    have hre := Complex.abs_re_le_norm (inner ℂ (a p.1 p.2) (ader ν a 1 p.1 p.2))
    nlinarith
  have key : (∫ ξ, ‖a t ξ‖ ^ 2) - ∫ ξ, ‖a 0 ξ‖ ^ 2 = ∫ s in (0 : ℝ)..t, ∫ ξ, h s ξ := by
    rw [← integral_sub (BoaW.integrable_norm_sq ha t) (BoaW.integrable_norm_sq ha 0),
      intervalIntegral_integral_swap hint]
    exact integral_congr_ae (Eventually.of_forall fun ξ => norm_sq_sub_eq ha hmild ξ ht)
  have hle : ∫ s in (0 : ℝ)..t, ∫ ξ, h s ξ ≤ 0 := by
    rw [intervalIntegral.integral_of_le ht.1]
    exact integral_nonpos fun s => integral_re_inner_ader_le hν ha hherm hdivF s
  linarith

end

end ATK.NSEnergia

#print axioms ATK.NSEnergia.cpx_sub
#print axioms ATK.NSEnergia.inner_cj3_cj3
#print axioms ATK.NSEnergia.integral_Ftri_eq_zero
#print axioms ATK.NSEnergia.norm_mul_w5_le
#print axioms ATK.NSEnergia.norm_Ftri_le
#print axioms ATK.NSEnergia.integrable_Ftri
#print axioms ATK.NSEnergia.inner_Nl_self
#print axioms ATK.NSEnergia.integral_inner_Nl_self
#print axioms ATK.NSEnergia.inner_lp_of_div
#print axioms ATK.NSEnergia.BoaW.inner_bound
#print axioms ATK.NSEnergia.BoaW.integrable_inner
#print axioms ATK.NSEnergia.BoaW.integrable_norm_sq
#print axioms ATK.NSEnergia.ader_one
#print axioms ATK.NSEnergia.norm_sq_sub_eq
#print axioms ATK.NSEnergia.integral_re_inner_ader_le
#print axioms ATK.NSEnergia.energia_decresce
