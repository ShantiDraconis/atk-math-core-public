import ATK.PlancherelL1L2
import Mathlib.Analysis.MellinInversion

/-!
# ATK — Plancherel de Mellin na linha `Re s = 1/2`

Para `f : (0, ∞) → ℂ` com `∫_0^∞ |f(t)| t^{−1/2} dt < ∞` e `∫_0^∞ |f(t)|² dt < ∞`:

  **`∫_0^∞ |f(t)|² dt = (1/2π) ∫_ℝ |𝓜f(1/2 + iτ)|² dτ`** (`integral_norm_sq_eq_mellin`).

Prova: com `t = e^{−u}` e `g(u) = e^{−u/2} f(e^{−u})`, tem-se `∫_0^∞ |f|² = ∫_ℝ |g|²`,
`𝓜f(1/2 + 2πiξ) = 𝓕g(ξ)` (`mellin_eq_fourier` da Mathlib) e `g ∈ L¹ ∩ L²`; aplica-se
`ATK.PlancherelL1L2.integral_norm_sq_fourier` e a substituição `τ = 2πξ`.
-/

open MeasureTheory FourierTransform Set Real

namespace ATK.MellinPlancherel

variable {f : ℝ → ℂ}

theorem rexp_neg_deriv :
    ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

theorem rexp_neg_image : rexp ∘ Neg.neg '' (univ : Set ℝ) = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

theorem rexp_neg_injOn : (univ : Set ℝ).InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- Lado de Fourier: `g(u) = e^{−u/2} f(e^{−u})`. -/
noncomputable def lado (f : ℝ → ℂ) (u : ℝ) : ℂ := rexp (-(1 / 2 : ℝ) * u) • f (rexp (-u))

/-- Mudança de variável `t = e^{−u}` para integrais reais sobre `(0, ∞)`. -/
theorem integral_Ioi_eq (h : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), h t = ∫ u, rexp (-u) * h (rexp (-u)) := by
  rw [← rexp_neg_image, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    rexp_neg_deriv rexp_neg_injOn]
  simp [abs_of_pos (Real.exp_pos _)]

/-- Integrabilidade na mesma mudança de variável. -/
theorem integrableOn_Ioi_iff (h : ℝ → ℝ) :
    IntegrableOn h (Ioi 0) ↔ Integrable (fun u => rexp (-u) * h (rexp (-u))) := by
  rw [← rexp_neg_image, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    rexp_neg_deriv rexp_neg_injOn]
  simp [abs_of_pos (Real.exp_pos _)]

/-- `|g(u)|² = e^{−u} |f(e^{−u})|²`. -/
theorem norm_sq_lado (u : ℝ) : ‖lado f u‖ ^ 2 = rexp (-u) * ‖f (rexp (-u))‖ ^ 2 := by
  have he : rexp (-(1 / 2 : ℝ) * u) ^ 2 = rexp (-u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [lado, norm_smul, mul_pow, Real.norm_of_nonneg (Real.exp_pos _).le, he]

/-- `g ∈ L¹` quando a integral de Mellin converge em `Re s = 1/2`. -/
theorem integrable_lado (hf : MellinConvergent f ((1 / 2 : ℝ) : ℂ)) : Integrable (lado f) := by
  rw [MellinConvergent, ← rexp_neg_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv rexp_neg_injOn, integrableOn_univ] at hf
  refine hf.congr (ae_of_all _ fun x => ?_)
  have hpos : 0 ≤ rexp (-x) := (Real.exp_pos _).le
  have hexp : ((1 / 2 : ℝ) : ℂ) - 1 = (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  simp only [Function.comp_apply, lado, abs_neg, abs_of_pos (Real.exp_pos _)]
  rw [hexp, ← Complex.ofReal_cpow hpos]
  simp only [smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- `𝓕 g (ξ) = 𝓜f(1/2 + 2πiξ)`. -/
theorem fourier_lado (ξ : ℝ) :
    𝓕 (lado f) ξ = mellin f (1 / 2 + ((2 * π * ξ : ℝ) : ℂ) * Complex.I) := by
  rw [mellin_eq_fourier]
  have hre : (1 / 2 + ((2 * π * ξ : ℝ) : ℂ) * Complex.I).re = 1 / 2 := by simp
  have him : (1 / 2 + ((2 * π * ξ : ℝ) : ℂ) * Complex.I).im = 2 * π * ξ := by simp
  have hξ : 2 * π * ξ / (2 * π) = ξ := by field_simp
  rw [hre, him, hξ]
  rfl

/-- **Plancherel de Mellin** na linha `Re s = 1/2`. -/
theorem integral_norm_sq_eq_mellin (h1 : MellinConvergent f ((1 / 2 : ℝ) : ℂ))
    (h2 : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 =
      (2 * π)⁻¹ * ∫ τ : ℝ, ‖mellin f (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2 := by
  have hg1 : Integrable (lado f) := integrable_lado h1
  have hsq : Integrable (fun u => ‖lado f u‖ ^ 2) := by
    have h := (integrableOn_Ioi_iff (fun t => ‖f t‖ ^ 2)).mp h2
    simpa [norm_sq_lado] using h
  have hg2 : MemLp (lado f) 2 :=
    (memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable).mpr hsq
  have e1 : ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 = ∫ u, ‖lado f u‖ ^ 2 := by
    rw [integral_Ioi_eq]
    simp_rw [norm_sq_lado]
  have e2 : ∫ u, ‖lado f u‖ ^ 2 = ∫ ξ, ‖𝓕 (lado f) ξ‖ ^ 2 :=
    (ATK.PlancherelL1L2.integral_norm_sq_fourier hg1 hg2).symm
  have e3 : ∫ ξ, ‖𝓕 (lado f) ξ‖ ^ 2 =
      ∫ ξ : ℝ, (fun τ : ℝ => ‖mellin f (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2) ((2 * π) * ξ) := by
    congr 1 with ξ
    rw [fourier_lado]
  rw [e1, e2, e3, Measure.integral_comp_mul_left
    (fun τ : ℝ => ‖mellin f (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2) (2 * π),
    abs_of_pos (by positivity), smul_eq_mul]

end ATK.MellinPlancherel

#print axioms ATK.MellinPlancherel.integral_Ioi_eq
#print axioms ATK.MellinPlancherel.integrableOn_Ioi_iff
#print axioms ATK.MellinPlancherel.norm_sq_lado
#print axioms ATK.MellinPlancherel.integrable_lado
#print axioms ATK.MellinPlancherel.fourier_lado
#print axioms ATK.MellinPlancherel.integral_norm_sq_eq_mellin
