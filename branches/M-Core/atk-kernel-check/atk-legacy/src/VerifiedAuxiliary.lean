import Mathlib

/-! Forward-only auxiliary lemmas. No conjecture is assumed or certified. -/
namespace ATK.VerifiedAuxiliary

-- Riemann: finite Gram examples and conditional Schur decrement.
theorem rh_finite_decrement : (5 : ℚ) / 6 - 7 / 12 = 1 / 4 := by norm_num
theorem rh_ratio : ((7 : ℚ) / 12) / (5 / 6) = 7 / 10 := by norm_num
theorem rh_relative_reduction : (1 : ℚ) - (7 / 10) = 3 / 10 := by norm_num
theorem rh_schur_nonnegative (r s : ℝ) (hs : 0 < s) : 0 ≤ r ^ 2 / s := by
  exact div_nonneg (sq_nonneg r) (le_of_lt hs)
theorem rh_schur_antitone (d₀ d₁ r s : ℝ) (hs : 0 < s)
    (h : d₀ - d₁ = r ^ 2 / s) : d₁ ≤ d₀ := by
  have hnonneg : 0 ≤ r ^ 2 / s := rh_schur_nonnegative r s hs
  linarith

-- Navier–Stokes: exact budget algebra, not universal bounds.
theorem ns_margin_example : (1 : ℚ) - 1 / 4 - 1 / 3 = 5 / 12 := by norm_num
theorem ns_budget_example : (1 : ℚ) / 4 + 1 / 3 = 7 / 12 := by norm_num
theorem ns_budget_identity (b t : ℝ) : (1 - b - t) + (b + t) = 1 := by ring
theorem ns_margin_positive (b t : ℝ) (h : b + t < 1) : 0 < 1 - b - t := by linarith
theorem ns_bulk_tail_bound (b t ν z B T : ℝ)
    (hB : B ≤ b * (ν * z)) (hT : T ≤ t * (ν * z)) :
    B + T ≤ (b + t) * (ν * z) := by
  calc
    B + T ≤ b * (ν * z) + t * (ν * z) := add_le_add hB hT
    _ = (b + t) * (ν * z) := by ring

-- BSD: determinant/regulator algebra, conditional division.
theorem bsd_regulator_example : (2 : ℚ) * 3 - 1 ^ 2 = 5 := by norm_num
theorem bsd_regulator_identity (h11 h12 h22 : ℝ) :
    h11 * h22 - h12 ^ 2 = h11 * h22 - h12 * h12 := by ring
theorem bsd_recover_h22 (h11 h12 h22 R : ℝ)
    (h11ne : h11 ≠ 0) (hR : R = h11 * h22 - h12 ^ 2) :
    h22 = (R + h12 ^ 2) / h11 := by
  apply (eq_div_iff h11ne).2
  nlinarith [hR]

-- Generic finite linear-system existence: requires a supplied inverse.
theorem hodge_linear_realization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    [Invertible A] : ∃ q : Fin n → ℚ, A *ᵥ q = b := by
  refine ⟨⅟ A *ᵥ b, ?_⟩
  rw [← Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]

#print axioms ATK.VerifiedAuxiliary.rh_schur_antitone
#print axioms ATK.VerifiedAuxiliary.ns_bulk_tail_bound
#print axioms ATK.VerifiedAuxiliary.bsd_recover_h22
#print axioms ATK.VerifiedAuxiliary.hodge_linear_realization
end ATK.VerifiedAuxiliary

#print axioms ATK.VerifiedAuxiliary.rh_finite_decrement
#print axioms ATK.VerifiedAuxiliary.rh_ratio
#print axioms ATK.VerifiedAuxiliary.rh_relative_reduction
#print axioms ATK.VerifiedAuxiliary.rh_schur_nonnegative
#print axioms ATK.VerifiedAuxiliary.ns_margin_example
#print axioms ATK.VerifiedAuxiliary.ns_budget_example
#print axioms ATK.VerifiedAuxiliary.ns_budget_identity
#print axioms ATK.VerifiedAuxiliary.ns_margin_positive
#print axioms ATK.VerifiedAuxiliary.bsd_regulator_example
#print axioms ATK.VerifiedAuxiliary.bsd_regulator_identity