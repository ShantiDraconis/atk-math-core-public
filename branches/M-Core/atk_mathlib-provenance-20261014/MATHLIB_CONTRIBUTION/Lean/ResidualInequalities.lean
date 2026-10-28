import Mathlib

/-!
# ATK Mathlib candidates — elementary residual inequalities

Origin: ShantiDraconis/m-core-riemann
Source: atk-kernel/ATK/Riemann.lean
Source blob SHA: 018b395f949eca88536537428244f4c2d369e06b

This module intentionally extracts only the elementary inequality. The
original source remains unchanged. This does not prove the Riemann hypothesis.
This is a candidate for review, not an upstream Mathlib contribution.

Build and axiom audit still required against the pinned Mathlib version.
-/

namespace ATK.MathlibCandidates

/-- A nonnegative quadratic correction decreases a real residual. -/
theorem residual_sub_square_div_le (residual correction denominator : ℝ)
    (hdenominator : 0 < denominator) :
    residual - correction ^ 2 / denominator ≤ residual := by
  have hnonneg : 0 ≤ correction ^ 2 / denominator :=
    div_nonneg (sq_nonneg correction) hdenominator.le
  linarith

end ATK.MathlibCandidates

#print axioms ATK.MathlibCandidates.residual_sub_square_div_le
