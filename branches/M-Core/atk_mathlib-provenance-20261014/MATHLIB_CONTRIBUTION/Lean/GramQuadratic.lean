import Mathlib

/-!
# ATK — general Gram quadratic residual

Source: ShantiDraconis/m-core-riemann/atk-kernel/ATK/Riemann.lean
Original blob SHA: 018b395f949eca88536537428244f4c2d369e06b
Original declarations: ATK.Riemann.gram_complete_square,
ATK.Riemann.gram_residual_le

The exact mathematical statements and proofs are preserved below under an
ATK candidate namespace. These are NOT proofs of RH. Compile and inspect
#print axioms before any certification or upstream submission.
-/

namespace ATK.MathlibCandidates

open Matrix

theorem gram_complete_square {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hG : G.IsSymm) (hdet : IsUnit G.det) (b c : n → ℝ) :
    1 - 2 * (b ⬝ᵥ c) + c ⬝ᵥ (G *ᵥ c)
      = (1 - b ⬝ᵥ (G⁻¹ *ᵥ b)) + (c - G⁻¹ *ᵥ b) ⬝ᵥ (G *ᵥ (c - G⁻¹ *ᵥ b)) := by
  have hw : G *ᵥ (G⁻¹ *ᵥ b) = b := by
    rw [mulVec_mulVec, mul_nonsing_inv G hdet, one_mulVec]
  have hwc : (G⁻¹ *ᵥ b) ⬝ᵥ (G *ᵥ c) = b ⬝ᵥ c := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hG.eq, hw]
  have hcw : c ⬝ᵥ (G *ᵥ (G⁻¹ *ᵥ b)) = b ⬝ᵥ c := by
    rw [hw, dotProduct_comm]
  have hww : (G⁻¹ *ᵥ b) ⬝ᵥ (G *ᵥ (G⁻¹ *ᵥ b)) = b ⬝ᵥ (G⁻¹ *ᵥ b) := by
    rw [hw, dotProduct_comm]
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hwc, hcw, hww]
  ring

theorem gram_residual_le {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hPSD : G.PosSemidef) (hG : G.IsSymm) (hdet : IsUnit G.det)
    (b c : n → ℝ) :
    1 - b ⬝ᵥ (G⁻¹ *ᵥ b) ≤ 1 - 2 * (b ⬝ᵥ c) + c ⬝ᵥ (G *ᵥ c) := by
  rw [gram_complete_square G hG hdet b c]
  have h := hPSD.dotProduct_mulVec_nonneg (c - G⁻¹ *ᵥ b)
  have hstar : star (c - G⁻¹ *ᵥ b) = c - G⁻¹ *ᵥ b := by
    ext i
    simp
  rw [hstar] at h
  linarith

end ATK.MathlibCandidates

#print axioms ATK.MathlibCandidates.gram_complete_square
#print axioms ATK.MathlibCandidates.gram_residual_le
