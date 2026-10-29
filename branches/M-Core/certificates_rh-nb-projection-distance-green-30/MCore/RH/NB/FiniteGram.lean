import Mathlib
import MCore.RH.NB.Distance

open scoped InnerProductSpace

namespace MCore.RH.NB

/-- A finite family in a real inner-product space. This is the algebraic layer needed
before identifying the vectors with the concrete Nyman--Beurling generators. -/
structure FiniteApproximationSystem (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) where
  target : E
  generator : Fin n → E

/-- Real Gram matrix of the finite generator family. -/
def gramMatrix {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (S : FiniteApproximationSystem E n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⟪S.generator i, S.generator j⟫_ℝ

/-- Every real Gram matrix is symmetric. -/
theorem gramMatrix_symmetric {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (S : FiniteApproximationSystem E n) :
    (gramMatrix S).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact real_inner_comm _ _

/-- The Gram quadratic form is nonnegative. This theorem requires no RH assumption
and does not assert invertibility. -/
theorem gram_quadratic_nonneg {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (S : FiniteApproximationSystem E n)
    (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * gramMatrix S i j * c j := by
  let v : E := ∑ i, c i • S.generator i
  have hv : 0 ≤ ⟪v, v⟫_ℝ := real_inner_self_nonneg
  have hexpand :
      ⟪v, v⟫_ℝ = ∑ i, ∑ j, c i * gramMatrix S i j * c j := by
    simp only [v, gramMatrix, inner_sum, sum_inner, real_inner_smul_left,
      real_inner_smul_right]
    congr 1
    funext i
    congr 1
    funext j
    rw [real_inner_comm]
    ring
  rw [hexpand] at hv
  exact hv

/-- Invertibility is kept as an explicit certificate. Later NB code must either prove
this from linear independence or use a projection formulation that does not require it. -/
structure InvertibleGramCertificate {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (S : FiniteApproximationSystem E n) where
  invertible : IsUnit (gramMatrix S).det

end MCore.RH.NB
