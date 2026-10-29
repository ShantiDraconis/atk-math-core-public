import Mathlib
import MCore.RH.NB.FiniteGramIndependence

open scoped InnerProductSpace

namespace MCore.RH.NB

/-- If the finite generators are linearly independent, the Gram matrix has trivial
right kernel. This is a pointwise finite-dimensional statement; it carries no
uniform lower bound in the family size. -/
theorem gram_mulVec_eq_zero_imp_coeff_zero_of_linearIndependent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (S : FiniteApproximationSystem E n)
    (hLI : LinearIndependent ℝ S.generator) (c : Fin n → ℝ)
    (hc : Matrix.mulVec (gramMatrix S) c = 0) : c = 0 := by
  apply (gram_quadratic_eq_zero_iff_of_linearIndependent S hLI c).mp
  have hq :
      (∑ i, ∑ j, c i * gramMatrix S i j * c j) =
        ∑ i, c i * (Matrix.mulVec (gramMatrix S) c) i := by
    simp only [Matrix.mulVec, dotProduct]
    congr 1
    funext i
    rw [Finset.mul_sum]
    congr 1
    funext j
    ring
  rw [hq, hc]
  simp

/-- The Gram matrix has trivial right kernel under finite linear independence. -/
theorem gram_mulVec_kernel_trivial_of_linearIndependent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (S : FiniteApproximationSystem E n)
    (hLI : LinearIndependent ℝ S.generator) :
    ∀ c : Fin n → ℝ, Matrix.mulVec (gramMatrix S) c = 0 → c = 0 := by
  intro c hc
  exact gram_mulVec_eq_zero_imp_coeff_zero_of_linearIndependent S hLI c hc

/-- A square matrix over the reals with trivial right `mulVec` kernel has nonzero determinant.
This is the exact finite-dimensional bridge used by the Gram layer. -/
theorem det_ne_zero_of_mulVec_kernel_trivial
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hker : ∀ c : Fin n → ℝ, Matrix.mulVec G c = 0 → c = 0) :
    G.det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hcG⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  exact hc0 (hker c hcG)

/-- For every fixed finite system, linear independence of the generators implies
that its Gram determinant is nonzero. No uniform conditioning claim is made. -/
theorem gram_det_ne_zero_of_linearIndependent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (S : FiniteApproximationSystem E n)
    (hLI : LinearIndependent ℝ S.generator) :
    (gramMatrix S).det ≠ 0 := by
  exact det_ne_zero_of_mulVec_kernel_trivial (gramMatrix S)
    (gram_mulVec_kernel_trivial_of_linearIndependent S hLI)

end MCore.RH.NB
