import Mathlib
import MCore.RH.NB.FiniteGram

open scoped InnerProductSpace

namespace MCore.RH.NB

/-- The synthesis map associated with a finite generator family. -/
def synthesis {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (S : FiniteApproximationSystem E n) (c : Fin n → ℝ) : E :=
  Fintype.linearCombination ℝ S.generator c

/-- The Gram quadratic form is exactly the squared norm of the synthesis vector. -/
theorem gram_quadratic_eq_norm_sq {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (S : FiniteApproximationSystem E n)
    (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * gramMatrix S i j * c j = ‖synthesis S c‖ ^ 2 := by
  have hinner :
      ⟪synthesis S c, synthesis S c⟫_ℝ =
        ∑ i, ∑ j, c i * gramMatrix S i j * c j := by
    simp only [synthesis, Fintype.linearCombination_apply, gramMatrix, inner_sum,
      sum_inner, real_inner_smul_left, real_inner_smul_right]
    congr 1
    funext i
    congr 1
    funext j
    rw [real_inner_comm]
    ring
  calc
    ∑ i, ∑ j, c i * gramMatrix S i j * c j =
        ⟪synthesis S c, synthesis S c⟫_ℝ := hinner.symm
    _ = ‖synthesis S c‖ ^ 2 := real_inner_self_eq_norm_sq (synthesis S c)

/-- Linear independence of the finite generators makes the synthesis map injective.
This is pointwise in `n`; it asserts no uniform conditioning as `n → ∞`. -/
theorem synthesis_eq_zero_iff_of_linearIndependent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (S : FiniteApproximationSystem E n)
    (hLI : LinearIndependent ℝ S.generator) (c : Fin n → ℝ) :
    synthesis S c = 0 ↔ c = 0 := by
  have hinj : Function.Injective (Fintype.linearCombination ℝ S.generator) := by
    rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    exact hLI
  constructor
  · intro h
    apply hinj
    simpa [synthesis] using h
  · intro h
    subst c
    simp [synthesis]

/-- A zero Gram quadratic form forces all coefficients to vanish under finite LI.
This is the coercivity/nondegeneracy fact needed before any determinant theorem. -/
theorem gram_quadratic_eq_zero_iff_of_linearIndependent
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (S : FiniteApproximationSystem E n)
    (hLI : LinearIndependent ℝ S.generator) (c : Fin n → ℝ) :
    (∑ i, ∑ j, c i * gramMatrix S i j * c j = 0) ↔ c = 0 := by
  rw [gram_quadratic_eq_norm_sq]
  rw [sq_eq_zero_iff, norm_eq_zero]
  exact synthesis_eq_zero_iff_of_linearIndependent S hLI c

end MCore.RH.NB
