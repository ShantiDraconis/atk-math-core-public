import Mathlib

namespace MCore.RH.LCRH

/-- Finite real Gram data. No invertibility or RH-related property is built into the definition. -/
structure FiniteGramData (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) where
  vector : Fin n → E

namespace FiniteGramData

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- The Gram matrix of the finite family. -/
def matrix (G : FiniteGramData E n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⟪G.vector i, G.vector j⟫_ℝ

/-- The vector represented by a coefficient family. -/
def combination (G : FiniteGramData E n) (c : Fin n → ℝ) : E :=
  ∑ i, c i • G.vector i

/-- Gram energy is represented geometrically as the squared norm of the combination.
A later matrix-expansion theorem may identify this with cᵀGc. -/
def energy (G : FiniteGramData E n) (c : Fin n → ℝ) : ℝ :=
  ‖G.combination c‖ ^ 2

/-- Positive-semidefiniteness of the geometric Gram energy requires no independence assumption. -/
theorem energy_nonneg (G : FiniteGramData E n) (c : Fin n → ℝ) :
    0 ≤ G.energy c := by
  exact sq_nonneg _

/-- The Gram matrix is symmetric in a real inner-product space. -/
theorem matrix_symm (G : FiniteGramData E n) (i j : Fin n) :
    G.matrix i j = G.matrix j i := by
  exact real_inner_comm _ _

/-- Independence is an explicit certificate. It is not silently inferred from a Gram matrix. -/
structure IndependenceCertificate (G : FiniteGramData E n) : Prop where
  independent : LinearIndependent ℝ G.vector

/-- Invertibility is also an explicit downstream certificate until the PosDef→invertible
matrix theorem is wired against the pinned Mathlib API. -/
structure InvertibilityCertificate (G : FiniteGramData E n) : Prop where
  invertible : IsUnit G.matrix.det

/-- Projection/Gram formulas must be proved for the concrete target and family; they
are not consequences of the abstract data alone. -/
structure ProjectionFormulaCertificate (G : FiniteGramData E n) (target : E) where
  projected : E
  in_span : projected ∈ Submodule.span ℝ (Set.range G.vector)
  residual_orthogonal : ∀ i, ⟪target - projected, G.vector i⟫_ℝ = 0

end FiniteGramData

end MCore.RH.LCRH
