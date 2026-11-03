import MCore.MaterialMath.TriCyclicAlgebra

namespace MCore.MaterialMath

namespace TriNumber

variable {α : Type*}

/-- Inverse coordinate map from the ordinary product α³. -/
def fromProduct (p : α × α × α) : TriNumber α where
  manifest := p.1
  crossing := p.2.1
  seed := p.2.2

theorem fromProduct_toProduct (x : TriNumber α) :
    fromProduct (toProduct x) = x := by
  cases x
  rfl

theorem toProduct_fromProduct (p : α × α × α) :
    toProduct (fromProduct p) = p := by
  rcases p with ⟨a, b, c⟩
  rfl

/-- Coordinate equivalence between tri-numbers and α³. -/
def productEquiv : TriNumber α ≃ α × α × α where
  toFun := toProduct
  invFun := fromProduct
  left_inv := fromProduct_toProduct
  right_inv := toProduct_fromProduct

/-- The coordinate map is continuous by construction of the induced topology. -/
theorem continuous_toProduct [TopologicalSpace α] :
    Continuous (toProduct : TriNumber α → α × α × α) := by
  exact continuous_induced_dom

/-- The inverse coordinate map is also continuous; hence the induced topology
is exactly the transported product topology. -/
theorem continuous_fromProduct [TopologicalSpace α] :
    Continuous (fromProduct : α × α × α → TriNumber α) := by
  apply (continuous_induced_rng).2
  simpa [Function.comp_def, toProduct, fromProduct] using
    (continuous_id : Continuous (fun p : α × α × α => p))

/-- Canonical homeomorphism with the ordinary product space α³. -/
def productHomeomorph [TopologicalSpace α] :
    TriNumber α ≃ₜ α × α × α where
  toEquiv := productEquiv
  continuous_toFun := continuous_toProduct
  continuous_invFun := continuous_fromProduct

end TriNumber

end MCore.MaterialMath
