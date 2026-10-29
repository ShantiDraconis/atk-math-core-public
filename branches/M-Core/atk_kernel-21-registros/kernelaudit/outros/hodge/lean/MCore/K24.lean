import MCore.K23

namespace MCore

#check FaithfulRationalCoefficientInterface
#check FaithfulConcreteModelObligation
#check ConcreteAlgebraicityPayload

/-- K24 makes the remaining coefficient-operation contract explicit.  K23
    identifies coefficients extensionally by their fraction encodings; K24
    additionally requires the abstract zero and addition operations to agree
    with integer fraction arithmetic by cross multiplication.  No division,
    field structure, geometry, or algebraicity is manufactured here. -/
structure RationalCoefficientOperationLaws (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G)
    (R : FaithfulRationalCoefficientInterface G M) where
  zero_numerator : R.numerator M.zero = 0
  add_fraction : ∀ a b : M.Coeff,
    R.numerator (M.add a b) *
        Int.ofNat (R.denominator a * R.denominator b) =
      (R.numerator a * Int.ofNat (R.denominator b) +
        R.numerator b * Int.ofNat (R.denominator a)) *
        Int.ofNat (R.denominator (M.add a b))

/-- K24 is still a specification bundle.  Existence for a concrete rational
    coefficient model is not asserted. -/
structure OperationFaithfulConcreteModelObligation
    (G : GradedRationalHodgeData) (M : CycleSpanMechanics G) where
  model : FaithfulConcreteModelObligation G M
  operationLaws : RationalCoefficientOperationLaws G M model.coefficients

/-- Forgetting the operation-fidelity layer recovers exactly K23. -/
def k24_to_k23_model
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : OperationFaithfulConcreteModelObligation G M) :
    FaithfulConcreteModelObligation G M := model.model

/-- The span equivalence remains the already-certified mechanical reduction. -/
theorem k24_span_equivalence
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : OperationFaithfulConcreteModelObligation G M)
    {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)) :
    G.inCycleClassSpan p α ↔ InConcreteCycleSpan M α :=
  k23_span_equivalence (k24_to_k23_model model) α

/-- Geometry remains an independent OPEN_BRIDGE input. -/
def k24_boundary
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : OperationFaithfulConcreteModelObligation G M)
    (geometry : GeometryObligation G M) : HodgeCertificationBoundary G M :=
  k23_boundary (k24_to_k23_model model) geometry

/-- Hodge closure remains conditional on the separate algebraicity payload. -/
theorem k24_closure_is_conditional
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : OperationFaithfulConcreteModelObligation G M)
    (geometry : GeometryObligation G M)
    (algebraicity : AlgebraicityObligation G M) :
    GradedRationalHodgeConjecture G :=
  k23_closure_is_conditional (k24_to_k23_model model) geometry algebraicity

structure K24Frontier where
  coefficientRepresentation : SignatureStatus
  coefficientOperations : SignatureStatus
  spanAdapter : SignatureStatus
  geometry : SignatureStatus
  algebraicity : SignatureStatus
  hodge : SignatureStatus

def k24_frontier : K24Frontier :=
  { coefficientRepresentation := .definitionInterface
    coefficientOperations := .definitionInterface
    spanAdapter := .openBridge
    geometry := .openBridge
    algebraicity := .openBridge
    hodge := .openBridge }

theorem k24_span_adapter_open : k24_frontier.spanAdapter = .openBridge := rfl
theorem k24_geometry_open : k24_frontier.geometry = .openBridge := rfl
theorem k24_algebraicity_open : k24_frontier.algebraicity = .openBridge := rfl
theorem k24_hodge_open : k24_frontier.hodge = .openBridge := rfl

def k24_coefficient_representation_status : SignatureStatus := .definitionInterface
def k24_coefficient_operations_status : SignatureStatus := .definitionInterface
def k24_reduction_status : SignatureStatus := .provedProperty

#print axioms k24_to_k23_model
#print axioms k24_span_equivalence
#print axioms k24_boundary
#print axioms k24_closure_is_conditional
#print axioms k24_span_adapter_open
#print axioms k24_geometry_open
#print axioms k24_algebraicity_open
#print axioms k24_hodge_open

end MCore
