import MCore.K24

namespace MCore

#check GradedRationalHodgeData
#check OperationFaithfulConcreteModelObligation
#check ConcreteAlgebraicityPayload

/-- K25 names the model-realization boundary explicitly.  It does not assert
    that the abstract carriers below are singular cohomology, actual algebraic
    cycles, or an implemented cycle-class map.  Those identifications are
    exactly the external formalization work this interface records. -/
structure ConcreteCohomologyModel (G : GradedRationalHodgeData) where
  rationalCohomologyRealized : Prop
  algebraicCyclesRealized : Prop
  hodgeTypeRealized : Prop
  cycleClassMapRealized : Prop

/-- Evidence that a proposed concrete model has discharged all four named
    realization obligations.  This is data supplied externally, not generated
    by the certification chain. -/
structure ConcreteCohomologyModelEvidence
    {G : GradedRationalHodgeData} (C : ConcreteCohomologyModel G) where
  rationalCohomology : C.rationalCohomologyRealized
  algebraicCycles : C.algebraicCyclesRealized
  hodgeType : C.hodgeTypeRealized
  cycleClassMap : C.cycleClassMapRealized

/-- K25 packages the concrete-model evidence separately from the already
    certified coefficient/span mechanics. -/
structure RealizedConcreteModelObligation
    (G : GradedRationalHodgeData) (M : CycleSpanMechanics G) where
  mechanics : OperationFaithfulConcreteModelObligation G M
  cohomologyModel : ConcreteCohomologyModel G
  realization : ConcreteCohomologyModelEvidence cohomologyModel

/-- Forgetting model realization recovers exactly the K24 obligation. -/
def k25_to_k24_model
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : RealizedConcreteModelObligation G M) :
    OperationFaithfulConcreteModelObligation G M := model.mechanics

/-- No new algebraicity is hidden in the model-realization layer. -/
theorem k25_span_equivalence
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : RealizedConcreteModelObligation G M)
    {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)) :
    G.inCycleClassSpan p α ↔ InConcreteCycleSpan M α :=
  k24_span_equivalence (k25_to_k24_model model) α

/-- Geometry remains a separate input even after a concrete model is named. -/
def k25_boundary
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : RealizedConcreteModelObligation G M)
    (geometry : GeometryObligation G M) : HodgeCertificationBoundary G M :=
  k24_boundary (k25_to_k24_model model) geometry

/-- Closure remains conditional on the conjectural algebraicity payload. -/
theorem k25_closure_is_conditional
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : RealizedConcreteModelObligation G M)
    (geometry : GeometryObligation G M)
    (algebraicity : AlgebraicityObligation G M) :
    GradedRationalHodgeConjecture G :=
  k24_closure_is_conditional (k25_to_k24_model model) geometry algebraicity

structure K25Frontier where
  concreteCohomologyModel : SignatureStatus
  coefficientMechanics : SignatureStatus
  spanAdapter : SignatureStatus
  geometry : SignatureStatus
  algebraicity : SignatureStatus
  hodge : SignatureStatus

def k25_frontier : K25Frontier :=
  { concreteCohomologyModel := .openBridge
    coefficientMechanics := .definitionInterface
    spanAdapter := .openBridge
    geometry := .openBridge
    algebraicity := .openBridge
    hodge := .openBridge }

theorem k25_concrete_model_open :
    k25_frontier.concreteCohomologyModel = .openBridge := rfl
theorem k25_span_adapter_open : k25_frontier.spanAdapter = .openBridge := rfl
theorem k25_geometry_open : k25_frontier.geometry = .openBridge := rfl
theorem k25_algebraicity_open : k25_frontier.algebraicity = .openBridge := rfl
theorem k25_hodge_open : k25_frontier.hodge = .openBridge := rfl

def k25_model_interface_status : SignatureStatus := .openBridge
def k25_reduction_status : SignatureStatus := .provedProperty

#print axioms k25_to_k24_model
#print axioms k25_span_equivalence
#print axioms k25_boundary
#print axioms k25_closure_is_conditional
#print axioms k25_concrete_model_open
#print axioms k25_span_adapter_open
#print axioms k25_geometry_open
#print axioms k25_algebraicity_open
#print axioms k25_hodge_open

end MCore
