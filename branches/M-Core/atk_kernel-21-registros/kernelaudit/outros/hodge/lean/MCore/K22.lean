import MCore.K21

namespace MCore

/-- K22 decomposes the post-K21 frontier into independent obligations.  In
    particular, supplying a coefficient/span model must not itself supply the
    geometric or algebraicity statements. -/
structure ConcreteModelObligation (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  spanSpecification : ConcreteCycleSpanSpecification G M

structure GeometryObligation (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  cycleClassGeometry : CycleClassGeometryInterface G M

structure AlgebraicityObligation (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  payload : ConcreteAlgebraicityPayload M

/-- Model + geometry constructs exactly the K20 boundary.  Algebraicity is not
    a field of either input and therefore cannot be smuggled through this map. -/
def k22_boundary
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : ConcreteModelObligation G M)
    (geometry : GeometryObligation G M) : HodgeCertificationBoundary G M :=
  k21_boundary_of_spec model.spanSpecification geometry.cycleClassGeometry

/-- Closure is deliberately conditional on a separately supplied algebraicity
    obligation.  This theorem is only logical plumbing; it does not construct
    the open payload. -/
theorem k22_closure_is_conditional
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : ConcreteModelObligation G M)
    (geometry : GeometryObligation G M)
    (algebraicity : AlgebraicityObligation G M) :
    GradedRationalHodgeConjecture G :=
  boundary_and_payload_imply_hodge (k22_boundary model geometry) algebraicity.payload

/-- Conversely, even with model and geometry fixed, Hodge only recovers the
    algebraicity payload through the already-certified equivalence; this does
    not turn the payload into an unconditional theorem. -/
theorem k22_hodge_recovers_payload
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : ConcreteModelObligation G M)
    (geometry : GeometryObligation G M)
    (h : GradedRationalHodgeConjecture G) :
    ConcreteAlgebraicityPayload M :=
  hodge_implies_payload_at_boundary (k22_boundary model geometry) h

/-- A fail-closed frontier record: each obligation has its own status. -/
structure K22Frontier where
  concreteModel : SignatureStatus
  geometry : SignatureStatus
  algebraicity : SignatureStatus
  hodge : SignatureStatus

def k22_frontier : K22Frontier :=
  { concreteModel := .definitionInterface
    geometry := .openBridge
    algebraicity := .openBridge
    hodge := .openBridge }

theorem k22_geometry_open : k22_frontier.geometry = .openBridge := rfl
theorem k22_algebraicity_open : k22_frontier.algebraicity = .openBridge := rfl
theorem k22_hodge_open : k22_frontier.hodge = .openBridge := rfl

def k22_reduction_status : SignatureStatus := .provedProperty

def k22_model_status : SignatureStatus := .definitionInterface

#print axioms k22_boundary
#print axioms k22_closure_is_conditional
#print axioms k22_hodge_recovers_payload
#print axioms k22_geometry_open
#print axioms k22_algebraicity_open
#print axioms k22_hodge_open

end MCore
