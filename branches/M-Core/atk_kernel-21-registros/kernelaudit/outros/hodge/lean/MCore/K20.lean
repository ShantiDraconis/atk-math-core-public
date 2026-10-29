import MCore.K19

namespace MCore

/-- Final K15-K20 boundary summary.  It packages the interfaces required to
    transport a concrete algebraicity proof, but contains no such proof. -/
structure HodgeCertificationBoundary (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  spanAdapter : CycleSpanAdapter G M
  geometry : CycleClassGeometryInterface G M

/-- If the still-open concrete algebraicity payload is explicitly supplied,
    the certified reduction chain transports it to the graded Hodge statement. -/
theorem boundary_and_payload_imply_hodge
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h : ConcreteAlgebraicityPayload M) :
    GradedRationalHodgeConjecture G :=
  (hodge_iff_concretePayload B.spanAdapter).2 h

/-- Conversely, Hodge plus the explicit span adapter recovers the concrete
    payload.  This is a logical equivalence, not new algebraicity evidence. -/
theorem hodge_implies_payload_at_boundary
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h : GradedRationalHodgeConjecture G) :
    ConcreteAlgebraicityPayload M :=
  (hodge_iff_concretePayload B.spanAdapter).1 h

/-- Exact final reduction under the explicit boundary interfaces. -/
theorem hodge_iff_payload_at_boundary
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) :
    GradedRationalHodgeConjecture G ↔ ConcreteAlgebraicityPayload M :=
  hodge_iff_concretePayload B.spanAdapter

/-- Epistemic firewall for the end of the K15-K20 chain. -/
def k20_reduction_status : SignatureStatus := .provedProperty

def k20_boundary_status : SignatureStatus := .definitionInterface

def k20_algebraicity_status : SignatureStatus := .openBridge

def k20_hodge_status : SignatureStatus := .openBridge

theorem k20_algebraicity_still_open :
    k20_algebraicity_status = .openBridge := rfl

theorem k20_hodge_still_open :
    k20_hodge_status = .openBridge := rfl

#print axioms boundary_and_payload_imply_hodge
#print axioms hodge_implies_payload_at_boundary
#print axioms hodge_iff_payload_at_boundary

end MCore
