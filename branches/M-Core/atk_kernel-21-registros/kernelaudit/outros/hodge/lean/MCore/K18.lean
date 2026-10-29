import MCore.K17

namespace MCore

/-- Concrete finite-cycle formulation of the remaining algebraicity payload. -/
def ConcreteAlgebraicityPayload {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
    G.isSmoothProjective X → G.isTypePP p α → InConcreteCycleSpan M α

/-- K18 normalizes the concrete payload to the K16 surjectivity formulation. -/
theorem concretePayload_iff_surjectivity
    {G : GradedRationalHodgeData} (M : CycleSpanMechanics G) :
    ConcreteAlgebraicityPayload M ↔ ConcreteHodgeSurjectivity M := by
  constructor
  · intro h X hsp p α hpp
    exact h X p α hsp hpp
  · intro h X p α hsp hpp
    exact h X hsp p α hpp

/-- Under the explicit K15 span adapter, the concrete finite-cycle payload is
    exactly the semantic graded Hodge statement.  No adapter is manufactured. -/
theorem hodge_iff_concretePayload
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M) :
    GradedRationalHodgeConjecture G ↔ ConcreteAlgebraicityPayload M := by
  exact (hodge_iff_concreteSurjectivity A).trans
    (concretePayload_iff_surjectivity M).symm

/-- Evidence wrapper is deliberately conditional: constructing this structure
    requires the still-open concrete algebraicity payload. -/
structure ConcreteAlgebraicityEvidence (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  proof : ConcreteAlgebraicityPayload M

/-- Explicit evidence plus the adapter transports to Hodge. -/
theorem concreteEvidence_closes
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M) (E : ConcreteAlgebraicityEvidence G M) :
    GradedRationalHodgeConjecture G :=
  (hodge_iff_concretePayload A).2 E.proof

def k18_payload_normalization_status : SignatureStatus := .provedProperty

def k18_span_adapter_status : SignatureStatus := .openBridge

def k18_concrete_algebraicity_status : SignatureStatus := .openBridge

theorem k18_adapter_still_open :
    k18_span_adapter_status = .openBridge := rfl

theorem k18_algebraicity_still_open :
    k18_concrete_algebraicity_status = .openBridge := rfl

#print axioms concretePayload_iff_surjectivity
#print axioms hodge_iff_concretePayload
#print axioms concreteEvidence_closes

end MCore
