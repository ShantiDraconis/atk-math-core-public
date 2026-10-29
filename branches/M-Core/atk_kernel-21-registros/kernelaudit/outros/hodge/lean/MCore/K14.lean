import MCore.K13

namespace MCore

/-- K14 names the exact remaining graded algebraicity payload. -/
def GradedAlgebraicityPayload (G : GradedRationalHodgeData) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
    GradedAlgebraicityAt G X p α

/-- The graded conjecture is exactly the remaining algebraicity payload. -/
theorem gradedHodge_iff_algebraicityPayload (G : GradedRationalHodgeData) :
    GradedRationalHodgeConjecture G ↔ GradedAlgebraicityPayload G := by
  exact gradedHodge_iff_pointwise G

/-- Explicit evidence object. Constructing this object requires the payload;
    its existence is not asserted by K14. -/
structure GradedAlgebraicityEvidence (G : GradedRationalHodgeData) where
  proof : GradedAlgebraicityPayload G

/-- Evidence closes the graded statement, but only because the open payload was
    explicitly supplied. -/
theorem gradedEvidence_closes
    {G : GradedRationalHodgeData} (E : GradedAlgebraicityEvidence G) :
    GradedRationalHodgeConjecture G :=
  (gradedHodge_iff_algebraicityPayload G).2 E.proof

/-- No-promotion converse: a genuine proof of the graded conjecture yields the
    evidence payload; the certificate never creates algebraicity. -/
def gradedEvidence_of_hodge
    {G : GradedRationalHodgeData} (h : GradedRationalHodgeConjecture G) :
    GradedAlgebraicityEvidence G :=
  ⟨(gradedHodge_iff_algebraicityPayload G).1 h⟩

def k14_reduction_status : SignatureStatus := .provedProperty

def k14_algebraicity_payload_status : SignatureStatus := .openBridge

theorem k14_payload_still_open :
    k14_algebraicity_payload_status = .openBridge := rfl

#print axioms gradedHodge_iff_algebraicityPayload
#print axioms gradedEvidence_closes
#print axioms gradedEvidence_of_hodge

end MCore
