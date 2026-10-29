import MCore.Hodge

namespace MCore

/-- A local algebraicity witness for one rational Hodge class.  The witness
    proposition is deliberately the semantic `rationalSpanOfCycles`; no
    existence theorem is smuggled into the definition. -/
def AlgebraicityAt (D : HodgeSemanticData) {X : D.Variety} (α : D.Class X) : Prop :=
  D.rationalSpanOfCycles α

/-- The pointwise form of the open bridge. -/
def PointwiseHodgeAlgebraicity (D : HodgeSemanticData) : Prop :=
  ∀ (X : D.Variety), D.isSmoothProjective X →
    ∀ α : D.Class X, D.isRationalHodgeClass α → AlgebraicityAt D α

/-- K9 reduction: the global conjecture and its pointwise algebraicity
    obligation are definitionally equivalent. -/
theorem rationalHodge_iff_pointwise (D : HodgeSemanticData) :
    RationalHodgeConjecture D ↔ PointwiseHodgeAlgebraicity D := by
  rfl

/-- A bridge can be consumed pointwise, but is never synthesized here. -/
theorem bridge_gives_pointwise {D : HodgeSemanticData} (h : HodgeBridge D) :
    PointwiseHodgeAlgebraicity D :=
  (rationalHodge_iff_pointwise D).mp (bridge_implies_hodge h)

/-- Conversely, a genuine proof of every local obligation closes the semantic
    conjecture.  This theorem only packages a supplied proof. -/
theorem pointwise_closes_hodge {D : HodgeSemanticData}
    (h : PointwiseHodgeAlgebraicity D) : RationalHodgeConjecture D :=
  (rationalHodge_iff_pointwise D).mpr h

/-- Audit classification: reduction is proved; the payload remains open. -/
def hodge_reduction_status : SignatureStatus := .provedProperty

def pointwise_algebraicity_payload_status : SignatureStatus := .openBridge

theorem hodge_reduction_proved : hodge_reduction_status = .provedProperty := rfl
theorem pointwise_payload_open :
    pointwise_algebraicity_payload_status = .openBridge := rfl

end MCore
