import MCore.K11

namespace MCore

/-- K12 packages exactly what was proved at K11.  The algebraicity payload is
    deliberately a field of evidence, never manufactured by the certificate. -/
structure K11LogicalCertificate (D : HodgeSemanticData)
    (H : FixedCodimensionHodgeData D) where
  forward : FixedCodimensionAlgebraicity D H → PointwiseHodgeAlgebraicity D
  backward : PointwiseHodgeAlgebraicity D → FixedCodimensionAlgebraicity D H

/-- Closed construction of the logical K11 certificate. -/
def k11LogicalCertificate (D : HodgeSemanticData)
    (H : FixedCodimensionHodgeData D) : K11LogicalCertificate D H :=
  ⟨fixedCodimension_implies_pointwise H,
   pointwise_implies_fixedCodimension H⟩

/-- No-promotion firewall: a logical certificate only transports an explicitly
    supplied algebraicity proof. -/
theorem k12_noPromotion
    {D : HodgeSemanticData} {H : FixedCodimensionHodgeData D}
    (cert : K11LogicalCertificate D H)
    (h : FixedCodimensionAlgebraicity D H) :
    RationalHodgeConjecture D := by
  exact pointwise_closes_hodge (cert.forward h)

/-- Conversely, an actual proof of Hodge supplies the open payload; this is
    reduction bookkeeping, not new algebraic geometry. -/
theorem k12_hodge_supplies_payload
    {D : HodgeSemanticData} {H : FixedCodimensionHodgeData D}
    (h : RationalHodgeConjecture D) :
    FixedCodimensionAlgebraicity D H := by
  exact pointwise_implies_fixedCodimension H
    ((rationalHodge_iff_pointwise D).mp h)

def k12_logical_certificate_status : SignatureStatus := .provedProperty

def k12_hodge_endpoint_status : SignatureStatus := .openBridge

theorem k12_endpoint_not_promoted :
    k12_hodge_endpoint_status = .openBridge := rfl

#print axioms k11LogicalCertificate
#print axioms k12_noPromotion
#print axioms k12_hodge_supplies_payload

end MCore
