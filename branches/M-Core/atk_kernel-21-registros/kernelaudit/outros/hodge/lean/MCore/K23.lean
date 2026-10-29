import MCore.K22

namespace MCore

#check RationalCoefficientInterface
#check ConcreteCycleSpanSpecification
#check ConcreteAlgebraicityPayload

/-- K23 strengthens the K21 coefficient representation without claiming that
    the abstract coefficient carrier is literally `Rat`.  Equality of encoded
    fractions is expressed by cross multiplication, avoiding division and any
    hidden field structure. -/
structure FaithfulRationalCoefficientInterface (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) extends RationalCoefficientInterface G M where
  ofInt_numerator : ∀ z : Int, numerator (ofInt z) = z
  ofInt_denominator : ∀ z : Int, denominator (ofInt z) = 1
  fraction_ext : ∀ a b : M.Coeff,
    a = b ↔ numerator a * Int.ofNat (denominator b) =
      numerator b * Int.ofNat (denominator a)

/-- The faithful coefficient interface is deliberately only a representation
    contract.  It does not manufacture a cycle-span adapter, geometry, or the
    algebraicity payload. -/
structure FaithfulConcreteModelObligation (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  coefficients : FaithfulRationalCoefficientInterface G M
  algebraicLaws : RationalCycleSpanLaws G M
  semanticAdapter : CycleSpanAdapter G M

/-- Forgetting the extra faithfulness laws recovers exactly the K21
    specification. -/
def k23_to_k21_spec
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : FaithfulConcreteModelObligation G M) :
    ConcreteCycleSpanSpecification G M :=
  { rationalCoefficients := model.coefficients.toRationalCoefficientInterface
    algebraicLaws := model.algebraicLaws
    semanticAdapter := model.semanticAdapter }

/-- K23 adds no algebraicity theorem: it only transports the stronger model
    contract into the already-certified K21 span equivalence. -/
theorem k23_span_equivalence
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : FaithfulConcreteModelObligation G M)
    {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)) :
    G.inCycleClassSpan p α ↔ InConcreteCycleSpan M α :=
  k21_span_equivalence (k23_to_k21_spec model) α

/-- Geometry remains an independent input. -/
def k23_boundary
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : FaithfulConcreteModelObligation G M)
    (geometry : GeometryObligation G M) : HodgeCertificationBoundary G M :=
  k21_boundary_of_spec (k23_to_k21_spec model) geometry.cycleClassGeometry

/-- Closure remains explicitly conditional on the separate open algebraicity
    payload.  The stronger coefficient contract cannot close Hodge by itself. -/
theorem k23_closure_is_conditional
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : FaithfulConcreteModelObligation G M)
    (geometry : GeometryObligation G M)
    (algebraicity : AlgebraicityObligation G M) :
    GradedRationalHodgeConjecture G :=
  boundary_and_payload_imply_hodge (k23_boundary model geometry) algebraicity.payload

structure K23Frontier where
  coefficientFaithfulness : SignatureStatus
  spanAdapter : SignatureStatus
  geometry : SignatureStatus
  algebraicity : SignatureStatus
  hodge : SignatureStatus

def k23_frontier : K23Frontier :=
  { coefficientFaithfulness := .definitionInterface
    spanAdapter := .openBridge
    geometry := .openBridge
    algebraicity := .openBridge
    hodge := .openBridge }

theorem k23_span_adapter_open : k23_frontier.spanAdapter = .openBridge := rfl
theorem k23_geometry_open : k23_frontier.geometry = .openBridge := rfl
theorem k23_algebraicity_open : k23_frontier.algebraicity = .openBridge := rfl
theorem k23_hodge_open : k23_frontier.hodge = .openBridge := rfl

def k23_coefficient_status : SignatureStatus := .definitionInterface
def k23_reduction_status : SignatureStatus := .provedProperty

#print axioms k23_to_k21_spec
#print axioms k23_span_equivalence
#print axioms k23_boundary
#print axioms k23_closure_is_conditional
#print axioms k23_span_adapter_open
#print axioms k23_geometry_open
#print axioms k23_algebraicity_open
#print axioms k23_hodge_open

end MCore
