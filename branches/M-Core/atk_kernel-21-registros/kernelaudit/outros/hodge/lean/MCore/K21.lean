import MCore.K20

namespace MCore

/-- Algebraic laws required for the finite cycle-span mechanics to behave as a
    rational linear span.  The operations already live in K15; K21 makes the
    previously implicit laws explicit rather than assuming algebraicity. -/
structure RationalCycleSpanLaws (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  coeffZeroAdd : ∀ a : M.Coeff, M.add M.zero a = a
  coeffAddZero : ∀ a : M.Coeff, M.add a M.zero = a
  coeffAddAssoc : ∀ a b c : M.Coeff, M.add (M.add a b) c = M.add a (M.add b c)
  classZeroAdd : ∀ {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)),
    M.addClass M.zeroClass α = α
  classAddZero : ∀ {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)),
    M.addClass α M.zeroClass = α
  classAddAssoc : ∀ {X : G.Variety} {p : Nat}
    (α β γ : G.CohomologyQ X (2 * p)),
    M.addClass (M.addClass α β) γ = M.addClass α (M.addClass β γ)
  zeroSmul : ∀ {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)),
    M.smul M.zero α = M.zeroClass
  addSmul : ∀ {X : G.Variety} {p : Nat} (a b : M.Coeff)
    (α : G.CohomologyQ X (2 * p)),
    M.smul (M.add a b) α = M.addClass (M.smul a α) (M.smul b α)

/-- K21 does not assert that the abstract coefficient carrier is Q.  Instead it
    records an explicit representation interface, whose laws must be supplied
    by a concrete model in a later stage. -/
structure RationalCoefficientInterface (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  ofInt : Int → M.Coeff
  numerator : M.Coeff → Int
  denominator : M.Coeff → Nat
  denominator_ne_zero : ∀ a : M.Coeff, denominator a ≠ 0

/-- Complete specification bundle needed before the semantic span can safely be
    identified with finite rational cycle combinations.  This is data, not a
    proof that such a model exists for actual algebraic geometry. -/
structure ConcreteCycleSpanSpecification (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  rationalCoefficients : RationalCoefficientInterface G M
  algebraicLaws : RationalCycleSpanLaws G M
  semanticAdapter : CycleSpanAdapter G M

/-- Once the explicit K21 specification is supplied, the semantic and concrete
    span predicates are mechanically equivalent. -/
theorem k21_span_equivalence
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (S : ConcreteCycleSpanSpecification G M)
    {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)) :
    G.inCycleClassSpan p α ↔ InConcreteCycleSpan M α :=
  S.semanticAdapter.span_iff α

/-- The specification can feed the already-certified K20 boundary, but K21
    still requires the independent geometry interface and algebraicity payload. -/
def k21_boundary_of_spec
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (S : ConcreteCycleSpanSpecification G M)
    (geometry : CycleClassGeometryInterface G M) :
    HodgeCertificationBoundary G M :=
  ⟨S.semanticAdapter, geometry⟩

def k21_specification_status : SignatureStatus := .definitionInterface
def k21_span_reduction_status : SignatureStatus := .provedProperty
def k21_geometry_status : SignatureStatus := .openBridge
def k21_algebraicity_status : SignatureStatus := .openBridge
def k21_hodge_status : SignatureStatus := .openBridge

theorem k21_geometry_still_open : k21_geometry_status = .openBridge := rfl
theorem k21_algebraicity_still_open : k21_algebraicity_status = .openBridge := rfl
theorem k21_hodge_still_open : k21_hodge_status = .openBridge := rfl

#print axioms k21_span_equivalence
#print axioms k21_boundary_of_spec

end MCore
