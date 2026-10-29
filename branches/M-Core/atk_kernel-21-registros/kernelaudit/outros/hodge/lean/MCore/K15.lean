import MCore.K14

namespace MCore

/-- Minimal algebraic mechanics for a cycle-class span.  This deliberately
    avoids importing external geometry: coefficients, finite support and the
    cycle-class map are explicit data. -/
structure CycleSpanMechanics (G : GradedRationalHodgeData) where
  Coeff : Type
  zero : Coeff
  add : Coeff → Coeff → Coeff
  smul : {X : G.Variety} → {p : Nat} → Coeff → G.CohomologyQ X (2 * p) → G.CohomologyQ X (2 * p)
  addClass : {X : G.Variety} → {p : Nat} → G.CohomologyQ X (2 * p) → G.CohomologyQ X (2 * p) → G.CohomologyQ X (2 * p)
  zeroClass : {X : G.Variety} → {p : Nat} → G.CohomologyQ X (2 * p)
  cycleClass : {X : G.Variety} → (p : Nat) → G.CycleQ X p → G.CohomologyQ X (2 * p)

/-- A finite formal linear combination of codimension-p cycles. -/
structure CycleCombination (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) (X : G.Variety) (p : Nat) where
  terms : List (M.Coeff × G.CycleQ X p)

/-- Mechanical evaluation of a finite cycle combination. -/
def CycleCombination.eval {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) {X : G.Variety} {p : Nat}
    (c : CycleCombination G M X p) : G.CohomologyQ X (2 * p) :=
  c.terms.foldr (fun t acc => M.addClass (M.smul t.1 (M.cycleClass p t.2)) acc) M.zeroClass

/-- Concrete witness-based membership in the generated finite span. -/
def InConcreteCycleSpan {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) {X : G.Variety} {p : Nat}
    (α : G.CohomologyQ X (2 * p)) : Prop :=
  ∃ c : CycleCombination G M X p, c.eval M = α

/-- Adapter requirement saying the semantic span predicate used by K13/K14 is
    exactly the concrete finite-combination predicate.  This is an interface,
    not an asserted theorem. -/
structure CycleSpanAdapter (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  span_iff : ∀ {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)),
    G.inCycleClassSpan p α ↔ InConcreteCycleSpan M α

theorem adapter_transports_span
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M) {X : G.Variety} {p : Nat}
    (α : G.CohomologyQ X (2 * p)) :
    G.inCycleClassSpan p α ↔ InConcreteCycleSpan M α :=
  A.span_iff α

def k15_mechanics_status : SignatureStatus := .definitionInterface

def k15_span_adapter_status : SignatureStatus := .openBridge

def k15_algebraicity_status : SignatureStatus := .openBridge

theorem k15_span_adapter_still_open : k15_span_adapter_status = .openBridge := rfl

theorem k15_algebraicity_still_open : k15_algebraicity_status = .openBridge := rfl

#print axioms CycleCombination.eval
#print axioms adapter_transports_span

end MCore
