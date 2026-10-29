import MCore.K15

namespace MCore

/-- Soundness of the cycle-class map: genuine codimension-p cycle classes land
    in Hodge type (p,p).  This is separated from the open surjectivity claim. -/
def CycleClassSoundness {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (z : G.CycleQ X p),
    G.isTypePP p (M.cycleClass p z)

/-- The actual remaining endpoint: every rational Hodge class has a concrete
    finite cycle-combination witness. -/
def ConcreteHodgeSurjectivity {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety), G.isSmoothProjective X →
    ∀ (p : Nat) (α : G.CohomologyQ X (2 * p)),
      G.isTypePP p α → InConcreteCycleSpan M α

/-- With a span adapter, concrete surjectivity implies the graded Hodge
    conjecture.  This theorem only transports an explicitly supplied witness. -/
theorem concreteSurjectivity_implies_hodge
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (h : ConcreteHodgeSurjectivity M) :
    GradedRationalHodgeConjecture G := by
  intro X hsp p α hpp
  exact (A.span_iff α).2 (h X hsp p α hpp)

/-- Converse reduction: a graded Hodge proof plus the adapter yields concrete
    finite-cycle witnesses. -/
theorem hodge_implies_concreteSurjectivity
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (h : GradedRationalHodgeConjecture G) :
    ConcreteHodgeSurjectivity M := by
  intro X hsp p α hpp
  exact (A.span_iff α).1 (h X hsp p α hpp)

/-- Exact logical boundary after K16. -/
theorem hodge_iff_concreteSurjectivity
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M) :
    GradedRationalHodgeConjecture G ↔ ConcreteHodgeSurjectivity M := by
  exact ⟨hodge_implies_concreteSurjectivity A,
    concreteSurjectivity_implies_hodge A⟩

def k16_cycle_class_soundness_status : SignatureStatus := .openBridge

def k16_concrete_surjectivity_status : SignatureStatus := .openBridge

def k16_reduction_status : SignatureStatus := .provedProperty

theorem k16_soundness_still_open :
    k16_cycle_class_soundness_status = .openBridge := rfl

theorem k16_surjectivity_still_open :
    k16_concrete_surjectivity_status = .openBridge := rfl

#print axioms concreteSurjectivity_implies_hodge
#print axioms hodge_implies_concreteSurjectivity
#print axioms hodge_iff_concreteSurjectivity

end MCore
