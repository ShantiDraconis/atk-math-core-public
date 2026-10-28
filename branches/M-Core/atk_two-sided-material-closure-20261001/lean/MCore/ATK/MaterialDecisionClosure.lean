import Mathlib

namespace MCore.ATK.MaterialDecision

/--
Material decision state.  No conjecture is used as an input hypothesis:
the state itself carries the produced evidence.
-/
inductive DecisionEvidence (P : Prop) where
  | unresolved
  | proved (hp : P)
  | refuted (hn : ¬ P)
  | inconsistent (hp : P) (hn : ¬ P)

/-- A problem is materially decided when an actual proof or refutation has
been produced.  This is intentionally stronger than merely invoking excluded
middle as a proposition. -/
inductive Decided (P : Prop) : Type where
  | proved (hp : P)
  | refuted (hn : ¬ P)

/-- Concrete trichotomy visible to the global system. -/
inductive DecisionTag where
  | open
  | trueClosed
  | falseClosed
  | inconsistentClosed
  deriving DecidableEq, Repr

def DecisionEvidence.tag {P : Prop} : DecisionEvidence P → DecisionTag
  | .unresolved => .open
  | .proved _ => .trueClosed
  | .refuted _ => .falseClosed
  | .inconsistent _ _ => .inconsistentClosed

def DecisionEvidence.toDecided?
    {P : Prop} :
    DecisionEvidence P → Option (Decided P)
  | .unresolved => none
  | .proved hp => some (.proved hp)
  | .refuted hn => some (.refuted hn)
  | .inconsistent hp _ => some (.proved hp)

theorem inconsistent_gives_false
    {P : Prop}
    (hp : P)
    (hn : ¬ P) :
    False :=
  hn hp

/--
Generic material alternatives independent of the conjecture proposition.

A is a positive-side concrete object.
B is a negative-side concrete object.
No P or not-P appears in the input type.
-/
inductive MaterialAlternative (A B : Type) where
  | open
  | positive (a : A)
  | negative (b : B)
  | both (a : A) (b : B)

/--
A common mathematical result Q can be closed if either concrete branch object
maps to Q.  No conjecture is passed as an assumption.
-/
structure AlternativeClosure (A B : Type) (Q : Prop) where
  fromPositive : A → Q
  fromNegative : B → Q

def closeAlternative
    {A B : Type}
    {Q : Prop}
    (C : AlternativeClosure A B Q) :
    MaterialAlternative A B → Option Q
  | .open => none
  | .positive a => some (C.fromPositive a)
  | .negative b => some (C.fromNegative b)
  | .both a _ => some (C.fromPositive a)

/--
Decision closure for the original proposition P.

The positive object must construct an actual proof of P.
The negative object must construct an actual proof of not-P.
Thus both branches are concrete evidence producers, not endpoint assumptions.
-/
structure MaterialDecisionSystem
    (P : Prop)
    (PositiveObject NegativeObject : Type) where
  prove : PositiveObject → P
  refute : NegativeObject → ¬ P

def decideFromAlternative
    {P : Prop}
    {A B : Type}
    (S : MaterialDecisionSystem P A B) :
    MaterialAlternative A B → DecisionEvidence P
  | .open => .unresolved
  | .positive a => .proved (S.prove a)
  | .negative b => .refuted (S.refute b)
  | .both a b => .inconsistent (S.prove a) (S.refute b)

/--
If both concrete branch objects are produced, the system detects an explicit
contradiction rather than silently promoting the positive side.
-/
theorem both_objects_detect_inconsistency
    {P : Prop}
    {A B : Type}
    (S : MaterialDecisionSystem P A B)
    (a : A)
    (b : B) :
    False :=
  (S.refute b) (S.prove a)

/--
A terminal question may be closed as a decision without fixing its truth value
in advance.  The output remembers which side was actually constructed.
-/
def materialDecision
    {P : Prop}
    {A B : Type}
    (S : MaterialDecisionSystem P A B) :
    MaterialAlternative A B → Option (Decided P)
  | .open => none
  | .positive a => some (.proved (S.prove a))
  | .negative b => some (.refuted (S.refute b))
  | .both a b =>
      False.elim ((S.refute b) (S.prove a))

/--
Observable-level decision architecture.

Both branches must report into one shared observable carrier O.  This closes
all representation bridges before the final proposition is inspected.
-/
structure ObservableDecisionSystem
    (P : Prop)
    (PositiveObject NegativeObject Observable : Type) where
  observePositive : PositiveObject → Observable
  observeNegative : NegativeObject → Observable

  PositiveLaw : Observable → Prop
  NegativeLaw : Observable → Prop

  positiveLaw :
    ∀ a, PositiveLaw (observePositive a)
  negativeLaw :
    ∀ b, NegativeLaw (observeNegative b)

  proveFromLaw :
    ∀ o, PositiveLaw o → P
  refuteFromLaw :
    ∀ o, NegativeLaw o → ¬ P

def ObservableDecisionSystem.toMaterialDecisionSystem
    {P : Prop}
    {A B O : Type}
    (S : ObservableDecisionSystem P A B O) :
    MaterialDecisionSystem P A B where
  prove := fun a =>
    S.proveFromLaw (S.observePositive a) (S.positiveLaw a)
  refute := fun b =>
    S.refuteFromLaw (S.observeNegative b) (S.negativeLaw b)

/--
Defect dynamics independent of truth-value assumptions.
-/
structure MaterialDynamics (S : Type) where
  defect : S → Nat
  contraction : S → S
  repression : S → S
  torsion : S → S
  excitation : S → S

  contraction_decreases :
    ∀ s, 0 < defect s → defect (contraction s) < defect s

  repression_nonincrease :
    ∀ s, defect (repression s) ≤ defect s

  torsion_preserves :
    ∀ s, defect (torsion s) = defect s

  ExcitationValid : S → Prop
  excitation_decreases :
    ∀ s, ExcitationValid s → 0 < defect s →
      defect (excitation s) < defect s

theorem torsion_preserves_open_defect
    {S : Type}
    (D : MaterialDynamics S)
    (s : S)
    (hpos : 0 < D.defect s) :
    0 < D.defect (D.torsion s) := by
  rw [D.torsion_preserves s]
  exact hpos

/--
Parallel composition of materially decided questions.
-/
structure DecisionBundle (P Q : Prop) where
  left : Decided P
  right : Decided Q

theorem decisionBundle_has_both_decisions
    {P Q : Prop}
    (B : DecisionBundle P Q) :
    Nonempty (Decided P) ∧ Nonempty (Decided Q) :=
  ⟨⟨B.left⟩, ⟨B.right⟩⟩

#print axioms MCore.ATK.MaterialDecision.inconsistent_gives_false
#print axioms MCore.ATK.MaterialDecision.both_objects_detect_inconsistency
#print axioms MCore.ATK.MaterialDecision.materialDecision
#print axioms MCore.ATK.MaterialDecision.ObservableDecisionSystem.toMaterialDecisionSystem
#print axioms MCore.ATK.MaterialDecision.torsion_preserves_open_defect
#print axioms MCore.ATK.MaterialDecision.decisionBundle_has_both_decisions

end MCore.ATK.MaterialDecision
