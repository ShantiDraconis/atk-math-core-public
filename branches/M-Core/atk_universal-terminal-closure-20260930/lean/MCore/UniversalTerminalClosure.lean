import MCore.FinalProofFirewall

namespace MCore.FinalProof

universe u

/--
A terminal lane separates the proposition that must ultimately be established
from the concrete type of objects that are allowed to establish it.

The only mathematical content of a lane is the projection closes.
Infrastructure, names, manifests, and equivalent hypotheses do not inhabit
Producer by themselves.
-/
structure TerminalLane where
  Target : Prop
  Producer : Type u
  closes : Producer → Target

/-- A lane is materially closed only by an actual inhabitant of its producer type. -/
def TerminalLane.Closed (L : TerminalLane) : Prop :=
  Nonempty L.Producer

/-- Material closure of one lane yields its target proposition. -/
theorem TerminalLane.target_of_closed
    (L : TerminalLane)
    (h : L.Closed) :
    L.Target := by
  rcases h with ⟨p⟩
  exact L.closes p

/--
A seven-lane terminal system. Fin 7 is used only as the finite index set;
no mathematical target is hidden in the indexing layer.
-/
structure SevenLaneSystem where
  lane : Fin 7 → TerminalLane

/-- All seven target propositions, with no ranking and no shortcut. -/
def SevenLaneSystem.FinalRoot (S : SevenLaneSystem) : Prop :=
  ∀ i : Fin 7, (S.lane i).Target

/-- Every terminal producer is inhabited. -/
def SevenLaneSystem.AllClosed (S : SevenLaneSystem) : Prop :=
  ∀ i : Fin 7, (S.lane i).Closed

/--
Universal terminal-closure theorem.

This theorem is intentionally only a composition theorem: it says that seven
material producer inhabitants imply the seven target propositions. It does
not manufacture any producer inhabitant.
-/
theorem universal_terminal_closure
    (S : SevenLaneSystem)
    (h : S.AllClosed) :
    S.FinalRoot := by
  intro i
  exact (S.lane i).target_of_closed (h i)

/--
A wrapper that merely stores a proposition is inhabitance-equivalent to the
proposition itself. Consequently such a wrapper cannot count as an
independent producer.
-/
structure EquivalentWrapper (P : Prop) where
  payload : P

theorem equivalentWrapper_nonempty_iff
    (P : Prop) :
    Nonempty (EquivalentWrapper P) ↔ P := by
  constructor
  · rintro ⟨w⟩
    exact w.payload
  · intro h
    exact ⟨⟨h⟩⟩

/--
The same conservation-of-difficulty fact for a wrapper carrying an exactly
equivalent hypothesis rather than the target syntactically.
-/
structure HypothesisWrapper (P Q : Prop) where
  hypothesis : Q
  forward : Q → P
  backward : P → Q

theorem hypothesisWrapper_nonempty_implies_target
    (P Q : Prop)
    (h : Nonempty (HypothesisWrapper P Q)) :
    P := by
  rcases h with ⟨w⟩
  exact w.forward w.hypothesis

/--
A producer is strictly useful at the terminal boundary when it comes from a
separate witness type and has a projection into the target.
-/
structure ProducerMap (P : Prop) where
  Witness : Type u
  project : Witness → P

def ProducerMap.Inhabited
    {P : Prop}
    (M : ProducerMap P) : Prop :=
  Nonempty M.Witness

theorem ProducerMap.target_of_inhabited
    {P : Prop}
    (M : ProducerMap P)
    (h : M.Inhabited) :
    P := by
  rcases h with ⟨w⟩
  exact M.project w

/--
Producer-first composition over all seven lanes. This is the exact reusable
form required by the master manifest: each lane must provide a witness type,
an inhabitant of that type, and a kernel-checked projection to its target.
-/
structure SevenProducerMaps where
  Target : Fin 7 → Prop
  producer : ∀ i : Fin 7, ProducerMap (Target i)

def SevenProducerMaps.AllInhabited
    (S : SevenProducerMaps) : Prop :=
  ∀ i : Fin 7, (S.producer i).Inhabited

def SevenProducerMaps.FinalRoot
    (S : SevenProducerMaps) : Prop :=
  ∀ i : Fin 7, S.Target i

theorem universal_producer_first_closure
    (S : SevenProducerMaps)
    (h : S.AllInhabited) :
    S.FinalRoot := by
  intro i
  exact (S.producer i).target_of_inhabited (h i)

/--
No-wrapper corollary: replacing a terminal target by EquivalentWrapper
does not lower its inhabitance requirement.
-/
theorem wrapper_conserves_terminal_difficulty
    (P : Prop) :
    P ↔ Nonempty (EquivalentWrapper P) := by
  exact (equivalentWrapper_nonempty_iff P).symm

#print axioms MCore.FinalProof.TerminalLane.target_of_closed
#print axioms MCore.FinalProof.universal_terminal_closure
#print axioms MCore.FinalProof.equivalentWrapper_nonempty_iff
#print axioms MCore.FinalProof.hypothesisWrapper_nonempty_implies_target
#print axioms MCore.FinalProof.ProducerMap.target_of_inhabited
#print axioms MCore.FinalProof.universal_producer_first_closure
#print axioms MCore.FinalProof.wrapper_conserves_terminal_difficulty

end MCore.FinalProof
