import MCore.FinalFail.TriadicObstructionCalculus
import MCore.FinalFail.MinimalOpenBridge

namespace MCore.FinalFail

/-- Two oriented forces on the closed triad.
advance moves start -> middle -> finish.
return moves finish -> middle -> start.
At the outer sites each force is absorbing rather than inventing a fourth site. -/
inductive ClosedForce where
  | advance
  | return
  deriving DecidableEq, Repr

def closedForceStep : ClosedForce → Fin3 → Fin3
  | .advance, .start => .middle
  | .advance, .middle => .finish
  | .advance, .finish => .finish
  | .return, .finish => .middle
  | .return, .middle => .start
  | .return, .start => .start

theorem advance_start_middle :
    closedForceStep .advance .start = .middle := rfl

theorem advance_middle_finish :
    closedForceStep .advance .middle = .finish := rfl

theorem return_finish_middle :
    closedForceStep .return .finish = .middle := rfl

theorem return_middle_start :
    closedForceStep .return .middle = .start := rfl

/-- The unlabeled transition relation forgets which force was selected.
This is where the middle genuinely has two admissible continuations. -/
inductive ClosedTransition : Fin3 → Fin3 → Prop
  | start_middle : ClosedTransition .start .middle
  | middle_finish : ClosedTransition .middle .finish
  | finish_middle : ClosedTransition .finish .middle
  | middle_start : ClosedTransition .middle .start

theorem middle_has_two_admissible_branches :
    ClosedTransition .middle .start ∧
    ClosedTransition .middle .finish := by
  exact ⟨ClosedTransition.middle_start, ClosedTransition.middle_finish⟩

theorem start_and_finish_meet_at_middle :
    ClosedTransition .start .middle ∧
    ClosedTransition .finish .middle := by
  exact ⟨ClosedTransition.start_middle, ClosedTransition.finish_middle⟩

/-- Closure predicate attached to the three sites already present in ClosedTriad. -/
def ClosedAt (T : ClosedTriad) : Fin3 → Prop
  | .start => T.startClosed
  | .middle => T.middleClosed
  | .finish => T.finishClosed

def AllSitesClosed (T : ClosedTriad) : Prop :=
  T.startClosed ∧ T.middleClosed ∧ T.finishClosed

theorem closed_transition_preserves_closed
    (T : ClosedTriad)
    (hAll : AllSitesClosed T)
    {a b : Fin3}
    (_ha : ClosedAt T a)
    (h : ClosedTransition a b) :
    ClosedAt T b := by
  rcases hAll with ⟨hs, hm, hf⟩
  cases h with
  | start_middle => exact hm
  | middle_finish => exact hf
  | finish_middle => exact hm
  | middle_start => exact hs

/-- Semantic HARD layer.
The four arrows are not definitions of a famous theorem: they are the exact
maps that an application must actually prove. Once supplied, start, center
and finish are equivalent within that application. -/
structure ClosedCenterHard (Start Center Finish : Prop) where
  start_to_center : Start → Center
  center_to_start : Center → Start
  center_to_finish : Center → Finish
  finish_to_center : Finish → Center

namespace ClosedCenterHard

variable {Start Center Finish : Prop}

theorem start_iff_center (H : ClosedCenterHard Start Center Finish) :
    Start ↔ Center :=
  ⟨H.start_to_center, H.center_to_start⟩

theorem center_iff_finish (H : ClosedCenterHard Start Center Finish) :
    Center ↔ Finish :=
  ⟨H.center_to_finish, H.finish_to_center⟩

theorem start_iff_finish (H : ClosedCenterHard Start Center Finish) :
    Start ↔ Finish := by
  constructor
  · intro hS
    exact H.center_to_finish (H.start_to_center hS)
  · intro hF
    exact H.center_to_start (H.finish_to_center hF)

theorem finish_of_start
    (H : ClosedCenterHard Start Center Finish)
    (hS : Start) : Finish :=
  H.center_to_finish (H.start_to_center hS)

theorem start_of_finish
    (H : ClosedCenterHard Start Center Finish)
    (hF : Finish) : Start :=
  H.center_to_start (H.finish_to_center hF)

/-- The center exposes both semantic continuations simultaneously.
Choosing a transition is not the same thing as asserting an exclusive outcome. -/
theorem center_exposes_both
    (H : ClosedCenterHard Start Center Finish)
    (hC : Center) :
    Start ∧ Finish :=
  ⟨H.center_to_start hC, H.center_to_finish hC⟩

end ClosedCenterHard

/-- FINAL_FAIL/HARD adapter: a certified start and a real four-arrow semantic
cycle are sufficient to close the finish proposition. The theorem does not
manufacture any of the four arrows. -/
structure ClosedCenterTerminalChain (Start Center Finish : Prop) where
  startClosed : Start
  hard : ClosedCenterHard Start Center Finish
  firewall : Firewall
  firewallClosed : FirewallClosed firewall

theorem closed_center_terminal_chain_closure
    {Start Center Finish : Prop}
    (H : ClosedCenterTerminalChain Start Center Finish) :
    Finish :=
  H.hard.finish_of_start H.startClosed

#print axioms MCore.FinalFail.middle_has_two_admissible_branches
#print axioms MCore.FinalFail.closed_transition_preserves_closed
#print axioms MCore.FinalFail.ClosedCenterHard.start_iff_finish
#print axioms MCore.FinalFail.closed_center_terminal_chain_closure

end MCore.FinalFail
