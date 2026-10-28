import Mathlib

namespace MCore.Research.UserProgram

inductive IRegime where
  | finite (n : ℕ)
  | infinite
  | indeterminate
deriving DecidableEq, Repr

def I3 : IRegime := .finite 3

theorem I3_ne_infinite : I3 ≠ .infinite := by decide
theorem I3_ne_indeterminate : I3 ≠ .indeterminate := by decide

inductive I3State where
  | manifesto
  | travessia
  | semente
deriving DecidableEq, Repr, Fintype

def I3State.next : I3State → I3State
  | .manifesto => .travessia
  | .travessia => .semente
  | .semente => .manifesto

theorem I3State.next_three (s : I3State) :
    s.next.next.next = s := by
  cases s <;> rfl

theorem I3State.next_ne_self (s : I3State) :
    s.next ≠ s := by
  cases s <;> decide

end MCore.Research.UserProgram
