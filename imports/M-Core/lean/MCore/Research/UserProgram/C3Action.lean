import Mathlib
import MCore.Research.UserProgram.IRegime

namespace MCore.Research.UserProgram

def I3State.index : I3State → ZMod 3
  | .manifesto => 0
  | .travessia => 1
  | .semente => 2

theorem I3State.index_injective : Function.Injective I3State.index := by
  intro a b h
  cases a <;> cases b <;> simp_all [I3State.index]

theorem I3State.index_next (s : I3State) :
    s.next.index = s.index + 1 := by
  cases s <;> native_decide

def rotate3 (k : ZMod 3) (s : I3State) : I3State :=
  match k.val with
  | 0 => s
  | 1 => s.next
  | _ => s.next.next

theorem rotate3_zero (s : I3State) : rotate3 0 s = s := by
  rfl

theorem rotate3_one (s : I3State) : rotate3 1 s = s.next := by
  rfl

end MCore.Research.UserProgram
