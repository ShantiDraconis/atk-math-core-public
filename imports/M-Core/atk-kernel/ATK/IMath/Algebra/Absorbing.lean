import ATK.IMath.Core.Phi3

namespace IMath
namespace Phi3

universe u

/--
An explicitly named experimental addition in which indeterminacy is absorbing.
It is deliberately not installed as the global Add operation on Phi3.
-/
def absorbingAdd {α : Type u} [Zero α] [Add α] :
    Phi3 α → Phi3 α → Phi3 α
  | .indeterminate _, _ => I
  | _, .indeterminate _ => I
  | .finite a, .finite b => .finite (a + b)
  | .infinity, _ => .infinity
  | _, .infinity => .infinity

@[simp] theorem absorbingAdd_I_left {α : Type u}
    [Zero α] [Add α] (x : Phi3 α) :
    absorbingAdd I x = I := by
  simp [absorbingAdd, I]

@[simp] theorem absorbingAdd_I_right {α : Type u}
    [Zero α] [Add α] (x : Phi3 α) :
    absorbingAdd x I = I := by
  cases x <;> rfl

/--
Any two distinct finite inputs collide after adding the canonical indeterminate
on the right. This gives a direct counterexample to right cancellation whenever
the base carrier contains a chosen distinct pair.
-/
theorem absorbingAdd_not_right_cancellative_of_ne {α : Type u}
    [Zero α] [Add α] {a b : α} (hab : a ≠ b) :
    ∃ x y : Phi3 α,
      x ≠ y ∧ absorbingAdd x I = absorbingAdd y I := by
  refine ⟨.finite a, .finite b, ?_, ?_⟩
  · intro h
    exact hab (finite_injective h)
  · calc
      absorbingAdd (.finite a) I = I := absorbingAdd_I_right _
      _ = absorbingAdd (.finite b) I := (absorbingAdd_I_right _).symm

end Phi3
end IMath
