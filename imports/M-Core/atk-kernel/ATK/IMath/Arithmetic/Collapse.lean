import ATK.IMath.Core.Phi3

namespace IMath
namespace Phi3

universe u

/--
Forget detailed provenance of an indeterminate while preserving finite
values and the distinguished infinity state.
-/
def collapse {α : Type u} [Zero α] : Phi3 α → Phi3 α
  | .finite a => .finite a
  | .infinity => .infinity
  | .indeterminate _ => I

@[simp] theorem collapse_finite {α : Type u} [Zero α] (a : α) :
    collapse (.finite a : Phi3 α) = .finite a := rfl

@[simp] theorem collapse_infinity {α : Type u} [Zero α] :
    collapse (.infinity : Phi3 α) = .infinity := rfl

@[simp] theorem collapse_indeterminate {α : Type u} [Zero α] (e : Expr α) :
    collapse (.indeterminate e : Phi3 α) = I := rfl

@[simp] theorem collapse_I {α : Type u} [Zero α] :
    collapse (I (α := α)) = I := rfl

theorem collapse_idempotent {α : Type u} [Zero α] (x : Phi3 α) :
    collapse (collapse x) = collapse x := by
  cases x <;> rfl

end Phi3
end IMath
