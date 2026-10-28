import ATK.IMath.Core.Phi3

namespace IMath
namespace Phi3

universe u

/--
Explicit division policy for the three-state domain.

The finite/nonzero case delegates to the underlying division.
The finite zero-over-zero case yields the canonical indeterminate.
A nonzero finite value over zero reaches the infinity state.
Infinity over infinity is indeterminate and retains its expression.
-/
def idiv {α : Type u} [Zero α] [Div α] [DecidableEq α] :
    Phi3 α → Phi3 α → Phi3 α
  | .finite a, .finite b =>
      if b = 0 then
        if a = 0 then I
        else .infinity
      else
        .finite (a / b)
  | .finite _, .infinity => .finite 0
  | .infinity, .finite _ => .infinity
  | .infinity, .infinity =>
      .indeterminate (.div .infinity .infinity)
  | .indeterminate e, y =>
      .indeterminate (.div e (toExpr y))
  | x, .indeterminate e =>
      .indeterminate (.div (toExpr x) e)

@[simp] theorem zero_idiv_zero {α : Type u}
    [Zero α] [Div α] [DecidableEq α] :
    idiv (.finite 0 : Phi3 α) (.finite 0) = I := by
  simp [idiv]

@[simp] theorem finite_ne_zero_idiv_zero {α : Type u}
    [Zero α] [Div α] [DecidableEq α]
    {a : α} (ha : a ≠ 0) :
    idiv (.finite a : Phi3 α) (.finite 0) = .infinity := by
  simp [idiv, ha]

@[simp] theorem finite_idiv_finite_ne_zero {α : Type u}
    [Zero α] [Div α] [DecidableEq α]
    (a b : α) (hb : b ≠ 0) :
    idiv (.finite a : Phi3 α) (.finite b) = .finite (a / b) := by
  simp [idiv, hb]

@[simp] theorem infinity_idiv_infinity {α : Type u}
    [Zero α] [Div α] [DecidableEq α] :
    idiv (.infinity : Phi3 α) .infinity =
      .indeterminate (.div .infinity .infinity) := rfl

@[simp] theorem finite_idiv_infinity {α : Type u}
    [Zero α] [Div α] [DecidableEq α] (a : α) :
    idiv (.finite a : Phi3 α) .infinity = .finite 0 := rfl

@[simp] theorem infinity_idiv_finite {α : Type u}
    [Zero α] [Div α] [DecidableEq α] (a : α) :
    idiv (.infinity : Phi3 α) (.finite a) = .infinity := rfl

end Phi3
end IMath
