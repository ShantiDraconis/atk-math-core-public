import ATK.IMath.Core.Phi3

namespace IMath

universe u

/-- An n-dimensional point whose coordinates live in the three-state domain. -/
abbrev IPoint (α : Type u) (n : ℕ) :=
  Fin n → Phi3 α

/-- Canonical embedding of an ordinary n-dimensional point. -/
def determinedPoint {α : Type u} {n : ℕ} (x : Fin n → α) : IPoint α n :=
  fun i => .finite (x i)

theorem determinedPoint_injective {α : Type u} {n : ℕ} :
    Function.Injective (@determinedPoint α n) := by
  intro x y h
  funext i
  have hi := congrFun h i
  exact Phi3.finite_injective hi

end IMath
