import Mathlib

namespace ATK.ConcreteSemantics

inductive BoolExpr where
  | atom : Nat → BoolExpr
  | neg : BoolExpr → BoolExpr
  | conj : BoolExpr → BoolExpr → BoolExpr
  | disj : BoolExpr → BoolExpr → BoolExpr
  deriving Repr

def eval (assignment : Nat → Bool) : BoolExpr → Bool
  | .atom n => assignment n
  | .neg e => !(eval assignment e)
  | .conj p q => eval assignment p && eval assignment q
  | .disj p q => eval assignment p || eval assignment q

/-- Concrete semantics of conjunction; no arbitrary `Prop` fields. -/
theorem eval_conj (a : Nat → Bool) (p q : BoolExpr) :
    eval a (.conj p q) = (eval a p && eval a q) := rfl

theorem eval_double_neg (a : Nat → Bool) (p : BoolExpr) :
    eval a (.neg (.neg p)) = eval a p := by
  simp [eval]

/-- This defines a verifier, not a lower bound against all SAT algorithms. -/
def verifies (a : Nat → Bool) (p : BoolExpr) : Prop := eval a p = true

theorem verifies_conj (a : Nat → Bool) (p q : BoolExpr) :
    verifies a (.conj p q) ↔ verifies a p ∧ verifies a q := by
  simp [verifies, eval, Bool.and_eq_true]

end ATK.ConcreteSemantics
