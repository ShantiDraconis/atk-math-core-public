namespace IMath

universe u v w

/-- Syntax tree retaining the provenance of an extended numerical expression. -/
inductive Expr (α : Type u) where
  | value : α → Expr α
  | infinity : Expr α
  | add : Expr α → Expr α → Expr α
  | sub : Expr α → Expr α → Expr α
  | mul : Expr α → Expr α → Expr α
  | div : Expr α → Expr α → Expr α
deriving Repr

namespace Expr

/-- Transport an expression along a map of its finite coefficients. -/
def map {α : Type u} {β : Type v} (f : α → β) : Expr α → Expr β
  | .value a => .value (f a)
  | .infinity => .infinity
  | .add x y => .add (map f x) (map f y)
  | .sub x y => .sub (map f x) (map f y)
  | .mul x y => .mul (map f x) (map f y)
  | .div x y => .div (map f x) (map f y)

@[simp] theorem map_value {α : Type u} {β : Type v}
    (f : α → β) (a : α) :
    map f (.value a) = .value (f a) := rfl

@[simp] theorem map_infinity {α : Type u} {β : Type v}
    (f : α → β) :
    map f (.infinity : Expr α) = .infinity := rfl

@[simp] theorem map_id {α : Type u} (e : Expr α) :
    map id e = e := by
  induction e <;> simp [map, *]

theorem map_comp {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (g : β → γ) (e : Expr α) :
    map g (map f e) = map (g ∘ f) e := by
  induction e <;> simp [map, Function.comp_def, *]

end Expr
end IMath
