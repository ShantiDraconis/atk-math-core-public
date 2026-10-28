import Mathlib

namespace MCore.Research.UserProgram

structure Operator (α : Type) where
  run : α → α

def Operator.comp {α : Type} (f g : Operator α) : Operator α :=
  ⟨f.run ∘ g.run⟩

def Operator.id (α : Type) : Operator α := ⟨id⟩

theorem Operator.comp_assoc {α : Type} (f g h : Operator α) :
    Operator.comp (Operator.comp f g) h =
      Operator.comp f (Operator.comp g h) := by
  cases f; cases g; cases h
  rfl

theorem Operator.id_comp {α : Type} (f : Operator α) :
    Operator.comp (Operator.id α) f = f := by
  cases f
  rfl

theorem Operator.comp_id {α : Type} (f : Operator α) :
    Operator.comp f (Operator.id α) = f := by
  cases f
  rfl

structure OperatorFamily (α : Type) where
  T : Operator α
  S : Operator α
  E : Operator α
  Q : Operator α
  Delta : Operator α
  Gamma : Operator α
  C : Operator α

end MCore.Research.UserProgram
