import MCore.Research.UserProgram.Operators

namespace MCore.Research.UserProgram

def Commute {α : Type} (f g : Operator α) : Prop :=
  Operator.comp f g = Operator.comp g f

def Idempotent {α : Type} (f : Operator α) : Prop :=
  Operator.comp f f = f

def Involution {α : Type} (f : Operator α) : Prop :=
  Operator.comp f f = Operator.id α

theorem commute_refl {α : Type} (f : Operator α) : Commute f f := by
  rfl

theorem commute_symm {α : Type} {f g : Operator α} :
    Commute f g → Commute g f := by
  intro h
  exact h.symm

theorem involution_idempotent_iff_id {α : Type} (f : Operator α)
    (hi : Involution f) (hd : Idempotent f) :
    f = Operator.id α := by
  rw [← hd, hi]

end MCore.Research.UserProgram
