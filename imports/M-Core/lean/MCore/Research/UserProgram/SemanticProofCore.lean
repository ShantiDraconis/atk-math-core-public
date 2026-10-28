import Mathlib
import MCore.Research.UserProgram.C3LinearSectors

namespace MCore.Research.UserProgram

/-! Typed semantic/proof layer for the user research program.
    An inhabitant carries an actual proof of its proposition; no assumed bridge is created here. -/

inductive NumericClass
  | natural | integer | rational | real | complex | cyclic3
  deriving DecidableEq, Repr

structure SemanticCarrier where
  Carrier : Type
  numericClass : NumericClass

def ComplexCarrier : SemanticCarrier :=
  ⟨ℂ, .complex⟩

def I3Carrier : SemanticCarrier :=
  ⟨I3State, .cyclic3⟩

structure SemanticMap (A B : SemanticCarrier) where
  run : A.Carrier → B.Carrier

def SemanticMap.id (A : SemanticCarrier) : SemanticMap A A :=
  ⟨id⟩

def SemanticMap.comp {A B C : SemanticCarrier}
    (g : SemanticMap B C) (f : SemanticMap A B) : SemanticMap A C :=
  ⟨g.run ∘ f.run⟩

theorem SemanticMap.comp_apply {A B C : SemanticCarrier}
    (g : SemanticMap B C) (f : SemanticMap A B) (x : A.Carrier) :
    (g.comp f).run x = g.run (f.run x) := rfl

structure Law (α : Type) where
  statement : α → Prop

structure Habitant {α : Type} (L : Law α) where
  witness : α
  proof : L.statement witness

structure Inhabitant (P : Prop) where
  proof : P

def Inhabitant.ofProof {P : Prop} (h : P) : Inhabitant P :=
  ⟨h⟩

theorem Inhabitant.sound {P : Prop} (h : Inhabitant P) : P :=
  h.proof

theorem Inhabitant.nonempty_iff (P : Prop) :
    Nonempty (Inhabitant P) ↔ P := by
  constructor
  · rintro ⟨h⟩
    exact h.proof
  · intro h
    exact ⟨⟨h⟩⟩

structure ProvenLaw (α : Type) where
  law : Law α
  inhabitant : Habitant law

def RotationLaw : Law I3State where
  statement s := s.next.next.next = s

def rotationHabitant : Habitant RotationLaw where
  witness := .manifesto
  proof := by decide

def RotationGlobalLaw : Prop :=
  ∀ s : I3State, s.next.next.next = s

def rotationGlobalInhabitant : Inhabitant RotationGlobalLaw :=
  ⟨I3State.next_three⟩

theorem rotationGlobalInhabitant_sound :
    RotationGlobalLaw :=
  rotationGlobalInhabitant.sound

structure SemanticFlow (A : SemanticCarrier) where
  step : SemanticMap A A

def SemanticFlow.iterate {A : SemanticCarrier}
    (F : SemanticFlow A) : ℕ → A.Carrier → A.Carrier
  | 0 => id
  | n + 1 => F.step.run ∘ F.iterate n

def I3Flow : SemanticFlow I3Carrier :=
  ⟨⟨I3State.next⟩⟩

theorem I3Flow_three (s : I3State) :
    I3Flow.iterate 3 s = s := by
  cases s <;> rfl

def I3FlowThreeInhabitant :
    Inhabitant (∀ s : I3State, I3Flow.iterate 3 s = s) :=
  ⟨I3Flow_three⟩

end MCore.Research.UserProgram
