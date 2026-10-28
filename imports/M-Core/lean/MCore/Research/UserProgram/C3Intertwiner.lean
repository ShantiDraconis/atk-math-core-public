import Mathlib
import MCore.Research.UserProgram.C3Fourier
import MCore.Research.UserProgram.Operators

namespace MCore.Research.UserProgram

def C3Operator := Operator ComplexThreeChannel

def rotationOperator : C3Operator :=
  ⟨ComplexThreeChannel.rotate⟩

def CommutesWithRotation (A : C3Operator) : Prop :=
  Operator.comp A rotationOperator = Operator.comp rotationOperator A

def commutatorDefect (A : C3Operator) (x : ComplexThreeChannel) : ComplexThreeChannel :=
  { manifesto := (A.run x.rotate).manifesto - (A.run x).rotate.manifesto
    travessia := (A.run x.rotate).travessia - (A.run x).rotate.travessia
    semente := (A.run x.rotate).semente - (A.run x).rotate.semente }

theorem commutes_iff_pointwise (A : C3Operator) :
    CommutesWithRotation A ↔ ∀ x, A.run x.rotate = (A.run x).rotate := by
  constructor
  · intro h x
    have := congrArg (fun op : C3Operator => op.run x) h
    simpa [CommutesWithRotation, Operator.comp, rotationOperator,
      Function.comp_apply] using this
  · intro h
    cases A with
    | mk run =>
      apply congrArg Operator.run |>.injective
      funext x
      simpa [Operator.comp, rotationOperator, Function.comp_apply] using h x

theorem commutatorDefect_zero_of_commutes
    (A : C3Operator) (hA : CommutesWithRotation A) (x : ComplexThreeChannel) :
    commutatorDefect A x =
      { manifesto := 0, travessia := 0, semente := 0 } := by
  rw [commutes_iff_pointwise] at hA
  have h := hA x
  simp [commutatorDefect, h]

def ConstantChannel (x : ComplexThreeChannel) : Prop :=
  x.manifesto = x.travessia ∧ x.travessia = x.semente

theorem meanPart_constant (x : ComplexThreeChannel) :
    ConstantChannel x.meanPart := by
  simp [ConstantChannel, ComplexThreeChannel.meanPart]

def PreservesConstantSector (A : C3Operator) : Prop :=
  ∀ x, ConstantChannel x → ConstantChannel (A.run x)

theorem commutes_preserves_rotation_fixed
    (A : C3Operator) (hA : CommutesWithRotation A)
    (x : ComplexThreeChannel) (hx : x.rotate = x) :
    (A.run x).rotate = A.run x := by
  rw [commutes_iff_pointwise] at hA
  simpa [hx] using (hA x).symm

theorem constant_iff_rotation_fixed (x : ComplexThreeChannel) :
    ConstantChannel x ↔ x.rotate = x := by
  constructor
  · rintro ⟨hMT, hTS⟩
    apply ComplexThreeChannel.ext <;>
      simp [ComplexThreeChannel.rotate, hMT, hTS]
  · intro h
    have hm := congrArg ComplexThreeChannel.manifesto h
    have ht := congrArg ComplexThreeChannel.travessia h
    constructor <;> simpa [ComplexThreeChannel.rotate] using ‹_›

theorem commutes_preserves_constant_sector
    (A : C3Operator) (hA : CommutesWithRotation A) :
    PreservesConstantSector A := by
  intro x hx
  rw [constant_iff_rotation_fixed] at hx ⊢
  exact commutes_preserves_rotation_fixed A hA x hx

end MCore.Research.UserProgram
