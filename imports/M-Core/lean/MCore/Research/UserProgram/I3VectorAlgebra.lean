import Mathlib
import MCore.Research.UserProgram.SemanticProofCore

namespace MCore.Research.UserProgram

structure I3Vector where
  manifesto : ℂ
  travessia : ℂ
  semente : ℂ

instance : Zero I3Vector := ⟨⟨0, 0, 0⟩⟩
instance : Add I3Vector :=
  ⟨fun x y => ⟨x.manifesto + y.manifesto,
    x.travessia + y.travessia, x.semente + y.semente⟩⟩
instance : Neg I3Vector :=
  ⟨fun x => ⟨-x.manifesto, -x.travessia, -x.semente⟩⟩
instance : SMul ℂ I3Vector :=
  ⟨fun z x => ⟨z * x.manifesto, z * x.travessia, z * x.semente⟩⟩

@[ext] theorem I3Vector.ext {x y : I3Vector}
    (hM : x.manifesto = y.manifesto)
    (hT : x.travessia = y.travessia)
    (hS : x.semente = y.semente) : x = y := by
  cases x
  cases y
  simp_all

theorem I3Vector.add_assoc (x y z : I3Vector) :
    (x + y) + z = x + (y + z) := by
  ext <;> simp [add_assoc]

theorem I3Vector.add_zero (x : I3Vector) : x + 0 = x := by
  ext <;> simp

theorem I3Vector.add_neg (x : I3Vector) : x + (-x) = 0 := by
  ext <;> simp

theorem I3Vector.smul_add (a : ℂ) (x y : I3Vector) :
    a • (x + y) = a • x + a • y := by
  ext <;> simp [mul_add]

theorem I3Vector.add_smul (a b : ℂ) (x : I3Vector) :
    (a + b) • x = a • x + b • x := by
  ext <;> simp [add_mul]

theorem I3Vector.mul_smul (a b : ℂ) (x : I3Vector) :
    (a * b) • x = a • (b • x) := by
  ext <;> simp [mul_assoc]

def I3Vector.rotate (x : I3Vector) : I3Vector :=
  ⟨x.travessia, x.semente, x.manifesto⟩

theorem I3Vector.rotate_three (x : I3Vector) :
    x.rotate.rotate.rotate = x := by
  rfl

def I3Vector.sum (x : I3Vector) : ℂ :=
  x.manifesto + x.travessia + x.semente

theorem I3Vector.sum_rotate (x : I3Vector) :
    x.rotate.sum = x.sum := by
  simp [I3Vector.rotate, I3Vector.sum]
  ring

def I3Vector.zeroSum (x : I3Vector) : Prop := x.sum = 0

theorem I3Vector.zeroSum_rotate {x : I3Vector} (hx : x.zeroSum) :
    x.rotate.zeroSum := by
  unfold I3Vector.zeroSum
  rw [I3Vector.sum_rotate, hx]

def I3VectorRotationInhabitant :
    Inhabitant (∀ x : I3Vector, x.rotate.rotate.rotate = x) :=
  ⟨I3Vector.rotate_three⟩

def I3VectorSumInvariantInhabitant :
    Inhabitant (∀ x : I3Vector, x.rotate.sum = x.sum) :=
  ⟨I3Vector.sum_rotate⟩

end MCore.Research.UserProgram
