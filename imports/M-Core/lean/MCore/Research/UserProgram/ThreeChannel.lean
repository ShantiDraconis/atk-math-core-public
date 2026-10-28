import Mathlib
import MCore.Research.UserProgram.CyclicInvariant

namespace MCore.Research.UserProgram

structure ThreeChannel (R : Type) [AddCommMonoid R] where
  manifesto : R
  travessia : R
  semente : R

def ThreeChannel.total {R : Type} [AddCommMonoid R] (x : ThreeChannel R) : R :=
  x.manifesto + x.travessia + x.semente

def ThreeChannel.rotate {R : Type} [AddCommMonoid R] (x : ThreeChannel R) : ThreeChannel R where
  manifesto := x.travessia
  travessia := x.semente
  semente := x.manifesto

theorem ThreeChannel.rotate_three {R : Type} [AddCommMonoid R] (x : ThreeChannel R) :
    x.rotate.rotate.rotate = x := by
  cases x
  rfl

theorem ThreeChannel.total_rotate {R : Type} [AddCommMonoid R] (x : ThreeChannel R) :
    x.rotate.total = x.total := by
  simp [ThreeChannel.rotate, ThreeChannel.total, add_assoc, add_comm, add_left_comm]

end MCore.Research.UserProgram
