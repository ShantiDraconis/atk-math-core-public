import Mathlib
import MCore.Research.UserProgram.C3Intertwiner

namespace MCore.Research.UserProgram

structure LinearC3Operator where
  run : ComplexThreeChannel →ₗ[ℂ] ComplexThreeChannel

def LinearC3Operator.commutesWithRotation (A : LinearC3Operator) : Prop :=
  ∀ x, A.run x.rotate = (A.run x).rotate

def RotationEigenvector (lam : ℂ) (x : ComplexThreeChannel) : Prop :=
  x.rotate =
    { manifesto := lam * x.manifesto
      travessia := lam * x.travessia
      semente := lam * x.semente }

def ComplexThreeChannel.smul (z : ℂ) (x : ComplexThreeChannel) : ComplexThreeChannel where
  manifesto := z * x.manifesto
  travessia := z * x.travessia
  semente := z * x.semente

theorem rotate_smul (z : ℂ) (x : ComplexThreeChannel) :
    (x.smul z).rotate = x.rotate.smul z := by
  rfl

theorem LinearC3Operator.map_smul_channel
    (A : LinearC3Operator) (z : ℂ) (x : ComplexThreeChannel) :
    A.run (x.smul z) = (A.run x).smul z := by
  change A.run (z • x) = z • A.run x
  exact A.run.map_smul z x

theorem LinearC3Operator.preserves_rotation_eigenspace
    (A : LinearC3Operator)
    (hA : A.commutesWithRotation)
    {lam : ℂ} {x : ComplexThreeChannel}
    (hx : RotationEigenvector lam x) :
    RotationEigenvector lam (A.run x) := by
  unfold RotationEigenvector at hx ⊢
  rw [← hA x, hx]
  exact A.map_smul_channel lam x

def sector0 (x : ComplexThreeChannel) : Prop := RotationEigenvector 1 x
def sector1 (x : ComplexThreeChannel) : Prop := RotationEigenvector omega3 x
def sector2 (x : ComplexThreeChannel) : Prop := RotationEigenvector (omega3^2) x

theorem LinearC3Operator.preserves_sector0
    (A : LinearC3Operator) (hA : A.commutesWithRotation)
    {x : ComplexThreeChannel} (hx : sector0 x) :
    sector0 (A.run x) :=
  A.preserves_rotation_eigenspace hA hx

theorem LinearC3Operator.preserves_sector1
    (A : LinearC3Operator) (hA : A.commutesWithRotation)
    {x : ComplexThreeChannel} (hx : sector1 x) :
    sector1 (A.run x) :=
  A.preserves_rotation_eigenspace hA hx

theorem LinearC3Operator.preserves_sector2
    (A : LinearC3Operator) (hA : A.commutesWithRotation)
    {x : ComplexThreeChannel} (hx : sector2 x) :
    sector2 (A.run x) :=
  A.preserves_rotation_eigenspace hA hx

end MCore.Research.UserProgram
