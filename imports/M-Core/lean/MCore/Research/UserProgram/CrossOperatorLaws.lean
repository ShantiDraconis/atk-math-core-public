import Mathlib
import MCore.Research.UserProgram.ConcreteOperators

namespace MCore.Research.UserProgram

def I3Vector.scale (z : ℂ) (x : I3Vector) : I3Vector := z • x

theorem opGamma_eq_three_C (x : I3Vector) :
    opGamma x = I3Vector.scale 3 (opC x) := by
  ext <;> simp [opGamma, opC, I3Vector.scale, I3Vector.sum, I3Vector.rotate]
  all_goals ring

theorem opC_delta_zero (x : I3Vector) :
    opC (opDelta x) = 0 := by
  ext <;> simp [opC, opDelta, I3Vector.sum, I3Vector.rotate]
  all_goals ring

theorem opDelta_C_zero (x : I3Vector) :
    opDelta (opC x) = 0 := by
  apply opDelta_zero_of_fixed
  exact opC_fixed x

theorem delta_cycle_telescopes (x : I3Vector) :
    opDelta x + opDelta x.rotate + opDelta x.rotate.rotate = 0 := by
  ext <;> simp [opDelta, I3Vector.rotate]
  all_goals ring

def oscillatoryPart (x : I3Vector) : I3Vector :=
  x + (-(opC x))

theorem oscillatoryPart_sum_zero (x : I3Vector) :
    (oscillatoryPart x).sum = 0 := by
  simp [oscillatoryPart, opC, I3Vector.sum]
  ring

theorem reconstruct_C_osc (x : I3Vector) :
    opC x + oscillatoryPart x = x := by
  ext <;> simp [oscillatoryPart, opC, I3Vector.sum]
  all_goals ring

theorem opC_oscillatory_zero (x : I3Vector) :
    opC (oscillatoryPart x) = 0 := by
  ext <;> simp [opC, oscillatoryPart, I3Vector.sum]
  all_goals ring

def CrossOperatorLaw : Prop :=
  (∀ x, opGamma x = I3Vector.scale 3 (opC x)) ∧
  (∀ x, opC (opDelta x) = 0) ∧
  (∀ x, opDelta (opC x) = 0) ∧
  (∀ x, opDelta x + opDelta x.rotate + opDelta x.rotate.rotate = 0) ∧
  (∀ x, (oscillatoryPart x).sum = 0) ∧
  (∀ x, opC x + oscillatoryPart x = x) ∧
  (∀ x, opC (oscillatoryPart x) = 0)

def crossOperatorInhabitant : Inhabitant CrossOperatorLaw :=
  ⟨opGamma_eq_three_C, opC_delta_zero, opDelta_C_zero,
    delta_cycle_telescopes, oscillatoryPart_sum_zero,
    reconstruct_C_osc, opC_oscillatory_zero⟩

end MCore.Research.UserProgram
