import Mathlib
import MCore.Research.UserProgram.I3VectorAlgebra

namespace MCore.Research.UserProgram

abbrev I3End := I3Vector → I3Vector

def opT : I3End := I3Vector.rotate
def opS : I3End := fun x => x.rotate.rotate
def opE : I3End := id
def opQ : I3End := fun x => (omega3 : ℂ) • x
def opDelta : I3End := fun x => x.rotate + (-x)
def opGamma : I3End := fun x => x + x.rotate + x.rotate.rotate
def opC : I3End := fun x =>
  let m : ℂ := x.sum / 3
  ⟨m, m, m⟩

theorem opT_three : opT ∘ opT ∘ opT = id := by
  funext x
  exact I3Vector.rotate_three x

theorem opS_eq_T_sq : opS = opT ∘ opT := by rfl

theorem opT_opS : opT ∘ opS = id := by
  funext x
  exact I3Vector.rotate_three x

theorem opS_opT : opS ∘ opT = id := by
  funext x
  exact I3Vector.rotate_three x

theorem opE_identity : opE = id := rfl

theorem opDelta_apply (x : I3Vector) :
    opDelta x = x.rotate + (-x) := rfl

theorem opDelta_zero_of_fixed {x : I3Vector} (hx : x.rotate = x) :
    opDelta x = 0 := by
  simp [opDelta, hx]

theorem opGamma_rotate (x : I3Vector) :
    opGamma x.rotate = opGamma x := by
  ext <;> simp [opGamma, I3Vector.rotate]
  all_goals ring

theorem opGamma_fixed (x : I3Vector) :
    (opGamma x).rotate = opGamma x := by
  ext <;> simp [opGamma, I3Vector.rotate]
  all_goals ring

theorem opC_fixed (x : I3Vector) :
    (opC x).rotate = opC x := by
  rfl

theorem opC_idempotent (x : I3Vector) :
    opC (opC x) = opC x := by
  ext <;> simp [opC, I3Vector.sum]
  all_goals ring

theorem opQ_rotate (x : I3Vector) :
    opQ x.rotate = (opQ x).rotate := by
  rfl

theorem opT_sum (x : I3Vector) : (opT x).sum = x.sum :=
  I3Vector.sum_rotate x

theorem opS_sum (x : I3Vector) : (opS x).sum = x.sum := by
  simp [opS, I3Vector.sum_rotate]

def SevenOperatorLaw : Prop :=
  (opT ∘ opT ∘ opT = id) ∧
  (opT ∘ opS = id) ∧
  (opS ∘ opT = id) ∧
  (∀ x, (opGamma x).rotate = opGamma x) ∧
  (∀ x, (opC x).rotate = opC x) ∧
  (∀ x, opC (opC x) = opC x) ∧
  (∀ x, opQ x.rotate = (opQ x).rotate)

def sevenOperatorInhabitant : Inhabitant SevenOperatorLaw :=
  ⟨opT_three, opT_opS, opS_opT, opGamma_fixed,
    opC_fixed, opC_idempotent, opQ_rotate⟩

end MCore.Research.UserProgram
