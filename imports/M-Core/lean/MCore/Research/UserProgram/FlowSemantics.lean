import Mathlib
import MCore.Research.UserProgram.CrossOperatorLaws

namespace MCore.Research.UserProgram

def orbit0 (x : I3Vector) : I3Vector := x
def orbit1 (x : I3Vector) : I3Vector := opT x
def orbit2 (x : I3Vector) : I3Vector := opT (opT x)
def orbit3 (x : I3Vector) : I3Vector := opT (opT (opT x))

theorem orbit3_eq_initial (x : I3Vector) :
    orbit3 x = orbit0 x := by
  exact I3Vector.rotate_three x

def conservedSum (x : I3Vector) : ℂ := x.sum

theorem conservedSum_orbit1 (x : I3Vector) :
    conservedSum (orbit1 x) = conservedSum x :=
  I3Vector.sum_rotate x

theorem conservedSum_orbit2 (x : I3Vector) :
    conservedSum (orbit2 x) = conservedSum x := by
  simp [conservedSum, orbit2, opT, I3Vector.sum_rotate]

theorem conservedSum_orbit3 (x : I3Vector) :
    conservedSum (orbit3 x) = conservedSum x := by
  rw [orbit3_eq_initial]
  rfl

theorem opC_orbit1 (x : I3Vector) :
    opC (orbit1 x) = opC x := by
  ext <;> simp [opC, orbit1, opT, I3Vector.sum_rotate]

theorem opC_orbit2 (x : I3Vector) :
    opC (orbit2 x) = opC x := by
  ext <;> simp [opC, orbit2, opT, I3Vector.sum_rotate]

def cycleDefect (x : I3Vector) : I3Vector :=
  opDelta (orbit0 x) + opDelta (orbit1 x) + opDelta (orbit2 x)

theorem cycleDefect_zero (x : I3Vector) :
    cycleDefect x = 0 := by
  simpa [cycleDefect, orbit0, orbit1, orbit2, opT] using
    delta_cycle_telescopes x

structure FlowCertificate (x : I3Vector) : Prop where
  periodic : orbit3 x = orbit0 x
  sum1 : conservedSum (orbit1 x) = conservedSum x
  sum2 : conservedSum (orbit2 x) = conservedSum x
  sum3 : conservedSum (orbit3 x) = conservedSum x
  center1 : opC (orbit1 x) = opC x
  center2 : opC (orbit2 x) = opC x
  defectCancellation : cycleDefect x = 0

def flowCertificate (x : I3Vector) : FlowCertificate x where
  periodic := orbit3_eq_initial x
  sum1 := conservedSum_orbit1 x
  sum2 := conservedSum_orbit2 x
  sum3 := conservedSum_orbit3 x
  center1 := opC_orbit1 x
  center2 := opC_orbit2 x
  defectCancellation := cycleDefect_zero x

def GlobalFlowLaw : Prop := ∀ x : I3Vector, FlowCertificate x

def globalFlowInhabitant : Inhabitant GlobalFlowLaw :=
  ⟨flowCertificate⟩

end MCore.Research.UserProgram
