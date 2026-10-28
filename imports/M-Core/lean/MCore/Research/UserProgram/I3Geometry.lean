import Mathlib
import MCore.Research.UserProgram.ThreeChannel

namespace MCore.Research.UserProgram

/-- A primitive cube root represented algebraically. -/
def omega3 : ℂ := (-1 + Real.sqrt 3 * Complex.I) / 2

theorem sqrt_three_sq : (Real.sqrt 3)^2 = 3 := by
  norm_num

theorem omega3_sq_add_omega3_add_one :
    omega3^2 + omega3 + 1 = 0 := by
  unfold omega3
  apply Complex.ext <;> simp [Complex.ext_iff, sqrt_three_sq] <;> ring_nf
  · rw [Real.sq_sqrt] <;> norm_num
  · ring

theorem omega3_cube : omega3^3 = 1 := by
  have h := omega3_sq_add_omega3_add_one
  calc
    omega3^3 - 1 = (omega3 - 1) * (omega3^2 + omega3 + 1) := by ring
    _ = 0 := by rw [h, mul_zero]
  exact sub_eq_zero.mp this

def I3State.phase : I3State → ℂ
  | .manifesto => 1
  | .travessia => omega3
  | .semente => omega3^2

theorem phase_sum_zero :
    I3State.phase .manifesto +
    I3State.phase .travessia +
    I3State.phase .semente = 0 := by
  simpa [I3State.phase, add_assoc, add_comm, add_left_comm] using
    omega3_sq_add_omega3_add_one

theorem phase_next (s : I3State) :
    I3State.phase s.next = omega3 * I3State.phase s := by
  cases s
  · simp [I3State.phase]
  · simp [I3State.phase, pow_two]
  · simp [I3State.phase, ← pow_succ, omega3_cube]

structure ComplexThreeChannel where
  manifesto : ℂ
  travessia : ℂ
  semente : ℂ

def ComplexThreeChannel.mean (x : ComplexThreeChannel) : ℂ :=
  (x.manifesto + x.travessia + x.semente) / 3

def ComplexThreeChannel.centered (x : ComplexThreeChannel) : ComplexThreeChannel where
  manifesto := x.manifesto - x.mean
  travessia := x.travessia - x.mean
  semente := x.semente - x.mean

theorem ComplexThreeChannel.centered_sum_zero (x : ComplexThreeChannel) :
    x.centered.manifesto + x.centered.travessia + x.centered.semente = 0 := by
  simp [ComplexThreeChannel.centered, ComplexThreeChannel.mean]
  ring

end MCore.Research.UserProgram
