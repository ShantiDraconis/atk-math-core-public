import Mathlib
import MCore.Research.UserProgram.I3Geometry

namespace MCore.Research.UserProgram

def ComplexThreeChannel.rotate (x : ComplexThreeChannel) : ComplexThreeChannel where
  manifesto := x.travessia
  travessia := x.semente
  semente := x.manifesto

def ComplexThreeChannel.fourier0 (x : ComplexThreeChannel) : ℂ :=
  (x.manifesto + x.travessia + x.semente) / 3

def ComplexThreeChannel.fourier1 (x : ComplexThreeChannel) : ℂ :=
  (x.manifesto + omega3^2 * x.travessia + omega3 * x.semente) / 3

def ComplexThreeChannel.fourier2 (x : ComplexThreeChannel) : ℂ :=
  (x.manifesto + omega3 * x.travessia + omega3^2 * x.semente) / 3

def ComplexThreeChannel.fromFourier (a0 a1 a2 : ℂ) : ComplexThreeChannel where
  manifesto := a0 + a1 + a2
  travessia := a0 + omega3 * a1 + omega3^2 * a2
  semente := a0 + omega3^2 * a1 + omega3 * a2

private theorem omega3_four : omega3^4 = omega3 := by
  calc
    omega3^4 = omega3^3 * omega3 := by ring
    _ = omega3 := by rw [omega3_cube, one_mul]

theorem ComplexThreeChannel.fourier_inversion (x : ComplexThreeChannel) :
    ComplexThreeChannel.fromFourier x.fourier0 x.fourier1 x.fourier2 = x := by
  apply ComplexThreeChannel.ext <;>
    simp [ComplexThreeChannel.fromFourier, ComplexThreeChannel.fourier0,
      ComplexThreeChannel.fourier1, ComplexThreeChannel.fourier2]
  all_goals
    have h := omega3_sq_add_omega3_add_one
    field_simp
    ring_nf at h ⊢
    nlinarith [h]

theorem ComplexThreeChannel.fourier0_rotate (x : ComplexThreeChannel) :
    x.rotate.fourier0 = x.fourier0 := by
  simp [ComplexThreeChannel.rotate, ComplexThreeChannel.fourier0]
  ring

theorem ComplexThreeChannel.fourier1_rotate (x : ComplexThreeChannel) :
    x.rotate.fourier1 = omega3 * x.fourier1 := by
  simp [ComplexThreeChannel.rotate, ComplexThreeChannel.fourier1]
  have h := omega3_sq_add_omega3_add_one
  have hc := omega3_cube
  field_simp
  ring_nf at h hc ⊢
  nlinarith [h, hc]

theorem ComplexThreeChannel.fourier2_rotate (x : ComplexThreeChannel) :
    x.rotate.fourier2 = omega3^2 * x.fourier2 := by
  simp [ComplexThreeChannel.rotate, ComplexThreeChannel.fourier2]
  have h := omega3_sq_add_omega3_add_one
  have hc := omega3_cube
  have h4 := omega3_four
  field_simp
  ring_nf at h hc h4 ⊢
  nlinarith [h, hc, h4]

end MCore.Research.UserProgram
