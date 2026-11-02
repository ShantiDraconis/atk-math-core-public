import MCore.MaterialMath.TriCyclicDecomposition

namespace MCore.MaterialMath

noncomputable section

namespace TriNumber

/-- Ambient Euclidean square of a real tri-state. -/
def euclideanSquare (x : TriNumber ℝ) : ℝ :=
  x.manifest^2 + x.crossing^2 + x.seed^2

/-- Fundamental quadratic identity:
spread = 3 * ambient square - total^2. -/
theorem spread_identity (x : TriNumber ℝ) :
    spread x = 3 * euclideanSquare x - (total x)^2 := by
  simp [spread, euclideanSquare, total]
  ring

/-- On the transverse zero-sum plane, spread is exactly three times the
ambient Euclidean square. -/
theorem spread_of_zeroSum
    (x : TriNumber ℝ) (h : ZeroSum x) :
    spread x = 3 * euclideanSquare x := by
  rw [spread_identity]
  simp [ZeroSum] at h
  rw [h]
  ring

/-- The Euclidean square is nonnegative. -/
theorem euclideanSquare_nonneg (x : TriNumber ℝ) :
    0 ≤ euclideanSquare x := by
  simp [euclideanSquare]
  positivity

/-- On the transverse plane, zero spread forces the zero state. -/
theorem zeroSum_and_zeroSpread_eq_zero
    (x : TriNumber ℝ)
    (hz : ZeroSum x)
    (hs : spread x = 0) :
    x = { manifest := 0, crossing := 0, seed := 0 } := by
  have hb : Balanced x :=
    (spread_eq_zero_iff_balanced x).1 hs
  exact balanced_and_zeroSum_eq_zero x hb hz

/-- Balanced modes carry no torsion against any state. -/
theorem torsion_balanced_left
    (x y : TriNumber ℝ)
    (hx : Balanced x) :
    torsion x y = 0 := by
  rcases x with ⟨m, c, s⟩
  rcases hx with ⟨hmc, hcs⟩
  change m = c at hmc
  change c = s at hcs
  subst c
  subst s
  simp [torsion]
  ring

/-- Balanced modes also carry no torsion on the right. -/
theorem torsion_balanced_right
    (x y : TriNumber ℝ)
    (hy : Balanced y) :
    torsion x y = 0 := by
  rw [torsion_skew]
  rw [torsion_balanced_left y x hy]
  simp

/-- Torsion depends only on the transverse fluctuations. -/
theorem torsion_fluctuation
    (x y : TriNumber ℝ) :
    torsion (fluctuation x) (fluctuation y) = torsion x y := by
  simp [torsion, fluctuation, mean, total]
  ring

/-- Quadratic phase radius on the transverse component. -/
def transverseRadiusSq (x : TriNumber ℝ) : ℝ :=
  euclideanSquare (fluctuation x)

/-- The spread is three times the squared transverse radius. -/
theorem spread_eq_three_transverseRadiusSq
    (x : TriNumber ℝ) :
    spread x = 3 * transverseRadiusSq x := by
  rw [← spread_fluctuation x]
  exact spread_of_zeroSum (fluctuation x) (fluctuation_zeroSum x)

/-- The transverse radius is rotation invariant. -/
theorem transverseRadiusSq_rotate
    (x : TriNumber ℝ) :
    transverseRadiusSq (rotate x) = transverseRadiusSq x := by
  unfold transverseRadiusSq
  rw [fluctuation_rotate]
  simp [euclideanSquare, rotate]
  ring

end TriNumber

/-- The geometry naturally splits into one equilibrium mode and a transverse
two-dimensional phase plane. -/
structure MaterialPhaseGeometry where
  state : TriNumber ℝ
  equilibrium : TriNumber ℝ := TriNumber.balancedProjection state
  transverse : TriNumber ℝ := TriNumber.fluctuation state

end

end MCore.MaterialMath
