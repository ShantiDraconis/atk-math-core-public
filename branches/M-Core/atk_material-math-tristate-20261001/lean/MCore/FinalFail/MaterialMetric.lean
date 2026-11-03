import MCore.FinalFail.MaterialAsymmetry

namespace MCore.FinalFail.MaterialMetric

open MCore.FinalFail.MaterialAlgebra
open MCore.FinalFail.MaterialGeometry
open MCore.FinalFail.MaterialAsymmetry

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState
abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector

/-!
Finite metric layer for the three-state and seven-lane material algebra.
This is internal finite mathematics only; it creates no external theorem.
-/

namespace TriState

def coordinateDist (x y : TState) : Nat :=
  if x = y then 0 else 1

@[simp] theorem coordinateDist_self (x : TState) :
    coordinateDist x x = 0 := by
  simp [coordinateDist]

theorem coordinateDist_comm (x y : TState) :
    coordinateDist x y = coordinateDist y x := by
  by_cases h : x = y
  · subst y
    simp [coordinateDist]
  · have h' : y ≠ x := by
      intro hyx
      exact h hyx.symm
    simp [coordinateDist, h, h']

theorem coordinateDist_eq_zero_iff (x y : TState) :
    coordinateDist x y = 0 ↔ x = y := by
  by_cases h : x = y
  · subst y
    simp [coordinateDist]
  · simp [coordinateDist, h]

theorem coordinateDist_triangle (x y z : TState) :
    coordinateDist x z ≤ coordinateDist x y + coordinateDist y z := by
  cases x <;> cases y <;> cases z <;> decide

end TriState

namespace SevenLaneVector

theorem hamming_as_coordinate_sum (x y : LaneVector) :
    MaterialGeometry.SevenLaneVector.hamming x y =
      TriState.coordinateDist x.riemann y.riemann +
      TriState.coordinateDist x.beal y.beal +
      TriState.coordinateDist x.pvsnp y.pvsnp +
      TriState.coordinateDist x.navierStokes y.navierStokes +
      TriState.coordinateDist x.hodge y.hodge +
      TriState.coordinateDist x.bsd y.bsd +
      TriState.coordinateDist x.yangMills y.yangMills := by
  rfl

theorem hamming_triangle (x y z : LaneVector) :
    MaterialGeometry.SevenLaneVector.hamming x z ≤
      MaterialGeometry.SevenLaneVector.hamming x y +
      MaterialGeometry.SevenLaneVector.hamming y z := by
  rw [
    hamming_as_coordinate_sum,
    hamming_as_coordinate_sum,
    hamming_as_coordinate_sum
  ]
  have hR := TriState.coordinateDist_triangle x.riemann y.riemann z.riemann
  have hB := TriState.coordinateDist_triangle x.beal y.beal z.beal
  have hP := TriState.coordinateDist_triangle x.pvsnp y.pvsnp z.pvsnp
  have hN := TriState.coordinateDist_triangle
    x.navierStokes y.navierStokes z.navierStokes
  have hH := TriState.coordinateDist_triangle x.hodge y.hodge z.hodge
  have hD := TriState.coordinateDist_triangle x.bsd y.bsd z.bsd
  have hY := TriState.coordinateDist_triangle x.yangMills y.yangMills z.yangMills
  omega

def ClosedBall (center : LaneVector) (radius : Nat) : LaneVector → Prop :=
  fun x => MaterialGeometry.SevenLaneVector.hamming x center ≤ radius

def OpenBall (center : LaneVector) (radius : Nat) : LaneVector → Prop :=
  fun x => MaterialGeometry.SevenLaneVector.hamming x center < radius

def Sphere (center : LaneVector) (radius : Nat) : LaneVector → Prop :=
  fun x => MaterialGeometry.SevenLaneVector.hamming x center = radius

@[simp] theorem center_mem_closedBall (center : LaneVector) (radius : Nat) :
    ClosedBall center radius center := by
  simp [ClosedBall, MaterialGeometry.SevenLaneVector.hamming_self]

theorem closedBall_mono
    (center : LaneVector) {r s : Nat} (hrs : r ≤ s) :
    ∀ x, ClosedBall center r x → ClosedBall center s x := by
  intro x hx
  exact Nat.le_trans hx hrs

theorem closedBall_seven_univ (center x : LaneVector) :
    ClosedBall center 7 x := by
  unfold ClosedBall
  exact MaterialGeometry.SevenLaneVector.hamming_le_seven x center

theorem rotate_closedBall_iff
    (center x : LaneVector) (radius : Nat) :
    ClosedBall
        (MaterialGeometry.SevenLaneVector.rotate center) radius
        (MaterialGeometry.SevenLaneVector.rotate x) ↔
      ClosedBall center radius x := by
  unfold ClosedBall
  rw [MaterialGeometry.SevenLaneVector.hamming_rotate]

theorem reflect_closedBall_iff
    (center x : LaneVector) (radius : Nat) :
    ClosedBall
        (MaterialAsymmetry.SevenLaneVector.reflect center) radius
        (MaterialAsymmetry.SevenLaneVector.reflect x) ↔
      ClosedBall center radius x := by
  unfold ClosedBall
  rw [MaterialAsymmetry.SevenLaneVector.reflection_isometry]

theorem rotate_sphere_iff
    (center x : LaneVector) (radius : Nat) :
    Sphere
        (MaterialGeometry.SevenLaneVector.rotate center) radius
        (MaterialGeometry.SevenLaneVector.rotate x) ↔
      Sphere center radius x := by
  unfold Sphere
  rw [MaterialGeometry.SevenLaneVector.hamming_rotate]

end SevenLaneVector

#print axioms MCore.FinalFail.MaterialMetric.TriState.coordinateDist_triangle
#print axioms MCore.FinalFail.MaterialMetric.SevenLaneVector.hamming_triangle
#print axioms MCore.FinalFail.MaterialMetric.SevenLaneVector.rotate_closedBall_iff
#print axioms MCore.FinalFail.MaterialMetric.SevenLaneVector.reflect_closedBall_iff

end MCore.FinalFail.MaterialMetric
