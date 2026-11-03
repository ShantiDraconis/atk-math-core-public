import MCore.FinalFail.MaterialGeometry
import MCore.FinalFail.MaterialField

namespace MCore.FinalFail.MaterialAsymmetry

open MCore.FinalFail.MaterialAlgebra
open MCore.FinalFail.MaterialGeometry

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState
abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector

/-!
# Directed and asymmetric arithmetic of the triadic material phase

This module derives a directional calculus from the already kernel-checked
three-element field table.  It is internal finite mathematics.  It does not
supply any open-problem terminal inhabitant.
-/

namespace TriState

/-- Reflection of the triadic phase.  Algebraically this is additive negation. -/
def reflect (x : TState) : TState := -x

@[simp] theorem reflect_involutive (x : TState) :
    reflect (reflect x) = x := by
  cases x <;> rfl

/-- Directed difference, from y to x. -/
def directedDiff (x y : TState) : TState :=
  x + (-y)

@[simp] theorem directedDiff_self (x : TState) :
    directedDiff x x = 0 := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x

theorem directedDiff_eq_zero_iff (x y : TState) :
    directedDiff x y = 0 ↔ x = y := by
  exact MCore.FinalFail.MaterialGeometry.TriState.delta_eq_zero_iff x y

/-- Reversing direction negates the directed difference. -/
theorem directedDiff_reverse (x y : TState) :
    directedDiff y x = -(directedDiff x y) := by
  cases x <;> cases y <;> rfl

/-- Translation invariance of directed difference. -/
theorem directedDiff_translate (x y a : TState) :
    directedDiff (x + a) (y + a) = directedDiff x y := by
  cases x <;> cases y <;> cases a <;> rfl

/-- Cocycle/chain law for directed differences. -/
theorem directedDiff_chain (x y z : TState) :
    directedDiff x z = directedDiff x y + directedDiff y z := by
  cases x <;> cases y <;> cases z <;> rfl

/-- The canonical rotation advances every state by the same unit phase. -/
theorem rotation_has_constant_increment (x : TState) :
    directedDiff (MCore.FinalFail.MaterialGeometry.TriState.rho x) x = .transit := by
  cases x <;> rfl

/-- Two rotations advance by the conjugate phase. -/
theorem rotation_two_has_constant_increment (x : TState) :
    directedDiff
      (MCore.FinalFail.MaterialGeometry.TriState.rho
        (MCore.FinalFail.MaterialGeometry.TriState.rho x)) x =
      .manifest := by
  cases x <;> rfl

/-- Dihedral relation: reflection conjugates the forward rotation to its inverse. -/
theorem reflect_rotate_reflect (x : TState) :
    reflect
      (MCore.FinalFail.MaterialGeometry.TriState.rho (reflect x)) =
    MCore.FinalFail.MaterialGeometry.TriState.rho
      (MCore.FinalFail.MaterialGeometry.TriState.rho x) := by
  cases x <;> rfl

/-- The rotation/reflection operators therefore obey the D3 presentation:
rho^3 = 1, sigma^2 = 1, sigma*rho*sigma = rho^-1. -/
theorem dihedral_three_relations (x : TState) :
    MCore.FinalFail.MaterialGeometry.TriState.rho
        (MCore.FinalFail.MaterialGeometry.TriState.rho
          (MCore.FinalFail.MaterialGeometry.TriState.rho x)) = x ∧
    reflect (reflect x) = x ∧
    reflect
      (MCore.FinalFail.MaterialGeometry.TriState.rho (reflect x)) =
      MCore.FinalFail.MaterialGeometry.TriState.rho
        (MCore.FinalFail.MaterialGeometry.TriState.rho x) := by
  exact ⟨
    MCore.FinalFail.MaterialGeometry.TriState.rho_three x,
    reflect_involutive x,
    reflect_rotate_reflect x
  ⟩

/-- Integer orientation coordinate for a directed pair. -/
def orientation (x y : TState) : Int :=
  Int.ofNat (MCore.FinalFail.MaterialDerived.TriState.code y) -
  Int.ofNat (MCore.FinalFail.MaterialDerived.TriState.code x)

theorem orientation_reverse (x y : TState) :
    orientation y x = - orientation x y := by
  unfold orientation
  omega

theorem orientation_self (x : TState) :
    orientation x x = 0 := by
  unfold orientation
  omega

theorem orientation_bounds (x y : TState) :
    -2 ≤ orientation x y ∧ orientation x y ≤ 2 := by
  cases x <;> cases y <;> norm_num [orientation, MCore.FinalFail.MaterialDerived.TriState.code]

/-- Integer orientation is additive along a directed chain. -/
theorem orientation_chain (x y z : TState) :
    orientation x z = orientation x y + orientation y z := by
  unfold orientation
  omega

end TriState

namespace SevenLaneVector

/-- Componentwise reflection. -/
def reflect (x : LaneVector) : LaneVector where
  riemann := TriState.reflect x.riemann
  beal := TriState.reflect x.beal
  pvsnp := TriState.reflect x.pvsnp
  navierStokes := TriState.reflect x.navierStokes
  hodge := TriState.reflect x.hodge
  bsd := TriState.reflect x.bsd
  yangMills := TriState.reflect x.yangMills

@[simp] theorem reflect_involutive (x : LaneVector) :
    reflect (reflect x) = x := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality <;>
    exact TriState.reflect_involutive _

/-- Componentwise directed difference. -/
def directedDiff (x y : LaneVector) : LaneVector where
  riemann := TriState.directedDiff x.riemann y.riemann
  beal := TriState.directedDiff x.beal y.beal
  pvsnp := TriState.directedDiff x.pvsnp y.pvsnp
  navierStokes := TriState.directedDiff x.navierStokes y.navierStokes
  hodge := TriState.directedDiff x.hodge y.hodge
  bsd := TriState.directedDiff x.bsd y.bsd
  yangMills := TriState.directedDiff x.yangMills y.yangMills

@[simp] theorem directedDiff_self (x : LaneVector) :
    directedDiff x x = MCore.FinalFail.MaterialAlgebra.SevenLaneVector.zero := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality <;>
    exact TriState.directedDiff_self _

theorem directedDiff_chain (x y z : LaneVector) :
    directedDiff x z = directedDiff x y + directedDiff y z := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · exact TriState.directedDiff_chain x.riemann y.riemann z.riemann
  · exact TriState.directedDiff_chain x.beal y.beal z.beal
  · exact TriState.directedDiff_chain x.pvsnp y.pvsnp z.pvsnp
  · exact TriState.directedDiff_chain x.navierStokes y.navierStokes z.navierStokes
  · exact TriState.directedDiff_chain x.hodge y.hodge z.hodge
  · exact TriState.directedDiff_chain x.bsd y.bsd z.bsd
  · exact TriState.directedDiff_chain x.yangMills y.yangMills z.yangMills

/-- Seven-lane D3 action law, inherited pointwise from TriState. -/
theorem reflect_rotate_reflect (x : LaneVector) :
    reflect
      (MCore.FinalFail.MaterialGeometry.SevenLaneVector.rotate (reflect x)) =
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.rotate
      (MCore.FinalFail.MaterialGeometry.SevenLaneVector.rotate x) := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality <;>
    exact TriState.reflect_rotate_reflect _

/-- Rotation is an isometry for the Hamming geometry. -/
theorem rotation_isometry (x y : LaneVector) :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming
      (MCore.FinalFail.MaterialGeometry.SevenLaneVector.rotate x)
      (MCore.FinalFail.MaterialGeometry.SevenLaneVector.rotate y) =
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming x y :=
  MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming_rotate x y

/-- Reflection is also an isometry for Hamming geometry. -/
theorem reflection_isometry (x y : LaneVector) :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming
      (reflect x) (reflect y) =
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming x y := by
  have hiff : ∀ a b : TState, TriState.reflect a = TriState.reflect b ↔ a = b := by
    intro a b
    cases a <;> cases b <;> decide
  unfold MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming reflect
  simp [hiff]

end SevenLaneVector

#print axioms MCore.FinalFail.MaterialAsymmetry.TriState.directedDiff_reverse
#print axioms MCore.FinalFail.MaterialAsymmetry.TriState.directedDiff_chain
#print axioms MCore.FinalFail.MaterialAsymmetry.TriState.dihedral_three_relations
#print axioms MCore.FinalFail.MaterialAsymmetry.TriState.orientation_chain
#print axioms MCore.FinalFail.MaterialAsymmetry.SevenLaneVector.directedDiff_chain
#print axioms MCore.FinalFail.MaterialAsymmetry.SevenLaneVector.reflect_rotate_reflect
#print axioms MCore.FinalFail.MaterialAsymmetry.SevenLaneVector.reflection_isometry

end MCore.FinalFail.MaterialAsymmetry
