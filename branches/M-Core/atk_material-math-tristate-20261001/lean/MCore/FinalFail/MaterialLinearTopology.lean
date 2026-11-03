import MCore.FinalFail.MaterialDerived
import MCore.FinalFail.MaterialGeometry

namespace MCore.FinalFail.MaterialLinearTopology

open MCore.FinalFail.MaterialAlgebra
open MCore.FinalFail.MaterialDerived
open MCore.FinalFail.MaterialGeometry

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState
abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector

/-!
# Finite linear/topological structure of the seven-lane material carrier

The carrier is the explicit 7-coordinate product of the already kernel-checked
three-element algebra.  Everything below is internal finite mathematics.
No theorem here produces an inhabitant of any external open-problem target.
-/

namespace TriState

/-- Support is exactly the indicator of nonzero-ness. -/
theorem support_eq_indicator (x : TState) :
    MCore.FinalFail.MaterialGeometry.TriState.support x =
      (if x = 0 then 0 else 1) := by
  cases x <;> rfl


@[simp] theorem zero_add_state (x : TState) :
    (0 : TState) + x = x := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.seed_add x

@[simp] theorem add_zero_state (x : TState) :
    x + (0 : TState) = x := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.add_seed x

/-- A nonzero scalar preserves zero/nonzero status. -/
theorem mul_eq_zero_iff_of_left_ne_zero
    (a x : TState) (ha : a ≠ 0) :
    a * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact hx
    · have hprod :=
        MCore.FinalFail.MaterialDerived.TriState.mul_eq_zero_iff a x
      exact (hprod.mp h).resolve_left ha
  · intro hx
    subst x
    exact MCore.FinalFail.MaterialAlgebra.TriState.mul_zero a

/-- Support is invariant under multiplication by a nonzero scalar. -/
theorem support_mul_left_nonzero
    (a x : TState) (ha : a ≠ 0) :
    MCore.FinalFail.MaterialGeometry.TriState.support (a * x) =
      MCore.FinalFail.MaterialGeometry.TriState.support x := by
  rw [support_eq_indicator, support_eq_indicator]
  have hiff := mul_eq_zero_iff_of_left_ne_zero a x ha
  by_cases hx : x = 0
  · simp [hx, hiff]
  · have hax : a * x ≠ 0 := by
      intro h
      exact hx (hiff.mp h)
    simp [hx, hax]

end TriState

namespace SevenLaneVector

/-- Canonical coordinate basis for the seven named lanes. -/
def eRiemann : LaneVector where
  riemann := 1
  beal := 0
  pvsnp := 0
  navierStokes := 0
  hodge := 0
  bsd := 0
  yangMills := 0

def eBeal : LaneVector where
  riemann := 0
  beal := 1
  pvsnp := 0
  navierStokes := 0
  hodge := 0
  bsd := 0
  yangMills := 0

def ePvsNP : LaneVector where
  riemann := 0
  beal := 0
  pvsnp := 1
  navierStokes := 0
  hodge := 0
  bsd := 0
  yangMills := 0

def eNavierStokes : LaneVector where
  riemann := 0
  beal := 0
  pvsnp := 0
  navierStokes := 1
  hodge := 0
  bsd := 0
  yangMills := 0

def eHodge : LaneVector where
  riemann := 0
  beal := 0
  pvsnp := 0
  navierStokes := 0
  hodge := 1
  bsd := 0
  yangMills := 0

def eBSD : LaneVector where
  riemann := 0
  beal := 0
  pvsnp := 0
  navierStokes := 0
  hodge := 0
  bsd := 1
  yangMills := 0

def eYangMills : LaneVector where
  riemann := 0
  beal := 0
  pvsnp := 0
  navierStokes := 0
  hodge := 0
  bsd := 0
  yangMills := 1

@[simp] theorem support_eRiemann :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount eRiemann = 1 := by rfl
@[simp] theorem support_eBeal :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount eBeal = 1 := by rfl
@[simp] theorem support_ePvsNP :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount ePvsNP = 1 := by rfl
@[simp] theorem support_eNavierStokes :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount eNavierStokes = 1 := by rfl
@[simp] theorem support_eHodge :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount eHodge = 1 := by rfl
@[simp] theorem support_eBSD :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount eBSD = 1 := by rfl
@[simp] theorem support_eYangMills :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount eYangMills = 1 := by rfl

/-- Every seven-lane vector is the sum of its seven scalar coordinate vectors. -/
theorem coordinate_decomposition (x : LaneVector) :
    x =
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul x.riemann eRiemann +
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul x.beal eBeal +
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul x.pvsnp ePvsNP +
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul x.navierStokes eNavierStokes +
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul x.hodge eHodge +
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul x.bsd eBSD +
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul x.yangMills eYangMills := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality <;>
    simp only [
      MCore.FinalFail.MaterialDerived.SevenLaneVector.smul,
      eRiemann, eBeal, ePvsNP, eNavierStokes, eHodge, eBSD, eYangMills,
      MCore.FinalFail.MaterialAlgebra.SevenLaneVector.add,
      MCore.FinalFail.MaterialAlgebra.TriState.mul_one,
      MCore.FinalFail.MaterialAlgebra.TriState.mul_zero,
      MCore.FinalFail.MaterialLinearTopology.TriState.zero_add_state,
      MCore.FinalFail.MaterialLinearTopology.TriState.add_zero_state
    ]

/-- The Hamming weight of a vector is its support count. -/
theorem supportCount_eq_hamming_zero (x : LaneVector) :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount x =
      MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming
        x MCore.FinalFail.MaterialAlgebra.SevenLaneVector.zero := by
  unfold MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount
  unfold MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming
  unfold MCore.FinalFail.MaterialAlgebra.SevenLaneVector.zero
  simp only [MCore.FinalFail.MaterialLinearTopology.TriState.support_eq_indicator]
  rfl

/-- Nonzero scalar multiplication preserves support/Hamming weight. -/
theorem supportCount_smul_nonzero
    (a : TState) (x : LaneVector) (ha : a ≠ 0) :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount (MCore.FinalFail.MaterialDerived.SevenLaneVector.smul a x) =
      MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount x := by
  unfold MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount
  unfold MCore.FinalFail.MaterialDerived.SevenLaneVector.smul
  rw [
    MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero a x.riemann ha,
    MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero a x.beal ha,
    MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero a x.pvsnp ha,
    MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero a x.navierStokes ha,
    MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero a x.hodge ha,
    MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero a x.bsd ha,
    MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero a x.yangMills ha
  ]

/-- Nonzero scalar multiplication is an isometry of the Hamming geometry. -/
theorem hamming_smul_nonzero
    (a : TState) (x y : LaneVector) (ha : a ≠ 0) :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming
        (MCore.FinalFail.MaterialDerived.SevenLaneVector.smul a x) (MCore.FinalFail.MaterialDerived.SevenLaneVector.smul a y) =
      MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming x y := by
  unfold MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming
  unfold MCore.FinalFail.MaterialDerived.SevenLaneVector.smul
  have hR :
      a * x.riemann = a * y.riemann ↔ x.riemann = y.riemann := by
    constructor
    · intro h
      exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha h
    · intro h
      exact congrArg (fun z : TState => a * z) h
  have hB :
      a * x.beal = a * y.beal ↔ x.beal = y.beal := by
    constructor
    · intro h
      exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha h
    · intro h
      exact congrArg (fun z : TState => a * z) h
  have hP :
      a * x.pvsnp = a * y.pvsnp ↔ x.pvsnp = y.pvsnp := by
    constructor
    · intro h
      exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha h
    · intro h
      exact congrArg (fun z : TState => a * z) h
  have hN :
      a * x.navierStokes = a * y.navierStokes ↔ x.navierStokes = y.navierStokes := by
    constructor
    · intro h
      exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha h
    · intro h
      exact congrArg (fun z : TState => a * z) h
  have hH :
      a * x.hodge = a * y.hodge ↔ x.hodge = y.hodge := by
    constructor
    · intro h
      exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha h
    · intro h
      exact congrArg (fun z : TState => a * z) h
  have hD :
      a * x.bsd = a * y.bsd ↔ x.bsd = y.bsd := by
    constructor
    · intro h
      exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha h
    · intro h
      exact congrArg (fun z : TState => a * z) h
  have hY :
      a * x.yangMills = a * y.yangMills ↔ x.yangMills = y.yangMills := by
    constructor
    · intro h
      exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha h
    · intro h
      exact congrArg (fun z : TState => a * z) h
  simp [hR, hB, hP, hN, hH, hD, hY]

end SevenLaneVector

#print axioms MCore.FinalFail.MaterialLinearTopology.TriState.support_mul_left_nonzero
#print axioms MCore.FinalFail.MaterialLinearTopology.SevenLaneVector.coordinate_decomposition
#print axioms MCore.FinalFail.MaterialLinearTopology.SevenLaneVector.supportCount_eq_hamming_zero
#print axioms MCore.FinalFail.MaterialLinearTopology.SevenLaneVector.supportCount_smul_nonzero
#print axioms MCore.FinalFail.MaterialLinearTopology.SevenLaneVector.hamming_smul_nonzero

end MCore.FinalFail.MaterialLinearTopology
