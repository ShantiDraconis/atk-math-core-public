import MCore.FinalFail.MaterialGeometry
import MCore.FinalFail.MaterialField
import MCore.FinalFail.MaterialGlobalAssembly

namespace MCore.FinalFail.MaterialSynthesis

open MCore.FinalFail.MaterialAlgebra
open MCore.FinalFail.MaterialCalculus
open MCore.FinalFail.MaterialDerived
open MCore.FinalFail.MaterialGeometry
open MCore.FinalFail.MaterialField

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState
abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector
abbrev EState := MCore.FinalFail.MaterialCalculus.EvidenceState

/-!
# Material synthesis laws

These theorems connect the already kernel-checked finite algebra, seven-lane
module, discrete evidence calculus and geometry. They are internal consequences
of the explicit finite definitions. They do not inhabit any external OPEN_MATH
terminal producer.
-/

namespace TriState

/-- Difference is invariant under a common translation. -/
theorem delta_translate
    (x y z : TState) :
    MaterialGeometry.TriState.delta (x + z) (y + z) =
      MaterialGeometry.TriState.delta x y := by
  cases x <;> cases y <;> cases z <;> rfl

/-- Reversing the arguments negates the finite difference. -/
theorem delta_swap
    (x y : TState) :
    MaterialGeometry.TriState.delta y x =
      - MaterialGeometry.TriState.delta x y := by
  cases x <;> cases y <;> rfl

/-- Simultaneous phase rotation preserves the algebraic difference. -/
theorem delta_rho
    (x y : TState) :
    MaterialGeometry.TriState.delta
        (MaterialGeometry.TriState.rho x)
        (MaterialGeometry.TriState.rho y) =
      MaterialGeometry.TriState.delta x y := by
  cases x <;> cases y <;> rfl

/-- The two nonzero tristable values are exactly +1 and -1. -/
theorem nonzero_eq_one_or_neg_one
    (x : TState) (hx : x ≠ 0) :
    x = 1 ∨ x = -(1 : TState) := by
  cases x with
  | seed =>
      exfalso
      exact hx rfl
  | transit =>
      exact Or.inl rfl
  | manifest =>
      exact Or.inr rfl

/-- Every nonzero scalar is self-inverse. -/
theorem nonzero_inv_eq_self
    (x : TState) (hx : x ≠ 0) :
    x⁻¹ = x := by
  exact MaterialDerived.TriState.inv_eq_self x

end TriState

namespace SevenLaneVector

/-- The uniform unit-phase vector. -/
def unitVector : LaneVector where
  riemann := 1
  beal := 1
  pvsnp := 1
  navierStokes := 1
  hodge := 1
  bsd := 1
  yangMills := 1

/-- Global phase rotation is translation by the uniform unit vector. -/
theorem rotate_eq_add_unitVector
    (x : LaneVector) :
    MaterialGeometry.SevenLaneVector.rotate x =
      x + unitVector := by
  apply MaterialAlgebra.SevenLaneVector.extensionality
  · exact MaterialDerived.TriState.rotate_eq_add_one x.riemann
  · exact MaterialDerived.TriState.rotate_eq_add_one x.beal
  · exact MaterialDerived.TriState.rotate_eq_add_one x.pvsnp
  · exact MaterialDerived.TriState.rotate_eq_add_one x.navierStokes
  · exact MaterialDerived.TriState.rotate_eq_add_one x.hodge
  · exact MaterialDerived.TriState.rotate_eq_add_one x.bsd
  · exact MaterialDerived.TriState.rotate_eq_add_one x.yangMills

/-- A nonzero tristable scalar acts injectively on the seven-lane carrier. -/
theorem smul_injective_nonzero
    (a : TState) (ha : a ≠ 0) :
    Function.Injective (fun x : LaneVector =>
      MaterialDerived.SevenLaneVector.smul a x) := by
  intro x y hxy
  apply MaterialAlgebra.SevenLaneVector.extensionality
  · exact MaterialDerived.TriState.mul_left_cancel_nonzero ha
      (congrArg (fun z : LaneVector => z.riemann) hxy)
  · exact MaterialDerived.TriState.mul_left_cancel_nonzero ha
      (congrArg (fun z : LaneVector => z.beal) hxy)
  · exact MaterialDerived.TriState.mul_left_cancel_nonzero ha
      (congrArg (fun z : LaneVector => z.pvsnp) hxy)
  · exact MaterialDerived.TriState.mul_left_cancel_nonzero ha
      (congrArg (fun z : LaneVector => z.navierStokes) hxy)
  · exact MaterialDerived.TriState.mul_left_cancel_nonzero ha
      (congrArg (fun z : LaneVector => z.hodge) hxy)
  · exact MaterialDerived.TriState.mul_left_cancel_nonzero ha
      (congrArg (fun z : LaneVector => z.bsd) hxy)
  · exact MaterialDerived.TriState.mul_left_cancel_nonzero ha
      (congrArg (fun z : LaneVector => z.yangMills) hxy)

/-- Multiplication by a nonzero scalar preserves equality exactly. -/
theorem smul_eq_iff_nonzero
    (a : TState) (ha : a ≠ 0)
    (x y : LaneVector) :
    MaterialDerived.SevenLaneVector.smul a x =
        MaterialDerived.SevenLaneVector.smul a y ↔
      x = y := by
  constructor
  · intro h
    exact smul_injective_nonzero a ha h
  · intro h
    exact congrArg (fun z : LaneVector =>
      MaterialDerived.SevenLaneVector.smul a z) h

/-- Hamming distance is invariant under two global phase rotations as well. -/
theorem hamming_rotate_twice
    (x y : LaneVector) :
    MaterialGeometry.SevenLaneVector.hamming
        (MaterialGeometry.SevenLaneVector.rotate
          (MaterialGeometry.SevenLaneVector.rotate x))
        (MaterialGeometry.SevenLaneVector.rotate
          (MaterialGeometry.SevenLaneVector.rotate y)) =
      MaterialGeometry.SevenLaneVector.hamming x y := by
  rw [MaterialGeometry.SevenLaneVector.hamming_rotate,
      MaterialGeometry.SevenLaneVector.hamming_rotate]

end SevenLaneVector

namespace EvidenceState

/-- Evidence duality reverses the sign of the first discrete derivative. -/
theorem derivative_dual
    (f : Nat → EState) (n : Nat) :
    EvidenceState.derivative
        (fun k => EvidenceState.dual (f k)) n =
      - EvidenceState.derivative f n := by
  unfold EvidenceState.derivative
  rw [EvidenceState.code_dual, EvidenceState.code_dual]
  ring

/-- Evidence duality also reverses the sign of the second derivative. -/
theorem secondDerivative_dual
    (f : Nat → EState) (n : Nat) :
    MaterialGeometry.EvidenceState.secondDerivative
        (fun k => EvidenceState.dual (f k)) n =
      - MaterialGeometry.EvidenceState.secondDerivative f n := by
  unfold MaterialGeometry.EvidenceState.secondDerivative
  rw [derivative_dual, derivative_dual]
  ring

/-- Duality preserves jump magnitude. -/
theorem jumpMagnitude_dual
    (f : Nat → EState) (n : Nat) :
    MaterialGeometry.EvidenceState.jumpMagnitude
        (fun k => EvidenceState.dual (f k)) n =
      MaterialGeometry.EvidenceState.jumpMagnitude f n := by
  unfold MaterialGeometry.EvidenceState.jumpMagnitude
  rw [derivative_dual]
  exact Int.natAbs_neg _

end EvidenceState

#print axioms MCore.FinalFail.MaterialSynthesis.TriState.delta_translate
#print axioms MCore.FinalFail.MaterialSynthesis.TriState.delta_rho
#print axioms MCore.FinalFail.MaterialSynthesis.TriState.nonzero_eq_one_or_neg_one
#print axioms MCore.FinalFail.MaterialSynthesis.SevenLaneVector.rotate_eq_add_unitVector
#print axioms MCore.FinalFail.MaterialSynthesis.SevenLaneVector.smul_injective_nonzero
#print axioms MCore.FinalFail.MaterialSynthesis.EvidenceState.derivative_dual
#print axioms MCore.FinalFail.MaterialSynthesis.EvidenceState.secondDerivative_dual
#print axioms MCore.FinalFail.MaterialSynthesis.EvidenceState.jumpMagnitude_dual

end MCore.FinalFail.MaterialSynthesis
