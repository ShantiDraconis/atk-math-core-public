import MCore.FinalFail.ExactGapLedger
import MCore.FinalFail.DirectProducerCuts
import MCore.FinalFail.MechanicalClosure
import MCore.FinalFail.MaterialProducerNormalForms

namespace MCore.FinalFail.MaterialOnly

/-!
# Material-only FINAL_ROOT boundary

The purpose of this layer is classification, not proof fabrication.

* Exactly seven OPEN_MATH slots remain: one material producer per unsolved lane.
* P01 machine assembly is tracked separately as mechanical closure.
* Wiring, wrappers, transports, registries and release packaging are not counted
  as mathematical gaps.
-/

open MCore.FinalFail
open MCore.FinalFail.Semantic

structure MaterialBoundary where
  globalOpenProblems : Nat
  directOpenProducers : Nat
  pendingMechanical : Nat
  global_exact : globalOpenProblems = 7
  direct_exact : directOpenProducers = 7
  wiring_separate : pendingMechanical = 1
  deriving Repr

def currentMaterialBoundary : MaterialBoundary :=
  { globalOpenProblems := openFinalProblems
    directOpenProducers := openDirectCount
    pendingMechanical := pendingMechanicalCount
    global_exact := openFinalProblems_eq_seven
    direct_exact := openDirectCount_eq_seven
    wiring_separate := pendingMechanicalCount_eq_one }

def materialMathReady : Prop :=
  producedDirectCount = 7

def mechanicalClosureReady : Prop :=
  closedMechanicalCount = mechanicalClosureCount

def finalRootReady : Prop :=
  materialMathReady ∧ mechanicalClosureReady

theorem material_math_not_ready :
    ¬ materialMathReady := by
  unfold materialMathReady
  simpa [producedDirectCount_eq_zero]

theorem final_root_not_ready :
    ¬ finalRootReady := by
  intro h
  exact material_math_not_ready h.1

/-- This is the fail-closed invariant requested by the material-only policy:
no purely mechanical task can reduce or increase the seven material slots. -/
theorem no_wiring_gap_in_open_math :
    openFinalProblems = 7 ∧
    openDirectCount = 7 ∧
    materialProducerPlanCount = 7 ∧
    pendingMechanicalCount = 1 := by
  exact ⟨openFinalProblems_eq_seven,
    openDirectCount_eq_seven,
    materialProducerPlanCount_eq_seven,
    pendingMechanicalCount_eq_one⟩

end MCore.FinalFail.MaterialOnly
