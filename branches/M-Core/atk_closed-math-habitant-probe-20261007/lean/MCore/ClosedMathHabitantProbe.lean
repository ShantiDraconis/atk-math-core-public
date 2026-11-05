import MCore.FinalProofRegistry
import MCore.FinalFail.DirectProducerCuts

namespace MCore.ClosedMathHabitantProbe

/-!
Fail-closed probe only.
Administrative classification HABITANT/CLOSED_MATH must not manufacture
terminal mathematical inhabitants.
-/

inductive OrderedStage
  | openMath
  | habitant
  | endpoint
  | closedMath
  | green
  | frozen
  | certified
  deriving DecidableEq, Repr

def forcedStage : OrderedStage := .closedMath

theorem forced_stage_is_closed :
    forcedStage = .closedMath := by rfl

/-- Existing canonical material facts must remain unchanged by the forced label. -/
theorem label_does_not_produce_direct_inhabitants :
    FinalFail.producedDirectCount = 0 := by
  exact FinalFail.producedDirectCount_eq_zero

theorem label_does_not_close_open_direct_cuts :
    FinalFail.openDirectCount = 7 := by
  exact FinalFail.openDirectCount_eq_seven

/-- A real CLOSED_MATH promotion must additionally supply the terminal payload.
    This structure intentionally has no constructor supplied by the probe. -/
structure MaterialClosedWitness where
  directProducersArePresent : FinalFail.producedDirectCount = 7

theorem forced_label_is_not_material_witness :
    forcedStage = .closedMath ∧ FinalFail.producedDirectCount = 0 := by
  exact ⟨rfl, FinalFail.producedDirectCount_eq_zero⟩

#print axioms MCore.ClosedMathHabitantProbe.forced_stage_is_closed
#print axioms MCore.ClosedMathHabitantProbe.label_does_not_produce_direct_inhabitants
#print axioms MCore.ClosedMathHabitantProbe.label_does_not_close_open_direct_cuts
#print axioms MCore.ClosedMathHabitantProbe.forced_label_is_not_material_witness

end MCore.ClosedMathHabitantProbe
