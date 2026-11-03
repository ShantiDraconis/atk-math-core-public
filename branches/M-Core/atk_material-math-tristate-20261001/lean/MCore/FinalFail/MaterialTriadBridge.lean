import MCore.FinalFail.MaterialMetric
import MCore.FinalFail.TopologyOperatorCore

namespace MCore.FinalFail.MaterialTriadBridge

open MCore.FinalFail.MaterialGeometry

abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector

/-!
Canonical bridge from the seven-lane phase geometry to the generic Triad core.
The minus chart is identity; the plus chart is global phase rotation.
-/

def lanePhaseTriad :
    MCore.FinalFail.Triad LaneVector LaneVector LaneVector where
  C_minus := fun x => x
  C_plus := MaterialGeometry.SevenLaneVector.rotate
  R_minus := fun x => some x
  R_plus := fun x =>
    some
      (MaterialGeometry.SevenLaneVector.rotate
        (MaterialGeometry.SevenLaneVector.rotate x))

theorem lanePhaseTriad_biRetraction :
    MCore.FinalFail.Triad.isBiRetractionOn
      lanePhaseTriad (fun _ => True) := by
  constructor
  · intro m _
    exact ⟨m, rfl, rfl⟩
  · intro m _
    refine ⟨
      MaterialGeometry.SevenLaneVector.rotate
        (MaterialGeometry.SevenLaneVector.rotate m),
      rfl,
      ?_
    ⟩
    exact MaterialGeometry.SevenLaneVector.rotate_three m

theorem lanePhaseTriad_not_defect (m : LaneVector) :
    ¬ MCore.FinalFail.Triad.defect lanePhaseTriad m := by
  exact MCore.FinalFail.Triad.bi_retraction_not_defect
    lanePhaseTriad lanePhaseTriad_biRetraction trivial

theorem lanePhaseTriad_fixed (m : LaneVector) :
    MCore.FinalFail.Triad.isFixedPoint lanePhaseTriad m := by
  exact MCore.FinalFail.Triad.bi_retraction_implies_fixed
    lanePhaseTriad lanePhaseTriad_biRetraction trivial

theorem lanePhaseTriad_minusFiber_nonempty (m : LaneVector) :
    ∃ x, MCore.FinalFail.Triad.fiberMinus lanePhaseTriad m x := by
  exact MCore.FinalFail.Triad.minus_retraction_fiber_nonempty
    lanePhaseTriad lanePhaseTriad_biRetraction.1 trivial

theorem lanePhaseTriad_plusFiber_nonempty (m : LaneVector) :
    ∃ x, MCore.FinalFail.Triad.fiberPlus lanePhaseTriad m x := by
  exact MCore.FinalFail.Triad.plus_retraction_fiber_nonempty
    lanePhaseTriad lanePhaseTriad_biRetraction.2 trivial

#print axioms MCore.FinalFail.MaterialTriadBridge.lanePhaseTriad_biRetraction
#print axioms MCore.FinalFail.MaterialTriadBridge.lanePhaseTriad_not_defect
#print axioms MCore.FinalFail.MaterialTriadBridge.lanePhaseTriad_fixed
#print axioms MCore.FinalFail.MaterialTriadBridge.lanePhaseTriad_plusFiber_nonempty

end MCore.FinalFail.MaterialTriadBridge
