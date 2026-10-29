import MCore.K23

namespace MCore

/-- A regulator family is kept abstract at K24, but cutoff and volume are
separate types so uniformity cannot be hidden in one undifferentiated Prop. -/
structure K24RegulatorFamily where
  Cutoff : Type
  Volume : Type
  admissible : Cutoff → Volume → Prop

/-- Concrete shape of the constructive-measure obligation.  `MeasureModel`
represents regulated Euclidean data; the structure does not assert existence. -/
structure K24RegulatedMeasureProblem (R : K24RegulatorFamily) where
  MeasureModel : R.Cutoff → R.Volume → Type
  existsOnAdmissible : Prop
  gaugeInvariantSector : Prop
  reflectionPositiveOnAdmissible : Prop
  cutoffTightness : Prop
  volumeTightness : Prop

/-- K24 records exactly which regulator controls would be sufficient to feed
K23.  The transfer itself remains an explicit scientific bridge. -/
structure K24MeasureToK23Bridge
    {F : K20ScientificFrontier}
    (R : K24RegulatorFamily)
    (P : K24RegulatedMeasureProblem R)
    (C : K23ConstructiveYM4Data F) where
  existenceFeeds : P.existsOnAdmissible → C.regulatedMeasuresExist
  gaugeSectorFeeds : P.gaugeInvariantSector → C.gaugeInvariantObservablesDefined
  reflectionFeeds : P.reflectionPositiveOnAdmissible → C.reflectionPositivityUniform
  tightnessFeedsConvergence :
    P.cutoffTightness → P.volumeTightness → C.schwingerFunctionsConverge

/-- The regulator package can provide four K23 inputs, but deliberately cannot
manufacture OS reconstruction applicability. -/
theorem k24_measure_controls_feed_k23
    {F : K20ScientificFrontier}
    {R : K24RegulatorFamily}
    {P : K24RegulatedMeasureProblem R}
    {C : K23ConstructiveYM4Data F}
    (B : K24MeasureToK23Bridge R P C)
    (he : P.existsOnAdmissible)
    (hg : P.gaugeInvariantSector)
    (hr : P.reflectionPositiveOnAdmissible)
    (hc : P.cutoffTightness)
    (hv : P.volumeTightness) :
    C.regulatedMeasuresExist ∧
    C.gaugeInvariantObservablesDefined ∧
    C.reflectionPositivityUniform ∧
    C.schwingerFunctionsConverge :=
  ⟨B.existenceFeeds he,
   B.gaugeSectorFeeds hg,
   B.reflectionFeeds hr,
   B.tightnessFeedsConvergence hc hv⟩

theorem k24_target_still_open :
    k6_dependency.target.status = .openBridge := k23_target_still_open

theorem k24_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k23_no_promotion

end MCore
