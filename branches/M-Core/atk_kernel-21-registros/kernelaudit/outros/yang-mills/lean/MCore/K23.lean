import MCore.K22

namespace MCore

/-- K23 refines only the construction/reconstruction block.  The fields are
scientific obligations; no actual four-dimensional Yang–Mills model is
constructed by this declaration. -/
structure K23ConstructiveYM4Data (F : K20ScientificFrontier) where
  regulatedMeasuresExist : Prop
  gaugeInvariantObservablesDefined : Prop
  reflectionPositivityUniform : Prop
  schwingerFunctionsConverge : Prop
  osReconstructionApplies : Prop
  realizesConstructiveYM4 :
    regulatedMeasuresExist →
    gaugeInvariantObservablesDefined →
    reflectionPositivityUniform →
    schwingerFunctionsConverge →
    osReconstructionApplies →
    F.constructiveYM4 ∧
      F.reflectionPositiveReconstruction ∧
      F.physicalHilbertRealization

/-- All five constructive inputs are kept explicit so that merely assuming a
continuum limit cannot be mistaken for a reconstruction theorem. -/
def K23ConstructionInputsHold
    {F : K20ScientificFrontier} (C : K23ConstructiveYM4Data F) : Prop :=
  C.regulatedMeasuresExist ∧
  C.gaugeInvariantObservablesDefined ∧
  C.reflectionPositivityUniform ∧
  C.schwingerFunctionsConverge ∧
  C.osReconstructionApplies

theorem k23_inputs_build_construction_block
    {F : K20ScientificFrontier}
    (C : K23ConstructiveYM4Data F)
    (h : K23ConstructionInputsHold C) : K22ConstructionBlock F := by
  rcases h with ⟨hm, ho, hrp, hs, hos⟩
  rcases C.realizesConstructiveYM4 hm ho hrp hs hos with ⟨hy, hr, hh⟩
  exact {
    constructiveYM4 := hy
    reflectionPositiveReconstruction := hr
    physicalHilbertRealization := hh
  }

theorem k23_target_still_open :
    k6_dependency.target.status = .openBridge := k22_target_still_open

theorem k23_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k22_no_promotion

end MCore
