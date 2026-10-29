import MCore.K21

namespace MCore

/-- K22 isolates the constructive/reconstruction block from the K21 witness
inventory.  These are scientific obligations, not asserted facts about YM4. -/
structure K22ConstructionBlock (F : K20ScientificFrontier) where
  constructiveYM4 : F.constructiveYM4
  reflectionPositiveReconstruction : F.reflectionPositiveReconstruction
  physicalHilbertRealization : F.physicalHilbertRealization

/-- K22 separately isolates the long-distance block needed downstream. -/
structure K22InfraredBlock (F : K20ScientificFrontier) where
  uniformExponentialClustering : F.uniformExponentialClustering
  observableCyclicity : F.observableCyclicity
  semigroupSpectralTransfer : F.semigroupSpectralTransfer

/-- Regulator-removal obligations remain independent from construction and IR
control; this prevents a continuum-limit assumption from silently supplying a
uniform gap. -/
structure K22LimitBlock (F : K20ScientificFrontier) where
  uniformRegulatedGap : F.uniformRegulatedGap
  continuumLimitControl : F.continuumLimitControl
  thermodynamicLimitControl : F.thermodynamicLimitControl
  gapPreservedUnderLimits : F.gapPreservedUnderLimits

theorem k22_blocks_assemble_witnesses
    {F : K20ScientificFrontier}
    (C : K22ConstructionBlock F)
    (I : K22InfraredBlock F)
    (L : K22LimitBlock F) : K21FrontierWitnesses F := {
  constructiveYM4 := C.constructiveYM4
  reflectionPositiveReconstruction := C.reflectionPositiveReconstruction
  physicalHilbertRealization := C.physicalHilbertRealization
  uniformExponentialClustering := I.uniformExponentialClustering
  observableCyclicity := I.observableCyclicity
  semigroupSpectralTransfer := I.semigroupSpectralTransfer
  uniformRegulatedGap := L.uniformRegulatedGap
  continuumLimitControl := L.continuumLimitControl
  thermodynamicLimitControl := L.thermodynamicLimitControl
  gapPreservedUnderLimits := L.gapPreservedUnderLimits
}

theorem k22_blocks_imply_mass_gap_conditionally
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (bridge : K20FrontierToMassGapBridge F D H G)
    (C : K22ConstructionBlock F)
    (I : K22InfraredBlock F)
    (L : K22LimitBlock F) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  k21_witnesses_imply_mass_gap_conditionally bridge
    (k22_blocks_assemble_witnesses C I L)

theorem k22_target_still_open :
    k6_dependency.target.status = .openBridge := k21_target_still_open

theorem k22_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k21_no_promotion

end MCore
