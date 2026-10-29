import MCore.K20

namespace MCore

/-- K21 turns the K20 frontier inventory into independently addressable
scientific obligations.  It does not provide witnesses for any obligation. -/
structure K21FrontierWitnesses (F : K20ScientificFrontier) where
  constructiveYM4 : F.constructiveYM4
  reflectionPositiveReconstruction : F.reflectionPositiveReconstruction
  physicalHilbertRealization : F.physicalHilbertRealization
  uniformExponentialClustering : F.uniformExponentialClustering
  observableCyclicity : F.observableCyclicity
  semigroupSpectralTransfer : F.semigroupSpectralTransfer
  uniformRegulatedGap : F.uniformRegulatedGap
  continuumLimitControl : F.continuumLimitControl
  thermodynamicLimitControl : F.thermodynamicLimitControl
  gapPreservedUnderLimits : F.gapPreservedUnderLimits

theorem k21_witnesses_close_frontier
    {F : K20ScientificFrontier}
    (W : K21FrontierWitnesses F) : K20FrontierClosed F :=
  ⟨W.constructiveYM4,
   W.reflectionPositiveReconstruction,
   W.physicalHilbertRealization,
   W.uniformExponentialClustering,
   W.observableCyclicity,
   W.semigroupSpectralTransfer,
   W.uniformRegulatedGap,
   W.continuumLimitControl,
   W.thermodynamicLimitControl,
   W.gapPreservedUnderLimits⟩

/-- The full witness package remains only a sufficient typed input to the
existing conditional endpoint. -/
theorem k21_witnesses_imply_mass_gap_conditionally
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (bridge : K20FrontierToMassGapBridge F D H G)
    (W : K21FrontierWitnesses F) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  k20_closed_frontier_implies_mass_gap bridge (k21_witnesses_close_frontier W)

theorem k21_target_still_open :
    k6_dependency.target.status = .openBridge := k20_target_still_open

theorem k21_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k20_no_promotion

end MCore
