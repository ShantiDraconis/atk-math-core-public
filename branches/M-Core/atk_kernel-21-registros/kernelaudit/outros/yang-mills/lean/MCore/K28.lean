import MCore.K27

namespace MCore

/-- K28 assembles the three independently audited scientific blocks without
turning their existence into a proof of the open Yang--Mills target. -/
structure K28FrontierBlocks (F : K20ScientificFrontier) where
  construction : K22ConstructionBlock F
  infrared : K22InfraredBlock F
  limits : K22LimitBlock F

theorem k28_blocks_recover_frontier
    {F : K20ScientificFrontier}
    (B : K28FrontierBlocks F) : K20FrontierClosed F := by
  rcases B.construction with ⟨hc, hr, hh⟩
  rcases B.infrared with ⟨hcl, hcyc, hsg⟩
  rcases B.limits with ⟨hug, hcont, htherm, hpres⟩
  exact ⟨hc, hr, hh, hcl, hcyc, hsg, hug, hcont, htherm, hpres⟩

/-- The endpoint remains conditional on the physical Hilbert realization and an
explicit K20 bridge.  K28 does not manufacture either one. -/
theorem k28_conditional_mass_gap
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (B : K28FrontierBlocks F)
    (bridge : K20FrontierToMassGapBridge F D H G) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  bridge (k28_blocks_recover_frontier B)

theorem k28_target_still_open :
    k6_dependency.target.status = .openBridge := k27_target_still_open

theorem k28_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k27_no_promotion

end MCore
