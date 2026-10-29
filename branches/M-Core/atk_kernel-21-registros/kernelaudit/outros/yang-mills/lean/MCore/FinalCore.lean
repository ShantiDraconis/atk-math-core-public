import MCore.K30

namespace MCore

/-- Minimal scientific frontier extracted from the certified K0--K30 audit.
    These are obligations, not assertions that four-dimensional Yang--Mills
    already satisfies them. -/
structure FinalScientificFrontier
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) where
  /-- Constructive continuum YM4, OS reconstruction and physical Hilbert
      realization, represented by the already audited construction block. -/
  construction : K22ConstructionBlock F
  /-- Infrared block contains uniform clustering, observable cyclicity and the
      semigroup/spectral transfer obligations exposed by K20/K22. -/
  infrared : K22InfraredBlock F
  /-- Limit block prevents a cutoff- or finite-volume gap from being promoted
      to the continuum target. -/
  limits : K22LimitBlock F
  /-- The final spectral witness is kept explicit.  Supplying this field is
      scientific content; FinalCore does not manufacture it. -/
  spectral : K29SpectralGapRealization D H G

/-- The three audited frontier blocks recover the complete K20 frontier. -/
theorem final_frontier_blocks_close_k20
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (W : FinalScientificFrontier F D H G) :
    K20FrontierClosed F :=
  k28_blocks_recover_frontier {
    construction := W.construction
    infrared := W.infrared
    limits := W.limits
  }

/-- Once a genuine spectral realization exists, the K14 mass-gap predicate is
    immediate.  This is the compressed endpoint theorem, not a YM4 witness. -/
theorem final_spectral_realization_implies_mass_gap
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (R : K29SpectralGapRealization D H G) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  ⟨R.gap, k29_realization_is_mass_gap R⟩

/-- Dense final composition: all historical wrappers are removed from the
    operational proof path. -/
theorem final_core_closes_conditional_chain
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (W : FinalScientificFrontier F D H G) :
    K20FrontierClosed F ∧ ∃ gap : D.Scale, K14MassGap D H G gap :=
  ⟨final_frontier_blocks_close_k20 W,
   final_spectral_realization_implies_mass_gap W.spectral⟩

/-- Firewall: compression does not change the epistemic status of the original
    Millennium target. -/
theorem final_core_target_still_open :
    k6_dependency.target.status = .openBridge :=
  k30_target_still_open

theorem final_core_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k30_no_promotion

end MCore
