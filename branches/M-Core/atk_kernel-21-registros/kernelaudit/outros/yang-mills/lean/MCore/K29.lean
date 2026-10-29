import MCore.K28

namespace MCore

/-- K29 decomposes the final K20 bridge into an explicit spectral exclusion
statement.  The scientific content is supplied as data; no gap is inferred from
frontier closure alone. -/
structure K29SpectralGapRealization
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) where
  gap : D.Scale
  gapPositive : G.positive gap
  excludesLowSpectrum :
    ∀ (psi : D.State) (hpsi : H.domain psi),
      D.physical psi → D.orthogonalToVacuum psi →
        G.gapBound gap psi (H.act psi hpsi)

theorem k29_realization_is_mass_gap
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (R : K29SpectralGapRealization D H G) : K14MassGap D H G R.gap :=
  ⟨R.gapPositive, R.excludesLowSpectrum⟩

/-- This is the remaining scientific transfer interface: frontier closure must
produce an actual spectral-gap realization in the chosen physical sector. -/
structure K29FrontierToSpectralRealization
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) where
  transfer : K20FrontierClosed F → K29SpectralGapRealization D H G

theorem k29_transfer_builds_k20_bridge
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (T : K29FrontierToSpectralRealization F D H G) :
    K20FrontierToMassGapBridge F D H G := by
  intro hF
  let R := T.transfer hF
  exact ⟨R.gap, k29_realization_is_mass_gap R⟩

theorem k29_blocks_and_transfer_yield_mass_gap
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (B : K28FrontierBlocks F)
    (T : K29FrontierToSpectralRealization F D H G) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  k28_conditional_mass_gap B (k29_transfer_builds_k20_bridge T)

theorem k29_target_still_open :
    k6_dependency.target.status = .openBridge := k28_target_still_open

theorem k29_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k28_no_promotion

end MCore
