import MCore.K29

namespace MCore

/-- Forward correction of the K25 clustering interface.  The prefactor and the
mass scale are distinct inputs of the exponential-control predicate. -/
structure K30ClusteringSystemV2 where
  Cutoff : Type
  Volume : Type
  Observable : Type
  Point : Type
  Bound : Type
  MassScale : Type
  Distance : Type
  connectedCorrelation :
    Cutoff → Volume → Observable → Observable → Point → Point → Bound
  separation : Point → Point → Distance
  exponentiallyControlled : Bound → Bound → MassScale → Distance → Prop

structure K30UniformExponentialClusteringV2 (S : K30ClusteringSystemV2) where
  prefactor : S.Bound
  massScale : S.MassScale
  holds : ∀ a V A B x y,
    S.exponentiallyControlled
      (S.connectedCorrelation a V A B x y)
      prefactor massScale (S.separation x y)

structure K30PointwiseClusteringV2 (S : K30ClusteringSystemV2) where
  prefactorAt : S.Cutoff → S.Volume → S.Bound
  massScaleAt : S.Cutoff → S.Volume → S.MassScale
  holds : ∀ a V A B x y,
    S.exponentiallyControlled
      (S.connectedCorrelation a V A B x y)
      (prefactorAt a V) (massScaleAt a V) (S.separation x y)

/-- Constructor, not a theorem: the codomain is clustering witness data in Type. -/
def k30_uniform_clustering_implies_pointwise
    {S : K30ClusteringSystemV2}
    (U : K30UniformExponentialClusteringV2 S) :
    K30PointwiseClusteringV2 S := {
  prefactorAt := fun _ _ => U.prefactor
  massScaleAt := fun _ _ => U.massScale
  holds := by
    intro a V A B x y
    exact U.holds a V A B x y
}

/-- K30 separates the remaining scientific transfer into four independently
inspectable obligations. None is derived merely from frontier closure. -/
structure K30SpectralTransferObligations
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) where
  gap : D.Scale
  positiveGap : G.positive gap
  physicalSectorControlled : Prop
  observableStatesDense : Prop
  clusteringTransfersToSemigroup : Prop
  semigroupExcludesLowSpectrum : Prop
  exclusionFromObligations :
    K20FrontierClosed F →
    physicalSectorControlled →
    observableStatesDense →
    clusteringTransfersToSemigroup →
    semigroupExcludesLowSpectrum →
    ∀ (psi : D.State) (hpsi : H.domain psi),
      D.physical psi → D.orthogonalToVacuum psi →
        G.gapBound gap psi (H.act psi hpsi)

structure K30SpectralTransferWitness
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (O : K30SpectralTransferObligations F D H G) where
  physicalSector : O.physicalSectorControlled
  density : O.observableStatesDense
  clusteringToSemigroup : O.clusteringTransfersToSemigroup
  spectralExclusion : O.semigroupExcludesLowSpectrum

/-- Constructor, not a theorem: its codomain is data in `Type`, not `Prop`. -/
def k30_obligations_build_realization
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (O : K30SpectralTransferObligations F D H G)
    (W : K30SpectralTransferWitness O)
    (hF : K20FrontierClosed F) : K29SpectralGapRealization D H G := {
  gap := O.gap
  gapPositive := O.positiveGap
  excludesLowSpectrum := fun psi hpsi hphysical horthogonal =>
    O.exclusionFromObligations hF W.physicalSector W.density
      W.clusteringToSemigroup W.spectralExclusion psi hpsi hphysical horthogonal
}

/-- Constructor for the remaining transfer interface. -/
def k30_witness_builds_transfer
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (O : K30SpectralTransferObligations F D H G)
    (W : K30SpectralTransferWitness O) :
    K29FrontierToSpectralRealization F D H G := {
  transfer := fun hF => k30_obligations_build_realization O W hF
}

/-- Once the explicit K30 witness exists, the already-certified K29 chain
propagates all the way to the mass-gap predicate; no K31 wrapper is needed. -/
theorem k30_witness_closes_conditional_chain
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (B : K28FrontierBlocks F)
    (O : K30SpectralTransferObligations F D H G)
    (W : K30SpectralTransferWitness O) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  k29_blocks_and_transfer_yield_mass_gap B (k30_witness_builds_transfer O W)

theorem k30_target_still_open :
    k6_dependency.target.status = .openBridge := k29_target_still_open

theorem k30_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k29_no_promotion

end MCore
