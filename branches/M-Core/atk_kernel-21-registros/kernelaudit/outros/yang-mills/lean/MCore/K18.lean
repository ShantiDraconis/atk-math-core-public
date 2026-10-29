import MCore.K17

namespace MCore

/-- Typed spectral-support interface.  The realization of this interface for the
physical Yang–Mills Hamiltonian is intentionally not asserted here. -/
structure K18SpectralSupportData (D : K14PhysicalHilbertData) where
  Scale : Type
  positive : Scale → Prop
  excludesOpenIntervalAboveVacuum : Scale → Prop

/-- Explicit bridge from semigroup decay to exclusion of low positive spectral
support.  This names the spectral-theoretic obligation instead of hiding it. -/
def K18SemigroupToSpectralBridge
    (S : K14SemigroupDecayData)
    (D : K14PhysicalHilbertData)
    (E : K18SpectralSupportData D) : Prop :=
  K14SemigroupDecay S → ∃ delta : E.Scale,
    E.positive delta ∧ E.excludesOpenIntervalAboveVacuum delta

/-- Explicit compatibility bridge between a spectral exclusion scale and the
mass-gap scale used by K14. -/
def K18SpectralToMassGapBridge
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (E : K18SpectralSupportData D) : Prop :=
  (∃ delta : E.Scale, E.positive delta ∧
      E.excludesOpenIntervalAboveVacuum delta) →
    ∃ gap : D.Scale, K14MassGap D H G gap

theorem k18_semigroup_decay_implies_mass_gap
    {S : K14SemigroupDecayData}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {E : K18SpectralSupportData D}
    (toSpectral : K18SemigroupToSpectralBridge S D E)
    (toGap : K18SpectralToMassGapBridge D H G E)
    (decay : K14SemigroupDecay S) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  toGap (toSpectral decay)

theorem k18_clustering_chain_implies_mass_gap
    {C : K14UniformExpClusteringData}
    {O : K17ObservableSectorData}
    {M : K17MatrixElementDecayData}
    {S : K14SemigroupDecayData}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {E : K18SpectralSupportData D}
    (toMatrix : K17ClusteringToMatrixElementsBridge C M)
    (reconstruct : K17ReconstructionCyclicityBridge O M S)
    (toSpectral : K18SemigroupToSpectralBridge S D E)
    (toGap : K18SpectralToMassGapBridge D H G E)
    (clustering : K14UniformExpClustering C)
    (cyclic : O.cyclicGeneratedSector) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  k18_semigroup_decay_implies_mass_gap toSpectral toGap
    (k17_clustering_and_cyclicity_imply_semigroup_decay
      toMatrix reconstruct clustering cyclic)

theorem k18_target_still_open :
    k6_dependency.target.status = .openBridge := k17_target_still_open

theorem k18_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k17_no_promotion

end MCore
