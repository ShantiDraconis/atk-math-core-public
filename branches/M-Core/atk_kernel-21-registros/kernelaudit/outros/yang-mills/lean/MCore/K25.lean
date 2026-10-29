import MCore.K24

namespace MCore

structure K25ClusteringSystem where
  Cutoff : Type
  Volume : Type
  Observable : Type
  Bound : Type
  Distance : Type
  admissible : Cutoff → Volume → Prop
  connectedCorrelation : Cutoff → Volume → Observable → Observable → Bound
  separation : Observable → Observable → Distance
  exponentiallyControlled : Bound → Bound → Distance → Prop

structure K25UniformExponentialClustering (S : K25ClusteringSystem) where
  prefactor : S.Bound
  massScale : S.Bound
  holds : ∀ a V O₁ O₂,
    S.admissible a V →
    S.exponentiallyControlled
      (S.connectedCorrelation a V O₁ O₂)
      massScale
      (S.separation O₁ O₂)

structure K25PointwiseClustering (S : K25ClusteringSystem) where
  prefactorAt : S.Cutoff → S.Volume → S.Bound
  massScaleAt : S.Cutoff → S.Volume → S.Bound
  holdsAt : ∀ a V O₁ O₂,
    S.admissible a V →
    S.exponentiallyControlled
      (S.connectedCorrelation a V O₁ O₂)
      (massScaleAt a V)
      (S.separation O₁ O₂)

structure K25ClusteringToInfraredBridge
    (F : K20ScientificFrontier)
    (S : K25ClusteringSystem)
    (U : K25UniformExponentialClustering S) where
  clusteringFeeds : F.uniformExponentialClustering
  observableCyclicityStillRequired : Prop
  semigroupTransferStillRequired : Prop
  cyclicityFeeds : observableCyclicityStillRequired → F.observableCyclicity
  transferFeeds : semigroupTransferStillRequired → F.semigroupSpectralTransfer

theorem k25_uniform_clustering_builds_infrared_block
    {F : K20ScientificFrontier}
    {S : K25ClusteringSystem}
    {U : K25UniformExponentialClustering S}
    (B : K25ClusteringToInfraredBridge F S U)
    (hc : B.observableCyclicityStillRequired)
    (hs : B.semigroupTransferStillRequired) : K22InfraredBlock F := {
  uniformExponentialClustering := B.clusteringFeeds
  observableCyclicity := B.cyclicityFeeds hc
  semigroupSpectralTransfer := B.transferFeeds hs
}

theorem k25_target_still_open :
    k6_dependency.target.status = .openBridge := k24_target_still_open

theorem k25_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k24_no_promotion

end MCore
