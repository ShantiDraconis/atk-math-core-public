import MCore.K16

namespace MCore

structure K17ObservableSectorData where
  State : Type
  Observable : Type
  vacuum : State
  generatedState : Observable → State
  physical : State → Prop
  orthogonalToVacuum : State → Prop
  cyclicGeneratedSector : Prop

structure K17MatrixElementDecayData where
  Observable : Type
  Rate : Type
  positive : Rate → Prop
  matrixElementDecay : Rate → Observable → Observable → Prop

def K17MatrixElementDecay (M : K17MatrixElementDecayData) : Prop :=
  ∃ m : M.Rate, M.positive m ∧
    ∀ O₁ O₂ : M.Observable, M.matrixElementDecay m O₁ O₂

def K17ClusteringToMatrixElementsBridge
    (C : K14UniformExpClusteringData)
    (M : K17MatrixElementDecayData) : Prop :=
  K14UniformExpClustering C → K17MatrixElementDecay M

def K17ReconstructionCyclicityBridge
    (O : K17ObservableSectorData)
    (M : K17MatrixElementDecayData)
    (S : K14SemigroupDecayData) : Prop :=
  O.cyclicGeneratedSector → K17MatrixElementDecay M → K14SemigroupDecay S

theorem k17_clustering_and_cyclicity_imply_semigroup_decay
    {C : K14UniformExpClusteringData}
    {O : K17ObservableSectorData}
    {M : K17MatrixElementDecayData}
    {S : K14SemigroupDecayData}
    (toMatrix : K17ClusteringToMatrixElementsBridge C M)
    (reconstruct : K17ReconstructionCyclicityBridge O M S)
    (clustering : K14UniformExpClustering C)
    (cyclic : O.cyclicGeneratedSector) :
    K14SemigroupDecay S :=
  reconstruct cyclic (toMatrix clustering)

theorem k17_target_still_open :
    k6_dependency.target.status = .openBridge :=
  k16_target_still_open

theorem k17_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k16_no_promotion

end MCore
