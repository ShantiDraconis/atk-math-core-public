import MCore.K13

namespace MCore

/-- K14.0: abstract physical Hilbert-layer interface. The scalar/analytic
    realization is intentionally not fabricated in this dependency-light core. -/
structure K14PhysicalHilbertData where
  State : Type
  Scale : Type
  vacuum : State
  zeroState : State
  physical : State → Prop
  orthogonalToVacuum : State → Prop
  norm : State → Scale
  unitNorm : Scale
  vacuum_normalized : norm vacuum = unitNorm

/-- K14.1: an unbounded Hamiltonian has an explicit domain and an action on
    domain elements. Dense definition, symmetry and self-adjointness remain
    realization obligations rather than global axioms. -/
structure K14HamiltonianOperator (D : K14PhysicalHilbertData) where
  domain : D.State → Prop
  act : (psi : D.State) → domain psi → D.State
  denselyDefined : Prop
  symmetric : Prop
  selfAdjoint : Prop

/-- K14.2: vacuum data are explicit. H Omega = 0 is represented by equality
    with the distinguished zero state, not with Omega itself. -/
structure K14VacuumAxiom (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D) where
  vacuum_mem_domain : H.domain D.vacuum
  vacuum_zero : H.act D.vacuum vacuum_mem_domain = D.zeroState
  vacuum_isolated_in_physical_kernel : Prop

/-- Ordered/metric content needed to state a quantitative gap is supplied by a
    concrete analytic realization. This keeps the core dependency-light. -/
structure K14GapScale (D : K14PhysicalHilbertData) where
  positive : D.Scale → Prop
  gapBound : D.Scale → D.State → D.State → Prop

/-- K14.3: mass gap is a predicate only; it asserts no witness. -/
def K14MassGap (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D) (S : K14GapScale D)
    (delta : D.Scale) : Prop :=
  S.positive delta ∧
    ∀ (psi : D.State) (hpsi : H.domain psi),
      D.physical psi → D.orthogonalToVacuum psi →
        S.gapBound delta psi (H.act psi hpsi)

/-- K14.4: semigroup decay remains a separately typed spectral predicate. -/
structure K14SemigroupDecayData where
  Rate : Type
  positive : Rate → Prop
  decayAtRate : Rate → Prop

def K14SemigroupDecay (S : K14SemigroupDecayData) : Prop :=
  ∃ m : S.Rate, S.positive m ∧ S.decayAtRate m

/-- K14.5: explicit data for the scientific clustering frontier. -/
structure K14UniformExpClusteringData where
  Cutoff : Type
  Volume : Type
  LocalObservable : Type
  Rate : Type
  positive : Rate → Prop
  uniformDecayBound : Rate → Cutoff → Volume → LocalObservable → Prop

/-- Uniformity in both cutoff and volume is part of the proposition. No YM4
    witness is supplied anywhere by K14. -/
def K14UniformExpClustering (C : K14UniformExpClusteringData) : Prop :=
  ∃ m : C.Rate, C.positive m ∧
    ∀ (a : C.Cutoff) (volume : C.Volume) (O : C.LocalObservable),
      C.uniformDecayBound m a volume O

/-- K14.5b: reconstruction/cyclicity is explicit rather than hidden inside a
    transfer-matrix slogan. -/
def K14ReconstructionCyclicityBridge
    (C : K14UniformExpClusteringData)
    (S : K14SemigroupDecayData) : Prop :=
  K14UniformExpClustering C → K14SemigroupDecay S

/-- K14.6: the scientific conclusion is conditional on an explicit bridge. -/
def K14ClusteringToMassGapBridge
    (C : K14UniformExpClusteringData)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (S : K14GapScale D) : Prop :=
  K14UniformExpClustering C → ∃ delta : D.Scale, K14MassGap D H S delta

/-- Pure modus ponens: this theorem contains no proof of YM4 clustering. -/
theorem k14_conditional_mass_gap
    {C : K14UniformExpClusteringData}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {S : K14GapScale D}
    (bridge : K14ClusteringToMassGapBridge C D H S)
    (clustering : K14UniformExpClustering C) :
    ∃ delta : D.Scale, K14MassGap D H S delta :=
  bridge clustering

theorem k14_target_still_open :
    k6_dependency.target.status = .openBridge :=
  k13_target_still_open

theorem k14_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k13_no_promotion

end MCore
