import MCore.K25

namespace MCore

/-- K26 makes the observable-sector gap explicit. Decay known only on selected
observable-generated states is not silently identified with a full physical
spectral gap. -/
structure K26ObservableSector where
  State : Type
  Observable : Type
  vacuum : State
  generatedState : Observable → State
  Physical : State → Prop
  InObservableClosure : State → Prop

structure K26CyclicityWitness (O : K26ObservableSector) where
  generatedPhysical : ∀ A, O.Physical (O.generatedState A)
  vacuumPhysical : O.Physical O.vacuum
  closureCoversPhysical : ∀ ψ, O.Physical ψ → O.InObservableClosure ψ

/-- Matrix-element decay is kept as its own predicate and is not definitionally
a spectral-gap statement. -/
structure K26SemigroupDecaySystem (O : K26ObservableSector) where
  Time : Type
  Bound : Type
  matrixElementDecay : O.State → O.State → Time → Bound → Prop
  spectralSupportAboveGap : O.State → Bound → Prop

structure K26ObservableDecayWitness
    (O : K26ObservableSector) (S : K26SemigroupDecaySystem O) where
  gapScale : S.Bound
  onGeneratedStates : ∀ A B t,
    S.matrixElementDecay (O.generatedState A) (O.generatedState B) t gapScale

/-- This is the nontrivial transfer obligation: density/cyclicity plus suitable
analytic control must extend observable matrix-element information to the
physical sector. It is data, not a theorem manufactured by K26. -/
structure K26DecayToSpectralBridge
    (O : K26ObservableSector)
    (S : K26SemigroupDecaySystem O)
    (C : K26CyclicityWitness O)
    (D : K26ObservableDecayWitness O S) where
  transfer : ∀ ψ, O.Physical ψ → S.spectralSupportAboveGap ψ D.gapScale

structure K26ToFrontierBridge
    (F : K20ScientificFrontier)
    (O : K26ObservableSector)
    (S : K26SemigroupDecaySystem O)
    (C : K26CyclicityWitness O)
    (D : K26ObservableDecayWitness O S)
    (T : K26DecayToSpectralBridge O S C D) where
  cyclicityFeeds : F.observableCyclicity
  spectralTransferFeeds : F.semigroupSpectralTransfer

theorem k26_bridge_supplies_infrared_auxiliaries
    {F : K20ScientificFrontier}
    {O : K26ObservableSector}
    {S : K26SemigroupDecaySystem O}
    {C : K26CyclicityWitness O}
    {D : K26ObservableDecayWitness O S}
    {T : K26DecayToSpectralBridge O S C D}
    (B : K26ToFrontierBridge F O S C D T) :
    F.observableCyclicity ∧ F.semigroupSpectralTransfer :=
  ⟨B.cyclicityFeeds, B.spectralTransferFeeds⟩

theorem k26_target_still_open :
    k6_dependency.target.status = .openBridge := k25_target_still_open

theorem k26_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k25_no_promotion

end MCore
