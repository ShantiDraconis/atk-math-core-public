import MCore.YangMills.A1.FrontierDecompositionV2
import MCore.K30

namespace MCore.YangMills.A1

/-!
B6.0 -- concrete A1 -> K20/K30 adapter boundary.

The previous A1 layer had no typed map from its regulated states/observables to
the K14 physical Hilbert layer.  Without such a map, a K20/K30 witness could
describe an unrelated abstract model.

This structure records the minimum coupling needed before the already-certified
K30 conditional chain is scientifically relevant to the A1 construction.

No inhabitant is provided here.
-/

structure B60ConcretePhysicalAdapter
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) where

  /-- Regulated states are mapped into the claimed physical state space. -/
  stateMap :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume),
      (C.fiber a V).State → D.State

  /-- Gauge-invariant observables have an associated physical state. -/
  observableState :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume),
      C.Signature.Observable → D.State

  /-- Admissible regulated states used by the reconstruction land in the
      physical sector. -/
  mappedStatesPhysical :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume)
      (ψ : (C.fiber a V).State),
      C.admissible a V → D.physical (stateMap a V ψ)

  /-- Observable-generated states used downstream are physical. -/
  observableStatesPhysical :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume)
      (A : C.Signature.Observable),
      C.admissible a V → D.physical (observableState a V A)

  /-- The abstract K20 construction block must be realized by this concrete A1
      construction, not by an unrelated model. -/
  constructionBlock : K22ConstructionBlock F
  constructionFromA1 :
    MeasureInvariance C →
    ObservableInvariance C →
    F.constructiveYM4 ∧
      F.reflectionPositiveReconstruction ∧
      F.physicalHilbertRealization

  /-- The long-distance and regulator-removal blocks remain explicit data. -/
  infraredBlock : K22InfraredBlock F
  limitBlock : K22LimitBlock F

  /-- Non-vacuity firewall: the claimed physical sector has an actual
      non-vacuum excitation in the Hamiltonian domain. -/
  excitation : D.State
  excitationInDomain : H.domain excitation
  excitationPhysical : D.physical excitation
  excitationOrthogonalVacuum : D.orthogonalToVacuum excitation

  /-- The K30 obligations used for the final exclusion are witnessed. -/
  transferWitness : K30SpectralTransferWitness O

def B60ConcretePhysicalOpenBridge
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) : Prop :=
  Nonempty (B60ConcretePhysicalAdapter C F D H G O)

/-- Mechanical composition only: once B6.0 is genuinely inhabited, the
existing K28/K30 chain yields its already-typed mass-gap predicate.  This
theorem does not construct B6.0. -/
theorem b60_adapter_closes_conditional_chain
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (A : B60ConcretePhysicalAdapter C F D H G O) :
    ∃ gap : D.Scale, K14MassGap D H G gap := by
  let blocks : K28FrontierBlocks F := {
    construction := A.constructionBlock
    infrared := A.infraredBlock
    limits := A.limitBlock
  }
  exact k30_witness_closes_conditional_chain blocks O A.transferWitness

/-- Fail-closed diagnostic: A1's legacy endpoint is not an inhabitant of B6.0.
There is intentionally no constructor from `A1ScientificOpenBridge C` to this
type. -/
def B60LegacyEndpointInsufficient
    (C : RegulatedYM4Construction) : Prop :=
  ∀ (h : A1ScientificOpenBridge C),
    MeasureInvariance C ∧ ObservableInvariance C

theorem b60_legacy_endpoint_contains_only_B1_B2
    (C : RegulatedYM4Construction) :
    B60LegacyEndpointInsufficient C := by
  intro h
  exact (a1_scientific_open_bridge_iff_B1_B2 C).mp h

end MCore.YangMills.A1
