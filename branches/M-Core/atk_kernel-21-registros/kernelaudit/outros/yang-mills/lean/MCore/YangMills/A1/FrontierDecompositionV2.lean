import MCore.YangMills.A1.PhantomBridgeTriviality
import MCore.K30

namespace MCore.YangMills.A1

/-!
A1 frontier audit, version 2.

This does not change any frozen K-chain.  It records the result of the
adversarial tests:

* B3 `ReflectionPositivityData C` is not a concrete reconstruction boundary:
  it is universally inhabitable because `C` is a phantom parameter.
* B4 `PositiveTransferData C` is likewise universally inhabitable.
* B5 `UniformRegulatorControl C` is universally inhabitable by estimate = 0.

Therefore those three interfaces cannot be counted as scientific Yang--Mills
closure.  The remaining physical frontier is redirected to the already
fail-closed K20/K30 route, whose witness requires an actual positive gap and
the four spectral-transfer obligations.

No Millennium-problem claim is promoted here.
-/

inductive BridgeStatusV2 where
  | externalReference (reference : String)
  | interfaceInvalidated (reason : String)
  | blockingOpen (target : String)
  deriving DecidableEq, Repr

structure SubBridgeV2 where
  name : String
  legacyField : String
  status : BridgeStatusV2
  note : String
  deriving DecidableEq, Repr

def a1DecompositionV2 : List SubBridgeV2 :=
  [ { name := "B1"
      legacyField := "MeasureInvariance"
      status := .externalReference
        "Concrete compact-gauge lattice measure invariance must be instantiated, not merely cited."
      note := "The type references C.GaugeAction and C.fiber.measure, so it is not invalidated by the phantom-parameter attack." }
  , { name := "B2"
      legacyField := "ObservableInvariance"
      status := .externalReference
        "Concrete Wilson/plaquette observable invariance must be instantiated."
      note := "The type references C.observable and C.GaugeAction." }
  , { name := "B3"
      legacyField := "ReflectionPositivityData"
      status := .interfaceInvalidated
        "C is phantom; a Unit test space with zero pairing inhabits the type for every construction."
      note := "See reflection_positivity_data_inhabited_for_every_construction." }
  , { name := "B4"
      legacyField := "PositiveTransferData"
      status := .interfaceInvalidated
        "C is phantom; an unrelated Hilbert space with zero transfer operator inhabits the type for every construction."
      note := "See positive_transfer_data_inhabited_for_every_construction." }
  , { name := "B5"
      legacyField := "UniformRegulatorControl"
      status := .interfaceInvalidated
        "The auxiliary estimate may be identically zero and need not encode a positive physical gap."
      note := "See uniform_regulator_control_inhabited_for_every_construction." }
  , { name := "B6"
      legacyField := "K20/K30 concrete physical realization"
      status := .blockingOpen
        "Instantiate the concrete 4D Yang--Mills construction, physical Hilbert/Hamiltonian data, and K30SpectralTransferWitness with uniform limit control."
      note := "This is the fail-closed scientific frontier; K30 itself does not manufacture the witness." }
  ]

theorem a1_v2_has_six_nodes : a1DecompositionV2.length = 6 := by
  rfl

theorem a1_v2_invalidates_exactly_three_legacy_interfaces :
    (a1DecompositionV2.filter (fun b =>
      match b.status with
      | .interfaceInvalidated _ => true
      | _ => false)).length = 3 := by
  decide

theorem a1_v2_has_exactly_one_blocking_node :
    (a1DecompositionV2.filter (fun b =>
      match b.status with
      | .blockingOpen _ => true
      | _ => false)).length = 1 := by
  decide

theorem a1_v2_blocking_node_is_k20_k30 :
    ∀ b ∈ a1DecompositionV2,
      (match b.status with | .blockingOpen _ => true | _ => false) = true →
      b.name = "B6" := by
  decide

/-- The old A1 endpoint cannot be used as a proxy for B6: by the certified
triviality reductions it carries no B3/B4/B5 physical content beyond B1+B2. -/
theorem legacy_a1_endpoint_reduces_to_B1_B2
    (C : RegulatedYM4Construction) :
    A1ScientificOpenBridge C ↔
      (MeasureInvariance C ∧ ObservableInvariance C) :=
  a1_scientific_open_bridge_iff_B1_B2 C

end MCore.YangMills.A1
