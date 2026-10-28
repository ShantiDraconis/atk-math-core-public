import Mathlib
import MCore.Research.UserProgram.FlowSemantics

namespace MCore.Research.UserProgram

structure I3KernelCertificate : Prop where
  stateCycle : RotationGlobalLaw
  vectorCycle : ∀ x : I3Vector, x.rotate.rotate.rotate = x
  vectorSumInvariant : ∀ x : I3Vector, x.rotate.sum = x.sum
  sevenOperators : SevenOperatorLaw
  crossOperators : CrossOperatorLaw
  globalFlow : GlobalFlowLaw

def i3KernelCertificate : I3KernelCertificate where
  stateCycle := rotationGlobalInhabitant.sound
  vectorCycle := I3VectorRotationInhabitant.sound
  vectorSumInvariant := I3VectorSumInvariantInhabitant.sound
  sevenOperators := sevenOperatorInhabitant.sound
  crossOperators := crossOperatorInhabitant.sound
  globalFlow := globalFlowInhabitant.sound

def I3KernelInhabitant : Inhabitant I3KernelCertificate :=
  ⟨i3KernelCertificate⟩

theorem I3KernelInhabitant_sound : I3KernelCertificate :=
  I3KernelInhabitant.sound

inductive ProofLayer
  | arithmetic
  | algebra
  | semantics
  | operators
  | flow
  | inhabitant
  deriving DecidableEq, Repr

structure ProvenanceEntry where
  layer : ProofLayer
  theoremName : String
  dependsOn : List String

def i3Provenance : List ProvenanceEntry :=
  [ ⟨.semantics, "rotationGlobalInhabitant", ["I3State.next_three"]⟩
  , ⟨.algebra, "I3VectorRotationInhabitant", ["I3Vector.rotate_three"]⟩
  , ⟨.arithmetic, "I3VectorSumInvariantInhabitant", ["I3Vector.sum_rotate"]⟩
  , ⟨.operators, "sevenOperatorInhabitant",
      ["opT_three", "opT_opS", "opS_opT", "opGamma_fixed",
       "opC_fixed", "opC_idempotent", "opQ_rotate"]⟩
  , ⟨.operators, "crossOperatorInhabitant",
      ["opGamma_eq_three_C", "opC_delta_zero", "opDelta_C_zero",
       "delta_cycle_telescopes", "oscillatoryPart_sum_zero",
       "reconstruct_C_osc", "opC_oscillatory_zero"]⟩
  , ⟨.flow, "globalFlowInhabitant", ["flowCertificate"]⟩
  , ⟨.inhabitant, "I3KernelInhabitant",
      ["rotationGlobalInhabitant", "I3VectorRotationInhabitant",
       "I3VectorSumInvariantInhabitant", "sevenOperatorInhabitant",
       "crossOperatorInhabitant", "globalFlowInhabitant"]⟩
  ]

theorem i3Provenance_nonempty : i3Provenance ≠ [] := by
  decide

def ExternalMaterialBridge (Endpoint : Prop) : Prop :=
  I3KernelCertificate → Endpoint

def ExternalMaterialInhabitant (Endpoint : Prop)
    (bridge : ExternalMaterialBridge Endpoint) : Inhabitant Endpoint :=
  ⟨bridge i3KernelCertificate⟩

end MCore.Research.UserProgram
