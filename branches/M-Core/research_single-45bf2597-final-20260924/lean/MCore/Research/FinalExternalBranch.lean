import MCore

namespace MCore.Research

inductive FinalExternalMode where
  | singleProducer
  | sevenCertificates
  | closedEmpty
  deriving DecidableEq, Repr

structure FinalExternalBranchState where
  mode : FinalExternalMode
  sourceAnchor : String
  endpoint : String
  producerCount : Nat
  requiredProducers : Nat
  finalRoot : Option String
  issued : Bool
  deriving Repr

def branchState : FinalExternalBranchState :=
  { mode := .singleProducer
    sourceAnchor := "45bf2597"
    endpoint := "FinalExternalGap"
    producerCount := 1
    requiredProducers := 1
    finalRoot := none
    issued := false }

theorem failClosed_until_root :
    branchState.finalRoot = none → branchState.issued = false := by
  intro _
  rfl

theorem producer_shape :
    branchState.producerCount = branchState.requiredProducers := by
  rfl

end MCore.Research
