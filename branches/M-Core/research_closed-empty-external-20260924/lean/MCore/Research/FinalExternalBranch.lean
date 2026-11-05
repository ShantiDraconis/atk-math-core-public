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
  { mode := .closedEmpty
    sourceAnchor := "CLOSED_EMPTY_0_OF_0"
    endpoint := "FinalExternalGap"
    producerCount := 0
    requiredProducers := 0
    finalRoot := none
    issued := false }

theorem closed_empty_shape :
    branchState.producerCount = 0 ∧
    branchState.requiredProducers = 0 := by
  decide

theorem endpoint_does_not_issue :
    branchState.finalRoot = none ∧ branchState.issued = false := by
  decide

end MCore.Research
