import MCore.V22.Universe

namespace MCore.V22

inductive ProofState where
  | provedTrue
  | provedFalse
  | open
  | indeterminate
  deriving DecidableEq, Repr

inductive PairState where
  | bothClosed
  | mixed
  | bothOpen
  | indeterminateCollision
  deriving DecidableEq, Repr

def classifyPair : ProofState → ProofState → PairState
  | .indeterminate, _ => .indeterminateCollision
  | _, .indeterminate => .indeterminateCollision
  | .open, .open => .bothOpen
  | .open, .provedTrue => .mixed
  | .open, .provedFalse => .mixed
  | .provedTrue, .open => .mixed
  | .provedFalse, .open => .mixed
  | .provedTrue, .provedTrue => .bothClosed
  | .provedTrue, .provedFalse => .bothClosed
  | .provedFalse, .provedTrue => .bothClosed
  | .provedFalse, .provedFalse => .bothClosed

inductive Polarity where
  | trueCase
  | falseCase
  deriving DecidableEq, Repr

structure PairScenario where
  left : Polarity
  right : Polarity
  deriving DecidableEq, Repr

inductive ScenarioMode where
  | observed
  | counterfactual (scenario : PairScenario)
  deriving DecidableEq, Repr

end MCore.V22
