import MCore.V22.Matrix

namespace MCore.V22

inductive Prover where
  | lean
  | coq
  | isabelle
  | agda
  deriving DecidableEq, Repr

inductive DebtKind where
  | sorryDebt
  | admitDebt
  | axiom
  | placeholder
  | unresolvedGoal
  | externalDependency
  | missingWitness
  | quantifierMismatch
  | scalingMismatch
  | constantMismatch
  deriving DecidableEq, Repr

inductive DebtStage where
  | raw
  | reviewed
  | blocking
  | discharged
  deriving DecidableEq, Repr

structure ProofDebt where
  node : Node
  prover : Prover
  sourcePath : String
  sourceRevision : String
  line : Nat
  kind : DebtKind
  stage : DebtStage
  expectedType : String
  dependencySummary : String
  closureSite : MCore.V21.ClosureSite
  deriving Repr

def ProofDebt.IsBlocking (d : ProofDebt) : Prop :=
  d.stage = .blocking

end MCore.V22
