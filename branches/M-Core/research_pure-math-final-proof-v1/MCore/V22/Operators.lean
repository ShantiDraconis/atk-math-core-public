import MCore.V22.ProofDebt

namespace MCore.V22

inductive OperatorKind where
  | implication
  | equivalence
  | reduction
  | witnessConstruction
  | obstruction
  | transport
  | normalization
  | refutation
  | closure
  deriving DecidableEq, Repr

structure OperatorShape where
  name : String
  kind : OperatorKind
  source : Node
  target : Node
  sourceType : String
  targetType : String
  closureSite : MCore.V21.ClosureSite
  deriving Repr

structure CertifiedOperator (P Q : Prop) where
  shape : OperatorShape
  run : P → Q

structure ConditionalOperator (Hyp P Q : Prop) where
  shape : OperatorShape
  run : Hyp → P → Q

end MCore.V22
