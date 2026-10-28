namespace MCore.ATL.V3

inductive NodeKind where
  | area | claim | producer | lemma | bridge | gate | certificate | externalEndpoint | minedArtifact
  deriving DecidableEq, Repr

inductive Policy where
  | constructive | classicalOk
  deriving DecidableEq, Repr

inductive OpenClass where
  | none | attackable | research | external
  deriving DecidableEq, Repr

inductive PromotionLayer where
  | source | build | kernel | semantic | scientific
  deriving DecidableEq, Repr

structure PrimitiveNode where
  id : String
  area : String
  kind : NodeKind
  version : Nat
  formalStatement : String
  semanticStatement : String
  sourceFiles : List String
  theoremNames : List String
  repo : String
  branch : String
  commit : String
  policy : Policy
  statementHash : Option String
  supersededBy : Option String
  deriving Repr

inductive EdgeKind where
  | dependsOn | implies | produces | validates | supersedes | replaces | mines
  deriving DecidableEq, Repr

structure Edge where
  fromId : String
  toId : String
  relation : EdgeKind
  deriving Repr

inductive LogKind where
  | evidence | openMathReason | openMathClass | provenance | cost | retry
  | promotion | regression | formulationFalsified | miningClass
  deriving DecidableEq, Repr

structure LogEvent where
  node : String
  kind : LogKind
  payload : String
  deriving Repr

/-- Derived state is intentionally separated from PrimitiveNode. -/
structure DerivedNode where
  dependencies : List String
  consumers : List String
  replacementPath : List String
  openClass : OpenClass
  layer : PromotionLayer
  attackable : Bool
  deriving Repr

def isAttackable (n : PrimitiveNode) (d : DerivedNode) : Bool :=
  n.supersededBy.isNone && d.openClass == .attackable

theorem research_not_attackable (n : PrimitiveNode) (d : DerivedNode)
    (h : d.openClass = .research) : isAttackable n d = false := by
  simp [isAttackable, h]

theorem external_not_attackable (n : PrimitiveNode) (d : DerivedNode)
    (h : d.openClass = .external) : isAttackable n d = false := by
  simp [isAttackable, h]

end MCore.ATL.V3
