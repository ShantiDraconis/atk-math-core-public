import MCore.ProofEngine.Obligation

namespace MCore.ProofEngine

inductive NodeKind
  | theorem | lemma | adapter | certificate | computation | barrier
  deriving DecidableEq, Repr

inductive MathClass
  | none
  | attackable
  | research
  | external
  deriving DecidableEq, Repr

/-- Persisted, authored fields only. No build/kernel/certificate state belongs here. -/
structure NodePrimitive where
  id : String
  area : String
  kind : NodeKind
  formalStatement : String
  semanticStatement : String
  sourceFiles : List String
  theoremNames : List String
  repo : String
  branch : String
  commit : String
  version : Nat
  supersededBy : Option String := none
  deriving Repr

/-- Append-only observations. These never overwrite authored node identity. -/
structure EvidenceEvent where
  evidenceId : String
  nodeId : String
  source : String
  detail : String
  deriving Repr

structure NodeLog where
  evidence : List EvidenceEvent := []
  openMathClass : MathClass := .none
  openMathReason : Option String := none
  provenanceState : String := ""
  deriving Repr

/-- A route is stored as node ids, never as an unvalidated prose string. -/
structure RouteSpec where
  nodeIds : List String
  deriving Repr

/-- Derived state is intentionally not part of persisted NodePrimitive/NodeLog. -/
structure DerivedNodeState where
  dependencies : List String
  consumers : List String
  replacementRoute : Option RouteSpec
  sourceGreen : Bool
  buildGreen : Bool
  kernelGreen : Bool
  semanticGreen : Bool
  scientificGreen : Bool
  deriving Repr

def eligibleForAttackCut (log : NodeLog) : Bool :=
  log.openMathClass == .attackable

end MCore.ProofEngine
