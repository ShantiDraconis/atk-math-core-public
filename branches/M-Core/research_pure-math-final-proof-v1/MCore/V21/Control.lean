import Mathlib

namespace MCore.V21

/-- Exact repository-head lock. A certificate is invalid if the observed head
    differs from the head recorded by the audit. -/
structure HeadExact where
  expected : String
  actual : String

def HeadExact.Closed (h : HeadExact) : Prop :=
  h.actual = h.expected

/-- Frozen S1 lock. These booleans are populated by the source-level audit. -/
structure FrozenS1 where
  sha : String
  untouched : Bool
  noK27 : Bool
  noK31 : Bool
  noK32 : Bool

def FrozenS1.Closed (s : FrozenS1) : Prop :=
  s.untouched = true ∧
  s.noK27 = true ∧
  s.noK31 = true ∧
  s.noK32 = true

inductive EndpointKind where
  | definitionOnly
  deriving DecidableEq, Repr

/-- Endpoint metadata. The definitionOnly tag records that the target
    proposition is stated rather than smuggled in as a proof hypothesis. -/
structure EndpointDefinition where
  name : String
  kind : EndpointKind
  assumptionSubstituteCount : Nat

def EndpointDefinition.Closed (e : EndpointDefinition) : Prop :=
  e.kind = .definitionOnly ∧ e.assumptionSubstituteCount = 0

/-- A real compression is a proof-producing map from the isolated middle
    obligation to the endpoint. -/
structure Compression (Middle Final : Prop) where
  close : Middle → Final

/-- Six-dimensional semantic audit. The SHA and literal declaration are
    evidence metadata; each dimension must independently be GREEN. -/
structure Audit6D where
  sourceSHA : String
  literalDeclaration : String
  hypothesisMatch : Bool
  conclusionMatch : Bool
  quantifierMatch : Bool
  scalingMatch : Bool
  constantMatch : Bool
  axiomAudit : Bool

def Audit6D.Closed (a : Audit6D) : Prop :=
  a.hypothesisMatch = true ∧
  a.conclusionMatch = true ∧
  a.quantifierMatch = true ∧
  a.scalingMatch = true ∧
  a.constantMatch = true ∧
  a.axiomAudit = true

/-- Residue ledger. RAW and REVIEWED are provenance counters. TARGET
    certification additionally requires every forbidden/blocking count zero. -/
structure ResidueLedger where
  raw : Nat := 0
  reviewed : Nat := 0
  blocking : Nat := 0
  sorryCount : Nat := 0
  admitCount : Nat := 0
  unaccountedAxiomCount : Nat := 0
  nanCount : Nat := 0
  nullRequiredWitnessCount : Nat := 0

def ResidueLedger.Closed (r : ResidueLedger) : Prop :=
  r.blocking = 0 ∧
  r.sorryCount = 0 ∧
  r.admitCount = 0 ∧
  r.unaccountedAxiomCount = 0 ∧
  r.nanCount = 0 ∧
  r.nullRequiredWitnessCount = 0

/-- BUILD is separate from mathematics: it certifies reproducibility and the
    axiom printout, never the theorem by itself. -/
structure BuildGate where
  lakeBuildGreen : Bool
  printAxiomsRun : Bool
  unexpectedAxiomCount : Nat

def BuildGate.Closed (b : BuildGate) : Prop :=
  b.lakeBuildGreen = true ∧
  b.printAxiomsRun = true ∧
  b.unexpectedAxiomCount = 0

/-- Counts of known placebo mechanisms. -/
structure NoPlacebo where
  ci : Nat := 0
  definition : Nat := 0
  compression : Nat := 0
  constant : Nat := 0
  external : Nat := 0
  adminPromotion : Nat := 0
  defaultAsProofSubstitute : Nat := 0
  optionNoneRequiredWitness : Nat := 0

def NoPlacebo.Closed (p : NoPlacebo) : Prop :=
  p.ci = 0 ∧
  p.definition = 0 ∧
  p.compression = 0 ∧
  p.constant = 0 ∧
  p.external = 0 ∧
  p.adminPromotion = 0 ∧
  p.defaultAsProofSubstitute = 0 ∧
  p.optionNoneRequiredWitness = 0

/-- The eight V2.1 locks. The compression proof itself is stored by the chain,
    while this pack records that its audit gate passed. -/
structure ControlPack where
  headExact : HeadExact
  frozenS1 : FrozenS1
  endpoint : EndpointDefinition
  compressionAuditGreen : Bool
  audit6d : Audit6D
  residues : ResidueLedger
  build : BuildGate
  noPlacebo : NoPlacebo

def ControlPack.Closed (c : ControlPack) : Prop :=
  c.headExact.Closed ∧
  c.frozenS1.Closed ∧
  c.endpoint.Closed ∧
  c.compressionAuditGreen = true ∧
  c.audit6d.Closed ∧
  c.residues.Closed ∧
  c.build.Closed ∧
  c.noPlacebo.Closed

end MCore.V21
