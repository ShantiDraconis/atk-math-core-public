import MCore.ATL.V3.Core

namespace MCore.ATL.V3

inductive LogicalShape where
  | forallExists | existsForall | forallEpsilonExistsDelta
  | forallNatExistsNat | numericEqualityWithBounds | structural | other
  deriving DecidableEq, Repr

inductive Miner where
  | dialectica | modulus | rate | numeric | structural
  deriving DecidableEq, Repr

inductive MiningClass where
  | applicable (miner : Miner)
  | notApplicable
  | requiresFormalization
  deriving DecidableEq, Repr

def classifyMining : LogicalShape → MiningClass
  | .forallExists => .applicable .dialectica
  | .existsForall => .applicable .dialectica
  | .forallEpsilonExistsDelta => .applicable .modulus
  | .forallNatExistsNat => .applicable .rate
  | .numericEqualityWithBounds => .applicable .numeric
  | .structural => .notApplicable
  | .other => .notApplicable

structure MinedEvidence where
  sourceNode : String
  extractionTheorem : String
  sourceStatementHash : String
  extractionStatementHash : String
  kernelAudited : Bool
  semanticAudited : Bool
  computationalArtifact : String
  deriving Repr

def MinedEvidence.emittable (e : MinedEvidence) : Bool :=
  e.kernelAudited && e.semanticAudited &&
  !e.extractionTheorem.isEmpty && !e.computationalArtifact.isEmpty

theorem unaudited_mining_not_emittable (e : MinedEvidence)
    (h : e.kernelAudited = false) : e.emittable = false := by
  simp [MinedEvidence.emittable, h]

end MCore.ATL.V3
