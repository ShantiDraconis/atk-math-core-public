import MCore.ProofEngine.Pattern

namespace MCore.ProofEngine

inductive EvidenceState
  | unknown
  | proved
  | disproved
  | conflict
  deriving DecidableEq, Repr

/-- Kernel-facing description of a proof-search obligation. Metadata strings
are provenance labels only; `target` and `hypotheses` carry the propositions. -/
structure Obligation where
  name : String
  target : Prop
  hypotheses : List Prop
  pattern : Pattern
  state : EvidenceState := .unknown

def Claimable (o : Obligation) : Prop :=
  o.state = .proved

theorem unknown_not_claimable (o : Obligation) (h : o.state = .unknown) :
    ¬ Claimable o := by
  simp [Claimable, h]

theorem conflict_not_claimable (o : Obligation) (h : o.state = .conflict) :
    ¬ Claimable o := by
  simp [Claimable, h]

end MCore.ProofEngine
