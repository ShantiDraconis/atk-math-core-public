namespace MCore.RH

/-- Scientific status of an obligation. This is metadata, not a third truth value for Prop. -/
inductive ProofStatus where
  | provedLean
  | provedExternal
  | numericalEvidence
  | openBridge
  | circularDependency
  | refutedRoute
  deriving DecidableEq, Repr

/-- Epistemic evidence for a proposition; `unresolved` does not alter classical truth. -/
inductive EvidenceStatus (P : Prop) where
  | provedTrue (h : P)
  | provedFalse (h : ¬ P)
  | unresolved

structure Obligation where
  name : String
  status : ProofStatus
  note : String
  deriving Repr

/-- A certificate may be gap-complete while the target theorem remains unproved. -/
structure Certificate where
  obligations : List Obligation
  targetProved : Bool
  noHiddenGaps : Bool
  deriving Repr

end MCore.RH
