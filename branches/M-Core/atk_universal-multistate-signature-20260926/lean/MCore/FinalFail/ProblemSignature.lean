namespace MCore.FinalFail

/-- Qualitative invariants used to compare terminal proof architectures. -/
inductive Directionality where | inward | outward | bidirectional
inductive Locality where | local | global | localToGlobal
inductive ObstructionKind where
  | primitive | transfer | algebraicity | complexity
  | rank | residue | spectral
inductive ClosureKind where | vanishing | positivity | emptiness
inductive ScalarGeometry where | discrete | real | complex | mixed

structure ProblemSignature where
  direction : Directionality
  locality : Locality
  obstruction : ObstructionKind
  closure : ClosureKind
  scalar : ScalarGeometry
  hasCompression : Bool
  hasRetraction : Bool

/-- Equality of signatures is the admissible notion of behavioral equivalence. -/
def BehaviorEquivalent (a b : ProblemSignature) : Prop := a = b

theorem behaviorEquivalent_refl (a : ProblemSignature) :
    BehaviorEquivalent a a := rfl

theorem behaviorEquivalent_symm {a b : ProblemSignature}
    (h : BehaviorEquivalent a b) : BehaviorEquivalent b a := by
  exact h.symm

theorem behaviorEquivalent_trans {a b c : ProblemSignature}
    (hab : BehaviorEquivalent a b) (hbc : BehaviorEquivalent b c) :
    BehaviorEquivalent a c := by
  exact hab.trans hbc

/-- A decimal class is valid only when a signature and an invariant-preserving
    classification proof are supplied. -/
structure DecimalClass where
  digit : Nat
  digit_ge_three : 3 ≤ digit
  digit_lt_ten : digit < 10
  signature : ProblemSignature

/-- Seven available decimal classes after reserving 0,1,2 for the triad. -/
def IsTerminalDigit (n : Nat) : Prop := 3 ≤ n ∧ n < 10

theorem terminalDigit_bounds {n : Nat} (h : IsTerminalDigit n) :
    3 ≤ n ∧ n < 10 := h

/-- A problem can be assigned to a decimal class only through exact signature
    equality; names or analogy are insufficient. -/
structure ClassifiedProblem where
  Problem : Type
  signature : ProblemSignature
  class : DecimalClass
  preserves : BehaviorEquivalent signature class.signature

/-- Compression/retraction duality is recorded as structure, not inferred from
    a problem name. -/
def HasTwoSidedDynamics (s : ProblemSignature) : Prop :=
  s.hasCompression = true ∧ s.hasRetraction = true

theorem classified_preserves_twoSided
    (P : ClassifiedProblem)
    (h : HasTwoSidedDynamics P.signature) :
    HasTwoSidedDynamics P.class.signature := by
  simpa [BehaviorEquivalent] using h

end MCore.FinalFail
