import MCore.FinalFail.ProblemSignature
import MCore.FinalFail.SevenProblemSignatures

namespace MCore.MultistateSignature

open MCore.FinalFail

/-- Canonical closure stages shared by every problem. -/
inductive ClosureStage where
  | c0
  | open
  | c2
  deriving DecidableEq, Repr

/-- The universal multistate number is the same 0/1/2 structural coordinate
for every problem.  It is not a problem identifier. -/
def structuralNumber : ClosureStage → Nat
  | .c0 => 0
  | .open => 1
  | .c2 => 2

/-- A manifestation is the universal 0/1/2 coordinate together with the
problem-specific signature in which that coordinate is realized. -/
structure Manifestation where
  problem : ProblemId
  stage : ClosureStage
  number : Nat
  signature : ProblemSignature
  number_is_structural : number = structuralNumber stage
  signature_is_problem : signature = signatureOf problem

def manifest (p : ProblemId) (st : ClosureStage) : Manifestation where
  problem := p
  stage := st
  number := structuralNumber st
  signature := signatureOf p
  number_is_structural := rfl
  signature_is_problem := rfl

/-- Every problem sees exactly the same 0/1/2 numeric skeleton. -/
theorem same_structural_number
    (p q : ProblemId) (st : ClosureStage) :
    (manifest p st).number = (manifest q st).number := by
  rfl

/-- The manifestations can differ even though the structural number is shared:
their problem signatures remain problem-specific. -/
theorem manifestation_signature
    (p : ProblemId) (st : ClosureStage) :
    (manifest p st).signature = signatureOf p := by
  rfl

/-- Each tracked problem realizes the full common 0 -> 1 -> 2 structure. -/
theorem problem_realizes_three_state_structure (p : ProblemId) :
    (manifest p .c0).number = 0 ∧
    (manifest p .open).number = 1 ∧
    (manifest p .c2).number = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Distinct problems may manifest the same structural state differently.
The common number does not collapse distinct repository-level signatures. -/
theorem distinct_problems_have_distinct_signatures
    {p q : ProblemId} (hpq : p ≠ q) (st : ClosureStage) :
    (manifest p st).signature ≠ (manifest q st).signature := by
  intro h
  have hs : signatureOf p = signatureOf q := by
    simpa [manifest] using h
  exact hpq (signature_assignment_injective hs)

/-- Main architectural theorem:
there is one common numeric 0/1/2 structure, and every tracked problem realizes
that structure through its own distinct signature. -/
theorem universal_multistate_manifestation :
    ∀ p : ProblemId,
      (manifest p .c0).number = 0 ∧
      (manifest p .open).number = 1 ∧
      (manifest p .c2).number = 2 ∧
      (∀ st : ClosureStage,
        (manifest p st).signature = signatureOf p) := by
  intro p
  exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

#print axioms same_structural_number
#print axioms manifestation_signature
#print axioms problem_realizes_three_state_structure
#print axioms distinct_problems_have_distinct_signatures
#print axioms universal_multistate_manifestation

end MCore.MultistateSignature
