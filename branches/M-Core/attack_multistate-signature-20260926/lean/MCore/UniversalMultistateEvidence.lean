import MCore.FinalFail.SevenProblemSignatures

namespace MCore.UniversalMultistateEvidence

open MCore.FinalFail

inductive StructuralState where
  | start
  | obstruction
  | terminal
  deriving DecidableEq, Repr

def structuralNumber : StructuralState → Nat
  | .start => 0
  | .obstruction => 1
  | .terminal => 2

inductive ManifestationKind where
  | vanishing
  | positiveGap
  | separation
  | realization
  | equality
  | exclusion
  | limitClosure
  deriving DecidableEq, Repr

def manifestationOf : ProblemId → ManifestationKind
  | .beal => .exclusion
  | .navierStokes => .limitClosure
  | .hodge => .realization
  | .pVsNP => .separation
  | .bsd => .equality
  | .riemann => .vanishing
  | .yangMills => .positiveGap

structure Realization where
  problem : ProblemId
  state : StructuralState
  number : Nat
  kind : ManifestationKind
  signature : ProblemSignature
  obstruction : TerminalObstruction
  number_ok : number = structuralNumber state
  kind_ok : kind = manifestationOf problem
  signature_ok : signature = signatureOf problem
  obstruction_ok : obstruction = obstructionOf problem

def realize (p : ProblemId) (s : StructuralState) : Realization where
  problem := p
  state := s
  number := structuralNumber s
  kind := manifestationOf p
  signature := signatureOf p
  obstruction := obstructionOf p
  number_ok := rfl
  kind_ok := rfl
  signature_ok := rfl
  obstruction_ok := rfl

theorem common_three_state_skeleton (p : ProblemId) :
    (realize p .start).number = 0 ∧
    (realize p .obstruction).number = 1 ∧
    (realize p .terminal).number = 2 := by
  exact ⟨rfl, rfl, rfl⟩

theorem same_number_different_problem
    (p q : ProblemId) (s : StructuralState) :
    (realize p s).number = (realize q s).number := by
  rfl

theorem realization_preserves_existing_obstruction
    (p : ProblemId) (s : StructuralState) :
    (realize p s).signature.obstruction =
      match (realize p s).obstruction with
      | .primitiveSolution => .primitive
      | .signedTransferDefect => .transfer
      | .nonAlgebraicHodgeClass => .algebraicity
      | .polynomialSATDecider => .complexity
      | .rankMismatch => .rank
      | .nonzeroDNLimit => .residue
      | .nonpositiveSpectralGap => .spectral := by
  simpa [realize] using signature_obstruction_matches p

theorem universal_structure_distinct_manifestations :
    ∀ p : ProblemId,
      (realize p .start).number = 0 ∧
      (realize p .obstruction).number = 1 ∧
      (realize p .terminal).number = 2 ∧
      (realize p .terminal).kind = manifestationOf p ∧
      (realize p .terminal).signature = signatureOf p ∧
      (realize p .terminal).obstruction = obstructionOf p := by
  intro p
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms common_three_state_skeleton
#print axioms same_number_different_problem
#print axioms realization_preserves_existing_obstruction
#print axioms universal_structure_distinct_manifestations

end MCore.UniversalMultistateEvidence
