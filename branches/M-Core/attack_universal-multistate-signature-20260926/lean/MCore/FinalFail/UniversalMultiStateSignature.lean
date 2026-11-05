import MCore.FinalFail.SevenProblemSignatures
import MCore.FinalFail.ExactGapLedger

namespace MCore.FinalFail

/-!
# Universal multistate signature

This file formalizes a meta-classification theorem.  It does not prove any
open mathematical endpoint.

The common object is a three-stage state machine

  C0 -> O -> C2

together with a problem-specific terminal gap form.  A natural-number code is
a canonical, injective encoding of the full classification signature.
-/

/-- The eight problems in the current atlas, including the historically solved
Poincare positive control. -/
inductive AtlasProblemId where
  | riemann
  | yangMills
  | pVsNP
  | beal
  | navierStokes
  | hodge
  | bsd
  | poincare
  deriving DecidableEq, Repr

/-- The common three-state skeleton. -/
inductive MultiStateStage where
  | c0Closed
  | openCore
  | c2Closed
  deriving DecidableEq, Repr

def MultiStateStage.code : MultiStateStage -> Nat
  | .c0Closed => 0
  | .openCore => 1
  | .c2Closed => 2

/-- Terminal shapes in the user's F-taxonomy. -/
inductive GapForm where
  | f1Vanishing
  | f2GapOrSeparation
  | f4Realization
  | f5Equality
  | f6Exclusion
  | f7Limit
  | f8FixedPoint
  deriving DecidableEq, Repr

def GapForm.code : GapForm -> Nat
  | .f1Vanishing => 1
  | .f2GapOrSeparation => 2
  | .f4Realization => 4
  | .f5Equality => 5
  | .f6Exclusion => 6
  | .f7Limit => 7
  | .f8FixedPoint => 8

def gapFormOf : AtlasProblemId -> GapForm
  | .riemann => .f1Vanishing
  | .yangMills => .f2GapOrSeparation
  | .pVsNP => .f2GapOrSeparation
  | .beal => .f6Exclusion
  | .navierStokes => .f7Limit
  | .hodge => .f4Realization
  | .bsd => .f5Equality
  | .poincare => .f8FixedPoint

/-- Human-readable terminal observable.  This is metadata, not evidence. -/
def terminalObservable : AtlasProblemId -> String
  | .riemann => "S_N -> 0"
  | .yangMills => "Delta > 0"
  | .pVsNP => "asymptotic separation / P != NP"
  | .beal => "X_bad = empty"
  | .navierStokes => "limit/regularity closure"
  | .hodge => "cycle-class realization / coker = 0"
  | .bsd => "r_alg = r_an / defect = 0"
  | .poincare => "M simply-connected => M ~= S3"

/-- Status of the mathematical producer, kept separate from the architecture. -/
inductive ProducerState where
  | openMath
  | historicallyProven
  deriving DecidableEq, Repr

def producerStateOf : AtlasProblemId -> ProducerState
  | .poincare => .historicallyProven
  | _ => .openMath

/--
The universal multistate number-structure.  This is the SAME structural object
for every problem.  It is not a problem identifier.

Its invariant skeleton is 0 -> 1 -> 2:
  0 = closed input boundary C0
  1 = tensioned/open middle O
  2 = closed terminal boundary C2

The problem-specific mathematics enters only through the manifestation fields
below.
-/
structure UniversalNumberStructure where
  c0 : Nat := 0
  openState : Nat := 1
  c2 : Nat := 2
  c0_lt_open : c0 < openState
  open_lt_c2 : openState < c2

def universalNumber : UniversalNumberStructure :=
  {
    c0 := 0
    openState := 1
    c2 := 2
    c0_lt_open := by decide
    open_lt_c2 := by decide
  }

/--
A manifestation is how the SAME universal number-structure appears inside one
problem.  The carrier/observable and terminal law vary by problem; the 0/1/2
architecture is shared.
-/
structure MultiStateManifestation where
  problem : AtlasProblemId
  number : UniversalNumberStructure
  form : GapForm
  observable : String
  producer : ProducerState

def manifestationOf (p : AtlasProblemId) : MultiStateManifestation :=
  {
    problem := p
    number := universalNumber
    form := gapFormOf p
    observable := terminalObservable p
    producer := producerStateOf p
  }

/-- Every problem manifests the exact same universal number-structure. -/
theorem same_universal_number_structure (p : AtlasProblemId) :
    (manifestationOf p).number = universalNumber := rfl

/-- The shared number has the invariant 0 -> 1 -> 2 architecture. -/
theorem universal_number_is_zero_one_two :
    universalNumber.c0 = 0 /\
    universalNumber.openState = 1 /\
    universalNumber.c2 = 2 := by
  decide

/--
The problems remain different because their manifestations can have different
F-forms and observables even though they share the same universal number.
-/
theorem manifestations_share_number
    (p q : AtlasProblemId) :
    (manifestationOf p).number = (manifestationOf q).number := by
  rfl

/--
Meta-theorem requested by the multistate attack:
there EXISTS one universal three-state number-structure, and every problem in
the atlas is a manifestation of that same structure.
-/
theorem universal_multistate_signature :
    exists N : UniversalNumberStructure,
      (N.c0 = 0 /\ N.openState = 1 /\ N.c2 = 2) /\
      forall p : AtlasProblemId,
        (manifestationOf p).number = N := by
  refine ⟨universalNumber, ?_, ?_⟩
  · exact universal_number_is_zero_one_two
  · intro p
    rfl

/--
Problem individuality is carried by the manifestation, not by a different
universal number.
-/
theorem same_number_different_manifestation_possible :
    (manifestationOf .riemann).number = (manifestationOf .hodge).number /\
    (manifestationOf .riemann).form ≠ (manifestationOf .hodge).form := by
  constructor
  · rfl
  · decide

/--
Evidence carried by the atlas: the universal structure is witnessed by the
problem-specific terminal statements already recorded in ExactGapLedger.

This theorem proves only that each manifestation is paired with a ledger entry
whose problem-name/terminal shape matches the atlas classification.  It is
evidence for the common architecture, not a proof of the open endpoint.
-/
def atlasProblemName : AtlasProblemId -> String
  | .riemann => "RIEMANN"
  | .yangMills => "YANG_MILLS"
  | .pVsNP => "P_VS_NP"
  | .beal => "BEAL"
  | .navierStokes => "NAVIER_STOKES"
  | .hodge => "HODGE"
  | .bsd => "BSD"
  | .poincare => "POINCARE"

def atlasResolutionShape : AtlasProblemId -> ResolutionShape
  | .riemann => .bridgeAndVanishing
  | .yangMills => .positivity
  | .pVsNP => .separation
  | .beal => .nonexistence
  | .navierStokes => .vanishing
  | .hodge => .quotientZero
  | .bsd => .equality
  | .poincare => .elimination

def ledgerEvidenceFor (p : AtlasProblemId) : Prop :=
  ∃ g ∈ exactGaps,
    g.problem = atlasProblemName p /\
    g.resolution = atlasResolutionShape p

theorem ledger_evidence_for_all_manifestations :
    ∀ p : AtlasProblemId, ledgerEvidenceFor p := by
  intro p
  cases p <;>
    simp [ledgerEvidenceFor, exactGaps, atlasProblemName, atlasResolutionShape]

/--
Combined theorem: one universal number-structure, distinct manifestations,
and explicit ledger evidence for every manifestation.
-/
theorem universal_multistate_theorem_with_evidence :
    ∃ N : UniversalNumberStructure,
      (N.c0 = 0 /\ N.openState = 1 /\ N.c2 = 2) /\
      (∀ p : AtlasProblemId,
        (manifestationOf p).number = N /\
        ledgerEvidenceFor p) := by
  refine ⟨universalNumber, universal_number_is_zero_one_two, ?_⟩
  intro p
  exact ⟨rfl, ledger_evidence_for_all_manifestations p⟩

#print axioms MCore.FinalFail.ledger_evidence_for_all_manifestations
#print axioms MCore.FinalFail.universal_multistate_theorem_with_evidence

/--
Important firewall: classification and numerical encoding do not discharge any
OPEN_MATH producer.
-/
theorem signature_does_not_promote_open_math
    (p : AtlasProblemId)
    (h : producerStateOf p = .openMath) :
    (manifestationOf p).producer = .openMath := by
  simpa [multistateSignatureOf] using h

#print axioms MCore.FinalFail.same_universal_number_structure
#print axioms MCore.FinalFail.universal_number_is_zero_one_two
#print axioms MCore.FinalFail.manifestations_share_number
#print axioms MCore.FinalFail.universal_multistate_signature
#print axioms MCore.FinalFail.same_number_different_manifestation_possible
#print axioms MCore.FinalFail.signature_does_not_promote_open_math

end MCore.FinalFail
