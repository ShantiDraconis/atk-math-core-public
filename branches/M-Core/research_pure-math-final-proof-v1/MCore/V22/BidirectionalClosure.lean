import MCore.V22.ExactBlockers

namespace MCore.V22

/-!
Pure-mathematics successor layer.

This file does not alter any frozen certificate and does not assert that an
open problem is solved.  It formalizes the common state space in which the
remaining mathematical obligations are attacked from both endpoints.
-/

inductive ClosureBit where
  | open
  | closed
  deriving DecidableEq, Repr

structure ClosureState where
  start : ClosureBit
  middle : ClosureBit
  finish : ClosureBit
  deriving DecidableEq, Repr

def state000 : ClosureState := ⟨.open, .open, .open⟩
def state001 : ClosureState := ⟨.open, .open, .closed⟩
def state010 : ClosureState := ⟨.open, .closed, .open⟩
def state011 : ClosureState := ⟨.open, .closed, .closed⟩
def state100 : ClosureState := ⟨.closed, .open, .open⟩
def state101 : ClosureState := ⟨.closed, .open, .closed⟩
def state110 : ClosureState := ⟨.closed, .closed, .open⟩
def state111 : ClosureState := ⟨.closed, .closed, .closed⟩

def allClosureStates : List ClosureState :=
  [state000, state001, state010, state011, state100, state101, state110, state111]

theorem closure_state_count : allClosureStates.length = 8 := by rfl

inductive ResearchDirection where
  | startToMiddle
  | middleToFinish
  | finishToMiddle
  | middleToStart
  deriving DecidableEq, Repr

inductive LemmaClass where
  | definition
  | algebraic
  | derived
  | necessary
  | sufficient
  | equivalence
  | negative
  | open
  deriving DecidableEq, Repr

inductive ParameterStatus where
  | known
  | derived
  | free
  | constrained
  | impossible
  | open
  deriving DecidableEq, Repr

/-- A residual is descriptive evidence about the remaining frontier.
    None of its fields is itself a proof of the final endpoint. -/
structure MathematicalResidual where
  parameters : List (String × ParameterStatus)
  missingOperators : List String
  missingLaws : List String
  missingInvariants : List String
  missingQuantifiers : List String
  necessaryConditions : List String
  sufficientConditions : List String
  endpoints : List String
  deriving Repr

structure BidirectionalProblem where
  problem : ProblemId
  state : ClosureState
  positiveWitnessType : String
  negativeWitnessType : String
  directions : List ResearchDirection
  residual : MathematicalResidual
  deriving Repr

def allResearchDirections : List ResearchDirection :=
  [.startToMiddle, .middleToFinish, .finishToMiddle, .middleToStart]

theorem research_direction_count : allResearchDirections.length = 4 := by rfl

/-- Structural 111 is intentionally only a state predicate.  Mathematical
    promotion additionally requires the problem-specific witness, statement,
    quantifier, directionality and no-circularity proofs. -/
def Structurally111 (x : BidirectionalProblem) : Prop :=
  x.state = state111

/-- Positive and negative witnesses cannot both be valid when their validators
    are logically incompatible.  Problem repositories must supply hDisjoint;
    the core never postulates it. -/
theorem witness_incompatibility
    {Wpos Wneg : Type} {ValidPos : Wpos → Prop} {ValidNeg : Wneg → Prop}
    (hDisjoint : ∀ wp wn, ValidPos wp → ValidNeg wn → False)
    (wp : Wpos) (wn : Wneg) (hp : ValidPos wp) :
    ¬ ValidNeg wn := by
  intro hn
  exact hDisjoint wp wn hp hn

/-- Residual reduction is a relation supplied by mathematics, not by the core.
    This prevents a bookkeeping update from masquerading as progress. -/
structure ResidualReduction
    (R : Type) (Smaller : R → R → Prop) (before after : R) : Prop where
  strictlySmaller : Smaller after before

end MCore.V22
