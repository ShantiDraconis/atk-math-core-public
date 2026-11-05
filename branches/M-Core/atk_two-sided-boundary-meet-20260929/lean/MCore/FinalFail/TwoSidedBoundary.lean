import MCore.FinalFail.ExactGapLedger

namespace MCore.FinalFail

/-!
# Two-sided accepted boundary

This module formalizes a neutral, fail-closed meeting point for two admissible
orientations of the same open problem.

The positive and negative sides are data types, not simultaneous proofs of
`P` and `¬P`.  Both sides are mapped into one canonical `Frontier`.  A
`Meet` inhabitant records the exact point where the two mapped boundary
objects coincide.

This lets downstream work choose either orientation without manufacturing a
contradiction or promoting an accepted hypothesis to an unconditional theorem.
-/

universe u v w

/-- Two admissible orientations terminating in the same canonical frontier. -/
structure TwoSidedBoundary where
  Positive : Type u
  Negative : Type v
  Frontier : Type w
  positiveMap : Positive → Frontier
  negativeMap : Negative → Frontier

namespace TwoSidedBoundary

/-- Exact coincidence witness: one accepted object from each orientation maps
to literally the same canonical frontier value. -/
structure Meet (B : TwoSidedBoundary) where
  positive : B.Positive
  negative : B.Negative
  coincide : B.positiveMap positive = B.negativeMap negative

/-- The accepted two-sided inhabitant.  This is intentionally conditional:
constructing it requires both accepted orientation objects and the equality
certificate at the common frontier. -/
abbrev AcceptedDualInhabitant (B : TwoSidedBoundary) :=
  Nonempty (Meet B)

/-- Enable the two-sided inhabitant from explicit accepted data. -/
theorem enableMeet
    (B : TwoSidedBoundary)
    (positive : B.Positive)
    (negative : B.Negative)
    (h : B.positiveMap positive = B.negativeMap negative) :
    AcceptedDualInhabitant B :=
  ⟨{ positive := positive, negative := negative, coincide := h }⟩

/-- The canonical comparison theorem: inside a `Meet`, the two routes are
exactly equal precisely at the shared frontier image. -/
theorem meet_exact_equality
    {B : TwoSidedBoundary}
    (m : Meet B) :
    B.positiveMap m.positive = B.negativeMap m.negative :=
  m.coincide

/-- Route choice remains explicit.  The common frontier does not erase which
orientation supplied the input. -/
inductive Side where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- A route-tagged accepted input. -/
abbrev OrientedInput (B : TwoSidedBoundary) :=
  Sum B.Positive B.Negative

/-- Execute only the selected orientation up to the common frontier. -/
def executeToFrontier
    (B : TwoSidedBoundary) :
    OrientedInput B → B.Frontier
  | Sum.inl p => B.positiveMap p
  | Sum.inr n => B.negativeMap n

/-- A `Meet` proves that choosing either stored route reaches the same
frontier value. -/
theorem execute_meet_agrees
    {B : TwoSidedBoundary}
    (m : Meet B) :
    executeToFrontier B (Sum.inl m.positive) =
      executeToFrontier B (Sum.inr m.negative) := by
  exact m.coincide

/-- Administrative state for the user's closed→core→closed cycle.  It is a
workflow coordinate only; no constructor here asserts a mathematical endpoint. -/
inductive BoundaryPhase where
  | closedStart
  | contracting
  | openCore
  | expanding
  | closedEnd
  deriving DecidableEq, Repr

/-- Symmetric five-stage cycle used for reporting/dispatch. -/
def phaseCycle : List BoundaryPhase :=
  [.closedStart, .contracting, .openCore, .expanding, .closedEnd]

theorem phaseCycle_length :
    phaseCycle.length = 5 := by
  decide

/-- Fail-closed invariant: this module contains no unconditional accepted dual
inhabitant.  It only exposes a constructor requiring explicit positive,
negative, and coincidence data. -/
def unconditionalDualCount : Nat := 0

theorem unconditionalDualCount_eq_zero :
    unconditionalDualCount = 0 := by
  rfl

end TwoSidedBoundary
end MCore.FinalFail
