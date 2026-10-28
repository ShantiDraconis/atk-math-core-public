import Mathlib

namespace MCore.FinalFail

inductive ProblemId where
  | beal | navierStokes | hodge | pVsNP | bsd | riemann | yangMills
  deriving DecidableEq

/-- Concrete obstruction vocabulary extracted from the current terminal HARDs.
These are types/relations, not claims that the corresponding open problem is solved. -/
inductive TerminalObstruction where
  | primitiveSolution
  | signedTransferDefect
  | nonAlgebraicHodgeClass
  | polynomialSATDecider
  | rankMismatch
  | nonzeroDNLimit
  | nonpositiveSpectralGap
  deriving DecidableEq

def obstructionOf : ProblemId → TerminalObstruction
  | .beal => .primitiveSolution
  | .navierStokes => .signedTransferDefect
  | .hodge => .nonAlgebraicHodgeClass
  | .pVsNP => .polynomialSATDecider
  | .bsd => .rankMismatch
  | .riemann => .nonzeroDNLimit
  | .yangMills => .nonpositiveSpectralGap

/-- Every active chain has its own obstruction class. -/
theorem obstruction_assignment_total (p : ProblemId) :
    ∃ o : TerminalObstruction, obstructionOf p = o := by
  exact ⟨obstructionOf p, rfl⟩

/-- The current seven obstruction constructors are pairwise assigned by problem.
This theorem is only classification of the formal vocabulary. -/
theorem obstruction_assignment_injective :
    Function.Injective obstructionOf := by
  intro a b h
  cases a <;> cases b <;> simp [obstructionOf] at h ⊢

/-- Dynamics at the terminal bridge: inward means reduction/compression into the
obstruction; outward means reconstruction from a discharged obstruction. -/
inductive TerminalDirection where
  | compress | retract
  deriving DecidableEq

structure TerminalNucleus where
  problem : ProblemId
  obstruction : TerminalObstruction
  correctObstruction : obstruction = obstructionOf problem
  CompressionState : Prop
  ClosedState : Prop
  compression_to_core : CompressionState → Prop
  core_to_closed : Prop → ClosedState

/--
A safe nucleus does not claim closure. It records the exact missing proposition
that must be supplied between compression and endpoint reconstruction.
-/
structure OpenRigidNucleus where
  problem : ProblemId
  Core : Prop
  Endpoint : Prop
  compressed_to_core : Prop
  core_to_endpoint : Core → Endpoint

/-- Closing an open nucleus requires the actual Core proof. -/
theorem close_local_nucleus (N : OpenRigidNucleus) (hCore : N.Core) :
    N.Endpoint :=
  N.core_to_endpoint hCore

/--
The decimal layer has seven slots and the active problem family has seven
constructors. This proves cardinal compatibility only; it does not choose a
mathematical digit assignment.
-/
def slotOf : ProblemId → Nat
  | .beal => 3
  | .navierStokes => 4
  | .hodge => 5
  | .pVsNP => 6
  | .bsd => 7
  | .riemann => 8
  | .yangMills => 9

theorem slotOf_range (p : ProblemId) :
    3 ≤ slotOf p ∧ slotOf p < 10 := by
  cases p <;> decide

theorem slotOf_injective : Function.Injective slotOf := by
  intro a b h
  cases a <;> cases b <;> simp [slotOf] at h ⊢

end MCore.FinalFail
