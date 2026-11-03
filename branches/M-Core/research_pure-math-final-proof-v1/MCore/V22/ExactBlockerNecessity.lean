import MCore.V22.ExactBlockers
import MCore.V22.BidirectionalClosure

namespace MCore.V22

/-!
Exact-blocker necessity layer.

This module proves only structural facts already encoded by the registry.
It deliberately does not prove any open mathematical endpoint.
-/

def HasExactBlocker (p : ProblemId) : Prop :=
  ∃ b ∈ exactMathematicalBlockers, b.problem = p

theorem blocker_mem_implies_hasExactBlocker
    {b : ExactBlocker}
    (hb : b ∈ exactMathematicalBlockers) :
    HasExactBlocker b.problem := by
  exact ⟨b, hb, rfl⟩

theorem hodge_has_exact_blocker : HasExactBlocker .hodge := by
  unfold HasExactBlocker
  simp [exactMathematicalBlockers]

theorem bsd_has_exact_blocker : HasExactBlocker .bsd := by
  unfold HasExactBlocker
  simp [exactMathematicalBlockers]

theorem beal_has_exact_blocker : HasExactBlocker .beal := by
  unfold HasExactBlocker
  simp [exactMathematicalBlockers]

theorem pnp_has_exact_blocker : HasExactBlocker .pVsNP := by
  unfold HasExactBlocker
  simp [exactMathematicalBlockers]

theorem riemann_has_exact_blocker : HasExactBlocker .riemann := by
  unfold HasExactBlocker
  simp [exactMathematicalBlockers]

theorem yangMills_has_exact_blocker : HasExactBlocker .yangMills := by
  unfold HasExactBlocker
  simp [exactMathematicalBlockers]

theorem navierStokes_has_exact_blocker : HasExactBlocker .navierStokes := by
  unfold HasExactBlocker
  simp [exactMathematicalBlockers]

def OpenResearchProblem (p : ProblemId) : Prop :=
  p = .hodge ∨ p = .bsd ∨ p = .beal ∨ p = .pVsNP ∨
  p = .riemann ∨ p = .yangMills ∨ p = .navierStokes

theorem open_problem_has_registered_exact_blocker
    {p : ProblemId} (hp : OpenResearchProblem p) :
    HasExactBlocker p := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hodge_has_exact_blocker
  · exact bsd_has_exact_blocker
  · exact beal_has_exact_blocker
  · exact pnp_has_exact_blocker
  · exact riemann_has_exact_blocker
  · exact yangMills_has_exact_blocker
  · exact navierStokes_has_exact_blocker

/-- A registered blocker is a research obligation, not a proof hypothesis.
    Closure requires an explicit discharge object supplied by the problem repo. -/
structure BlockerDischarge (b : ExactBlocker) where
  witnessType : Type
  witness : witnessType
  validates : witnessType → Prop
  valid : validates witness

def AllBlockersDischarged
    (D : (b : ExactBlocker) → b ∈ exactMathematicalBlockers → Prop) : Prop :=
  ∀ (b : ExactBlocker) (hb : b ∈ exactMathematicalBlockers), D b hb

end MCore.V22
