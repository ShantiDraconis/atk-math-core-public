import MCore.Core
import Mathlib

namespace MCore

/-- A quotient-like invariant is undefined at a zero locus until an extension
is supplied. We model the relevant audit fact directly: two approaches to the
same zero state have incompatible limiting values. -/
structure TwoPathLimitFailure where
  limit₁ : ℝ
  limit₂ : ℝ
  distinct : limit₁ ≠ limit₂

/-- No single real value can equal both distinct path limits. -/
theorem no_path_independent_extension (h : TwoPathLimitFailure) :
    ¬ ∃ L : ℝ, L = h.limit₁ ∧ L = h.limit₂ := by
  rintro ⟨L, h1, h2⟩
  apply h.distinct
  rw [← h1, ← h2]

/-- Status of a zero-locus definition. -/
inductive ZeroLocusStatus where
  | total
  | needsRegularization
  | pathDependent
  deriving DecidableEq, Repr

end MCore
