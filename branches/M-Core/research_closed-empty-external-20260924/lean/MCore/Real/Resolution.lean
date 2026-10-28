import Mathlib.Data.Real.Basic
import Mathlib.Logic.Relation

namespace MCore.Real

/-- The three resolution phases. This is a state model, not standard arithmetic. -/
inductive ResolutionState where
  | indeterminate
  | resolving (r τ : ℝ) (hτ : 0 < τ ∧ τ < 1)
  | resolved (r : ℝ)

/-- A resolution criterion is supplied externally as an actual proposition
    about the selected real endpoint. No default inhabitant is manufactured. -/
abbrev ResolutionEvidence := ℝ → Prop

/-- One-step resolution dynamics. A real endpoint may be entered only when
    evidence for that same endpoint is available. -/
inductive ResolutionStep (E : ResolutionEvidence) :
    ResolutionState → ResolutionState → Prop where
  | begin
      {r τ : ℝ}
      (e : E r)
      (hτ : 0 < τ ∧ τ < 1) :
      ResolutionStep E
        .indeterminate
        (.resolving r τ hτ)
  | finish
      {r τ : ℝ}
      {hτ : 0 < τ ∧ τ < 1}
      (e : E r) :
      ResolutionStep E
        (.resolving r τ hτ)
        (.resolved r)

/-- Zero or more valid resolution steps. -/
abbrev ResolutionPath (E : ResolutionEvidence) :=
  Relation.ReflTransGen (ResolutionStep E)

/-- Indeterminacy marker: only the resolved phase is closed. -/
def indeterminacy : ResolutionState → Nat
  | .indeterminate => 1
  | .resolving _ _ _ => 1
  | .resolved _ => 0

@[simp] theorem indeterminacy_resolved (r : ℝ) :
    indeterminacy (.resolved r) = 0 := rfl

end MCore.Real
