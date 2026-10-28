import MCore.Real.Resolution

namespace MCore.Real

/-- Minimal real producer. Its only mathematical payload is evidence for the
    selected endpoint plus a path whose transitions are checked by ResolutionStep. -/
structure RealProducer (E : ResolutionEvidence) where
  endpoint : ℝ
  evidence : E endpoint
  path : ResolutionPath E .indeterminate (.resolved endpoint)

theorem RealProducer.closed
    {E : ResolutionEvidence}
    (P : RealProducer E) :
    indeterminacy (.resolved P.endpoint) = 0 := by
  simp

/-- A producer immediately supplies an actual existential evidence witness. -/
theorem RealProducer.hasEvidence
    {E : ResolutionEvidence}
    (P : RealProducer E) :
    ∃ r : ℝ, E r :=
  ⟨P.endpoint, P.evidence⟩

end MCore.Real
