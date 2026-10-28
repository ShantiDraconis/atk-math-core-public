import MCore.Real.Resolution

namespace MCore.Real

/-- Minimal endpoint criterion induced by the terminal pole 1/1:
    the selected real endpoint must be exactly 1. -/
def E : ResolutionEvidence :=
  fun r => r = (1 : ℝ)

theorem E_one : E 1 := by
  rfl

end MCore.Real
