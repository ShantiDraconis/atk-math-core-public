import MCore.Core
import Mathlib

namespace MCore

/-- Problem-specific rescaling action. M-Core does not assume that unrelated
Millennium problems share the Navier–Stokes scaling map. -/
structure Scaling (U Λ : Type*) where
  act : Λ → U → U

/-- Scale criticality means invariance under the adapter's declared scaling. -/
def ScaleCritical {U Λ : Type*} (s : Scaling U Λ) (I : U → ℝ) : Prop :=
  ∀ λ u, I (s.act λ u) = I u

/-- Calibration constants are data, not theorems. -/
structure Calibration where
  phiObserved : ℝ := 0.6
  epsilonObserved : ℝ := 0.6
  samples : List ℝ := [0.309, 0.594, 0.609]

/-- A threshold is rigid only after a proof obligation certifies it. -/
structure CertifiedThreshold where
  value : ℝ
  positive : 0 < value
  belowOne : value < 1

end MCore
