import MCore.A4Scale

namespace MCore

/-- Pure scale fixture: no Phi, epsilon0, or stopping-time statement is hidden
inside the scaling theorem. -/
def realScaling : Scaling ℝ ℝ where
  act := fun lam u => lam * u

/-- A scale-critical audit fixture. This is deliberately a structural example,
not yet the Navier-Stokes functional. -/
noncomputable def scaleFixtureI (_u : ℝ) : ℝ := (2 : ℝ) / 5

theorem scaleFixture_invariant : ScaleCritical realScaling scaleFixtureI := by
  intro lam u
  rfl

/-- The numerical calibration remains separate data. -/
def calibrationOnly : Calibration where
  phiObserved := 0.6
  epsilonObserved := 0.6
  samples := [0.309, 0.594, 0.609]

end MCore
