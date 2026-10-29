import MCore.FinalCore

namespace MCore

/-- Minimal analytic data needed to turn decay into a spectral exclusion.
    This deliberately does not pretend that K14's abstract State/Scale types
    already form a Hilbert space or carry a spectral measure. -/
structure SpectralDecayModel where
  State : Type
  Rate : Type
  Time : Type
  physical : State → Prop
  orthogonalToVacuum : State → Prop
  positiveRate : Rate → Prop
  matrixElementDecay : Rate → State → Prop
  excludesBelow : Rate → State → Prop

/-- The genuinely analytic edge.  A witness of this structure must prove the
    transfer for the concrete model; it is not manufactured from Prop wrappers. -/
structure DecayToSpectralExclusion (M : SpectralDecayModel) where
  transfer : ∀ (m : M.Rate) (ψ : M.State),
    M.positiveRate m →
    M.physical ψ →
    M.orthogonalToVacuum ψ →
    M.matrixElementDecay m ψ →
    M.excludesBelow m ψ

/-- Once the analytic transfer is supplied, application to one state is purely
    logical and belongs in CORE. -/
theorem decay_implies_exclusion
    {M : SpectralDecayModel}
    (T : DecayToSpectralExclusion M)
    (m : M.Rate) (ψ : M.State)
    (hm : M.positiveRate m)
    (hp : M.physical ψ)
    (ho : M.orthogonalToVacuum ψ)
    (hd : M.matrixElementDecay m ψ) :
    M.excludesBelow m ψ :=
  T.transfer m ψ hm hp ho hd

/-- Diagnostic frontier: this is the minimum missing edge exposed by the
    current repository types.  A future concrete Hilbert/spectral model should
    instantiate it using an actual spectral theorem. -/
def SpectralAnalyticOpenBridge (M : SpectralDecayModel) : Prop :=
  Nonempty (DecayToSpectralExclusion M)

end MCore
