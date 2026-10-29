import Mathlib
import MCore.RH.NB.Distance
import MCore.RH.NB.MCoreNBEstimate
import MCore.RH.NB.FiniteGram

namespace MCore.RH.NB

/-- Quantitative spectral/coercivity datum for a finite Gram system.  No positivity
or uniform lower bound is built into the definition. -/
structure GramCoercivityDatum where
  alpha : ℕ → ℝ

/-- The six-operator 3+3 research object.  This is an interface only: concrete
operators and analytic hypotheses must be supplied by a later model. -/
structure SixOperatorDatum (X : Type) where
  I : Fin 3 → X → X
  D : Fin 3 → X → X

/-- Nine commutators D_i I_j - I_j D_i, represented abstractly so that no
linearity/subtraction assumptions are silently introduced at this layer. -/
structure CommutatorDatum (X Y : Type) where
  value : Fin 3 → Fin 3 → X → Y

/-- A regularization-error candidate is deliberately separate from the actual NB
error.  A model calculation alone cannot inhabit `controlsNBError`. -/
structure RegularizationErrorCandidate where
  value : ℝ → ℝ
  nonnegative : ∀ eps, 0 ≤ eps → 0 ≤ value eps

/-- What is required before a candidate regularization error may be promoted into
an NB bound.  This is the missing analytic identification, not a definition. -/
structure NBRegularizationControl
    {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X)
    (candidate : RegularizationErrorCandidate) where
  regularizedTarget : ℝ → X
  controlsNBError : ∀ (N : ℕ) (eps : ℝ), 0 < eps →
    Metric.infDist (regularizedTarget eps) (F.admissible N) ^ 2 ≤ candidate.value eps

/-- Abstract central quantitative bridge.  `A`, `B`, their limits, and the estimate
are fields that must be proved by a concrete M-Core-to-NB construction; none is
chosen here. -/
structure CentralBridgeCertificate (d : ApproximationDatum) where
  mcoreError : ℝ
  A : ℕ → ℝ
  B : ℕ → ℝ
  estimate : ∀ N, d.error N ≤ A N * mcoreError + B N
  A_nonnegative : ∀ N, 0 ≤ A N
  B_nonnegative : ∀ N, 0 ≤ B N
  A_tendsToZero : Filter.Tendsto A Filter.atTop (nhds 0)
  B_tendsToZero : Filter.Tendsto B Filter.atTop (nhds 0)
  mcoreError_nonnegative : 0 ≤ mcoreError

/-- Once the genuinely quantitative bridge exists, convergence is elementary.
This theorem contains no RH/NB criterion and no hidden approximation hypothesis. -/
theorem convergence_of_central_bridge
    (d : ApproximationDatum) (h : CentralBridgeCertificate d) :
    ApproximationConverges d := by
  have hAconst : Filter.Tendsto (fun N => h.A N * h.mcoreError)
      Filter.atTop (nhds (0 * h.mcoreError)) :=
    h.A_tendsToZero.mul_const h.mcoreError
  have hAB : Filter.Tendsto (fun N => h.A N * h.mcoreError + h.B N)
      Filter.atTop (nhds 0) := by
    simpa using hAconst.add h.B_tendsToZero
  have hlo : ∀ᶠ N in Filter.atTop, 0 ≤ d.error N :=
    Filter.Eventually.of_forall d.nonnegative
  have hhi : ∀ᶠ N in Filter.atTop,
      d.error N ≤ h.A N * h.mcoreError + h.B N :=
    Filter.Eventually.of_forall h.estimate
  exact squeeze_zero' hlo hhi hAB

/-- Endpoint composition remains conditional on an explicit admissibility
certificate and an explicit external criterion. -/
theorem rh_endpoint_of_closed_bridge
    {RH : Prop} (d : ApproximationDatum)
    (bridge : CentralBridgeCertificate d)
    (adm : CriterionAdmissibility d)
    (externalCriterion : adm.admissible → ApproximationConverges d → RH) : RH := by
  exact externalCriterion adm.certificate (convergence_of_central_bridge d bridge)

end MCore.RH.NB
