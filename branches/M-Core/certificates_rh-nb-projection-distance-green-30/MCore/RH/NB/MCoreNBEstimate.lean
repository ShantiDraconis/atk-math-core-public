import MCore.RH.NB.Distance

namespace MCore.RH.NB

/-- Quantitative decomposition of the proposed M-Core→NB estimate.
No field asserts RH or NB convergence. -/
structure MCoreNBEstimate (d : ApproximationDatum) where
  A : ℕ → ℝ
  B : ℕ → ℝ
  intrinsicError : ℝ
  intrinsicError_nonneg : 0 ≤ intrinsicError
  A_nonneg : ∀ N, 0 ≤ A N
  B_nonneg : ∀ N, 0 ≤ B N
  estimate : ∀ N, d.error N ≤ A N * intrinsicError + B N
  A_tendsToZero : Filter.Tendsto A Filter.atTop (nhds 0)
  B_tendsToZero : Filter.Tendsto B Filter.atTop (nhds 0)

/-- Once the quantitative estimate and both decay statements are actually supplied,
the resulting approximation error tends to zero. This theorem closes only the
analytic composition step; constructing `h` remains OPEN_BRIDGE. -/
theorem estimate_implies_convergence
    (d : ApproximationDatum) (h : MCoreNBEstimate d) :
    ApproximationConverges d := by
  have hAconst :
      Filter.Tendsto (fun N => h.A N * h.intrinsicError)
        Filter.atTop (nhds (0 * h.intrinsicError)) :=
    h.A_tendsToZero.mul_const h.intrinsicError
  have hA0 :
      Filter.Tendsto (fun N => h.A N * h.intrinsicError)
        Filter.atTop (nhds 0) := by
    simpa using hAconst
  have hmajorant :
      Filter.Tendsto (fun N => h.A N * h.intrinsicError + h.B N)
        Filter.atTop (nhds 0) := by
    simpa using hA0.add h.B_tendsToZero
  have hnonneg : ∀ᶠ N in Filter.atTop, 0 ≤ d.error N :=
    Filter.Eventually.of_forall d.nonnegative
  have hbound : ∀ᶠ N in Filter.atTop,
      d.error N ≤ h.A N * h.intrinsicError + h.B N :=
    Filter.Eventually.of_forall h.estimate
  exact squeeze_zero' hnonneg hbound hmajorant

/-- Admissibility is deliberately independent of convergence: it certifies that the
objects whose distance is estimated are genuinely objects of the external criterion. -/
structure CriterionAdmissibility (d : ApproximationDatum) where
  admissible : Prop
  certificate : admissible

/-- The final external criterion must consume both the independently certified
admissibility and convergence. This keeps the endpoint conditional and prevents the
admissibility certificate from being a decorative/unused field. -/
theorem estimate_to_external_endpoint
    {RH : Prop} (d : ApproximationDatum)
    (hEst : MCoreNBEstimate d)
    (hAdm : CriterionAdmissibility d)
    (external : hAdm.admissible → ApproximationConverges d → RH) : RH := by
  exact external hAdm.certificate (estimate_implies_convergence d hEst)

end MCore.RH.NB
