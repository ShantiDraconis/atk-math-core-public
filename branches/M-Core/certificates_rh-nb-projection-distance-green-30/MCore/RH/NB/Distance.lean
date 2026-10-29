import Mathlib
import MCore.RH.ResearchObligations

namespace MCore.RH.NB

/-- Abstract nested approximation spaces. This layer deliberately does not identify
these spaces with the Nyman--Beurling spaces until the admissibility bridge is built. -/
structure ApproximationFamily (X : Type) [PseudoMetricSpace X] where
  target : X
  admissible : ℕ → Set X
  nested : ∀ {m n : ℕ}, m ≤ n → admissible m ⊆ admissible n

/-- Squared distance to the N-th admissible approximation set. -/
noncomputable def distanceSq {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X) (N : ℕ) : ℝ :=
  (Metric.infDist F.target (F.admissible N)) ^ 2

/-- Distance is nonnegative without any RH assumption. -/
theorem distanceSq_nonneg {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X) (N : ℕ) :
    0 ≤ distanceSq F N := by
  exact sq_nonneg _

/-- The abstract NB error is exactly a `ResearchObligations.ApproximationDatum`. -/
noncomputable def asDatum {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X) : ApproximationDatum where
  error := distanceSq F
  nonnegative := distanceSq_nonneg F

/-- The endpoint remains an explicit convergence obligation, not a theorem smuggled
into the definition. -/
def Converges {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X) : Prop :=
  ApproximationConverges (asDatum F)

/-- A quantitative majorant is useful only when its bound and decay are separately proved. -/
structure MajorantCertificate {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X) where
  E : ℕ → ℝ
  bound : ∀ N, distanceSq F N ≤ E N
  tendsToZero : Filter.Tendsto E Filter.atTop (nhds 0)

/-- Closed infrastructure lemma: a nonnegative NB-distance bounded by a decaying
majorant converges to zero. The hard mathematics is precisely construction of `cert`. -/
theorem converges_of_majorant {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X) (cert : MajorantCertificate F) :
    Converges F := by
  have hnonneg : ∀ᶠ N in Filter.atTop, 0 ≤ distanceSq F N :=
    Filter.Eventually.of_forall (distanceSq_nonneg F)
  have hbound : ∀ᶠ N in Filter.atTop, distanceSq F N ≤ cert.E N :=
    Filter.Eventually.of_forall cert.bound
  exact squeeze_zero' hnonneg hbound cert.tendsToZero

/-- Gram/projection identities are not assumed by `ApproximationFamily`; a concrete
certificate must prove the formula for the actual finite-dimensional family. -/
structure GramProjectionCertificate {X : Type} [PseudoMetricSpace X]
    (F : ApproximationFamily X) where
  gramFormula : ℕ → ℝ
  formula_correct : ∀ N, distanceSq F N = gramFormula N

end MCore.RH.NB
