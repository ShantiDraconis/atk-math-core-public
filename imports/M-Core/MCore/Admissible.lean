import MCore.A1Amplitude
import MCore.A3Zero
import MCore.A4Scale
import MCore.DAG

namespace MCore

/-- Certified facts exposed by a concrete adapter.  No numerical calibration or
open bridge is promoted to a theorem here. -/
structure AuditRecord (U Λ : Type*) [AddCommGroup U] [Module ℝ U] where
  I : U → ℝ
  scaling : Scaling U Λ
  dependencyGraph : Graph
  amplitudeLaw : AmplitudeHomogeneous I
  downstreamGate : PassesDownstreamGate dependencyGraph
  zeroStatus : ZeroLocusStatus
  scaleLaw : ScaleCritical scaling I

/-- The four obligations used by the composition layer.  A1 is recorded as a
certified structural fact; A2/A3/A4 are the admissibility gates. -/
structure CertifiedObligations {U Λ : Type*} [AddCommGroup U] [Module ℝ U]
    (R : AuditRecord U Λ) : Prop where
  A1 : AmplitudeHomogeneous R.I
  A2 : PassesDownstreamGate R.dependencyGraph
  A3 : R.zeroStatus = .total
  A4 : ScaleCritical R.scaling R.I

/-- Classification is deliberately small: it cannot represent an open bridge
as proved. -/
inductive Classification where
  | admissible
  | zeroLocusBlocked
  deriving DecidableEq, Repr

/-- Conservative classification from certified information only. -/
def classify {U Λ : Type*} [AddCommGroup U] [Module ℝ U]
    (R : AuditRecord U Λ) : Classification :=
  if R.zeroStatus = .total then .admissible else .zeroLocusBlocked

/-- Membership now means that all four certified obligations are available,
not merely that the zero-locus flag is total. -/
def InS {U Λ : Type*} [AddCommGroup U] [Module ℝ U]
    (R : AuditRecord U Λ) : Prop :=
  Nonempty (CertifiedObligations R)

/-- Every AuditRecord already carries A1, A2 and A4; zero totality is the final
condition needed to construct the complete certificate. -/
theorem certifiedObligations_iff_zeroTotal
    {U Λ : Type*} [AddCommGroup U] [Module ℝ U]
    (R : AuditRecord U Λ) :
    InS R ↔ R.zeroStatus = .total := by
  constructor
  · rintro ⟨h⟩
    exact h.A3
  · intro hzero
    exact ⟨{
      A1 := R.amplitudeLaw
      A2 := R.downstreamGate
      A3 := hzero
      A4 := R.scaleLaw
    }⟩

/-- Composition theorem: a concrete adapter record plus its remaining zero
obligation yields the complete A1-A4 certificate and admissible classification. -/
theorem adapter_to_classification
    {U Λ : Type*} [AddCommGroup U] [Module ℝ U]
    (R : AuditRecord U Λ) (hzero : R.zeroStatus = .total) :
    InS R ∧ classify R = .admissible := by
  constructor
  · exact (certifiedObligations_iff_zeroTotal R).2 hzero
  · simp [classify, hzero]

end MCore
