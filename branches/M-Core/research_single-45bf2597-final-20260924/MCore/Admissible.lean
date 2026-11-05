import MCore.A1Amplitude
import MCore.A2SelfRef
import MCore.A3Zero
import MCore.A4Scale

namespace MCore

/-- An adapter may enter S only by exposing all four audit obligations.
A1 is deliberately an obstruction flag rather than an assumption: degree-one
amplitude homogeneity plus a positive witness proves failure of a universal
fixed gap on an amplitude-unbounded class. -/
structure AuditRecord (U Λ : Type*) [AddCommGroup U] [Module ℝ U] where
  I : U → ℝ
  scaling : Scaling U Λ
  dependencyGraph : Graph
  amplitudeLaw : AmplitudeHomogeneous I
  selfRefGate : PassesSelfRefGate dependencyGraph
  zeroStatus : ZeroLocusStatus
  scaleLaw : ScaleCritical scaling I

/-- Membership is intentionally conservative: zero-locus totality is required.
Problem adapters can weaken/replace this only by proving a regularized total
extension and then constructing a new record for that extension. -/
def InS {U Λ : Type*} [AddCommGroup U] [Module ℝ U]
    (R : AuditRecord U Λ) : Prop :=
  R.zeroStatus = .total

end MCore
