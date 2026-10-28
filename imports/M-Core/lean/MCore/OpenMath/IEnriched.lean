import Mathlib

namespace MCore.OpenMath.IEnriched

/-- An enriched local resolution state.  The fields are mathematical data;
no claim is made that they are uniquely determined by a quotient. -/
structure State where
  value : ℝ
  tension : ℝ
  compression : ℝ
  flow : ℝ → ℝ
  vector : ℝ → ℝ
  precision : ℝ → ℝ

/-- The classical projection forgets the extra state and retains the resolved value. -/
def resolve (s : State) : ℝ := s.value

/-- A quotient flow away from zeros of the denominator. -/
noncomputable def quotientFlow (f g : ℝ → ℝ) (x : ℝ) : ℝ := f x / g x

/-- Canonical state attached to a proved limit.  Tension/compression/vector/precision
are explicit observables rather than hidden semantics. -/
noncomputable def ofLimit (f g : ℝ → ℝ) (L : ℝ) : State where
  value := L
  tension := 0
  compression := 0
  flow := quotientFlow f g
  vector := fun x => quotientFlow f g x - L
  precision := fun x => |quotientFlow f g x - L|

@[simp] theorem resolve_ofLimit (f g : ℝ → ℝ) (L : ℝ) :
    resolve (ofLimit f g L) = L := rfl

/-- Kernel-level compatibility theorem: whenever the classical quotient tends to L,
the enriched state's projection is L and its precision observable tends to zero. -/
theorem limit_resolution_compatible
    (f g : ℝ → ℝ) (a L : ℝ)
    (hlim : Filter.Tendsto (fun x => f x / g x) (nhdsWithin a {a}ᶜ) (nhds L)) :
    resolve (ofLimit f g L) = L ∧
      Filter.Tendsto (fun x => (ofLimit f g L).precision x)
        (nhdsWithin a {a}ᶜ) (nhds 0) := by
  constructor
  · rfl
  · have hsub : Filter.Tendsto (fun x => f x / g x - L)
        (nhdsWithin a {a}ᶜ) (nhds 0) := by
      simpa using hlim.sub_const L
    simpa [ofLimit, quotientFlow] using hsub.abs

/-- Fail-closed L'Hospital bridge: the analytic theorem is supplied as a proved
classical limit hypothesis; this layer certifies preservation by the enriched state.
It does not manufacture L'Hospital's hypotheses. -/
theorem lHospital_resolution_bridge
    (f g : ℝ → ℝ) (a L : ℝ)
    (hLHospital :
      Filter.Tendsto (fun x => f x / g x) (nhdsWithin a {a}ᶜ) (nhds L)) :
    resolve (ofLimit f g L) = L :=
  (limit_resolution_compatible f g a L hLHospital).1

/-- Completeness is deliberately scoped: all information declared to belong to a
State is recoverable from the state itself.  This is not a claim of total analytic
information about arbitrary functions. -/
def Observables (s : State) :=
  (s.value, s.tension, s.compression, s.flow, s.vector, s.precision)

theorem observables_complete (s t : State)
    (h : Observables s = Observables t) : s = t := by
  cases s
  cases t
  simp_all [Observables]

end MCore.OpenMath.IEnriched
