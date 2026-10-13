namespace MCore.FinalFail.RPA

/-!
# RPA confirmation duality

A generic, conjecture-independent formalization of the certification rule:

OPEN_MATH + CLOSED_MATH
  = OPEN_BRIDGE + CLOSED_BRIDGE
  = MATH
  = FINAL_ROOT
  = GLOBAL_EXTERNAL_CERTIFICATE

The equalities below are equalities of *views* of one confirmed transition.
They do not manufacture a mathematical endpoint.  A completed confirmation
contains both endpoint witnesses and an identity-preserving bridge.
-/

/-- The two endpoint positions are distinct even when their semantics are equivalent. -/
inductive EndpointRole where
  | openEndpoint
  | closedEndpoint
  deriving DecidableEq, Repr

theorem endpoint_roles_distinct :
    EndpointRole.openEndpoint ≠ EndpointRole.closedEndpoint := by
  decide

/-- Structural bridge between the open and closed propositions. -/
structure RPAFrame (OpenMath ClosedMath : Prop) : Prop where
  identityPreserved : OpenMath ↔ ClosedMath

/-- A certifiable RPA transition contains both endpoint witnesses and the bridge.

The structure is `Prop`-valued, so it cannot carry `EndpointRole` data fields
(Lean rejects data projections out of a `Prop`).  Every constructor in this
library used the fixed roles `.openEndpoint` / `.closedEndpoint`, so the roles
are recorded by the proof that those two fixed positions are distinct. -/
structure RPAConfirmation (OpenMath ClosedMath : Prop) : Prop where
  rolesDistinct : EndpointRole.openEndpoint ≠ EndpointRole.closedEndpoint
  openWitness : OpenMath
  closedWitness : ClosedMath
  frame : RPAFrame OpenMath ClosedMath

namespace RPAConfirmation

variable {OpenMath ClosedMath : Prop}

theorem source (h : RPAConfirmation OpenMath ClosedMath) : OpenMath :=
  h.openWitness

theorem destination (h : RPAConfirmation OpenMath ClosedMath) : ClosedMath :=
  h.closedWitness

theorem transition (h : RPAConfirmation OpenMath ClosedMath) :
    OpenMath ↔ ClosedMath :=
  h.frame.identityPreserved

/-- OPEN alone is not an RPA confirmation: a CLOSED witness is still required. -/
theorem open_requires_closed
    (hOpen : OpenMath)
    (hFrame : RPAFrame OpenMath ClosedMath) :
    RPAConfirmation OpenMath ClosedMath ↔ ClosedMath := by
  constructor
  · intro h
    exact h.closedWitness
  · intro hClosed
    exact ⟨endpoint_roles_distinct, hOpen, hClosed, hFrame⟩

/-- CLOSED alone is not an RPA confirmation: an OPEN witness is still required. -/
theorem closed_requires_open
    (hClosed : ClosedMath)
    (hFrame : RPAFrame OpenMath ClosedMath) :
    RPAConfirmation OpenMath ClosedMath ↔ OpenMath := by
  constructor
  · intro h
    exact h.openWitness
  · intro hOpen
    exact ⟨endpoint_roles_distinct, hOpen, hClosed, hFrame⟩

end RPAConfirmation

/-- Canonical dual-endpoint state: two distinct positions, two witnesses, one preserved identity. -/
abbrev DualEndpointState (OpenMath ClosedMath : Prop) : Prop :=
  RPAConfirmation OpenMath ClosedMath

/-- View 1: dual mathematical endpoints. -/
abbrev OpenClosedMath (OpenMath ClosedMath : Prop) : Prop :=
  RPAConfirmation OpenMath ClosedMath

/-- View 2: the same confirmed transition viewed as a bridge. -/
abbrev OpenClosedBridge (OpenMath ClosedMath : Prop) : Prop :=
  RPAConfirmation OpenMath ClosedMath

/-- View 3: the fixed mathematical identity carried by the bridge. -/
abbrev MathFixedPoint (OpenMath ClosedMath : Prop) : Prop :=
  RPAConfirmation OpenMath ClosedMath

/-- View 4: canonical root of the fixed-point transition. -/
abbrev FinalRoot (OpenMath ClosedMath : Prop) : Prop :=
  RPAConfirmation OpenMath ClosedMath

/-- View 5: externally auditable certificate of that root. -/
abbrev GlobalExternalCertificate (OpenMath ClosedMath : Prop) : Prop :=
  RPAConfirmation OpenMath ClosedMath

theorem dual_endpoint_state_iff_open_closed_math
    (OpenMath ClosedMath : Prop) :
    DualEndpointState OpenMath ClosedMath ↔
      OpenClosedMath OpenMath ClosedMath :=
  Iff.rfl

theorem five_views_same_identity
    (OpenMath ClosedMath : Prop) :
    (OpenClosedMath OpenMath ClosedMath ↔
      OpenClosedBridge OpenMath ClosedMath) ∧
    (OpenClosedBridge OpenMath ClosedMath ↔
      MathFixedPoint OpenMath ClosedMath) ∧
    (MathFixedPoint OpenMath ClosedMath ↔
      FinalRoot OpenMath ClosedMath) ∧
    (FinalRoot OpenMath ClosedMath ↔
      GlobalExternalCertificate OpenMath ClosedMath) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem global_certificate_projects_open
    {OpenMath ClosedMath : Prop}
    (h : GlobalExternalCertificate OpenMath ClosedMath) :
    OpenMath :=
  h.openWitness

theorem global_certificate_projects_closed
    {OpenMath ClosedMath : Prop}
    (h : GlobalExternalCertificate OpenMath ClosedMath) :
    ClosedMath :=
  h.closedWitness

theorem global_certificate_preserves_identity
    {OpenMath ClosedMath : Prop}
    (h : GlobalExternalCertificate OpenMath ClosedMath) :
    OpenMath ↔ ClosedMath :=
  h.frame.identityPreserved

/--
Fail-closed boundary: a frame/equivalence is not itself a completed external
certificate.  Completion requires the endpoint witnesses carried by
RPAConfirmation.
-/
theorem frame_plus_open_and_closed_closes
    {OpenMath ClosedMath : Prop}
    (hFrame : RPAFrame OpenMath ClosedMath)
    (hOpen : OpenMath)
    (hClosed : ClosedMath) :
    GlobalExternalCertificate OpenMath ClosedMath :=
  ⟨endpoint_roles_distinct, hOpen, hClosed, hFrame⟩

#print axioms MCore.FinalFail.RPA.endpoint_roles_distinct
#print axioms MCore.FinalFail.RPA.dual_endpoint_state_iff_open_closed_math
#print axioms MCore.FinalFail.RPA.five_views_same_identity
#print axioms MCore.FinalFail.RPA.global_certificate_projects_open
#print axioms MCore.FinalFail.RPA.global_certificate_projects_closed
#print axioms MCore.FinalFail.RPA.global_certificate_preserves_identity
#print axioms MCore.FinalFail.RPA.frame_plus_open_and_closed_closes

end MCore.FinalFail.RPA
