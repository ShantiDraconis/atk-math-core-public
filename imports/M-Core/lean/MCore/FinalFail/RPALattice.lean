import MCore.FinalFail.RPAConfirmation

namespace MCore.FinalFail.RPA

/-- Free multiplicity state before imposing idempotence. -/
structure EndpointMultiplicity where
  openCount : Nat
  closedCount : Nat
  deriving DecidableEq, Repr

def EndpointMultiplicity.add
    (a b : EndpointMultiplicity) : EndpointMultiplicity :=
  ⟨a.openCount + b.openCount, a.closedCount + b.closedCount⟩

instance : Add EndpointMultiplicity := ⟨EndpointMultiplicity.add⟩

def openAtom : EndpointMultiplicity := ⟨1, 0⟩
def closedAtom : EndpointMultiplicity := ⟨0, 1⟩

@[simp] theorem open_plus_open :
    openAtom + openAtom = ⟨2, 0⟩ := rfl

@[simp] theorem closed_plus_closed :
    closedAtom + closedAtom = ⟨0, 2⟩ := rfl

@[simp] theorem open_plus_closed :
    openAtom + closedAtom = ⟨1, 1⟩ := rfl

/-- Idempotent quotient: only presence/absence of each endpoint remains. -/
inductive CanonicalEndpointState
  | empty
  | open
  | closed
  | full
  deriving DecidableEq, Repr

def normalizeMultiplicity (s : EndpointMultiplicity) : CanonicalEndpointState :=
  match s.openCount == 0, s.closedCount == 0 with
  | true, true => .empty
  | false, true => .open
  | true, false => .closed
  | false, false => .full

@[simp] theorem normalize_open :
    normalizeMultiplicity openAtom = .open := by
  rfl

@[simp] theorem normalize_closed :
    normalizeMultiplicity closedAtom = .closed := by
  rfl

@[simp] theorem normalize_open_open :
    normalizeMultiplicity (openAtom + openAtom) = .open := by
  rfl

@[simp] theorem normalize_closed_closed :
    normalizeMultiplicity (closedAtom + closedAtom) = .closed := by
  rfl

@[simp] theorem normalize_open_closed :
    normalizeMultiplicity (openAtom + closedAtom) = .full := by
  rfl

def CanonicalSemantics
    (OpenMath ClosedMath : Prop) :
    CanonicalEndpointState → Prop
  | .empty => True
  | .open => OpenMath
  | .closed => ClosedMath
  | .full => DualEndpointState OpenMath ClosedMath

abbrev Full (OpenMath ClosedMath : Prop) : Prop :=
  CanonicalSemantics OpenMath ClosedMath .full

theorem full_iff_dual_endpoint_state
    (OpenMath ClosedMath : Prop) :
    Full OpenMath ClosedMath ↔
      DualEndpointState OpenMath ClosedMath :=
  Iff.rfl

theorem full_iff_global_external_certificate
    (OpenMath ClosedMath : Prop) :
    Full OpenMath ClosedMath ↔
      GlobalExternalCertificate OpenMath ClosedMath :=
  Iff.rfl

/-- Under idempotence, every positive OPEN multiplicity collapses to OPEN,
every positive CLOSED multiplicity collapses to CLOSED, and joint presence
collapses to FULL. -/
theorem normalize_positive_positive_full
    (n m : Nat)
    (hn : n ≠ 0)
    (hm : m ≠ 0) :
    normalizeMultiplicity ⟨n, m⟩ = .full := by
  have h1 : (n == 0) = false := by
    cases n with
    | zero => exact absurd rfl hn
    | succ k => rfl
  have h2 : (m == 0) = false := by
    cases m with
    | zero => exact absurd rfl hm
    | succ k => rfl
  unfold normalizeMultiplicity
  rw [h1, h2]

#print axioms MCore.FinalFail.RPA.normalize_positive_positive_full
#print axioms MCore.FinalFail.RPA.full_iff_dual_endpoint_state
#print axioms MCore.FinalFail.RPA.full_iff_global_external_certificate

end MCore.FinalFail.RPA
