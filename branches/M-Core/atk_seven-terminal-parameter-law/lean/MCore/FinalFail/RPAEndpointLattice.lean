import MCore.FinalFail.RPATransitionDuality

namespace MCore.FinalFail.RPA

/-!
# Dual endpoint lattice

Free multiplicity layer:
  n·OPEN + m·CLOSED

Idempotent quotient:
  ∅, OPEN, CLOSED, FULL

FULL is the maximal dual-endpoint state and is identified with the existing
RPA transition/final-root/global-certificate view.
-/

/-- Free multiplicity state before idempotence. -/
structure FreeEndpointState where
  openCount : Nat
  closedCount : Nat
  deriving DecidableEq, Repr

def freeEmpty : FreeEndpointState := ⟨0, 0⟩
def freeOpen : FreeEndpointState := ⟨1, 0⟩
def freeClosed : FreeEndpointState := ⟨0, 1⟩
def freeDual : FreeEndpointState := ⟨1, 1⟩
def freeOpenSq : FreeEndpointState := ⟨2, 0⟩
def freeClosedSq : FreeEndpointState := ⟨0, 2⟩
def freeOpenOpenClosed : FreeEndpointState := ⟨2, 1⟩
def freeOpenClosedClosed : FreeEndpointState := ⟨1, 2⟩
def freeFull22 : FreeEndpointState := ⟨2, 2⟩

def FreeEndpointState.add
    (a b : FreeEndpointState) : FreeEndpointState :=
  ⟨a.openCount + b.openCount, a.closedCount + b.closedCount⟩

theorem free_open_plus_closed :
    freeOpen.add freeClosed = freeDual := by
  rfl

theorem free_open_plus_open :
    freeOpen.add freeOpen = freeOpenSq := by
  rfl

theorem free_closed_plus_closed :
    freeClosed.add freeClosed = freeClosedSq := by
  rfl

theorem free_open_open_closed :
    freeOpenSq.add freeClosed = freeOpenOpenClosed := by
  rfl

theorem free_open_closed_closed :
    freeOpen.add freeClosedSq = freeOpenClosedClosed := by
  rfl

theorem free_two_two_full :
    freeOpenSq.add freeClosedSq = freeFull22 := by
  rfl

/-- Idempotent quotient: only presence/absence of each endpoint matters. -/
inductive CanonicalEndpointState where
  | empty
  | open
  | closed
  | full
  deriving DecidableEq, Repr

def normalizeFree (s : FreeEndpointState) : CanonicalEndpointState :=
  match s.openCount = 0, s.closedCount = 0 with
  | true, true => .empty
  | false, true => .open
  | true, false => .closed
  | false, false => .full

theorem normalize_empty :
    normalizeFree freeEmpty = .empty := by
  rfl

theorem normalize_open :
    normalizeFree freeOpen = .open := by
  rfl

theorem normalize_closed :
    normalizeFree freeClosed = .closed := by
  rfl

theorem normalize_dual :
    normalizeFree freeDual = .full := by
  rfl

theorem normalize_open_sq :
    normalizeFree freeOpenSq = .open := by
  rfl

theorem normalize_closed_sq :
    normalizeFree freeClosedSq = .closed := by
  rfl

theorem normalize_open_open_closed :
    normalizeFree freeOpenOpenClosed = .full := by
  rfl

theorem normalize_open_closed_closed :
    normalizeFree freeOpenClosedClosed = .full := by
  rfl

theorem normalize_two_two_full :
    normalizeFree freeFull22 = .full := by
  rfl

/-- Canonical idempotent join. -/
def CanonicalEndpointState.join :
    CanonicalEndpointState → CanonicalEndpointState → CanonicalEndpointState
  | .empty, x => x
  | x, .empty => x
  | .open, .open => .open
  | .closed, .closed => .closed
  | .full, _ => .full
  | _, .full => .full
  | .open, .closed => .full
  | .closed, .open => .full

theorem join_open_idempotent :
    CanonicalEndpointState.open.join .open = .open := by
  rfl

theorem join_closed_idempotent :
    CanonicalEndpointState.closed.join .closed = .closed := by
  rfl

theorem join_open_closed_full :
    CanonicalEndpointState.open.join .closed = .full := by
  rfl

theorem join_closed_open_full :
    CanonicalEndpointState.closed.join .open = .full := by
  rfl

theorem join_full_absorbing_left (x : CanonicalEndpointState) :
    CanonicalEndpointState.full.join x = .full := by
  cases x <;> rfl

theorem join_full_absorbing_right (x : CanonicalEndpointState) :
    x.join .full = .full := by
  cases x <;> rfl

/-- The maximal canonical state means both endpoint positions are present. -/
def FullEndpointPayload (OpenEndpoint ClosedEndpoint : Prop) : Prop :=
  Nonempty (DualEndpointState OpenEndpoint ClosedEndpoint)

theorem full_eq_dualEndpointState
    (OpenEndpoint ClosedEndpoint : Prop) :
    FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      Nonempty (DualEndpointState OpenEndpoint ClosedEndpoint) := by
  rfl

theorem full_eq_math
    (OpenEndpoint ClosedEndpoint : Prop) :
    FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      Math OpenEndpoint ClosedEndpoint := by
  exact (dualEndpointState_iff_transition OpenEndpoint ClosedEndpoint).trans Iff.rfl

theorem full_eq_finalRoot
    (OpenEndpoint ClosedEndpoint : Prop) :
    FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      FinalRoot OpenEndpoint ClosedEndpoint := by
  exact (dualEndpointState_iff_transition OpenEndpoint ClosedEndpoint).trans Iff.rfl

theorem full_eq_globalExternalCertificate
    (OpenEndpoint ClosedEndpoint : Prop) :
    FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      GlobalExternalCertificate OpenEndpoint ClosedEndpoint := by
  exact dual_endpoint_eq_global_external OpenEndpoint ClosedEndpoint

/--
Maximal canonical RPA state:
FULL = DUAL_ENDPOINT_STATE = MATH = FINAL_ROOT = GLOBAL_EXTERNAL_CERTIFICATE.
-/
theorem full_maximal_chain
    (OpenEndpoint ClosedEndpoint : Prop) :
    (FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      Nonempty (DualEndpointState OpenEndpoint ClosedEndpoint)) ∧
    (FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      Math OpenEndpoint ClosedEndpoint) ∧
    (FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      FinalRoot OpenEndpoint ClosedEndpoint) ∧
    (FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      GlobalExternalCertificate OpenEndpoint ClosedEndpoint) := by
  exact ⟨Iff.rfl,
    full_eq_math OpenEndpoint ClosedEndpoint,
    full_eq_finalRoot OpenEndpoint ClosedEndpoint,
    full_eq_globalExternalCertificate OpenEndpoint ClosedEndpoint⟩


/-! ## Ordered words through length three -/

/-- Ordered OPEN/CLOSED symbol. Order is retained before multiplicity collapse. -/
inductive EndpointAtom where
  | open
  | closed
  deriving DecidableEq, Repr

abbrev EndpointWord := List EndpointAtom

def evalWord : EndpointWord → FreeEndpointState
  | [] => freeEmpty
  | .open :: xs =>
      freeOpen.add (evalWord xs)
  | .closed :: xs =>
      freeClosed.add (evalWord xs)

def wO   : EndpointWord := [.open]
def wC   : EndpointWord := [.closed]

def wOO  : EndpointWord := [.open, .open]
def wOC  : EndpointWord := [.open, .closed]
def wCO  : EndpointWord := [.closed, .open]
def wCC  : EndpointWord := [.closed, .closed]

def wOOO : EndpointWord := [.open, .open, .open]
def wCCC : EndpointWord := [.closed, .closed, .closed]
def wOOC : EndpointWord := [.open, .open, .closed]
def wOCO : EndpointWord := [.open, .closed, .open]
def wCOO : EndpointWord := [.closed, .open, .open]
def wOCC : EndpointWord := [.open, .closed, .closed]
def wCOC : EndpointWord := [.closed, .open, .closed]
def wCCO : EndpointWord := [.closed, .closed, .open]

def wOOCC : EndpointWord := [.open, .open, .closed, .closed]

theorem eval_O :
    evalWord wO = ⟨1, 0⟩ := by rfl

theorem eval_C :
    evalWord wC = ⟨0, 1⟩ := by rfl

theorem eval_OO :
    evalWord wOO = ⟨2, 0⟩ := by rfl

theorem eval_OC :
    evalWord wOC = ⟨1, 1⟩ := by rfl

theorem eval_CO :
    evalWord wCO = ⟨1, 1⟩ := by rfl

theorem eval_CC :
    evalWord wCC = ⟨0, 2⟩ := by rfl

theorem eval_OOO :
    evalWord wOOO = ⟨3, 0⟩ := by rfl

theorem eval_CCC :
    evalWord wCCC = ⟨0, 3⟩ := by rfl

theorem eval_OOC :
    evalWord wOOC = ⟨2, 1⟩ := by rfl

theorem eval_OCO :
    evalWord wOCO = ⟨2, 1⟩ := by rfl

theorem eval_COO :
    evalWord wCOO = ⟨2, 1⟩ := by rfl

theorem eval_OCC :
    evalWord wOCC = ⟨1, 2⟩ := by rfl

theorem eval_COC :
    evalWord wCOC = ⟨1, 2⟩ := by rfl

theorem eval_CCO :
    evalWord wCCO = ⟨1, 2⟩ := by rfl

theorem eval_OOCC :
    evalWord wOOCC = ⟨2, 2⟩ := by rfl

/-- The 14 ordered words of lengths 1, 2 and 3 are pairwise enumerated. -/
def wordsUpToThree : List EndpointWord :=
  [wO, wC,
   wOO, wOC, wCO, wCC,
   wOOO, wOOC, wOCO, wOCC, wCOO, wCOC, wCCO, wCCC]

theorem wordsUpToThree_count :
    wordsUpToThree.length = 14 := by
  rfl

/-- Ordered paths remain distinct before quotienting. -/
theorem OOC_ne_OCO : wOOC ≠ wOCO := by decide
theorem OCO_ne_COO : wOCO ≠ wCOO := by decide
theorem OCC_ne_COC : wOCC ≠ wCOC := by decide
theorem COC_ne_CCO : wCOC ≠ wCCO := by decide

/-- Their free multiplicity images coincide exactly by counts. -/
theorem three_open_two_one_same_multiplicity :
    evalWord wOOC = evalWord wOCO ∧
    evalWord wOCO = evalWord wCOO := by
  exact ⟨rfl, rfl⟩

theorem three_closed_one_two_same_multiplicity :
    evalWord wOCC = evalWord wCOC ∧
    evalWord wCOC = evalWord wCCO := by
  exact ⟨rfl, rfl⟩

/-- Under idempotence all mixed words normalize to FULL. -/
theorem normalize_OOC_full :
    normalizeFree (evalWord wOOC) = .full := by rfl
theorem normalize_OCO_full :
    normalizeFree (evalWord wOCO) = .full := by rfl
theorem normalize_COO_full :
    normalizeFree (evalWord wCOO) = .full := by rfl
theorem normalize_OCC_full :
    normalizeFree (evalWord wOCC) = .full := by rfl
theorem normalize_COC_full :
    normalizeFree (evalWord wCOC) = .full := by rfl
theorem normalize_CCO_full :
    normalizeFree (evalWord wCCO) = .full := by rfl

theorem normalize_OOO_open :
    normalizeFree (evalWord wOOO) = .open := by rfl

theorem normalize_CCC_closed :
    normalizeFree (evalWord wCCC) = .closed := by rfl

/-- FULL witness requested explicitly as OPEN+OPEN+CLOSED+CLOSED. -/
theorem ordered_OOCC_is_freeFull22 :
    evalWord wOOCC = freeFull22 := by
  rfl

theorem ordered_OOCC_normalizes_FULL :
    normalizeFree (evalWord wOOCC) = .full := by
  rfl

/--
The ordered FULL word is the maximal certificate once both endpoint payloads
are supplied in the existing dual endpoint state.
-/
theorem ordered_FULL_eq_globalExternalCertificate
    (OpenEndpoint ClosedEndpoint : Prop) :
    FullEndpointPayload OpenEndpoint ClosedEndpoint ↔
      GlobalExternalCertificate OpenEndpoint ClosedEndpoint :=
  full_eq_globalExternalCertificate OpenEndpoint ClosedEndpoint


#print axioms MCore.FinalFail.RPA.free_open_plus_closed
#print axioms MCore.FinalFail.RPA.normalize_open_sq
#print axioms MCore.FinalFail.RPA.normalize_closed_sq
#print axioms MCore.FinalFail.RPA.normalize_two_two_full
#print axioms MCore.FinalFail.RPA.join_open_idempotent
#print axioms MCore.FinalFail.RPA.join_closed_idempotent
#print axioms MCore.FinalFail.RPA.full_maximal_chain

end MCore.FinalFail.RPA
