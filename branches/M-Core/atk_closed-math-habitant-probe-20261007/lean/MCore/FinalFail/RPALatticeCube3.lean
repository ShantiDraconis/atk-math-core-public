import MCore.FinalFail.RPALattice

namespace MCore.FinalFail.RPA

inductive EndpointAtom
  | open
  | closed
  deriving DecidableEq, Repr

abbrev EndpointWord := List EndpointAtom

def W_OPEN : EndpointWord := [.open]
def W_CLOSED : EndpointWord := [.closed]

def W_OPEN_CLOSED : EndpointWord := [.open, .closed]
def W_CLOSED_OPEN : EndpointWord := [.closed, .open]
def W_OPEN_OPEN : EndpointWord := [.open, .open]
def W_CLOSED_CLOSED : EndpointWord := [.closed, .closed]

def W_OPEN_OPEN_OPEN : EndpointWord := [.open, .open, .open]
def W_CLOSED_CLOSED_CLOSED : EndpointWord := [.closed, .closed, .closed]
def W_OPEN_OPEN_CLOSED : EndpointWord := [.open, .open, .closed]
def W_OPEN_CLOSED_OPEN : EndpointWord := [.open, .closed, .open]
def W_CLOSED_OPEN_OPEN : EndpointWord := [.closed, .open, .open]
def W_OPEN_CLOSED_CLOSED : EndpointWord := [.open, .closed, .closed]
def W_CLOSED_OPEN_CLOSED : EndpointWord := [.closed, .open, .closed]
def W_CLOSED_CLOSED_OPEN : EndpointWord := [.closed, .closed, .open]

def W_FULL : EndpointWord := [.open, .open, .closed, .closed]

def wordMultiplicity (w : EndpointWord) : EndpointMultiplicity :=
  w.foldl
    (fun s a =>
      match a with
      | .open => s + openAtom
      | .closed => s + closedAtom)
    ⟨0, 0⟩

def normalizeWord (w : EndpointWord) : CanonicalEndpointState :=
  normalizeMultiplicity (wordMultiplicity w)

@[simp] theorem norm_OPEN :
    normalizeWord W_OPEN = .open := by rfl

@[simp] theorem norm_CLOSED :
    normalizeWord W_CLOSED = .closed := by rfl

@[simp] theorem norm_OPEN_CLOSED :
    normalizeWord W_OPEN_CLOSED = .full := by rfl

@[simp] theorem norm_CLOSED_OPEN :
    normalizeWord W_CLOSED_OPEN = .full := by rfl

@[simp] theorem norm_OPEN_OPEN :
    normalizeWord W_OPEN_OPEN = .open := by rfl

@[simp] theorem norm_CLOSED_CLOSED :
    normalizeWord W_CLOSED_CLOSED = .closed := by rfl

@[simp] theorem norm_OPEN_OPEN_OPEN :
    normalizeWord W_OPEN_OPEN_OPEN = .open := by rfl

@[simp] theorem norm_CLOSED_CLOSED_CLOSED :
    normalizeWord W_CLOSED_CLOSED_CLOSED = .closed := by rfl

@[simp] theorem norm_OPEN_OPEN_CLOSED :
    normalizeWord W_OPEN_OPEN_CLOSED = .full := by rfl

@[simp] theorem norm_OPEN_CLOSED_OPEN :
    normalizeWord W_OPEN_CLOSED_OPEN = .full := by rfl

@[simp] theorem norm_CLOSED_OPEN_OPEN :
    normalizeWord W_CLOSED_OPEN_OPEN = .full := by rfl

@[simp] theorem norm_OPEN_CLOSED_CLOSED :
    normalizeWord W_OPEN_CLOSED_CLOSED = .full := by rfl

@[simp] theorem norm_CLOSED_OPEN_CLOSED :
    normalizeWord W_CLOSED_OPEN_CLOSED = .full := by rfl

@[simp] theorem norm_CLOSED_CLOSED_OPEN :
    normalizeWord W_CLOSED_CLOSED_OPEN = .full := by rfl

@[simp] theorem norm_FULL :
    normalizeWord W_FULL = .full := by rfl

def WordSemantics
    (OpenMath ClosedMath : Prop)
    (w : EndpointWord) : Prop :=
  CanonicalSemantics OpenMath ClosedMath (normalizeWord w)

theorem full_word_iff_global_external_certificate
    (OpenMath ClosedMath : Prop) :
    WordSemantics OpenMath ClosedMath W_FULL ↔
      GlobalExternalCertificate OpenMath ClosedMath := by
  rfl

theorem all_length3_mixed_words_are_full
    (OpenMath ClosedMath : Prop) :
    (WordSemantics OpenMath ClosedMath W_OPEN_OPEN_CLOSED ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_OPEN_CLOSED_OPEN ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_CLOSED_OPEN_OPEN ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_OPEN_CLOSED_CLOSED ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_CLOSED_OPEN_CLOSED ↔
      GlobalExternalCertificate OpenMath ClosedMath) ∧
    (WordSemantics OpenMath ClosedMath W_CLOSED_CLOSED_OPEN ↔
      GlobalExternalCertificate OpenMath ClosedMath) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

#print axioms MCore.FinalFail.RPA.norm_OPEN_OPEN
#print axioms MCore.FinalFail.RPA.norm_CLOSED_CLOSED
#print axioms MCore.FinalFail.RPA.norm_OPEN_OPEN_OPEN
#print axioms MCore.FinalFail.RPA.norm_CLOSED_CLOSED_CLOSED
#print axioms MCore.FinalFail.RPA.all_length3_mixed_words_are_full
#print axioms MCore.FinalFail.RPA.full_word_iff_global_external_certificate

end MCore.FinalFail.RPA
