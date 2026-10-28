import MCore.V21.ClosedChain

namespace MCore.V21

/-- Where a problem-specific closure is achieved relative to the M-Core
    process. The site is descriptive; it never substitutes for a proof. -/
inductive ClosureSite where
  | leftBoundary
  | interior
  | rightBoundary
  deriving DecidableEq, Repr

/-- Heterogeneous package accepted by the closed core.
    Every value of this type already contains a TargetCertificate. -/
structure PackedClosure where
  problemId : String
  site : ClosureSite
  Start : Prop
  Middle : Prop
  Final : Prop
  certificate : TargetCertificate Start Middle Final

/-- The closed locus of M-Core is the type of already-verified closures.
    M-Core does not manufacture the mathematical closure here; it receives it. -/
abbrev CoreClosedLocus := PackedClosure

/-- The central absorption operator. Every verified problem closure, whether
    obtained at the left boundary, interior, or right boundary, is normalized
    into the same closed locus. -/
def absorb
    {Start Middle Final : Prop}
    (problemId : String)
    (site : ClosureSite)
    (cert : TargetCertificate Start Middle Final) :
    CoreClosedLocus :=
  { problemId := problemId
    site := site
    Start := Start
    Middle := Middle
    Final := Final
    certificate := cert }

/-- The identity of the closed core is literally closed: once an object is in
    CoreClosedLocus, applying the core identity does not change it. -/
def coreIdentity (c : CoreClosedLocus) : CoreClosedLocus := c

theorem coreIdentity_fixed (c : CoreClosedLocus) :
    coreIdentity c = c := rfl

theorem PackedClosure.endpoint (c : PackedClosure) :
    c.Start → c.Final :=
  c.certificate.endpoint

/-- Re-absorbing a closed object through the identity layer preserves its
    endpoint proof. -/
theorem closed_locus_stable (c : CoreClosedLocus) :
    c.Start → c.Final :=
  c.endpoint

end MCore.V21
