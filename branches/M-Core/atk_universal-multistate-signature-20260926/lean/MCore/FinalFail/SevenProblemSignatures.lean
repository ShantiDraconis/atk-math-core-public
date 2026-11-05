import MCore.FinalFail.ProblemSignature
import MCore.FinalFail.SevenLocalNuclei

namespace MCore.FinalFail

def signatureOf : ProblemId → ProblemSignature
  | .beal =>
      { direction := .inward, locality := .local,
        obstruction := .primitive, closure := .emptiness,
        scalar := .discrete, hasCompression := true, hasRetraction := false }
  | .navierStokes =>
      { direction := .bidirectional, locality := .localToGlobal,
        obstruction := .transfer, closure := .vanishing,
        scalar := .real, hasCompression := true, hasRetraction := true }
  | .hodge =>
      { direction := .outward, locality := .localToGlobal,
        obstruction := .algebraicity, closure := .emptiness,
        scalar := .complex, hasCompression := true, hasRetraction := true }
  | .pVsNP =>
      { direction := .bidirectional, locality := .global,
        obstruction := .complexity, closure := .emptiness,
        scalar := .discrete, hasCompression := true, hasRetraction := true }
  | .bsd =>
      { direction := .bidirectional, locality := .localToGlobal,
        obstruction := .rank, closure := .vanishing,
        scalar := .mixed, hasCompression := true, hasRetraction := true }
  | .riemann =>
      { direction := .inward, locality := .global,
        obstruction := .residue, closure := .vanishing,
        scalar := .complex, hasCompression := true, hasRetraction := false }
  | .yangMills =>
      { direction := .outward, locality := .localToGlobal,
        obstruction := .spectral, closure := .positivity,
        scalar := .mixed, hasCompression := true, hasRetraction := true }

theorem signature_obstruction_matches (p : ProblemId) :
    (signatureOf p).obstruction =
      match obstructionOf p with
      | .primitiveSolution => .primitive
      | .signedTransferDefect => .transfer
      | .nonAlgebraicHodgeClass => .algebraicity
      | .polynomialSATDecider => .complexity
      | .rankMismatch => .rank
      | .nonzeroDNLimit => .residue
      | .nonpositiveSpectralGap => .spectral := by
  cases p <;> rfl

theorem signature_assignment_injective : Function.Injective signatureOf := by
  intro a b h
  cases a <;> cases b <;> simp [signatureOf] at h ⊢

end MCore.FinalFail
