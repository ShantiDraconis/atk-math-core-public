import MCore.Canonical.Claim

namespace MCore.OpenMath.PNP

def terminal : MCore.Canonical.ClaimRecord where
  id := "PNP-F2-TERMINAL"
  lane := "PNP"
  statement := "Produce a genuine asymptotic SAT lower-bound witness sufficient for the frozen separation reduction."
  kind := .conjecture
  state := .openMath
  producer := some "CanonicalNotInPWitness / genuine SAT lower-bound producer"
  dependencies := ["P01 physical verifier construction", "P02/T10 encoding coverage", "uniform effective coverage"]
  reusable := false
  notes := "No fixed-point or wrapper is accepted as a substitute for the material lower bound."

end MCore.OpenMath.PNP
