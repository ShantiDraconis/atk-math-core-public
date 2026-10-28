import MCore.Canonical.Claim

namespace MCore.OpenMath.YM

def terminal : MCore.Canonical.ClaimRecord where
  id := "YM-F2-TERMINAL"
  lane := "YM"
  statement := "Construct the physical four-dimensional realization and a positive lower bound that remains uniform in the physical limit."
  kind := .conjecture
  state := .openMath
  producer := some "B6UniformLowerBound + physical-limit realization"
  dependencies := ["UV uniformity", "same-H bridge", "IR uniformity", "limit preservation"]
  reusable := false
  notes := "Finite regulated spectral gaps alone do not inhabit this producer."

end MCore.OpenMath.YM
