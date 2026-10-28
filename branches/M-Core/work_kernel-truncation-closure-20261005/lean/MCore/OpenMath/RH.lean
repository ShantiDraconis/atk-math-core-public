import MCore.Canonical.Claim

namespace MCore.OpenMath.RH

def terminal : MCore.Canonical.ClaimRecord where
  id := "RH-F1-TERMINAL"
  lane := "RH"
  statement := "Produce an unconditional concrete vanishing/density witness sufficient for the frozen RH reduction chain."
  kind := .conjecture
  state := .openMath
  producer := some "ConcreteVanishingUpperBound / FiniteSpanApproximatesChi inhabitant"
  dependencies := ["validated finite-span/Vasyunin machinery", "kernel-audited reduction to RH"]
  reusable := false
  notes := "Metadata only: this record does not assert RH or the producer."

end MCore.OpenMath.RH
