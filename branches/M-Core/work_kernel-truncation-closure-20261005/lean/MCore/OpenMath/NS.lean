import MCore.Canonical.Claim

namespace MCore.OpenMath.NS

def terminal : MCore.Canonical.ClaimRecord where
  id := "NS-F7-TERMINAL"
  lane := "NS"
  statement := "Derive the strict a-priori budget/gain needed by the frozen global-regularity reduction from ActualNS data."
  kind := .conjecture
  state := .openMath
  producer := some "strict_budget_from_NSE / BulkTailProducer"
  dependencies := ["nontrivial harmonic-analysis bridge", "signed gain/depletion estimate"]
  reusable := false
  notes := "Fail-closed route objects are not inhabitants of this producer."

end MCore.OpenMath.NS
