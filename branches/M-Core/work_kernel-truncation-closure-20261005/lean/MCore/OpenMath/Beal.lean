import MCore.Canonical.Claim

namespace MCore.OpenMath.Beal

def terminal : MCore.Canonical.ClaimRecord where
  id := "BEAL-F6-TERMINAL"
  lane := "BEAL"
  statement := "Exclude the primitive gcd-one case for every admissible Beal datum."
  kind := .conjecture
  state := .openMath
  producer := some "UniversalTripleGCDLowerBound / primitive-case exclusion"
  dependencies := ["validated splitter/K9/K10/quartic-Denes consequences where applicable"]
  reusable := false
  notes := "Subclass elimination is not universal primitive-case exclusion."

end MCore.OpenMath.Beal
