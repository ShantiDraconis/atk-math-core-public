import MCore.Canonical.Claim

namespace MCore.OpenMath.Hodge

def terminal : MCore.Canonical.ClaimRecord where
  id := "HODGE-F4-TERMINAL"
  lane := "HODGE"
  statement := "Construct the universal algebraic-cycle realization of rational Hodge classes required by the frozen reduction."
  kind := .conjecture
  state := .openMath
  producer := some "ConcreteAlgebraicityPayload"
  dependencies := ["concrete realization map", "cycle-class compatibility"]
  reusable := false
  notes := "An assumed realization field is not accepted as a producer."

end MCore.OpenMath.Hodge
