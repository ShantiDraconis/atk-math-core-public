import MCore.Canonical.Claim

namespace MCore.Reuse

structure ReuseEntry where
  id : String
  canonicalModule : String
  purpose : String
  consumers : List String := []
  deriving Repr, DecidableEq

def registry : List ReuseEntry := [
  ⟨"NONEMPTY_TRANSPORT", "MCore.Reuse.Transport", "Transport a concrete inhabitant through an explicit function.", ["RH","PNP","NS","BSD","HODGE","YM","BEAL"]⟩,
  ⟨"IMPLICATION_COMPOSITION", "MCore.Reuse.Transport", "Compose already-proved implication edges without reopening their proofs.", ["RH","PNP","NS","BSD","HODGE","YM","BEAL"]⟩,
  ⟨"IFF_TRANSPORT", "MCore.Reuse.Transport", "Reuse a proved equivalence in either direction.", ["RH","PNP","NS","BSD","HODGE","YM","BEAL"]⟩
]

end MCore.Reuse
