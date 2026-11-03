import MCore.Audit.MasterClaims

namespace MCore.Audit

structure DependencyEdge where
  upstream : String
  downstream : String
  relation : String
  frozen : Bool := false
  deriving Repr, DecidableEq

def dependencyEdges : List DependencyEdge := [
  ⟨"RH-SUPPORT", "RH-F1-TERMINAL", "validated support feeds exact terminal producer", false⟩,
  ⟨"PNP-P01", "PNP-F2-TERMINAL", "physical verifier construction", false⟩,
  ⟨"PNP-P02-T10", "PNP-F2-TERMINAL", "encoding/lower-bound support", false⟩,
  ⟨"NS-HARMONIC", "NS-F7-TERMINAL", "harmonic-analysis bridge", false⟩,
  ⟨"BSD-NORMALIZATION", "BSD-F5-RANK", "canonical normalization", false⟩,
  ⟨"BSD-NORMALIZATION", "BSD-F5-REFINED", "canonical normalization", false⟩,
  ⟨"HODGE-REALIZATION", "HODGE-F4-TERMINAL", "concrete cycle realization", false⟩,
  ⟨"YM-UNIFORM-LIMIT", "YM-F2-TERMINAL", "uniform positive-gap preservation", false⟩,
  ⟨"BEAL-PRIMITIVE", "BEAL-F6-TERMINAL", "primitive-case exclusion", false⟩
]

end MCore.Audit
