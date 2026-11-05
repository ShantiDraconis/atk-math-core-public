import MCore.FinalFail.ExactGapLedger

namespace MCore.FinalFail

structure IsolatedDelta where
  problem : String
  deltaStatement : String
  requiredMachinery : List String
  forbiddenShortcut : List String
  sourceAnchor : String
  deriving Repr

def isolatedDeltas : List IsolatedDelta := [
  { problem := "BEAL", deltaStatement := "primitive Beal solution -> contradiction/common divisor", requiredMachinery := ["primitive reduction", "genuine arithmetic producer"], forbiddenShortcut := ["assume CommonDivisor", "invent Frey/modularity bridge without theorem source"], sourceAnchor := "BealSpecification + K9/K10" },
  { problem := "POINCARE", deltaStatement := "faithful formal import of the historically closed chain to S3", requiredMachinery := ["formal 3-manifold endpoint", "verified known-proof dependencies"], forbiddenShortcut := ["PoincareResolved -> PoincareResolved", "True endpoint"], sourceAnchor := "positive-control source still to pin at theorem level" },
  { problem := "NAVIER_STOKES", deltaStatement := "independent compensator budget + quantitative signed cancellation + OPEN_CZ positive scale gain", requiredMachinery := ["T_cross tensor", "independent compensator", "signed CZ estimate"], forbiddenShortcut := ["C_N := -T_N", "absolute bound substituted for signed gain"], sourceAnchor := "audit/09_required_cancellations.md; audit/76_stretchFar_signed_blocking.md" },
  { problem := "HODGE", deltaStatement := "rational Hodge class -> rational span of algebraic cycle classes", requiredMachinery := ["general algebraicity/surjectivity"], forbiddenShortcut := ["store algebraic cycle inside input class"], sourceAnchor := "Hodge.lean; R3a frozen provenance" },
  { problem := "P_VS_NP", deltaStatement := "construct official-model language with genuine asymptotic not_in_p proof", requiredMachinery := ["official model match", "universal asymptotic lower bound"], forbiddenShortcut := ["finite C12 evidence -> universal lower bound", "witness supplied as hypothesis"], sourceAnchor := "EndpointCompression; ThreeTracks; K10" },
  { problem := "BSD", deltaStatement := "for every arithmetic-analytic datum, analyticOrderAtOne = mordellWeilRank", requiredMachinery := ["universal rank/order theorem"], forbiddenShortcut := ["particular curves -> all curves", "numerical approximation -> exact equality"], sourceAnchor := "K12; ThreeWorldClosure recovery" },
  { problem := "RIEMANN", deltaStatement := "concrete DNLimit=0 plus independently verified DNLimit=0 iff RH", requiredMachinery := ["exact vanishing estimate", "unconditional endpoint equivalence"], forbiddenShortcut := ["DNLimit approximately zero -> zero", "conditional bridge -> unconditional bridge"], sourceAnchor := "BackwardDenseEndpoint.lean; K8 ad3011f1..." },
  { problem := "YANG_MILLS", deltaStatement := "genuine 4D construction/OS reconstruction plus positive physical spectral gap", requiredMachinery := ["4D continuum construction", "OS/Hamiltonian identification", "spectral positivity"], forbiddenShortcut := ["inhabited abstract structure", "correlation decay alone -> physical mass gap"], sourceAnchor := "K21 0352c6af...; hardened physical interfaces" }
]

def deltaFor? (problem : String) : Option IsolatedDelta :=
  isolatedDeltas.find? (fun d => d.problem == problem)

end MCore.FinalFail
