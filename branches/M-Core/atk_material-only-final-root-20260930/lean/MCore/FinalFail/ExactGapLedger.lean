import MCore.FinalFail.SevenLocalNuclei

namespace MCore.FinalFail

inductive GapState where
  | proved | historicallySolvedToAudit | openMath | externalBridge
  deriving DecidableEq, Repr

inductive ResolutionShape where
  | nonexistence | elimination | vanishing | quotientZero
  | separation | equality | bridgeAndVanishing | positivity
  deriving DecidableEq, Repr

structure ExactGap where
  problem : String
  statement : String
  resolution : ResolutionShape
  state : GapState
  source : String
  provenance : String
  deriving Repr

def exactGaps : List ExactGap := [
  { problem := "BEAL", statement := "GCDLowerBoundProducer: forall d : BealData, 1 < gcd(d.a,gcd(d.b,d.c)); equivalently exclude the admissible primitive gcd=1 residual case", resolution := .nonexistence, state := .openMath, source := "m-core-beal frozen/gcd-lower-bound-producer-green-d6fe130c", provenance := "bealConjecture_iff_gcdLowerBoundProducer; wrappers are downstream only" },
  { problem := "POINCARE", statement := "faithfully import the known geometrization/Ricci-flow-with-surgery chain through recognition M ~= S3", resolution := .elimination, state := .historicallySolvedToAudit, source := "positive-control import pending exact theorem-level formal source", provenance := "historically solved; not counted as a new FINAL_PROOF result" },
  { problem := "NAVIER_STOKES", statement := "construct ActualNSToSignedGainCore on genuine flow-derived EnstrophyData: theta < 1 and stretch(t) <= theta*nu*z(t) + C*y(t)^2", resolution := .vanishing, state := .openMath, source := "navier-stokes-critical-barrier-audit frozen/ns-signed-gain-core-green-df808543", provenance := "SignedGainCore <-> normalized certificate at Nonempty level; downstream differential budget already certified" },
  { problem := "HODGE", statement := "on genuine smooth projective geometry, construct ConcreteAlgebraicityPayload universally: every rational Hodge class is a rational finite combination of algebraic cycle classes", resolution := .quotientZero, state := .openMath, source := "m-core-hodge frozen/h01-minimal-forward-payload-green-42eaf7d4", provenance := "ConcreteAlgebraicityPayload <-> TrivialQbarR2Payload on the intended semantics; degenerate empty models forbidden" },
  { problem := "P_VS_NP", statement := "G21Pointwise: for every fixed PolyDTMCandidate produce an input on which CorrectAt SATTarget fails; equivalently SAT is not in P in the bound official model", resolution := .separation, state := .openMath, source := "m-core-p-vs-np P02G21G22Attack + FinalExternalTwoGap", provenance := "P01 is mechanical closure and is not counted as OPEN_MATH; G2.2/G3/final wiring already closed" },
  { problem := "BSD", statement := "on the same genuine EllipticCurveQ domain prove (1) analytic rank = Mordell-Weil rank and (2) the refined leading-coefficient period/regulator/Sha/Tamagawa/torsion identity", resolution := .equality, state := .openMath, source := "m-core-bsd realizable-domain firewall + BSD rank/refined interfaces", provenance := "unrestricted BSDArithmeticAnalyticData forall was counter-audited; curve-specific evidence cannot universalize" },
  { problem := "RIEMANN", statement := "construct FiniteSpanApproximatesChi concreteGeneratorFamily; certified equivalent normal form is DNLimit = 0 / DNToZero", resolution := .bridgeAndVanishing, state := .openMath, source := "m-core-riemann frozen/nb-zero-limit-density-equivalence-green-d6a291b4", provenance := "finiteSpanApproximatesChi_iff_DNLimit_eq_zero; BCF/zero-residue is only a sufficient attack route" },
  { problem := "YANG_MILLS", statement := "bind one genuine 4D physical realization to C/F/D/H/G/O and construct Nonempty (B60ConcretePhysicalAdapter C F D H G O), yielding the K30 positive spectral-gap transfer", resolution := .positivity, state := .openMath, source := "m-core-yang-mills B60ConcretePhysicalAdapter + K30", provenance := "degenerate Unit/True and phantom-interface models are explicitly non-promotable" }
]

def openFinalProblems : Nat :=
  exactGaps.foldl (fun n g => if g.state = .openMath then n + 1 else n) 0

theorem openFinalProblems_eq_seven : openFinalProblems = 7 := by decide

end MCore.FinalFail
