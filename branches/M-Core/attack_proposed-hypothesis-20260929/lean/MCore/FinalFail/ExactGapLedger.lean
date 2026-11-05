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
  { problem := "BEAL", statement := "primitive/common-gcd=1 Beal equation -> contradiction; equivalently every BealData has a nontrivial common divisor", resolution := .nonexistence, state := .openMath, source := "m-core-beal/lean/MCore/BealSpecification.lean + K9/K10", provenance := "K6 frozen 434d6b7b...; K9 frozen e3b8598a..." },
  { problem := "POINCARE", statement := "faithfully import the known geometrization/Ricci-flow-with-surgery chain through recognition M ~= S3", resolution := .elimination, state := .historicallySolvedToAudit, source := "positive-control import pending exact theorem-level formal source", provenance := "historically solved; not counted as a new FINAL_PROOF result" },
  { problem := "NAVIER_STOKES", statement := "construct a legitimate compensator with independent quantitative budget and prove signed far-field direction-field cancellation with positive scale gain", resolution := .vanishing, state := .openMath, source := "navier-stokes-critical-barrier-audit/audit/76_stretchFar_signed_blocking.md + audit/09_required_cancellations.md", provenance := "fail-proof run 35565581964 GREEN; no endpoint promotion" },
  { problem := "HODGE", statement := "for every smooth projective X and rational Hodge class alpha, produce rational span of algebraic cycle classes", resolution := .quotientZero, state := .openMath, source := "m-core-hodge Hodge.lean + R3a provenance", provenance := "R3a frozen/audited reduction; general algebraicity remains open" },
  { problem := "P_VS_NP", statement := "produce a genuine asymptotic SAT lower bound in the fixed official model yielding not_in_p", resolution := .separation, state := .openMath, source := "m-core-p-vs-np EndpointCompression/ThreeTracks/K10", provenance := "historical triadic source recovered and hash-pinned; ApproximationBridge remains open" },
  { problem := "BSD", statement := "prove universally analyticOrderAtOne = mordellWeilRank; full BSD additionally needs the leading-coefficient arithmetic identity", resolution := .equality, state := .openMath, source := "m-core-bsd K12 + ThreeWorldClosure/NumericClasses recovery", provenance := "certified architecture preserves substantive rank equality as open" },
  { problem := "RIEMANN", statement := "prove concrete DNLimit=0 and independently prove/audit DNLimit=0 iff RiemannHypothesis", resolution := .bridgeAndVanishing, state := .openMath, source := "m-core-riemann/BackwardDenseEndpoint.lean", provenance := "K8 GREEN run 35565114760 SHA ad3011f1...; K8 not to be redone" },
  { problem := "YANG_MILLS", statement := "construct genuine 4D continuum theory with OS reconstruction/Hamiltonian identification and prove a positive spectral mass gap", resolution := .positivity, state := .openMath, source := "m-core-yang-mills hardened physical interfaces + K21/K14", provenance := "K21 GREEN 0352c6af...; fail-proof 35518892629 forbids trivial physical interfaces" }
]

def openFinalProblems : Nat :=
  exactGaps.foldl (fun n g => if g.state = .openMath then n + 1 else n) 0

theorem openFinalProblems_eq_seven : openFinalProblems = 7 := by decide

end MCore.FinalFail
