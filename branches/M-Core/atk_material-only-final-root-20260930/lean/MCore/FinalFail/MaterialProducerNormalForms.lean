import MCore.FinalFail.DirectProducerCuts

namespace MCore.FinalFail.Semantic

/-!
# Material producer normal forms

These records are attack normal forms. They do not assert any missing theorem.
An equivalent normal form may replace the terminal producer. A sufficient
normal form is only an allowed stronger route and must project kernel-checkably
to the terminal target before promotion.
-/

inductive ReductionExactness where
  | equivalent
  | sufficient
  | splitExactComponents
  deriving DecidableEq, Repr

structure MaterialProducerPlan where
  problem : ProblemId
  terminalTarget : String
  attackNormalForm : String
  consumer : String
  exactness : ReductionExactness
  forbiddenSubstitute : String
  deriving Repr

def materialProducerPlans : List MaterialProducerPlan := [
  { problem := .riemann
    terminalTarget := "FiniteSpanApproximatesChi concreteGeneratorFamily"
    attackNormalForm := "prove DNLimit = 0 directly, or produce an explicit VanishingUpperBound/zero-residue estimate whose bound tends to zero"
    consumer := "finiteSpanApproximatesChi_iff_DNLimit_eq_zero -> DNToZero -> audited RH endpoint"
    exactness := .equivalent
    forbiddenSubstitute := "finite-N zero checks, numerical trend, or a new convergence hypothesis without a proof" },
  { problem := .beal
    terminalTarget := "GCDLowerBoundProducer"
    attackNormalForm := "exclude the residual primitive case gcd(a,gcd(b,c)) = 1 for every admissible BealData"
    consumer := "gcd lower bound -> CommonDivisor -> CommonPrime -> Beal endpoint"
    exactness := .equivalent
    forbiddenSubstitute := "reopening CommonPrime wrappers or conductor bookkeeping without eliminating the primitive residual case" },
  { problem := .pVsNP
    terminalTarget := "G21Pointwise"
    attackNormalForm := "for each fixed PolyDTMCandidate produce one explicit input x where CorrectAt SATTarget x fails"
    consumer := "G21Pointwise <-> P02Target <-> SAT not in P -> certified FinalExternal consumer"
    exactness := .equivalent
    forbiddenSubstitute := "literal fixed-point route, finite candidate table, or P01 machine wiring" },
  { problem := .navierStokes
    terminalTarget := "ActualNSToSignedGainCore"
    attackNormalForm := "from genuine ActualNS data produce theta < 1 and stretch(t) <= theta*nu*z(t) + C*y(t)^2"
    consumer := "SignedGainCore -> normalized SignedGainCertificate -> differential depletion margin -> regularity route"
    exactness := .sufficient
    forbiddenSubstitute := "DynamicCriticalGeometry/FullChain wrappers or fixed-delta assumptions already falsified by scaling" },
  { problem := .hodge
    terminalTarget := "genuine geometry binding + ConcreteAlgebraicityPayload"
    attackNormalForm := "for each genuine smooth projective X and rational Hodge class alpha, explicitly produce a rational finite combination of algebraic cycle classes equal to alpha"
    consumer := "ConcreteAlgebraicityPayload <-> endpoint-equivalent R2 payload -> Hodge endpoint"
    exactness := .equivalent
    forbiddenSubstitute := "empty-variety/constant-Qbar degenerate models or abstract payloads with no geometry binding" },
  { problem := .bsd
    terminalTarget := "genuine elliptic-curve domain + rank equality + refined leading-coefficient identity"
    attackNormalForm := "split on the same genuine EllipticCurveQ into (analytic rank = Mordell-Weil rank) and the refined period/regulator/Sha/Tamagawa/torsion identity"
    consumer := "rank component + refined component -> BSD endpoint"
    exactness := .splitExactComponents
    forbiddenSubstitute := "unrestricted abstract BSDArithmeticAnalyticData or curve-specific evidence promoted universally" },
  { problem := .yangMills
    terminalTarget := "genuine 4D physical binding + B60ConcretePhysicalAdapter/K30"
    attackNormalForm := "bind C/F/D/H/G/O to one genuine 4D realization and prove a uniform positive physical mass lower bound preserved through reconstruction/spectral transfer"
    consumer := "B60ConcretePhysicalAdapter -> K30 transfer -> positive spectral mass gap"
    exactness := .sufficient
    forbiddenSubstitute := "Unit/True degenerate models, phantom interfaces, or legacy zero-estimate witnesses" }
]

def materialProducerPlanCount : Nat := materialProducerPlans.length

theorem materialProducerPlanCount_eq_seven :
    materialProducerPlanCount = 7 := by
  decide

end MCore.FinalFail.Semantic
