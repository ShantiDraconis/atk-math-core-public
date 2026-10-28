import MCore.V22.NodeLocator

namespace MCore.V22

inductive ExactBlockerKind where
  | hodgeAlgebraicityConstructor
  | bsdRankConstructor
  | bealCommonPrimeConstructor
  | pnpMaterialOrientation
  | rhClassicalZetaAdapter
  | rhCriticalLineProof
  | ymConcreteTheoryAdapter
  | ymExistenceMassGapProof
  | nsPointwiseDepletionFromActualNS
  | nsUniformizationBridge
  deriving DecidableEq, Repr

structure ExactBlocker where
  problem : ProblemId
  parent : Node
  kind : ExactBlockerKind
  expectedArtifact : String
  deriving Repr

def exactMathematicalBlockers : List ExactBlocker :=
  [
    { problem := .hodge
      parent := { problem := .hodge, stage := .middle }
      kind := .hodgeAlgebraicityConstructor
      expectedArtifact :=
        "forall smooth projective X and rational Hodge class alpha, construct rationalSpanOfCycles alpha" },
    { problem := .bsd
      parent := { problem := .bsd, stage := .middle }
      kind := .bsdRankConstructor
      expectedArtifact :=
        "forall BSDArithmeticAnalyticData d, prove BSDRankPart d" },
    { problem := .beal
      parent := { problem := .beal, stage := .middle }
      kind := .bealCommonPrimeConstructor
      expectedArtifact :=
        "forall BealData d, construct CommonPrime d.a d.b d.c" },
    { problem := .pVsNP
      parent := { problem := .pVsNP, stage := .middle }
      kind := .pnpMaterialOrientation
      expectedArtifact :=
        "either PolySATCertificate + SATCompletenessTransfer, or LowerBoundWitness P NP" },
    { problem := .riemann
      parent := { problem := .riemann, stage := .middle }
      kind := .rhClassicalZetaAdapter
      expectedArtifact :=
        "construct ClassicalZetaAdapter with exact zero_match and line_match" },
    { problem := .riemann
      parent := { problem := .riemann, stage := .middle }
      kind := .rhCriticalLineProof
      expectedArtifact :=
        "prove FinalEndpoint: every nontrivial zero lies on the critical line" },
    { problem := .yangMills
      parent := { problem := .yangMills, stage := .middle }
      kind := .ymConcreteTheoryAdapter
      expectedArtifact :=
        "construct ConcreteTheoryAdapter matching concrete existence, positivity, and mass-gap semantics" },
    { problem := .yangMills
      parent := { problem := .yangMills, stage := .middle }
      kind := .ymExistenceMassGapProof
      expectedArtifact :=
        "prove ExistsQuantumTheory and construct a positive HasMassGap witness" },
    { problem := .navierStokes
      parent := { problem := .navierStokes, stage := .middle }
      kind := .nsPointwiseDepletionFromActualNS
      expectedArtifact :=
        "derive PointwiseClosedDepletion from ActualNS without an oracle" },
    { problem := .navierStokes
      parent := { problem := .navierStokes, stage := .middle }
      kind := .nsUniformizationBridge
      expectedArtifact :=
        "promote pointwise positive depletion gaps to one uniform positive gap under justified NS hypotheses" }
  ]

theorem exact_mathematical_blocker_count :
    exactMathematicalBlockers.length = 10 := by
  rfl

def blockersFor (p : ProblemId) : List ExactBlocker :=
  exactMathematicalBlockers.filter (fun b => b.problem = p)

theorem rh_has_two_exact_blockers :
    (blockersFor .riemann).length = 2 := by
  native_decide

theorem ym_has_two_exact_blockers :
    (blockersFor .yangMills).length = 2 := by
  native_decide

theorem ns_has_two_exact_blockers :
    (blockersFor .navierStokes).length = 2 := by
  native_decide

theorem hodge_has_one_exact_blocker :
    (blockersFor .hodge).length = 1 := by
  native_decide

theorem bsd_has_one_exact_blocker :
    (blockersFor .bsd).length = 1 := by
  native_decide

theorem beal_has_one_exact_blocker :
    (blockersFor .beal).length = 1 := by
  native_decide

theorem pnp_has_one_exact_blocker :
    (blockersFor .pVsNP).length = 1 := by
  native_decide

end MCore.V22
