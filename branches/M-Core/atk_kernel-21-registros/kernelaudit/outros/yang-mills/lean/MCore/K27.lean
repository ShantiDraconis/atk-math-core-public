import MCore.K26

namespace MCore

/-- K27 isolates the limit problem: a positive gap at each regulator is weaker
than one common positive lower bound that survives both limits. -/
structure K27RegulatedGapSystem where
  Cutoff : Type
  Volume : Type
  Gap : Type
  admissible : Cutoff → Volume → Prop
  gapAt : Cutoff → Volume → Gap
  positive : Gap → Prop
  lowerBoundedBy : Gap → Gap → Prop

structure K27PointwisePositiveGap (S : K27RegulatedGapSystem) where
  positiveAt : ∀ a V, S.admissible a V → S.positive (S.gapAt a V)

structure K27UniformPositiveGap (S : K27RegulatedGapSystem) where
  commonGap : S.Gap
  commonGapPositive : S.positive commonGap
  uniformLowerBound : ∀ a V, S.admissible a V →
    S.lowerBoundedBy (S.gapAt a V) commonGap

/-- Continuum and thermodynamic control are separate from pointwise positivity. -/
structure K27LimitControl (S : K27RegulatedGapSystem) where
  continuumLimitControlled : Prop
  thermodynamicLimitControlled : Prop
  uniformGapPreserved : K27UniformPositiveGap S →
    continuumLimitControlled →
    thermodynamicLimitControlled → Prop

structure K27LimitWitness
    (S : K27RegulatedGapSystem)
    (U : K27UniformPositiveGap S)
    (L : K27LimitControl S) where
  continuum : L.continuumLimitControlled
  thermodynamic : L.thermodynamicLimitControlled
  preservation : L.uniformGapPreserved U continuum thermodynamic

structure K27ToFrontierBridge
    (F : K20ScientificFrontier)
    (S : K27RegulatedGapSystem)
    (U : K27UniformPositiveGap S)
    (L : K27LimitControl S)
    (W : K27LimitWitness S U L) where
  regulatedGapFeeds : F.uniformRegulatedGap
  continuumFeeds : F.continuumLimitControl
  thermodynamicFeeds : F.thermodynamicLimitControl
  preservationFeeds : F.gapPreservedUnderLimits

theorem k27_bridge_builds_limit_block
    {F : K20ScientificFrontier}
    {S : K27RegulatedGapSystem}
    {U : K27UniformPositiveGap S}
    {L : K27LimitControl S}
    {W : K27LimitWitness S U L}
    (B : K27ToFrontierBridge F S U L W) : K22LimitBlock F := {
  uniformRegulatedGap := B.regulatedGapFeeds
  continuumLimitControl := B.continuumFeeds
  thermodynamicLimitControl := B.thermodynamicFeeds
  gapPreservedUnderLimits := B.preservationFeeds
}

theorem k27_target_still_open :
    k6_dependency.target.status = .openBridge := k26_target_still_open

theorem k27_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) := k26_no_promotion

end MCore
