import MCore.FinalFail.MaterialDerived

namespace MCore.FinalFail.MaterialGlobalAssembly

open MCore.FinalFail.Semantic
open MCore.FinalFail.MaterialCalculus

universe uL uF uS uV uC uZ uE uT

/--
Seven typed material producers.  Each field carries an actual proof of the
corresponding positive semantic component.  This structure does not synthesize
any field; it only packages already-existing producers.
-/
structure SevenMaterialProducers
    (Language : Type uL)
    (InP InNP : Language → Prop)
    (SAT : Language)
    (Flow : Type uF)
    (Stabilizer : Type uS)
    (ActualNS : Flow → Prop)
    (Stabilizes : Stabilizer → Flow → Prop)
    (Variety : Type uV)
    (Class : Variety → Type uC)
    (Cycle : Variety → Type uZ)
    (SmoothProjective : Variety → Prop)
    (RationalHodge : {X : Variety} → Class X → Prop)
    (Realizes : {X : Variety} → Cycle X → Class X → Prop)
    (Curve : Type uE)
    (Realizable : Curve → Prop)
    (AnalyticOrder MordellWeilRank : Curve → Int)
    (RefinedFormula : Curve → Prop)
    (Theory : Type uT)
    (Genuine4D OSReconstructs PositiveMassGap : Theory → Prop) where
  riemann : MaterialProducer RiemannHypothesis
  beal : MaterialProducer (Nonempty BealUniversalGCDTarget)
  pvsnp :
    MaterialProducer
      (Nonempty (PvsNPSeparationTarget Language InP InNP SAT))
  navierStokes :
    MaterialProducer
      (Nonempty
        (NavierStokesStabilizationTarget
          Flow Stabilizer ActualNS Stabilizes))
  hodge :
    MaterialProducer
      (Nonempty
        (HodgeRealizationTarget
          Variety Class Cycle SmoothProjective RationalHodge Realizes))
  bsd :
    MaterialProducer
      (Nonempty
        (BSDRealizableTarget
          Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula))
  yangMills :
    MaterialProducer
      (Nonempty
        (YangMills4DGapTarget
          Theory Genuine4D OSReconstructs PositiveMassGap))

/-- Exact producer-to-root assembly. -/
def SevenMaterialProducers.toPositiveRoot
    {Language : Type uL}
    {InP InNP : Language → Prop}
    {SAT : Language}
    {Flow : Type uF}
    {Stabilizer : Type uS}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    {Variety : Type uV}
    {Class : Variety → Type uC}
    {Cycle : Variety → Type uZ}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    {Curve : Type uE}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    {Theory : Type uT}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (P :
      SevenMaterialProducers
        Language InP InNP SAT
        Flow Stabilizer ActualNS Stabilizes
        Variety Class Cycle SmoothProjective RationalHodge Realizes
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
        Theory Genuine4D OSReconstructs PositiveMassGap) :
    GlobalPositiveMaterialRoot
      Language InP InNP SAT
      Flow Stabilizer ActualNS Stabilizes
      Variety Class Cycle SmoothProjective RationalHodge Realizes
      Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
      Theory Genuine4D OSReconstructs PositiveMassGap :=
  {
    riemann := P.riemann.produce
    beal := P.beal.produce
    pvsnp := P.pvsnp.produce
    navierStokes := P.navierStokes.produce
    hodge := P.hodge.produce
    bsd := P.bsd.produce
    yangMills := P.yangMills.produce
  }

/-- Packaging a positive root back into seven typed producers loses no
mathematical information. -/
def SevenMaterialProducers.ofPositiveRoot
    {Language : Type uL}
    {InP InNP : Language → Prop}
    {SAT : Language}
    {Flow : Type uF}
    {Stabilizer : Type uS}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    {Variety : Type uV}
    {Class : Variety → Type uC}
    {Cycle : Variety → Type uZ}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    {Curve : Type uE}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    {Theory : Type uT}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (G :
      GlobalPositiveMaterialRoot
        Language InP InNP SAT
        Flow Stabilizer ActualNS Stabilizes
        Variety Class Cycle SmoothProjective RationalHodge Realizes
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
        Theory Genuine4D OSReconstructs PositiveMassGap) :
    SevenMaterialProducers
      Language InP InNP SAT
      Flow Stabilizer ActualNS Stabilizes
      Variety Class Cycle SmoothProjective RationalHodge Realizes
      Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
      Theory Genuine4D OSReconstructs PositiveMassGap :=
  {
    riemann := ⟨G.riemann⟩
    beal := ⟨G.beal⟩
    pvsnp := ⟨G.pvsnp⟩
    navierStokes := ⟨G.navierStokes⟩
    hodge := ⟨G.hodge⟩
    bsd := ⟨G.bsd⟩
    yangMills := ⟨G.yangMills⟩
  }

theorem producer_root_roundtrip
    {Language : Type uL}
    {InP InNP : Language → Prop}
    {SAT : Language}
    {Flow : Type uF}
    {Stabilizer : Type uS}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    {Variety : Type uV}
    {Class : Variety → Type uC}
    {Cycle : Variety → Type uZ}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    {Curve : Type uE}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    {Theory : Type uT}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (G :
      GlobalPositiveMaterialRoot
        Language InP InNP SAT
        Flow Stabilizer ActualNS Stabilizes
        Variety Class Cycle SmoothProjective RationalHodge Realizes
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
        Theory Genuine4D OSReconstructs PositiveMassGap) :
    (SevenMaterialProducers.ofPositiveRoot G).toPositiveRoot = G := by
  cases G
  rfl

/-- Any genuine seven-producer bundle forces the bookkeeping evidence aggregate
to be PROVED.  The converse is intentionally absent: metadata cannot generate
mathematical producers. -/
theorem producers_force_proved_evidence
    {Language : Type uL}
    {InP InNP : Language → Prop}
    {SAT : Language}
    {Flow : Type uF}
    {Stabilizer : Type uS}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    {Variety : Type uV}
    {Class : Variety → Type uC}
    {Cycle : Variety → Type uZ}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    {Curve : Type uE}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    {Theory : Type uT}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (P :
      SevenMaterialProducers
        Language InP InNP SAT
        Flow Stabilizer ActualNS Stabilizes
        Variety Class Cycle SmoothProjective RationalHodge Realizes
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
        Theory Genuine4D OSReconstructs PositiveMassGap) :
    (provedEvidenceVectorOfPositiveRoot P.toPositiveRoot).aggregate =
      EvidenceState.proved := by
  rfl

#print axioms MCore.FinalFail.MaterialGlobalAssembly.SevenMaterialProducers.toPositiveRoot
#print axioms MCore.FinalFail.MaterialGlobalAssembly.producer_root_roundtrip
#print axioms MCore.FinalFail.MaterialGlobalAssembly.producers_force_proved_evidence

end MCore.FinalFail.MaterialGlobalAssembly
