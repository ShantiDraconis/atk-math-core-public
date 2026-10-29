import MCore.FinalFail.Semantic.Riemann
import MCore.FinalFail.Semantic.Beal
import MCore.FinalFail.Semantic.PvsNP
import MCore.FinalFail.Semantic.NavierStokes
import MCore.FinalFail.Semantic.Hodge
import MCore.FinalFail.Semantic.BSD
import MCore.FinalFail.Semantic.YangMills

namespace MCore.FinalFail.Semantic

/-!
# Accepted semantic activation

These theorems do one thing only: convert an explicitly accepted mathematical
hypothesis into the exact semantic target already chosen for that lane.

They do not create any external theorem.  Their value is that downstream ATK
work can consume the classical-shaped target directly instead of repeatedly
unpacking the accepted hypothesis.
-/

theorem accepted_beal_produces_semantic_inhabitant
    (h : ∀ d : BealEquationData,
      1 < Nat.gcd d.a (Nat.gcd d.b d.c)) :
    Nonempty BealUniversalGCDTarget :=
  ⟨{ commonGCD := h }⟩

theorem accepted_pvsnp_produces_semantic_inhabitant
    {Language : Type u}
    {InP InNP : Language → Prop}
    {SAT : Language}
    (hNP : InNP SAT)
    (hNotP : ¬ InP SAT) :
    Nonempty (PvsNPSeparationTarget Language InP InNP SAT) :=
  ⟨{ sat_in_np := hNP, sat_not_in_p := hNotP }⟩

theorem accepted_ns_produces_semantic_inhabitant
    {Flow : Type u} {Stabilizer : Type v}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    (component : Stabilizer)
    (h : ∀ u, ActualNS u → Stabilizes component u) :
    Nonempty
      (NavierStokesStabilizationTarget
        Flow Stabilizer ActualNS Stabilizes) :=
  ⟨{ component := component, controls := h }⟩

theorem accepted_hodge_produces_semantic_inhabitant
    {Variety : Type u}
    {Class : Variety → Type v}
    {Cycle : Variety → Type w}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    (h :
      ∀ X, SmoothProjective X →
        ∀ α : Class X, RationalHodge α →
          ∃ Z : Cycle X, Realizes Z α) :
    Nonempty
      (HodgeRealizationTarget
        Variety Class Cycle SmoothProjective RationalHodge Realizes) :=
  ⟨{ realize := h }⟩

theorem accepted_bsd_produces_semantic_inhabitant
    {Curve : Type u}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    (hRank :
      ∀ E, Realizable E → AnalyticOrder E = MordellWeilRank E)
    (hRefined :
      ∀ E, Realizable E → RefinedFormula E) :
    Nonempty
      (BSDRealizableTarget
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula) :=
  ⟨{ rankEquality := hRank, refined := hRefined }⟩

theorem accepted_ym_produces_semantic_inhabitant
    {Theory : Type u}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (theory : Theory)
    (h4D : Genuine4D theory)
    (hOS : OSReconstructs theory)
    (hGap : PositiveMassGap theory) :
    Nonempty
      (YangMills4DGapTarget
        Theory Genuine4D OSReconstructs PositiveMassGap) :=
  ⟨{
    theory := theory
    genuine4D := h4D
    reconstructs := hOS
    positiveGap := hGap
  }⟩

/-- Administrative count for the accepted-hypothesis universe only.
This is deliberately separate from the unconditional classical producer count. -/
def assumedSemanticLaneCount : Nat := 7

theorem assumedSemanticLaneCount_eq_seven :
    assumedSemanticLaneCount = 7 := by
  rfl

end MCore.FinalFail.Semantic
