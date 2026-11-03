import MCore.MaterialMath.OperatorLaws

namespace MCore.MaterialMath

universe uL uF uS uV uC uZ uE uT

/--
A tri-state kernel becomes mathematically relevant to the seven-lane root only
through exact problem-specific adapters.  The tri-state algebra itself is
unconditional; the seven adapter fields are the remaining mathematical
obligations.
-/
abbrev TriStateTerminalAdapters
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
    (Genuine4D OSReconstructs PositiveMassGap : Theory → Prop) :=
  TerminalMaterialAdapters
    (TriNumber ℝ)
    Language InP InNP SAT
    Flow Stabilizer ActualNS Stabilizes
    Variety Class Cycle SmoothProjective RationalHodge Realizes
    Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
    Theory Genuine4D OSReconstructs PositiveMassGap

/--
Exact closure theorem for the user's three-state material number.

No extra mathematical claim is hidden here: once the seven exact adapters are
constructed, every explicit TriNumber state produces the positive global root.
-/
theorem triState_closes_global_root
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
    (A :
      TriStateTerminalAdapters
        Language InP InNP SAT
        Flow Stabilizer ActualNS Stabilizes
        Variety Class Cycle SmoothProjective RationalHodge Realizes
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
        Theory Genuine4D OSReconstructs PositiveMassGap)
    (x : TriNumber ℝ) :
    MCore.FinalFail.Semantic.GlobalPositiveMaterialRoot
      Language InP InNP SAT
      Flow Stabilizer ActualNS Stabilizes
      Variety Class Cycle SmoothProjective RationalHodge Realizes
      Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
      Theory Genuine4D OSReconstructs PositiveMassGap :=
  A.toGlobalPositiveRoot x

/--
Rotation invariance gives three equivalent phase presentations of the same
material state.  It does not manufacture any terminal adapter.
-/
theorem triState_three_phase_orbit
    (x : TriNumber ℝ) :
    TriNumber.rotate (TriNumber.rotate (TriNumber.rotate x)) = x :=
  TriNumber.rotate_three x

/--
Balanced tri-states are precisely the fixed points of the order-three phase
rotation.  This is an unconditional F8 law internal to the tri-state algebra.
-/
theorem triState_fixed_iff_balanced
    (x : TriNumber ℝ) :
    FixedPoint TriNumber.rotate x ↔ TriNumber.Balanced x :=
  rotate_fixed_iff_balanced x

/--
A vanishing phase-energy trajectory gives a genuine F1 law, but it closes a
concrete problem only after a separately proved identification of that
trajectory with the problem's exact terminal observable.
-/
def triStateVanishing
    (x : ℕ → TriNumber ℝ)
    (h :
      Filter.Tendsto
        (fun n => TriNumber.phaseEnergy (x n))
        Filter.atTop (nhds 0)) :
    VanishingLaw (fun n => TriNumber.phaseEnergy (x n)) :=
  trajectoryVanishingLaw x h

/--
A positive phase-energy lower bound gives a genuine F2 law, again without
silently identifying it with SAT lower bounds or a Yang--Mills mass gap.
-/
def triStateGap
    (admissible : TriNumber ℝ → Prop)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hLower : ∀ x, admissible x → δ ≤ TriNumber.phaseEnergy x) :
    GapLaw (TriNumber ℝ) admissible TriNumber.phaseEnergy :=
  phaseEnergyGapLaw admissible δ hδ hLower

#print axioms MCore.MaterialMath.triState_closes_global_root
#print axioms MCore.MaterialMath.triState_three_phase_orbit
#print axioms MCore.MaterialMath.triState_fixed_iff_balanced

end MCore.MaterialMath
