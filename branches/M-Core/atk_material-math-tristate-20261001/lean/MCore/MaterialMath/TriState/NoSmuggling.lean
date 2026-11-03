import MCore.MaterialMath.TriState.Dynamics
import MCore.FinalFail.GlobalPositiveMaterialFrontier

namespace MCore.MaterialMath

/-- A material interpretation is an explicit map from tri-state data to a target.
The map itself carries all problem-specific mathematical content. -/
abbrev MaterialInterpretation (Target : Sort*) :=
  TriNumber Int → Target

/-- Since the tri-state source is inhabited by I3, giving a material
interpretation into Target is exactly as strong, at the level of existence,
as giving an inhabitant of Target. This is the no-smuggling theorem. -/
theorem nonempty_materialInterpretation_iff_target
    {Target : Sort*} :
    Nonempty (MaterialInterpretation Target) ↔ Nonempty Target := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F TriNumber.I3⟩
  · rintro ⟨t⟩
    exact ⟨fun _ => t⟩

/-- In particular, no purely formal tri-state construction proves RH unless
the interpretation already contains enough mathematics to prove RH. -/
theorem triState_RH_bridge_iff_RH :
    Nonempty (MaterialInterpretation MCore.FinalFail.Semantic.RiemannHypothesis) ↔
      Nonempty MCore.FinalFail.Semantic.RiemannHypothesis :=
  nonempty_materialInterpretation_iff_target

/-- Generic positive-root version of the same firewall. -/
theorem triState_global_bridge_iff_global_root
    {Language : Type*}
    {InP InNP : Language → Prop}
    {SAT : Language}
    {Flow Stabilizer : Type*}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    {Variety : Type*}
    {Class Cycle : Variety → Type*}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    {Curve : Type*}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    {Theory : Type*}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop} :
    Nonempty
        (MaterialInterpretation
          (MCore.FinalFail.Semantic.GlobalPositiveMaterialRoot
            Language InP InNP SAT
            Flow Stabilizer ActualNS Stabilizes
            Variety Class Cycle SmoothProjective RationalHodge Realizes
            Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
            Theory Genuine4D OSReconstructs PositiveMassGap)) ↔
      Nonempty
        (MCore.FinalFail.Semantic.GlobalPositiveMaterialRoot
          Language InP InNP SAT
          Flow Stabilizer ActualNS Stabilizes
          Variety Class Cycle SmoothProjective RationalHodge Realizes
          Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
          Theory Genuine4D OSReconstructs PositiveMassGap) :=
  nonempty_materialInterpretation_iff_target

end MCore.MaterialMath
