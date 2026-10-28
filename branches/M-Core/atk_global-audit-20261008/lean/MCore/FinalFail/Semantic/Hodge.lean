import MCore.FinalFail.BoundaryAtoms

namespace MCore.FinalFail.Semantic

universe u v w

/-- Faithful positive Hodge target relative to a fixed geometry layer. -/
structure HodgeRealizationTarget
    (Variety : Type u)
    (Class : Variety → Type v)
    (Cycle : Variety → Type w)
    (SmoothProjective : Variety → Prop)
    (RationalHodge : {X : Variety} → Class X → Prop)
    (Realizes : {X : Variety} → Cycle X → Class X → Prop) where
  realize :
    ∀ X, SmoothProjective X →
      ∀ α : Class X, RationalHodge α →
        ∃ Z : Cycle X, Realizes Z α

abbrev HodgeInterpretation
    (Variety : Type u)
    (Class : Variety → Type v)
    (Cycle : Variety → Type w)
    (SmoothProjective : Variety → Prop)
    (RationalHodge : {X : Variety} → Class X → Prop)
    (Realizes : {X : Variety} → Cycle X → Class X → Prop) :=
  BoundaryInterpretation .hodge
    (HodgeRealizationTarget Variety Class Cycle
      SmoothProjective RationalHodge Realizes)

theorem hodge_interpretation_iff_target
    (Variety : Type u)
    (Class : Variety → Type v)
    (Cycle : Variety → Type w)
    (SmoothProjective : Variety → Prop)
    (RationalHodge : {X : Variety} → Class X → Prop)
    (Realizes : {X : Variety} → Cycle X → Class X → Prop) :
    Nonempty (HodgeInterpretation Variety Class Cycle
      SmoothProjective RationalHodge Realizes) ↔
      Nonempty (HodgeRealizationTarget Variety Class Cycle
        SmoothProjective RationalHodge Realizes) :=
  nonempty_boundaryInterpretation_iff_nonempty_target

end MCore.FinalFail.Semantic
