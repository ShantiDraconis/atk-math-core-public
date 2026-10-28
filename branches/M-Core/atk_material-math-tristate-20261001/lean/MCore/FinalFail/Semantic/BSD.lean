import MCore.FinalFail.BoundaryAtoms

namespace MCore.FinalFail.Semantic

universe u

/-- Full BSD target on a fixed realizable elliptic-curve domain.  Rank equality
and the refined formula are forced onto the same domain. -/
structure BSDRealizableTarget
    (Curve : Type u)
    (Realizable : Curve → Prop)
    (AnalyticOrder MordellWeilRank : Curve → Int)
    (RefinedFormula : Curve → Prop) where
  rankEquality :
    ∀ E, Realizable E → AnalyticOrder E = MordellWeilRank E
  refined :
    ∀ E, Realizable E → RefinedFormula E

abbrev BSDInterpretation
    (Curve : Type u)
    (Realizable : Curve → Prop)
    (AnalyticOrder MordellWeilRank : Curve → Int)
    (RefinedFormula : Curve → Prop) :=
  BoundaryInterpretation .bsd
    (BSDRealizableTarget Curve Realizable
      AnalyticOrder MordellWeilRank RefinedFormula)

theorem bsd_interpretation_iff_target
    (Curve : Type u)
    (Realizable : Curve → Prop)
    (AnalyticOrder MordellWeilRank : Curve → Int)
    (RefinedFormula : Curve → Prop) :
    Nonempty (BSDInterpretation Curve Realizable
      AnalyticOrder MordellWeilRank RefinedFormula) ↔
      Nonempty (BSDRealizableTarget Curve Realizable
        AnalyticOrder MordellWeilRank RefinedFormula) :=
  nonempty_boundaryInterpretation_iff_nonempty_target

end MCore.FinalFail.Semantic
