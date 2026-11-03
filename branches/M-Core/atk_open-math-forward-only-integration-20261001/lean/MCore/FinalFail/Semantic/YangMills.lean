import MCore.FinalFail.BoundaryAtoms

namespace MCore.FinalFail.Semantic

universe u

/-- Genuine YM target relative to a fixed theory representation.  The same
theory must satisfy the 4D, reconstruction, and positive-gap predicates. -/
structure YangMills4DGapTarget
    (Theory : Type u)
    (Genuine4D OSReconstructs PositiveMassGap : Theory → Prop) where
  theory : Theory
  genuine4D : Genuine4D theory
  reconstructs : OSReconstructs theory
  positiveGap : PositiveMassGap theory

abbrev YangMillsInterpretation
    (Theory : Type u)
    (Genuine4D OSReconstructs PositiveMassGap : Theory → Prop) :=
  BoundaryInterpretation .yangMills
    (YangMills4DGapTarget Theory Genuine4D OSReconstructs PositiveMassGap)

theorem ym_interpretation_iff_target
    (Theory : Type u)
    (Genuine4D OSReconstructs PositiveMassGap : Theory → Prop) :
    Nonempty (YangMillsInterpretation Theory Genuine4D OSReconstructs PositiveMassGap) ↔
      Nonempty (YangMills4DGapTarget Theory Genuine4D OSReconstructs PositiveMassGap) :=
  nonempty_boundaryInterpretation_iff_nonempty_target

end MCore.FinalFail.Semantic
