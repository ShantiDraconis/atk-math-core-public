import MCore.FinalFail.BoundaryAtoms

namespace MCore.FinalFail.Semantic

universe u

/-- Exact separation target relative to a fixed, externally bound official
complexity model.  The model predicates are parameters, so this file cannot
replace the official-model binding with a toy model. -/
structure PvsNPSeparationTarget
    (Language : Type u)
    (InP InNP : Language → Prop)
    (SAT : Language) where
  sat_in_np : InNP SAT
  sat_not_in_p : ¬ InP SAT

abbrev PvsNPInterpretation
    (Language : Type u)
    (InP InNP : Language → Prop)
    (SAT : Language) :=
  BoundaryInterpretation .pVsNP
    (PvsNPSeparationTarget Language InP InNP SAT)

theorem pvsnp_interpretation_iff_target
    (Language : Type u)
    (InP InNP : Language → Prop)
    (SAT : Language) :
    Nonempty (PvsNPInterpretation Language InP InNP SAT) ↔
      Nonempty (PvsNPSeparationTarget Language InP InNP SAT) :=
  nonempty_boundaryInterpretation_iff_nonempty_target

end MCore.FinalFail.Semantic
