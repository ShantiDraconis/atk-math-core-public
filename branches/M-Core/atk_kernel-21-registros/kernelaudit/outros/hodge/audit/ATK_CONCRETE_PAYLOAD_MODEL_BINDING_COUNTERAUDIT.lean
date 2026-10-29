import MCore.K18

namespace MCore

/-- Counter-audit: the abstract graded interface admits a vacuous model with
no varieties. This does not concern genuine algebraic geometry; it shows that
model binding is part of the material Hodge obligation. -/
def emptyGradedHodgeData : GradedRationalHodgeData where
  Variety := Empty
  CohomologyQ := fun X _ => nomatch X
  CycleQ := fun X _ => nomatch X
  isSmoothProjective := fun X => nomatch X
  isTypePP := fun {X} _ _ => nomatch X
  inCycleClassSpan := fun {X} _ _ => nomatch X

def emptyCycleSpanMechanics :
    CycleSpanMechanics emptyGradedHodgeData where
  Coeff := Unit
  zero := ()
  add := fun _ _ => ()
  smul := fun {X} {_} _ _ => nomatch X
  addClass := fun {X} {_} _ _ => nomatch X
  zeroClass := by
    intro X p
    exact nomatch X
  cycleClass := fun {X} _ _ => nomatch X

/-- The abstract concrete-algebraicity payload is inhabited vacuously on the
empty model. Therefore a genuine Hodge producer must also bind G and M to the
intended geometry/cycle-class semantics. -/
theorem concretePayload_vacuous_on_empty_model :
    ConcreteAlgebraicityPayload emptyCycleSpanMechanics := by
  intro X
  exact nomatch X

end MCore
