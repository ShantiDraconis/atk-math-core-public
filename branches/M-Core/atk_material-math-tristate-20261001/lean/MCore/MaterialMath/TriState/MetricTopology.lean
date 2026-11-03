import MCore.MaterialMath.TriState.Core

namespace MCore.MaterialMath

namespace Phase3

theorem cyclicDistance_eq_zero_iff (p q : Phase3) :
    cyclicDistance p q = 0 ↔ p = q := by
  by_cases h : p = q
  · subst q
    simp [cyclicDistance]
  · simp [cyclicDistance, h]

theorem cyclicDistance_triangle (p q r : Phase3) :
    cyclicDistance p r ≤ cyclicDistance p q + cyclicDistance q r := by
  cases p <;> cases q <;> cases r <;> decide

/-- The discrete phase metric is in fact ultrametric. -/
theorem cyclicDistance_ultrametric (p q r : Phase3) :
    cyclicDistance p r ≤
      max (cyclicDistance p q) (cyclicDistance q r) := by
  cases p <;> cases q <;> cases r <;> decide

/-- Natural-radius open ball for the finite phase metric. -/
def ball (p : Phase3) (radius : Nat) : Set Phase3 :=
  {q | cyclicDistance p q < radius}

/-- Radius one isolates exactly one phase. -/
theorem ball_one_eq_singleton (p : Phase3) :
    ball p 1 = {p} := by
  ext q
  by_cases h : q = p
  · subst q
    simp [ball, cyclicDistance]
  · have hpq : p ≠ q := by
      intro hp
      exact h hp.symm
    simp [ball, cyclicDistance, h, hpq]

/-- Radius two contains the complete three-state phase space. -/
theorem ball_two_eq_univ (p : Phase3) :
    ball p 2 = Set.univ := by
  ext q
  by_cases h : p = q
  · subst q
    simp [ball, cyclicDistance]
  · simp [ball, cyclicDistance, h]

/-- Every singleton is a metric ball, hence the induced finite topology is discrete. -/
theorem singleton_is_ball (p : Phase3) :
    ({p} : Set Phase3) = ball p 1 := by
  symm
  exact ball_one_eq_singleton p

end Phase3

end MCore.MaterialMath
