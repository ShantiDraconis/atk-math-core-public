import MCore.MaterialMath.TerminalPatterns
import MCore.MaterialMath.TriState.Geometry

namespace MCore.MaterialMath

/-- Closed, unconditional F1 producer. -/
theorem internal_F1_vanishing :
    VanishesAtInfinity (fun _ : Nat => (0 : ℝ)) :=
  vanishing_zero

/-- Non-base phase sector used for an unconditional discrete F2 gap. -/
abbrev NonBasePhase := {p : Phase3 // p ≠ Phase3.seed}

/-- Closed, unconditional F2 producer: every non-base phase lies at unit
cyclic distance from the base phase. -/
theorem internal_F2_positive_gap :
    PositiveGap
      (fun p : NonBasePhase =>
        (Phase3.cyclicDistance Phase3.seed p.1 : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro p
  have hne : Phase3.seed ≠ p.1 := by
    intro h
    exact p.2 h.symm
  have hdist :
      Phase3.cyclicDistance Phase3.seed p.1 = 1 :=
    Phase3.cyclicDistance_eq_one hne
  norm_num [hdist]

/-- Closed, unconditional F4 realization producer: every phase realizes itself. -/
theorem internal_F4_realization :
    UniversalRealization (fun p q : Phase3 => q = p) := by
  intro p
  exact ⟨p, rfl⟩

/-- Closed, unconditional F5 equality producer. -/
theorem internal_F5_equality :
    UniversalEquality
      (fun p : Phase3 => p)
      (fun p : Phase3 => p) := by
  intro p
  rfl

/-- Closed, unconditional F6 exclusion producer. -/
theorem internal_F6_exclusion :
    UniversalExclusion (fun _ : Phase3 => False) := by
  intro p h
  exact h

/-- Closed, unconditional F7 strict-budget producer. -/
theorem internal_F7_strict_budget :
    StrictBudget
      (fun _ : Phase3 => (0 : ℝ))
      (fun _ : Phase3 => (1 : ℝ)) := by
  refine ⟨0, by norm_num, by norm_num, ?_⟩
  intro p
  norm_num

/-- Closed, unconditional F8 fixed-point producer for the third iterate. -/
theorem internal_F8_fixed_point :
    HasFixedPoint
      (fun p : Phase3 =>
        Phase3.rotate (Phase3.rotate (Phase3.rotate p))) := by
  exact ⟨Phase3.seed, Phase3.rotate_three Phase3.seed⟩

/-- Stronger F8 law: every phase is a fixed point of the third iterate. -/
theorem internal_F8_all_fixed :
    ∀ p : Phase3,
      Phase3.rotate (Phase3.rotate (Phase3.rotate p)) = p :=
  Phase3.rotate_three

/-- Compact record of the unconditional internal producer family. -/
structure InternalProducerSuite where
  f1 : VanishesAtInfinity (fun _ : Nat => (0 : ℝ))
  f2 :
    PositiveGap
      (fun p : NonBasePhase =>
        (Phase3.cyclicDistance Phase3.seed p.1 : ℝ))
  f4 : UniversalRealization (fun p q : Phase3 => q = p)
  f5 :
    UniversalEquality
      (fun p : Phase3 => p)
      (fun p : Phase3 => p)
  f6 : UniversalExclusion (fun _ : Phase3 => False)
  f7 :
    StrictBudget
      (fun _ : Phase3 => (0 : ℝ))
      (fun _ : Phase3 => (1 : ℝ))
  f8 :
    HasFixedPoint
      (fun p : Phase3 =>
        Phase3.rotate (Phase3.rotate (Phase3.rotate p)))

/-- The complete internal producer suite is inhabited without any open
mathematical premise. -/
def internalProducerSuite : InternalProducerSuite where
  f1 := internal_F1_vanishing
  f2 := internal_F2_positive_gap
  f4 := internal_F4_realization
  f5 := internal_F5_equality
  f6 := internal_F6_exclusion
  f7 := internal_F7_strict_budget
  f8 := internal_F8_fixed_point

theorem internalProducerSuite_inhabited :
    Nonempty InternalProducerSuite :=
  ⟨internalProducerSuite⟩

end MCore.MaterialMath
