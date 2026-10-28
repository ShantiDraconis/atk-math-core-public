import Mathlib

namespace IMath

/--
A local zero-over-zero germ retains numerator, denominator and a center at
which both vanish.
-/
structure Germ00 where
  numerator : ℝ → ℝ
  denominator : ℝ → ℝ
  center : ℝ
  numerator_zero : numerator center = 0
  denominator_zero : denominator center = 0

/-- Epsilon-delta resolution of the quotient away from the center. -/
def ResolvesTo (g : Germ00) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x,
    0 < |x - g.center| →
    |x - g.center| < δ →
    |g.numerator x / g.denominator x - L| < ε

def xOverX : Germ00 where
  numerator := fun x => x
  denominator := fun x => x
  center := 0
  numerator_zero := rfl
  denominator_zero := rfl

def xSqOverX : Germ00 where
  numerator := fun x => x ^ 2
  denominator := fun x => x
  center := 0
  numerator_zero := by norm_num
  denominator_zero := rfl

theorem xOverX_ne_xSqOverX :
    xOverX ≠ xSqOverX := by
  intro h
  have hn := congrArg (fun g : Germ00 => g.numerator 2) h
  norm_num [xOverX, xSqOverX] at hn

theorem xOverX_resolvesTo_one :
    ResolvesTo xOverX 1 := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro x hxpos hxlt
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    norm_num [xOverX] at hxpos
  simpa [xOverX, hx0] using hε

theorem xSqOverX_resolvesTo_zero :
    ResolvesTo xSqOverX 0 := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hxpos hxlt
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    norm_num [xSqOverX] at hxpos
  have hquot : x ^ 2 / x = x := by
    field_simp [pow_two, hx0]
  simpa [xSqOverX, hquot] using hxlt

theorem same_form_different_resolutions :
    ResolvesTo xOverX 1 ∧ ResolvesTo xSqOverX 0 :=
  ⟨xOverX_resolvesTo_one, xSqOverX_resolvesTo_zero⟩

end IMath
