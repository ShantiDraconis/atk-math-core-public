import ATK.IMath.Core.Phi3
import Mathlib.Data.Complex.Basic

namespace IMath

/-- Embed an ordinary complex number as a finite three-state value. -/
def ofComplex (z : ℂ) : Phi3 ℂ :=
  .finite z

/-- Embed an ordinary real number through the standard real-to-complex map. -/
def ofReal (x : ℝ) : Phi3 ℂ :=
  .finite (x : ℂ)

theorem ofComplex_injective :
    Function.Injective ofComplex := by
  intro z w h
  exact Phi3.finite_injective h

theorem ofReal_injective :
    Function.Injective ofReal := by
  intro x y h
  have hc : (x : ℂ) = (y : ℂ) := Phi3.finite_injective h
  have hr := congrArg Complex.re hc
  simpa using hr

theorem ofReal_eq_ofComplex (x : ℝ) :
    ofReal x = ofComplex (x : ℂ) := rfl

end IMath
