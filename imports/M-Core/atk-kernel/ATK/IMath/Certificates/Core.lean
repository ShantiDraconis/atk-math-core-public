import ATK.IMath.Core.Embeddings
import ATK.IMath.Arithmetic.Division
import ATK.IMath.Arithmetic.Collapse
import ATK.IMath.Algebra.Absorbing
import ATK.IMath.Refinement.Realization
import ATK.IMath.Analysis.Germ
import ATK.IMath.Geometry.Point

namespace IMath.Certificates

theorem C01_I_is_indeterminate :
    Phi3.state (Phi3.I (α := ℂ)) = .indeterminate :=
  Phi3.state_I

theorem C02_I_is_not_infinity :
    Phi3.I (α := ℂ) ≠ (.infinity : Phi3 ℂ) :=
  Phi3.I_ne_infinity

theorem C03_I_is_not_finite (z : ℂ) :
    Phi3.I (α := ℂ) ≠ (.finite z : Phi3 ℂ) :=
  Phi3.I_ne_finite z

theorem C04_real_embedding_injective :
    Function.Injective ofReal :=
  ofReal_injective

theorem C05_complex_embedding_injective :
    Function.Injective ofComplex :=
  ofComplex_injective

theorem C06_zero_over_zero_is_I :
    Phi3.idiv (.finite (0 : ℂ)) (.finite 0) = Phi3.I :=
  Phi3.zero_idiv_zero

theorem C07_infinity_over_infinity_retains_provenance :
    Phi3.idiv (.infinity : Phi3 ℂ) .infinity =
      .indeterminate (.div .infinity .infinity) :=
  Phi3.infinity_idiv_infinity

theorem C08_collapse_is_idempotent (x : Phi3 ℂ) :
    Phi3.collapse (Phi3.collapse x) = Phi3.collapse x :=
  Phi3.collapse_idempotent x

theorem C09_absorbing_addition_refutes_right_cancellation :
    ∃ a b : Phi3 ℂ,
      a ≠ b ∧
      Phi3.absorbingAdd a Phi3.I =
        Phi3.absorbingAdd b Phi3.I := by
  exact Phi3.absorbingAdd_not_right_cancellative_of_ne
    (a := (0 : ℂ)) (b := 1) (by norm_num)

theorem C10_refinement_transitive
    {A B C : Realization ℂ}
    (hAB : refines A B) (hBC : refines B C) :
    refines A C :=
  refines_trans hAB hBC

theorem C11_contextual_zero_over_zero_germs_differ :
    xOverX ≠ xSqOverX :=
  xOverX_ne_xSqOverX

theorem C12_x_over_x_resolves_to_one :
    ResolvesTo xOverX 1 :=
  xOverX_resolvesTo_one

theorem C13_x_squared_over_x_resolves_to_zero :
    ResolvesTo xSqOverX 0 :=
  xSqOverX_resolvesTo_zero

theorem C14_same_substitution_form_different_resolutions :
    ResolvesTo xOverX 1 ∧ ResolvesTo xSqOverX 0 :=
  same_form_different_resolutions

theorem C15_determined_geometry_embedding_injective {n : ℕ} :
    Function.Injective (@determinedPoint ℂ n) :=
  determinedPoint_injective

end IMath.Certificates

#print axioms IMath.Certificates.C01_I_is_indeterminate
#print axioms IMath.Certificates.C04_real_embedding_injective
#print axioms IMath.Certificates.C06_zero_over_zero_is_I
#print axioms IMath.Certificates.C08_collapse_is_idempotent
#print axioms IMath.Certificates.C09_absorbing_addition_refutes_right_cancellation
#print axioms IMath.Certificates.C10_refinement_transitive
#print axioms IMath.Certificates.C14_same_substitution_form_different_resolutions
#print axioms IMath.Certificates.C15_determined_geometry_embedding_injective
