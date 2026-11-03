import MCore.FinalFail.MaterialDerived

namespace MCore.FinalFail.MaterialField

open MCore.FinalFail.MaterialAlgebra
open MCore.FinalFail.MaterialDerived

/--
A finite, explicitly checkable certificate for the field laws needed from a
three-element carrier.  It is intentionally weaker than installing a global
Mathlib Field instance: every law is visible and auditable.
-/
structure ThreeElementFieldCertificate (K : Type)
    [Zero K] [One K] [Add K] [Mul K] [Neg K] [Inv K] where
  zero_ne_one : (0 : K) ≠ 1
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : K, a + b = b + a
  zero_add : ∀ a : K, 0 + a = a
  add_zero : ∀ a : K, a + 0 = a
  add_neg : ∀ a : K, a + (-a) = 0
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : K, a * b = b * a
  one_mul : ∀ a : K, 1 * a = a
  mul_one : ∀ a : K, a * 1 = a
  zero_mul : ∀ a : K, 0 * a = 0
  mul_zero : ∀ a : K, a * 0 = 0
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : K, (a + b) * c = a * c + b * c
  inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1

namespace TriState

theorem zero_ne_one : (0 : TriState) ≠ 1 := by
  decide

/-- Every tristable value is one of the three canonical constants. -/
theorem exhaustive (x : TriState) :
    x = .seed ∨ x = .transit ∨ x = .manifest := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Exactly the field-table laws of the explicit three-state arithmetic. -/
def fieldCertificate : ThreeElementFieldCertificate TriState where
  zero_ne_one := zero_ne_one
  add_assoc := MCore.FinalFail.MaterialAlgebra.TriState.add_assoc
  add_comm := MCore.FinalFail.MaterialAlgebra.TriState.add_comm
  zero_add := MCore.FinalFail.MaterialAlgebra.TriState.seed_add
  add_zero := MCore.FinalFail.MaterialAlgebra.TriState.add_seed
  add_neg := MCore.FinalFail.MaterialAlgebra.TriState.add_neg
  mul_assoc := MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc
  mul_comm := MCore.FinalFail.MaterialAlgebra.TriState.mul_comm
  one_mul := MCore.FinalFail.MaterialAlgebra.TriState.one_mul
  mul_one := MCore.FinalFail.MaterialAlgebra.TriState.mul_one
  zero_mul := MCore.FinalFail.MaterialAlgebra.TriState.zero_mul
  mul_zero := MCore.FinalFail.MaterialAlgebra.TriState.mul_zero
  left_distrib := MCore.FinalFail.MaterialAlgebra.TriState.left_distrib
  right_distrib := MCore.FinalFail.MaterialAlgebra.TriState.right_distrib
  inv_cancel := MCore.FinalFail.MaterialAlgebra.TriState.mul_inv_cancel

/-- Characteristic three in additive form. -/
theorem field_characteristic_three (x : TriState) :
    (x + x) + x = 0 := by
  exact MaterialDerived.TriState.characteristic_three x

/-- Nonzero multiplicative elements have order dividing two. -/
theorem nonzero_multiplicative_exponent_two
    (x : TriState) (hx : x ≠ 0) :
    x * x = 1 := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.nonzero_square_eq_one x hx

/-- Frobenius x^3=x for all three elements. -/
theorem frobenius_identity (x : TriState) :
    (x * x) * x = x := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.cubic_idempotence x

/--
Classification statement: the explicitly defined tristable arithmetic has
three elements and satisfies the complete field table above.

This theorem is about the finite algebra defined in M-Core; it makes no claim
that a symbolic expression such as 0/0 has this value in ordinary arithmetic.
-/
theorem tristate_is_three_element_field_table :
    (∀ x : TriState,
      x = .seed ∨ x = .transit ∨ x = .manifest) ∧
    (0 : TriState) ≠ 1 := by
  exact ⟨exhaustive, zero_ne_one⟩

end TriState

#print axioms MCore.FinalFail.MaterialField.TriState.fieldCertificate
#print axioms MCore.FinalFail.MaterialField.TriState.field_characteristic_three
#print axioms MCore.FinalFail.MaterialField.TriState.frobenius_identity
#print axioms MCore.FinalFail.MaterialField.TriState.tristate_is_three_element_field_table

end MCore.FinalFail.MaterialField
