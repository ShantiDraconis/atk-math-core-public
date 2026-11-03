import MCore.FinalFail.MaterialDerived
import MCore.FinalFail.MaterialField

namespace MCore.FinalFail.MaterialArithmetic

open MCore.FinalFail.MaterialAlgebra
open MCore.FinalFail.MaterialDerived

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState

/-!
# Arithmetic constants and the natural-number reduction into the triadic carrier

This is the explicit arithmetic of the already kernel-checked three-element
field table.  It is finite modular arithmetic, not a claim about a new
classical analytic number system.
-/

namespace TriState

def zero : TState := 0
def one : TState := 1
def two : TState := .manifest
def minusOne : TState := -(1 : TState)

@[simp] theorem zero_eq_seed : zero = .seed := rfl
@[simp] theorem one_eq_transit : one = .transit := rfl
@[simp] theorem two_eq_manifest : two = .manifest := rfl
@[simp] theorem two_eq_neg_one : two = minusOne := rfl

@[simp] theorem one_add_one : (1 : TState) + 1 = two := rfl
@[simp] theorem two_add_one : two + 1 = 0 := rfl
@[simp] theorem one_add_two : (1 : TState) + two = 0 := rfl
@[simp] theorem two_mul_two : two * two = 1 := rfl

/-- Natural numbers mapped by repeated addition of the unit. -/
def ofNat : Nat → TState
  | 0 => 0
  | n + 1 => ofNat n + 1

@[simp] theorem ofNat_zero : ofNat 0 = 0 := rfl

@[simp] theorem ofNat_succ (n : Nat) :
    ofNat (n + 1) = ofNat n + 1 := rfl

@[simp] theorem ofNat_one : ofNat 1 = 1 := rfl
@[simp] theorem ofNat_two : ofNat 2 = two := rfl
@[simp] theorem ofNat_three : ofNat 3 = 0 := rfl

/-- Adding three unit phases is the identity on every state. -/
theorem add_three_units (x : TState) :
    ((x + 1) + 1) + 1 = x := by
  cases x <;> rfl

/-- The natural embedding is periodic with period three. -/
theorem ofNat_add_three (n : Nat) :
    ofNat (n + 3) = ofNat n := by
  change ((ofNat n + 1) + 1) + 1 = ofNat n
  exact add_three_units (ofNat n)

/-- Three acts as zero in the natural embedding. -/
theorem characteristic_three_nat :
    ofNat 3 = ofNat 0 := by
  rfl

/-- Six also reduces to zero by two periods. -/
theorem ofNat_six :
    ofNat 6 = 0 := by
  rw [show 6 = 3 + 3 by decide, ofNat_add_three]
  rfl

/-- Successor arithmetic cycles seed -> transit -> manifest -> seed. -/
theorem successor_cycle (x : TState) :
    (x + 1, (x + 1) + 1, ((x + 1) + 1) + 1) =
      (x + 1, (x + 1) + 1, x) := by
  rw [add_three_units]

/-- The named constant two is the unique nontrivial additive inverse of one. -/
theorem two_is_additive_inverse_of_one :
    (1 : TState) + two = 0 ∧ two + 1 = 0 := by
  exact ⟨rfl, rfl⟩

end TriState

#print axioms MCore.FinalFail.MaterialArithmetic.TriState.ofNat_add_three
#print axioms MCore.FinalFail.MaterialArithmetic.TriState.two_is_additive_inverse_of_one
#print axioms MCore.FinalFail.MaterialArithmetic.TriState.add_three_units

end MCore.FinalFail.MaterialArithmetic
