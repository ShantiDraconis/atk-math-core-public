import MCore.MaterialMath.TriState.Core

namespace MCore.MaterialMath

namespace Phase3

/-- Canonical cyclic index of the three phases. -/
def index : Phase3 → Nat
  | .seed => 0
  | .passage => 1
  | .manifest => 2

theorem index_lt_three (p : Phase3) :
    index p < 3 := by
  cases p <;> decide

/-- Exact angular representative in degrees: 0, 120, 240. -/
def angleDegrees (p : Phase3) : Nat :=
  120 * index p

theorem angleDegrees_values :
    angleDegrees .seed = 0 ∧
    angleDegrees .passage = 120 ∧
    angleDegrees .manifest = 240 := by
  decide

/-- One rotation advances by exactly 120 degrees modulo a full turn. -/
theorem rotate_adds_120_mod_360 (p : Phase3) :
    angleDegrees (rotate p) % 360 =
      (angleDegrees p + 120) % 360 := by
  cases p <;> decide

/-- Two rotations advance by exactly 240 degrees modulo a full turn. -/
theorem rotate2_adds_240_mod_360 (p : Phase3) :
    angleDegrees (rotate2 p) % 360 =
      (angleDegrees p + 240) % 360 := by
  cases p <;> decide

/-- Three rotations complete one full turn and return to the same phase. -/
theorem full_turn_closure (p : Phase3) :
    rotate (rotate (rotate p)) = p ∧
    (angleDegrees p + 360) % 360 = angleDegrees p % 360 := by
  constructor
  · exact rotate_three p
  · omega

/-- The three canonical angular representatives are pairwise distinct. -/
theorem angleDegrees_injective :
    Function.Injective angleDegrees := by
  intro p q h
  cases p <;> cases q <;> simp [angleDegrees, index] at h ⊢

end Phase3

end MCore.MaterialMath
