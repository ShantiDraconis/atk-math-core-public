import MCore.MaterialMath.TriState.OperationalAlgebra

namespace MCore.MaterialMath

open TriNumber
open TriAlgebra

namespace TriPotent

/-- Tripotent element: x^3 = x. -/
def IsTripotent
    {α : Type*} [MonoidWithZero α]
    (x : TriNumber α) : Prop :=
  x ^ 3 = x

/-- The distinguished tri-state constant is tripotent. -/
theorem I3_tripotent :
    IsTripotent I3 := by
  funext p
  cases p <;> norm_num [IsTripotent, I3]

/-- Cyclic rotation preserves tripotence. -/
theorem rotate_preserves_tripotent
    {α : Type*} [MonoidWithZero α]
    {x : TriNumber α}
    (h : IsTripotent x) :
    IsTripotent (TriNumber.rotate x) := by
  unfold IsTripotent at h ⊢
  rw [← TriAlgebra.rotate_pow x 3, h]

theorem J3_tripotent :
    IsTripotent J3 := by
  exact rotate_preserves_tripotent I3_tripotent

theorem K3_tripotent :
    IsTripotent K3 := by
  exact rotate_preserves_tripotent J3_tripotent

/-- Polynomial annihilation form of tripotence for I3. -/
theorem I3_annihilator :
    I3 * (I3 - 1) * (I3 + 1) = 0 := by
  funext p
  cases p <;> norm_num [I3]

/-- The entire three-state orbit has the same annihilating polynomial. -/
theorem J3_annihilator :
    J3 * (J3 - 1) * (J3 + 1) = 0 := by
  funext p
  cases p <;> norm_num [J3, I3, TriNumber.rotate, Phase3.rotate]

theorem K3_annihilator :
    K3 * (K3 - 1) * (K3 + 1) = 0 := by
  funext p
  cases p <;>
    norm_num [K3, J3, I3, TriNumber.rotate2, TriNumber.rotate, Phase3.rotate]

end TriPotent

end MCore.MaterialMath
