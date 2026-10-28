namespace MCore.OpenMath.I

/-- Indexing regime for the I-family. The indeterminate constructor is symbolic,
not the result of evaluating zero divided by zero in an ambient field. -/
inductive Regime where
  | finite (n : Nat)
  | infinite
  | indeterminate
  deriving DecidableEq, Repr

abbrev I3 : Regime := .finite 3
abbrev I10 : Regime := .finite 10
abbrev IInfinite : Regime := .infinite
abbrev IZeroDivZero : Regime := .indeterminate

@[simp] theorem I3_is_finite : I3 = .finite 3 := rfl
@[simp] theorem I10_is_finite : I10 = .finite 10 := rfl
@[simp] theorem IInfinite_is_infinite : IInfinite = .infinite := rfl
@[simp] theorem IZeroDivZero_is_indeterminate : IZeroDivZero = .indeterminate := rfl

theorem regimes_distinct :
    I3 ≠ IInfinite ∧ I3 ≠ IZeroDivZero ∧ IInfinite ≠ IZeroDivZero := by
  decide

end MCore.OpenMath.I
