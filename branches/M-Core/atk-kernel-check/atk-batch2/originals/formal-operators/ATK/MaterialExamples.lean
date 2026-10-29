/-! Fully concrete elementary inhabitants; these are NOT conjecture certificates. -/
namespace ATK

theorem natural_zero_inhabitant : ∃ n : Nat, n = 0 :=
  ⟨0, rfl⟩

theorem natural_succ_positive (n : Nat) : 0 < Nat.succ n := by
  exact Nat.zero_lt_succ n

theorem no_strict_decrease_from_zero (f : Nat → Nat)
    (h : f 0 < 0) : False :=
  Nat.not_lt_zero _ h
end ATK
