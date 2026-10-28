import Mathlib

/-!
# ATK — conditional exponent gcd bound

Source: ShantiDraconis/m-core-beal/atk-kernel/ATK/Beal.lean
Original blob SHA: 9f5b1fd68eab75d34d3f843d0308c518012c85c1

The FermatLastTheorem assumption is EXPLICIT and not discharged here.
This is not an unconditional proof of Beal. Kernel check pending.
-/

namespace ATK.MathlibCandidates

theorem exponent_gcd_le_two (hFLT : FermatLastTheorem)
    {A B C x y z : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hEq : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x (Nat.gcd y z) ≤ 2 := by
  by_contra hd
  push_neg at hd
  obtain ⟨r, hr⟩ : Nat.gcd x (Nat.gcd y z) ∣ x := Nat.gcd_dvd_left _ _
  obtain ⟨s, hs⟩ : Nat.gcd x (Nat.gcd y z) ∣ y :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨t, ht⟩ : Nat.gcd x (Nat.gcd y z) ∣ z :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  generalize hdd : Nat.gcd x (Nat.gcd y z) = d at hd hr hs ht
  have key : (A ^ r) ^ d + (B ^ s) ^ d = (C ^ t) ^ d := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm r d, mul_comm s d, mul_comm t d,
      ← hr, ← hs, ← ht]
    exact hEq
  exact hFLT d (by omega) (A ^ r) (B ^ s) (C ^ t)
    (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC) key

end ATK.MathlibCandidates

#print axioms ATK.MathlibCandidates.exponent_gcd_le_two
