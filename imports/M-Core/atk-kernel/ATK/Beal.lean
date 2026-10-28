import Mathlib

/-!
# ATK — Beal: restrição dos expoentes via Fermat

* `exponent_gcd_le_two` — dado o Último Teorema de Fermat (como HIPÓTESE explícita `hFLT`),
  toda solução de Aˣ + Bʸ = Cᶻ com A, B, C ≠ 0 tem gcd(x, y, z) ≤ 2.

Por que hipótese e não teorema: a prova completa de Fermat ainda não está formalizada na
Mathlib (há um projeto em andamento). `#print axioms` mostra que nenhum axioma extra entra;
a dependência de Fermat fica visível no enunciado.

Isto não prova Beal: casos com gcd(x,y,z) ∈ {1, 2} continuam abertos em geral.
-/

namespace ATK.Beal

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

end ATK.Beal

#print axioms ATK.Beal.exponent_gcd_le_two
