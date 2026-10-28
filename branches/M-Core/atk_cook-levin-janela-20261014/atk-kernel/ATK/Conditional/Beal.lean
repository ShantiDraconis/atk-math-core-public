import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Condicional — Conjectura de Beal

(Beal não é um dos problemas do milênio; está aqui porque é um lane do M-Core.)

Enunciado-alvo `BealConjecture`: aˣ + bʸ = cᶻ com a, b, c > 0 e x, y, z > 2 ⇒ a, b, c têm
um fator primo comum. Fidelidade: OFICIAL (enunciado elementar completo).

Forma condicional:

  `FermatLastTheorem → GCDLowerBoundSmallExponents → BealConjecture`

* `FermatLastTheorem` (PONTE; Wiles 1995, Taylor–Wiles 1995): definido na Mathlib,
  prova ainda em formalização (projeto FLT do Imperial College).
* `GCDLowerBoundSmallExponents` (ABERTA): a forma gcd do lane `m-core-beal`,
  restrita aos expoentes com gcd(x, y, z) ≤ 2 — Fermat elimina todo o resto.

Também certificado: `BealConjecture ↔ GCDLowerBound` (a forma gcd do registro do M-Core é
uma reformulação exata, não uma redução).
-/

namespace ATK.Conditional.Beal

/-- Enunciado oficial. -/
def BealConjecture : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    a ^ x + b ^ y = c ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

/-- Forma gcd (terminal `GCDLowerBoundProducer` do registro). -/
def GCDLowerBound : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    a ^ x + b ^ y = c ^ z → 1 < Nat.gcd a (Nat.gcd b c)

/-- HIPÓTESE ABERTA: a forma gcd só para gcd(x, y, z) ≤ 2. -/
def GCDLowerBoundSmallExponents : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    Nat.gcd x (Nat.gcd y z) ≤ 2 →
    a ^ x + b ^ y = c ^ z → 1 < Nat.gcd a (Nat.gcd b c)

theorem one_lt_gcd_iff {a b c : ℕ} (ha : 0 < a) :
    1 < Nat.gcd a (Nat.gcd b c) ↔ ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c := by
  constructor
  · intro h
    obtain ⟨p, hp, hpd⟩ :=
      Nat.exists_prime_and_dvd (n := Nat.gcd a (Nat.gcd b c)) (by omega)
    exact ⟨p, hp, hpd.trans (Nat.gcd_dvd_left _ _),
      hpd.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)),
      hpd.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))⟩
  · rintro ⟨p, hp, hpa, hpb, hpc⟩
    have hdvd : p ∣ Nat.gcd a (Nat.gcd b c) := Nat.dvd_gcd hpa (Nat.dvd_gcd hpb hpc)
    have hpos : 0 < Nat.gcd a (Nat.gcd b c) := Nat.gcd_pos_of_pos_left _ ha
    have h1 := Nat.le_of_dvd hpos hdvd
    have h2 := hp.two_le
    omega

/-- A forma gcd é equivalente ao enunciado oficial. -/
theorem beal_iff_gcdLowerBound : BealConjecture ↔ GCDLowerBound := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz he
    exact (one_lt_gcd_iff ha).2 (h a b c x y z ha hb hc hx hy hz he)
  · intro h a b c x y z ha hb hc hx hy hz he
    exact (one_lt_gcd_iff ha).1 (h a b c x y z ha hb hc hx hy hz he)

/-- Fermat ⇒ gcd(x, y, z) ≤ 2 em toda solução (mesma prova de `ATK.Beal.exponent_gcd_le_two`). -/
theorem exponent_gcd_le_two (hFLT : FermatLastTheorem)
    {A B C x y z : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hEq : A ^ x + B ^ y = C ^ z) :
    Nat.gcd x (Nat.gcd y z) ≤ 2 := by
  by_contra hd
  rw [not_le] at hd
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

/-- **Condicional Beal.** -/
theorem beal_conditional (hBridge : FermatLastTheorem)
    (hOpen : GCDLowerBoundSmallExponents) : BealConjecture := by
  rw [beal_iff_gcdLowerBound]
  intro a b c x y z ha hb hc hx hy hz he
  exact hOpen a b c x y z ha hb hc hx hy hz
    (exponent_gcd_le_two hBridge ha.ne' hb.ne' hc.ne' he) he

end ATK.Conditional.Beal

#print axioms ATK.Conditional.Beal.one_lt_gcd_iff
#print axioms ATK.Conditional.Beal.beal_iff_gcdLowerBound
#print axioms ATK.Conditional.Beal.exponent_gcd_le_two
#print axioms ATK.Conditional.Beal.beal_conditional
