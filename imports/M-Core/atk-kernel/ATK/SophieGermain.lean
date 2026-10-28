import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.FLT.Basic

/-!
# ATK — Ponte B2 (FLT): o teorema de Sophie Germain

A ponte B2 do lane Beal é o último teorema de Fermat, reduzido no kernel a expoentes primos
`p ≥ 5` (`ATK.BridgeReduction.flt_iff_primos_ge_cinco`). Este arquivo prova o **teorema de Sophie
Germain** (c. 1823), o primeiro resultado geral sobre o "primeiro caso" de FLT:

> se `p` é primo ímpar e `q = 2p + 1` também é primo, então `xᵖ + yᵖ = zᵖ` não tem solução inteira
> com `p ∤ xyz`.

Vale para `p = 3, 5, 11, 23, 29, 41, 53, …` (primos de Sophie Germain). Em particular,
`flt_caso_um_cinco`: o primeiro caso de FLT para `p = 5` (com `q = 11`), e
`flt_cinco_iff_caso_dois`: FLT(5) equivale ao segundo caso (`5 ∣ xyz`).

Prova (clássica):
1. mod `q`, toda `p`-ésima potência é `0` ou `±1` (`t^{2p} = t^{q−1} = 1`), logo `aᵖ + bᵖ + cᵖ ≡ 0`
   força `q ∣ abc` (`zero_de_soma`);
2. com `a, b, c` dois a dois coprimos e `p ∤ a`, `b + c` e `Q(b, c) = (bᵖ + cᵖ)/(b + c)` são coprimos
   (`Q ≡ p·c^{p−1}` módulo `b + c`), e o produto é `(−a)ᵖ`, logo ambos são `p`-ésimas potências
   (`fator`);
3. se `q ∣ a`: `2a = (a + b) + (c + a) − (b + c)` é soma de três `p`-ésimas potências, logo
   `q ∣ b + c`; então `Q(b, c) ≡ p·c^{p−1}` e `Q(c, a) ≡ c^{p−1}` mod `q`, e `p ≡ (β/δ)ᵖ ∈ {0, ±1}`,
   absurdo porque `1 < p < q − 1`.

B2 continua `PARCIAL_NO_MODELO_DO_LANE`: o segundo caso (`p ∣ xyz`) e os primos que não são de
Sophie Germain ficam de fora (o caso geral é o teorema de Wiles).
-/

namespace ATK.SophieGermain

open Finset

/-- `Q(b, c) = Σ_{i<p} bⁱ (−c)^{p−1−i}`, com `Q(b, c)·(b + c) = bᵖ + cᵖ` para `p` ímpar. -/
def Q {R : Type*} [CommRing R] (p : ℕ) (b c : R) : R :=
  ∑ i ∈ range p, b ^ i * (-c) ^ (p - 1 - i)

theorem Q_mul {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (b c : R) :
    Q p b c * (b + c) = b ^ p + c ^ p := by
  have h := geom_sum₂_mul b (-c) p
  rw [sub_neg_eq_add, Odd.neg_pow hp, sub_neg_eq_add] at h
  exact h

theorem Q_cast {p : ℕ} (n : ℕ) (b c : ℤ) :
    ((Q p b c : ℤ) : ZMod n) = Q p (b : ZMod n) (c : ZMod n) := by
  simp only [Q]
  push_cast
  rfl

/-- `Q(−c, c) = p·c^{p−1}` (`p` ímpar). -/
theorem Q_neg {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (c : R) :
    Q p (-c) c = p * c ^ (p - 1) := by
  have hterm : ∀ i ∈ range p, (-c) ^ i * (-c) ^ (p - 1 - i) = c ^ (p - 1) := by
    intro i hi
    rw [mem_range] at hi
    rw [← pow_add, show i + (p - 1 - i) = p - 1 by omega]
    obtain ⟨k, rfl⟩ := hp
    rw [show 2 * k + 1 - 1 = 2 * k by omega, pow_mul, pow_mul, neg_sq]
  rw [Q, sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]

/-- `Q(b, 0) = b^{p−1}` (`p ≥ 1`). -/
theorem Q_zero {R : Type*} [CommRing R] {p : ℕ} (hp : 1 ≤ p) (b : R) :
    Q p b 0 = b ^ (p - 1) := by
  rw [Q, sum_eq_single (p - 1)]
  · simp
  · intro i hi hne
    rw [mem_range] at hi
    rw [neg_zero, zero_pow (by omega), mul_zero]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-! ## Potências mod `q = 2p + 1` -/

section modq

variable {p : ℕ} {q : ℕ} [hq : Fact q.Prime] (hpq : q = 2 * p + 1)
include hpq

/-- Mod `q = 2p + 1`, toda `p`-ésima potência não nula é `±1`. -/
theorem pot_pm_um {t : ZMod q} (ht : t ≠ 0) : t ^ p = 1 ∨ t ^ p = -1 := by
  have h : t ^ p * t ^ p = 1 := by
    rw [← pow_add, show p + p = q - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one ht
  exact mul_self_eq_one_iff.mp h

/-- Mod `q = 2p + 1` (`q > 3`): `xᵖ + yᵖ + zᵖ = 0` força `x`, `y` ou `z` nulo. -/
theorem zero_de_soma (h3 : 3 < q) {x y z : ZMod q} (h : x ^ p + y ^ p + z ^ p = 0) :
    x = 0 ∨ y = 0 ∨ z = 0 := by
  have h3' : (3 : ZMod q) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  by_contra hne
  push Not at hne
  obtain ⟨hx, hy, hz⟩ := hne
  rcases pot_pm_um hpq hx with hx' | hx' <;> rcases pot_pm_um hpq hy with hy' | hy' <;>
    rcases pot_pm_um hpq hz with hz' | hz' <;> rw [hx', hy', hz'] at h <;>
    first
      | exact h3' (by linear_combination h)
      | exact h3' (by linear_combination -h)
      | exact one_ne_zero (by linear_combination h)
      | exact one_ne_zero (by linear_combination -h)

end modq

/-! ## A fatoração -/

/-- Se `aᵖ + bᵖ + cᵖ = 0`, `b, c` coprimos e `p ∤ a` (`p` primo ímpar), então `b + c` e `Q(b, c)`
são `p`-ésimas potências. -/
theorem fator {p : ℕ} (hp : p.Prime) (hodd : Odd p) {a b c : ℤ} (h : a ^ p + b ^ p + c ^ p = 0)
    (hbc : IsCoprime b c) (hpa : ¬ (p : ℤ) ∣ a) :
    (∃ α : ℤ, b + c = α ^ p) ∧ ∃ β : ℤ, Q p b c = β ^ p := by
  have hprod : (b + c) * Q p b c = (-a) ^ p := by
    rw [mul_comm, Q_mul hodd, Odd.neg_pow hodd]
    linear_combination h
  have hcop : IsCoprime (b + c) (Q p b c) := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨h1, -⟩
      rw [h1, zero_mul] at hprod
      have ha : -a = 0 := pow_eq_zero_iff hp.ne_zero |>.mp hprod.symm
      exact hpa (by rw [neg_eq_zero.mp ha]; exact dvd_zero _)
    · intro r hr hr1 hr2
      have hn : r.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hr
      have := Fact.mk hn
      have cast0 : ∀ x : ℤ, r ∣ x ↔ (x : ZMod r.natAbs) = 0 := fun x => by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_natAbs, abs_dvd]
      have hbc' : (b : ZMod r.natAbs) = -(c : ZMod r.natAbs) := by
        have := (cast0 _).mp hr1
        push_cast at this
        linear_combination this
      have hQ := (cast0 _).mp hr2
      rw [Q_cast, hbc', Q_neg hodd] at hQ
      rcases mul_eq_zero.mp hQ with h1 | h1
      · have hrp : r ∣ (p : ℤ) := (cast0 p).mpr (by exact_mod_cast h1)
        have hra : r ∣ a := by
          have : r ∣ (-a) ^ p := hprod ▸ dvd_mul_of_dvd_left hr1 _
          exact dvd_neg.mp (hr.dvd_of_dvd_pow this)
        have hnp : r.natAbs = p := by
          have := Int.natAbs_dvd_natAbs.mpr hrp
          rw [Int.natAbs_natCast] at this
          exact (Nat.prime_dvd_prime_iff_eq hn hp).mp this
        exact hpa (by rw [← hnp]; exact Int.natAbs_dvd.mpr hra)
      · have hc0 : (c : ZMod r.natAbs) = 0 := pow_eq_zero_iff (by
          have := hp.two_le; omega) |>.mp h1
        have hrc : r ∣ c := (cast0 c).mpr hc0
        have hrb : r ∣ b := (cast0 b).mpr (by rw [hbc', hc0, neg_zero])
        exact hr.not_isUnit (hbc.isUnit_of_dvd' hrb hrc)
  exact Int.eq_pow_of_mul_eq_pow_odd hcop hodd hprod

/-! ## O teorema -/

/-- O caso em que `q ∣ a`. -/
theorem caso_q_dvd {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hq : (2 * p + 1).Prime)
    {a b c : ℤ} (h : a ^ p + b ^ p + c ^ p = 0)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a)
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) (hpc : ¬ (p : ℤ) ∣ c)
    (hqa : ((2 * p + 1 : ℕ) : ℤ) ∣ a) : False := by
  have := Fact.mk hq
  set q := 2 * p + 1 with hqdef
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · rw [h2] at hodd; exact absurd hodd (by decide)
    · have := hp.two_le
      by_contra hlt
      have : p = 2 := by omega
      rw [this] at hodd; exact absurd hodd (by decide)
  have cast0 : ∀ x : ℤ, (q : ℤ) ∣ x ↔ (x : ZMod q) = 0 := fun x =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x q).symm
  obtain ⟨⟨α, hα⟩, β, hβ⟩ := fator hp hodd h hbc hpa
  obtain ⟨⟨γ, hγ⟩, δ, hδ⟩ := fator hp hodd (by linear_combination h) hca hpb
  obtain ⟨⟨ε, hε⟩, -⟩ := fator hp hodd (by linear_combination h) hab hpc
  have ha0 : (a : ZMod q) = 0 := (cast0 a).mp hqa
  -- coprimalidade mod q
  have hnz : ∀ x : ℤ, IsCoprime a x → (x : ZMod q) ≠ 0 := by
    intro x hx hx0
    have hqx : (q : ℤ) ∣ x := (cast0 x).mpr hx0
    have hu := hx.isUnit_of_dvd' hqa hqx
    rw [Int.isUnit_iff] at hu
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
    omega
  have hb0 := hnz b hab
  have hc0 := hnz c hca.symm
  -- passo 3: 2a como soma de três potências
  have hsum : (ε : ZMod q) ^ p + (γ : ZMod q) ^ p + (-(α : ZMod q)) ^ p = 0 := by
    have e1 : ((a + b : ℤ) : ZMod q) = (ε : ZMod q) ^ p := by rw [hε]; push_cast; rfl
    have e2 : ((c + a : ℤ) : ZMod q) = (γ : ZMod q) ^ p := by rw [hγ]; push_cast; rfl
    have e3 : ((b + c : ℤ) : ZMod q) = (α : ZMod q) ^ p := by rw [hα]; push_cast; rfl
    push_cast at e1 e2 e3
    rw [Odd.neg_pow hodd, ← e1, ← e2, ← e3, ha0]
    ring
  rcases zero_de_soma hqdef (by omega) hsum with hε0 | hγ0 | hα0
  · -- q ∣ a + b ⇒ q ∣ b
    apply hb0
    have e1 : ((a + b : ℤ) : ZMod q) = (ε : ZMod q) ^ p := by rw [hε]; push_cast; rfl
    push_cast at e1
    rw [hε0, zero_pow hp.ne_zero, ha0, zero_add] at e1
    exact e1
  · apply hc0
    have e2 : ((c + a : ℤ) : ZMod q) = (γ : ZMod q) ^ p := by rw [hγ]; push_cast; rfl
    push_cast at e2
    rw [hγ0, zero_pow hp.ne_zero, ha0, add_zero] at e2
    exact e2
  · -- b ≡ −c mod q
    have hbc' : (b : ZMod q) = -(c : ZMod q) := by
      have e3 : ((b + c : ℤ) : ZMod q) = (α : ZMod q) ^ p := by rw [hα]; push_cast; rfl
      push_cast at e3
      rw [neg_eq_zero.mp hα0, zero_pow hp.ne_zero] at e3
      linear_combination e3
    have hβ' : (β : ZMod q) ^ p = p * (c : ZMod q) ^ (p - 1) := by
      have := congrArg (fun x : ℤ => (x : ZMod q)) hβ
      rw [Q_cast, hbc', Q_neg hodd] at this
      push_cast at this
      exact this.symm
    have hδ' : (δ : ZMod q) ^ p = (c : ZMod q) ^ (p - 1) := by
      have := congrArg (fun x : ℤ => (x : ZMod q)) hδ
      rw [Q_cast, ha0, Q_zero (by omega)] at this
      push_cast at this
      exact this.symm
    have hcp : (c : ZMod q) ^ (p - 1) ≠ 0 := pow_ne_zero _ hc0
    have hδ0 : (δ : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hδ'
      exact hcp hδ'.symm
    have key : ((β : ZMod q) * (δ : ZMod q)⁻¹) ^ p = p := by
      rw [mul_pow, hβ', inv_pow, hδ', mul_assoc, mul_inv_cancel₀ hcp, mul_one]
    have hpq : (p : ZMod q) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd hp.pos h0
      omega
    by_cases ht : (β : ZMod q) * (δ : ZMod q)⁻¹ = 0
    · rw [ht, zero_pow hp.ne_zero] at key
      exact hpq key.symm
    rcases pot_pm_um hqdef ht with h1 | h1
    · rw [key] at h1
      have : ((p : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by exact_mod_cast h1
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at this
      omega
    · rw [key] at h1
      have : ((p + 1 : ℕ) : ZMod q) = 0 := by push_cast; rw [h1]; ring
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_of_dvd (by omega) this
      omega

/-- **Teorema de Sophie Germain** (forma simétrica, coprima): `p` primo ímpar, `2p + 1` primo,
`aᵖ + bᵖ + cᵖ = 0` com `a, b, c` dois a dois coprimos ⇒ `p ∣ abc`. -/
theorem sophieGermain_coprimo {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hq : (2 * p + 1).Prime)
    {a b c : ℤ} (h : a ^ p + b ^ p + c ^ p = 0)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) :
    (p : ℤ) ∣ a * b * c := by
  by_contra hdiv
  have hpa : ¬ (p : ℤ) ∣ a := fun h => hdiv (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hpb : ¬ (p : ℤ) ∣ b := fun h => hdiv (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have hpc : ¬ (p : ℤ) ∣ c := fun h => hdiv (dvd_mul_of_dvd_right h _)
  have := Fact.mk hq
  have hp3 : 3 < 2 * p + 1 := by have := hp.two_le; omega
  have hsum : (a : ZMod (2 * p + 1)) ^ p + (b : ZMod (2 * p + 1)) ^ p +
      (c : ZMod (2 * p + 1)) ^ p = 0 := by
    have := congrArg (fun x : ℤ => (x : ZMod (2 * p + 1))) h
    push_cast at this
    exact this
  have cast0 : ∀ x : ℤ, (x : ZMod (2 * p + 1)) = 0 → (((2 * p + 1 : ℕ) : ℤ)) ∣ x := fun x hx =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x _).mp hx
  rcases zero_de_soma rfl hp3 hsum with ha | hb | hc
  · exact caso_q_dvd hp hodd hq h hab hbc hca hpa hpb hpc (cast0 a ha)
  · exact caso_q_dvd hp hodd hq (by linear_combination h) hbc hca hab hpb hpc hpa (cast0 b hb)
  · exact caso_q_dvd hp hodd hq (by linear_combination h) hca hab hbc hpc hpa hpb (cast0 c hc)

/-- **Teorema de Sophie Germain** (primeiro caso de FLT): `p` primo ímpar com `2p + 1` primo ⇒
`xᵖ + yᵖ ≠ zᵖ` sempre que `p ∤ xyz`. -/
theorem sophieGermain {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hq : (2 * p + 1).Prime)
    {x y z : ℤ} (hxyz : ¬ (p : ℤ) ∣ x * y * z) : x ^ p + y ^ p ≠ z ^ p := by
  intro h
  -- nenhum é zero
  have hx0 : x ≠ 0 := by rintro rfl; exact hxyz (by simp)
  have hy0 : y ≠ 0 := by rintro rfl; exact hxyz (by simp)
  -- d = mdc(x, y); d ∣ z
  obtain ⟨d, x', y', hd, hcop, rfl, rfl⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left y hx0)
  have hdz : (d : ℤ) ∣ z := by
    have : (d : ℤ) ^ p ∣ z ^ p := ⟨x' ^ p + y' ^ p, by rw [← h]; ring⟩
    exact (Int.pow_dvd_pow_iff hp.ne_zero).mp this
  obtain ⟨z', rfl⟩ := hdz
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have h' : x' ^ p + y' ^ p + (-z') ^ p = 0 := by
    rw [Odd.neg_pow hodd]
    have : (d : ℤ) ^ p * (x' ^ p + y' ^ p - z' ^ p) = 0 := by
      rw [mul_sub, mul_add]; rw [mul_pow, mul_pow, mul_pow] at h; linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (pow_eq_zero_iff hp.ne_zero |>.mp h0) hd0
    · linear_combination h0
  have hab : IsCoprime x' y' := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  -- os outros pares são coprimos
  have cop3 : ∀ u v w : ℤ, u ^ p + v ^ p + w ^ p = 0 → IsCoprime u v → IsCoprime v w := by
    intro u v w huvw huv
    apply isCoprime_of_prime_dvd
    · rintro ⟨rfl, rfl⟩
      have : u = 0 := by
        have := huvw
        simp only [zero_pow hp.ne_zero, add_zero] at this
        exact pow_eq_zero_iff hp.ne_zero |>.mp this
      subst this
      exact (Prime.not_isUnit (Int.prime_two)) (huv.isUnit_of_dvd' (dvd_zero 2) (dvd_zero 2))
    · intro r hr hrv hrw
      have : r ∣ u ^ p := ⟨-(v ^ p + w ^ p) / r, by
        have h1 : r ∣ v ^ p + w ^ p := dvd_add (dvd_pow hrv hp.ne_zero) (dvd_pow hrw hp.ne_zero)
        obtain ⟨k, hk⟩ := h1
        rw [show u ^ p = -(v ^ p + w ^ p) by linear_combination huvw, hk]
        rw [show -(r * k) = r * -k by ring, Int.mul_ediv_cancel_left _ hr.ne_zero]⟩
      exact hr.not_isUnit (huv.isUnit_of_dvd' (hr.dvd_of_dvd_pow this) hrv)
  have hbc := cop3 x' y' (-z') h' hab
  have hca := cop3 y' (-z') x' (by linear_combination h') hbc
  have := sophieGermain_coprimo hp hodd hq h' hab hbc hca
  apply hxyz
  have e : x' * (d : ℤ) * (y' * (d : ℤ)) * ((d : ℤ) * z') = -((d : ℤ) ^ 3 * (x' * y' * -z')) := by
    ring
  rw [e]
  exact (dvd_neg.mpr (dvd_mul_of_dvd_right this _))

/-- **Primeiro caso de FLT para `p = 5`** (`q = 11`). -/
theorem flt_caso_um_cinco {x y z : ℤ} (h : ¬ (5 : ℤ) ∣ x * y * z) : x ^ 5 + y ^ 5 ≠ z ^ 5 :=
  sophieGermain (p := 5) (by norm_num) (by decide) (by norm_num) (by exact_mod_cast h)

/-- Com o primeiro caso provado, **FLT(5) equivale ao segundo caso** (`5 ∣ xyz`). -/
theorem flt_cinco_iff_caso_dois :
    FermatLastTheoremFor 5 ↔
      ∀ x y z : ℤ, x ≠ 0 → y ≠ 0 → z ≠ 0 → (5 : ℤ) ∣ x * y * z → x ^ 5 + y ^ 5 ≠ z ^ 5 := by
  rw [fermatLastTheoremFor_iff_int]
  constructor
  · intro h x y z hx hy hz _
    exact h x y z hx hy hz
  · intro h x y z hx hy hz
    by_cases h5 : (5 : ℤ) ∣ x * y * z
    · exact h x y z hx hy hz h5
    · exact flt_caso_um_cinco h5

end ATK.SophieGermain

#print axioms ATK.SophieGermain.Q_mul
#print axioms ATK.SophieGermain.Q_cast
#print axioms ATK.SophieGermain.Q_neg
#print axioms ATK.SophieGermain.Q_zero
#print axioms ATK.SophieGermain.pot_pm_um
#print axioms ATK.SophieGermain.zero_de_soma
#print axioms ATK.SophieGermain.fator
#print axioms ATK.SophieGermain.caso_q_dvd
#print axioms ATK.SophieGermain.sophieGermain_coprimo
#print axioms ATK.SophieGermain.sophieGermain
#print axioms ATK.SophieGermain.flt_caso_um_cinco
#print axioms ATK.SophieGermain.flt_cinco_iff_caso_dois
