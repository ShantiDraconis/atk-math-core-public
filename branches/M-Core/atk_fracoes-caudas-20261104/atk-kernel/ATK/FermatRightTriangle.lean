import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Int.Lemmas

/-!
# ATK — Teorema do triângulo retângulo de Fermat: `x⁴ − y⁴ ≠ z²`

A Mathlib tem `not_fermat_42` (`x⁴ + y⁴ ≠ z²`), mas não a equação irmã `x⁴ − y⁴ = z²`.
Este arquivo a prova por **descida infinita** sobre `|x|`, no estilo de `Mathlib.NumberTheory.FLT.Four`:

* `not_fermat_4m4`: `y ≠ 0 → z ≠ 0 → x⁴ − y⁴ ≠ z²`.

Descida. Numa solução mínima, `mdc(x, y) = 1` e `(y², z, x²)` é um triplo pitagórico primitivo.
* `y` ímpar: `y² = m² − n²`, `z = 2mn`, `x² = m² + n²`, logo `m⁴ − n⁴ = (xy)²` com `|m| < |x|`.
* `y` par: `z = m² − n²`, `y² = 2mn`, `x² = m² + n²`; o triplo `(m, n, x)` dá `r, s` coprimos com
  `(y/2)² = rs(r² − s²)`; os três fatores são quadrados (`r = j²`, `s = k²`, `r² − s² = D²`) e
  `j⁴ − k⁴ = D²` com `|j| < |x|`.

Consequências clássicas, também certificadas aqui:
* `not_fourth_add_sq_eq_fourth`: `x⁴ + y² ≠ z⁴` (forma usada para Beal);
* `sq_ne_two_mul_sq`: `a² ≠ 2d²` para `a ≠ 0` (irracionalidade de √2, por descida);
* `not_sq_add_and_sub_sq`: `x² + y²` e `x² − y²` não são ambos quadrados (`y ≠ 0`);
* `fermat_right_triangle`: a área de um triângulo pitagórico não é um quadrado (`ab ≠ 2d²`);
* `one_not_congruent`: não há triângulo retângulo de lados racionais com área 1.

Status: teoremas clássicos de Fermat. O que é novo é a formalização no atk-kernel.
-/

namespace ATK.FermatRightTriangle

/-- Solução não trivial de `a⁴ − b⁴ = c²` (`b, c ≠ 0`). -/
def FermatM42 (a b c : ℤ) : Prop :=
  b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2

namespace FermatM42

theorem a_ne_zero {a b c : ℤ} (h : FermatM42 a b c) : a ≠ 0 := by
  rintro rfl
  obtain ⟨hb, -, heq⟩ := h
  have hb4 : 0 < b ^ 4 := by positivity
  nlinarith [sq_nonneg c]

theorem neg_a {a b c : ℤ} (h : FermatM42 a b c) : FermatM42 (-a) b c := by
  obtain ⟨hb, hc, heq⟩ := h
  exact ⟨hb, hc, by rw [← heq]; ring⟩

theorem of_mul {a b c k : ℤ} (hk : k ≠ 0) (h : FermatM42 (k * a) (k * b) (k ^ 2 * c)) :
    FermatM42 a b c := by
  obtain ⟨hb, hc, heq⟩ := h
  refine ⟨right_ne_zero_of_mul hb, right_ne_zero_of_mul hc, ?_⟩
  apply (mul_right_inj' (pow_ne_zero 4 hk)).mp
  linear_combination heq

/-- Solução com `|a|` mínimo. -/
def Minimal (a b c : ℤ) : Prop :=
  FermatM42 a b c ∧ ∀ a1 b1 c1 : ℤ, FermatM42 a1 b1 c1 → Int.natAbs a ≤ Int.natAbs a1

theorem exists_minimal {a b c : ℤ} (h : FermatM42 a b c) : ∃ a0 b0 c0, Minimal a0 b0 c0 := by
  classical
  have hex : ∃ n : ℕ, ∃ s : ℤ × ℤ × ℤ, FermatM42 s.1 s.2.1 s.2.2 ∧ n = Int.natAbs s.1 :=
    ⟨Int.natAbs a, (a, b, c), h, rfl⟩
  obtain ⟨s0, hs0, hs1⟩ := Nat.find_spec hex
  refine ⟨s0.1, s0.2.1, s0.2.2, hs0, ?_⟩
  intro a1 b1 c1 h1
  rw [← hs1]
  exact Nat.find_min' hex ⟨(a1, b1, c1), h1, rfl⟩

/-- Numa solução mínima, `a` e `b` são coprimos. -/
theorem coprime_of_minimal {a b c : ℤ} (h : Minimal a b c) : IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a1, rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b1, rfl⟩ := Int.natCast_dvd.mpr hpb
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2]
    exact Dvd.intro (a1 ^ 4 - b1 ^ 4) (by ring)
  obtain ⟨c1, rfl⟩ := hpc
  have hf : FermatM42 a1 b1 c1 := of_mul (Int.natCast_ne_zero.mpr hp.ne_zero) h.1
  have ha1 : a1 ≠ 0 := hf.a_ne_zero
  apply Nat.le_lt_asymm (h.2 _ _ _ hf)
  rw [Int.natAbs_mul, Int.natAbs_natCast, lt_mul_iff_one_lt_left]
  · exact hp.one_lt
  · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 ha1)

theorem exists_pos_minimal {a b c : ℤ} (h : FermatM42 a b c) :
    ∃ a0 b0 c0, Minimal a0 b0 c0 ∧ 0 < a0 := by
  obtain ⟨a0, b0, c0, hf⟩ := exists_minimal h
  rcases lt_trichotomy 0 a0 with h1 | h1 | h1
  · exact ⟨a0, b0, c0, hf, h1⟩
  · exact absurd h1.symm hf.1.a_ne_zero
  · refine ⟨-a0, b0, c0, ⟨hf.1.neg_a, ?_⟩, neg_pos.mpr h1⟩
    intro a1 b1 c1 h1'
    rw [Int.natAbs_neg]
    exact hf.2 a1 b1 c1 h1'

end FermatM42

/-- `mdc(r, s) = 1 ⇒ mdc(r² − s², rs) = 1`. -/
theorem isCoprime_sq_sub {r s : ℤ} (h : IsCoprime r s) : IsCoprime (r ^ 2 - s ^ 2) (r * s) := by
  have h1 : IsCoprime (r ^ 2 - s ^ 2) r := by
    have h' := ((IsCoprime.mul_left h.symm h.symm).neg_left).add_mul_left_left r
    rwa [show -(s * s) + r * r = r ^ 2 - s ^ 2 by ring] at h'
  have h2 : IsCoprime (r ^ 2 - s ^ 2) s := by
    have h' := (IsCoprime.mul_left h h).add_mul_left_left (-s)
    rwa [show r * r + s * -s = r ^ 2 - s ^ 2 by ring] at h'
  exact h1.mul_right h2

/-- Descida, caso `b` ímpar. -/
theorem descent_odd {a b c : ℤ} (ha : 0 < a) (hb : b ≠ 0) (hc : c ≠ 0)
    (heq : a ^ 4 - b ^ 4 = c ^ 2) (hcop : IsCoprime (b ^ 2) c) (hbodd : b % 2 = 1) :
    ∃ a1 b1 c1, FermatM42 a1 b1 c1 ∧ Int.natAbs a1 < Int.natAbs a := by
  have ht : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
    delta PythagoreanTriple
    linear_combination (-1 : ℤ) * heq
  have hb2 : b ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, hbodd]
    decide
  obtain ⟨m, n, h1, h2, h3, -, -, -⟩ :=
    ht.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hcop) hb2 (by positivity)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hc
    rw [h2]
    ring
  refine ⟨m, n, a * b, ⟨hn, mul_ne_zero ha.ne' hb, ?_⟩, ?_⟩
  · rw [mul_pow, h3, h1]
    ring
  · rw [Int.natAbs_lt_iff_sq_lt, h3]
    have : 0 < n ^ 2 := by positivity
    linarith

/-- Passo final do caso par: `b'² = rs(r² − s²)` com fatores positivos coprimos. -/
theorem descent_even_core {a b' r s : ℤ} (hr : 0 < r) (hs : 0 < s)
    (hd : 0 < r ^ 2 - s ^ 2) (hrs : Int.gcd r s = 1) (ha' : a = r ^ 2 + s ^ 2)
    (hb'eq : (r * s) * (r ^ 2 - s ^ 2) = b' ^ 2) :
    ∃ a1 b1 c1, FermatM42 a1 b1 c1 ∧ Int.natAbs a1 < Int.natAbs a := by
  have hcop1 : Int.gcd (r * s) (r ^ 2 - s ^ 2) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (isCoprime_sq_sub (Int.isCoprime_iff_gcd_eq_one.mpr hrs)).symm
  have hcop2 : Int.gcd (r ^ 2 - s ^ 2) (r * s) = 1 := by
    rw [Int.gcd_comm]
    exact hcop1
  have hrs_pos : 0 < r * s := mul_pos hr hs
  obtain ⟨E, hE⟩ := Int.sq_of_gcd_eq_one hcop1 hb'eq
  have hrsE : r * s = E ^ 2 := by
    rcases hE with h | h
    · exact h
    · exfalso
      nlinarith [sq_nonneg E]
  obtain ⟨D, hD⟩ := Int.sq_of_gcd_eq_one hcop2 ((mul_comm _ _).trans hb'eq)
  have hDeq : r ^ 2 - s ^ 2 = D ^ 2 := by
    rcases hD with h | h
    · exact h
    · exfalso
      nlinarith [sq_nonneg D]
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one hrs hrsE
  have hrj : r = j ^ 2 := by
    rcases hj with h | h
    · exact h
    · exfalso
      nlinarith [sq_nonneg j]
  have hsr : Int.gcd s r = 1 := by
    rw [Int.gcd_comm]
    exact hrs
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one hsr ((mul_comm s r).trans hrsE)
  have hsk : s = k ^ 2 := by
    rcases hk with h | h
    · exact h
    · exfalso
      nlinarith [sq_nonneg k]
  refine ⟨j, k, D, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro rfl
    rw [hsk] at hs
    simp at hs
  · rintro rfl
    rw [hDeq] at hd
    simp at hd
  · rw [← hDeq, hrj, hsk]
    ring
  · rw [Int.natAbs_lt_iff_sq_lt, ← hrj]
    have hr2 : r ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
    have hs2 : 0 < s ^ 2 := by positivity
    have ha2 : a ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
    linarith

/-- Descida, caso `b` par. -/
theorem descent_even {a b c : ℤ} (ha : 0 < a) (hb : b ≠ 0)
    (heq : a ^ 4 - b ^ 4 = c ^ 2) (hcop : IsCoprime (b ^ 2) c) (hbeven : b % 2 = 0) :
    ∃ a1 b1 c1, FermatM42 a1 b1 c1 ∧ Int.natAbs a1 < Int.natAbs a := by
  have hcodd : c % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one c with h | h
    · exfalso
      have h2b : (2 : ℤ) ∣ b ^ 2 :=
        (Int.dvd_of_emod_eq_zero hbeven).trans (dvd_pow_self b two_ne_zero)
      have hu := hcop.isUnit_of_dvd' h2b (Int.dvd_of_emod_eq_zero h)
      rw [Int.isUnit_iff] at hu
      omega
    · exact h
  have ht : PythagoreanTriple c (b ^ 2) (a ^ 2) := by
    delta PythagoreanTriple
    linear_combination (-1 : ℤ) * heq
  obtain ⟨m, n, -, h2, h3, hmn, hpar, hm0⟩ :=
    ht.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hcop.symm) hcodd (by positivity)
  obtain ⟨b', rfl⟩ := Int.dvd_of_emod_eq_zero hbeven
  have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
  have hmn_pos : 0 < m * n := by
    have : 0 < (2 * b') ^ 2 := by positivity
    nlinarith
  have hm : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hmn_pos
      simp at hmn_pos
  have hn : 0 < n := by
    by_contra hn
    have hn' := not_lt.mp hn
    nlinarith
  have key : ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ 0 < r ^ 2 - s ^ 2 ∧ Int.gcd r s = 1 ∧
      a = r ^ 2 + s ^ 2 ∧ m * n = 2 * (r * s) * (r ^ 2 - s ^ 2) := by
    rcases hpar with ⟨-, hn2⟩ | ⟨hm2, -⟩
    · -- `m` par, `n` ímpar: triplo `(n, m, a)`
      have ht2 : PythagoreanTriple n m a := by
        delta PythagoreanTriple
        linear_combination (-1 : ℤ) * h3
      have hnm : Int.gcd n m = 1 := by
        rw [Int.gcd_comm]
        exact hmn
      obtain ⟨r, s, e1, e2, e3, hrs, -, hr0⟩ := ht2.coprime_classification' hnm hn2 ha
      have hrs_pos : 0 < r * s := by nlinarith
      have hr : 0 < r := by
        rcases hr0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hrs_pos
          simp at hrs_pos
      have hs : 0 < s := by
        by_contra hs
        have hs' := not_lt.mp hs
        nlinarith
      exact ⟨r, s, hr, hs, by rw [← e1]; exact hn, hrs, e3, by rw [e1, e2]; ring⟩
    · -- `m` ímpar, `n` par: triplo `(m, n, a)`
      have ht2 : PythagoreanTriple m n a := by
        delta PythagoreanTriple
        linear_combination (-1 : ℤ) * h3
      obtain ⟨r, s, e1, e2, e3, hrs, -, hr0⟩ := ht2.coprime_classification' hmn hm2 ha
      have hrs_pos : 0 < r * s := by nlinarith
      have hr : 0 < r := by
        rcases hr0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hrs_pos
          simp at hrs_pos
      have hs : 0 < s := by
        by_contra hs
        have hs' := not_lt.mp hs
        nlinarith
      exact ⟨r, s, hr, hs, by rw [← e1]; exact hm, hrs, e3, by rw [e1, e2]; ring⟩
  obtain ⟨r, s, hr, hs, hd, hrs, ha', hmn'⟩ := key
  have h4 : (4 : ℤ) * ((r * s) * (r ^ 2 - s ^ 2)) = 4 * b' ^ 2 := by
    linear_combination (-1 : ℤ) * h2 - 2 * hmn'
  exact descent_even_core hr hs hd hrs ha' (mul_left_cancel₀ (by norm_num) h4)

namespace FermatM42

/-- Não existe solução mínima com `a > 0`. -/
theorem not_minimal {a b c : ℤ} (h : Minimal a b c) (ha : 0 < a) : False := by
  have hab : IsCoprime a b := coprime_of_minimal h
  obtain ⟨⟨hb, hc, heq⟩, hmin⟩ := h
  have hcop : IsCoprime (b ^ 2) c := by
    have h1 : IsCoprime (b ^ 4) (a ^ 4) := hab.symm.pow
    have h2 : IsCoprime (b ^ 4) (a ^ 4 + b ^ 4 * (-1)) := h1.add_mul_left_right (-1)
    rw [show a ^ 4 + b ^ 4 * (-1) = c ^ 2 by linear_combination heq] at h2
    have h3 : IsCoprime b c := (IsCoprime.pow_iff (by norm_num) (by norm_num)).mp h2
    exact h3.pow_left
  have hdesc : ∃ a1 b1 c1, FermatM42 a1 b1 c1 ∧ Int.natAbs a1 < Int.natAbs a := by
    rcases Int.emod_two_eq_zero_or_one b with hb2 | hb2
    · exact descent_even ha hb heq hcop hb2
    · exact descent_odd ha hb hc heq hcop hb2
  obtain ⟨a1, b1, c1, hf, hlt⟩ := hdesc
  exact absurd (hmin a1 b1 c1 hf) (not_le.mpr hlt)

end FermatM42

/-- **Teorema do triângulo retângulo de Fermat** (forma diofantina): `x⁴ − y⁴ ≠ z²`. -/
theorem not_fermat_4m4 {a b c : ℤ} (hb : b ≠ 0) (hc : c ≠ 0) : a ^ 4 - b ^ 4 ≠ c ^ 2 := by
  intro heq
  obtain ⟨a0, b0, c0, hmin, hpos⟩ := FermatM42.exists_pos_minimal (a := a) ⟨hb, hc, heq⟩
  exact FermatM42.not_minimal hmin hpos

/-- Forma aditiva, usada para Beal: `x⁴ + y² ≠ z⁴` com `x, y ≠ 0`. -/
theorem not_fourth_add_sq_eq_fourth {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ 4 + y ^ 2 ≠ z ^ 4 := by
  intro h
  exact not_fermat_4m4 (a := z) hx hy (by linear_combination (-1 : ℤ) * h)

/-- `a² ≠ 2d²` para `a ≠ 0` (irracionalidade de √2), por descida sobre `|a|`. -/
theorem sq_ne_two_mul_sq_aux : ∀ (n : ℕ) (a d : ℤ), a.natAbs = n → a ≠ 0 → a ^ 2 ≠ 2 * d ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a d hn ha heq
    have h2a : (2 : ℤ) ∣ a := Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨d ^ 2, heq⟩
    obtain ⟨a', rfl⟩ := h2a
    have ha' : a' ≠ 0 := right_ne_zero_of_mul ha
    have hd : d ^ 2 = 2 * a' ^ 2 := by linarith
    have hd0 : d ≠ 0 := by
      rintro rfl
      have : 0 < a' ^ 2 := by positivity
      linarith
    have hlt : d.natAbs < n := by
      rw [← hn, Int.natAbs_lt_iff_sq_lt]
      have : 0 < a' ^ 2 := by positivity
      nlinarith
    exact ih _ hlt d a' rfl hd0 hd

theorem sq_ne_two_mul_sq {a d : ℤ} (ha : a ≠ 0) : a ^ 2 ≠ 2 * d ^ 2 :=
  sq_ne_two_mul_sq_aux _ a d rfl ha

/-- `x² + y²` e `x² − y²` não são ambos quadrados quando `y ≠ 0`. -/
theorem not_sq_add_and_sub_sq {x y u v : ℤ} (hy : y ≠ 0)
    (hu : x ^ 2 + y ^ 2 = u ^ 2) (hv : x ^ 2 - y ^ 2 = v ^ 2) : False := by
  by_cases hv0 : v = 0
  · subst hv0
    have hxy : x ^ 2 = y ^ 2 := by linear_combination hv
    have hu0 : u ≠ 0 := by
      rintro rfl
      have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg x]
    exact sq_ne_two_mul_sq (d := y) hu0 (by linear_combination -hu + hxy)
  · have hu0 : u ≠ 0 := by
      rintro rfl
      have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg x]
    exact not_fermat_4m4 (a := x) hy (mul_ne_zero hu0 hv0) (by
      have : x ^ 4 - y ^ 4 = (x ^ 2 + y ^ 2) * (x ^ 2 - y ^ 2) := by ring
      rw [this, hu, hv]
      ring)

/-- **Fermat**: a área de um triângulo pitagórico não nulo não é um quadrado (`ab ≠ 2d²`). -/
theorem fermat_right_triangle {a b c d : ℤ} (h : PythagoreanTriple a b c) (ha : a ≠ 0)
    (hb : b ≠ 0) : a * b ≠ 2 * d ^ 2 := by
  intro hab
  have hp : a * a + b * b = c * c := h
  have hd : d ≠ 0 := by
    rintro rfl
    have : a * b = 0 := by simpa using hab
    exact mul_ne_zero ha hb this
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 := by linear_combination (-1 : ℤ) * hp
  have key : c ^ 4 - (2 * d) ^ 4 = (a ^ 2 - b ^ 2) ^ 2 := by
    have e : (2 * d) ^ 4 = 4 * (a * b) ^ 2 := by rw [hab]; ring
    rw [e, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
    ring
  by_cases hz : a ^ 2 - b ^ 2 = 0
  · have hsq : a ^ 2 = b ^ 2 := by linear_combination hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · subst h1
      exact sq_ne_two_mul_sq (d := d) ha (by linear_combination hab)
    · subst h1
      have : 0 < b ^ 2 := by positivity
      nlinarith [sq_nonneg d]
  · exact not_fermat_4m4 (mul_ne_zero two_ne_zero hd) hz key

/-- **1 não é número congruente**: não há triângulo retângulo de lados racionais com área 1. -/
theorem one_not_congruent {a b c : ℚ} (h : a ^ 2 + b ^ 2 = c ^ 2) : a * b / 2 ≠ 1 := by
  intro harea
  have hab : a * b = 2 := by linarith
  have ha : a ≠ 0 := by rintro rfl; simp at hab
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = (a.den : ℤ) * b.den * c.den := ⟨_, rfl⟩
  have hL0 : (L : ℚ) ≠ 0 := by
    rw [hL]
    push_cast
    exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr a.den_nz) (Nat.cast_ne_zero.mpr b.den_nz))
      (Nat.cast_ne_zero.mpr c.den_nz)
  obtain ⟨A, hAd⟩ : ∃ A : ℤ, A = a.num * b.den * c.den := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℤ, B = b.num * a.den * c.den := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C : ℤ, C = c.num * a.den * b.den := ⟨_, rfl⟩
  have hA : (A : ℚ) = a * L := by
    rw [hAd, hL]
    push_cast
    rw [← Rat.mul_den_eq_num a]
    ring
  have hB : (B : ℚ) = b * L := by
    rw [hBd, hL]
    push_cast
    rw [← Rat.mul_den_eq_num b]
    ring
  have hC : (C : ℚ) = c * L := by
    rw [hCd, hL]
    push_cast
    rw [← Rat.mul_den_eq_num c]
    ring
  have htri : PythagoreanTriple A B C := by
    delta PythagoreanTriple
    have : (A : ℚ) * A + B * B = C * C := by
      rw [hA, hB, hC]
      linear_combination (L : ℚ) ^ 2 * h
    exact_mod_cast this
  have hA0 : A ≠ 0 := by
    intro h0
    have : (A : ℚ) = 0 := by exact_mod_cast h0
    rw [hA] at this
    exact mul_ne_zero ha hL0 this
  have hB0 : B ≠ 0 := by
    intro h0
    have : (B : ℚ) = 0 := by exact_mod_cast h0
    rw [hB] at this
    exact mul_ne_zero hb hL0 this
  have hprod : A * B = 2 * L ^ 2 := by
    have : (A : ℚ) * B = 2 * (L : ℚ) ^ 2 := by
      rw [hA, hB]
      linear_combination (L : ℚ) ^ 2 * hab
    exact_mod_cast this
  exact fermat_right_triangle htri hA0 hB0 hprod

end ATK.FermatRightTriangle

#print axioms ATK.FermatRightTriangle.isCoprime_sq_sub
#print axioms ATK.FermatRightTriangle.descent_odd
#print axioms ATK.FermatRightTriangle.descent_even_core
#print axioms ATK.FermatRightTriangle.descent_even
#print axioms ATK.FermatRightTriangle.FermatM42.not_minimal
#print axioms ATK.FermatRightTriangle.not_fermat_4m4
#print axioms ATK.FermatRightTriangle.not_fourth_add_sq_eq_fourth
#print axioms ATK.FermatRightTriangle.sq_ne_two_mul_sq
#print axioms ATK.FermatRightTriangle.not_sq_add_and_sub_sq
#print axioms ATK.FermatRightTriangle.fermat_right_triangle
#print axioms ATK.FermatRightTriangle.one_not_congruent
