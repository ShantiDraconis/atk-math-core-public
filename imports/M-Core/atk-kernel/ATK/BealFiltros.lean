import ATK.Conditional.Beal

/-!
# ATK — Beal: filtros de paridade e o valor exato de `g*`

* Exemplos: `3³ + 6³ = 3⁵` (mdc 3) e **`2³ + 2³ = 2⁴` (mdc 2)**.
* **`beal_iff_gEstrela`**: com `g* = min {mdc(a,b,c) : aˣ + bʸ = cᶻ, x,y,z > 2}`,
  **Beal ⟺ `g* = 2`**. Corrige o texto anexado ("se Beal for verdadeira, `g* ∈ {2, 3}`"): o exemplo
  `2³ + 2³ = 2⁴` mostra `g* ≤ 2` incondicionalmente, então Beal fixa `g* = 2` exatamente.
* **`exatamente_uma_par`**: numa solução dois a dois coprima, exatamente uma base é par.
* **`mod8_expoentes_pares`**: `a, b` ímpares, `c` par, `z ≥ 3`: `x` e `y` não podem ser ambos pares.
* **`mod8_expoentes_impares`**: `a, b` ímpares, `x, y` ímpares, `c` par, `z ≥ 3` ⇒ `8 ∣ a + b`.
* **`mod4_x_par`**: `a, b` ímpares, `c` par, `z ≥ 2`, `x` par ⇒ `y` ímpar e `b ≡ 3 (mod 4)`.

São filtros necessários: eliminam famílias de candidatos, não o caso residual (O2 aberta).
-/

namespace ATK.BealFiltros

open ATK.Conditional.Beal

theorem exemplo_mdc_tres : 3 ^ 3 + 6 ^ 3 = 3 ^ 5 ∧ Nat.gcd 3 (Nat.gcd 6 3) = 3 := by norm_num

theorem exemplo_mdc_dois : 2 ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ Nat.gcd 2 (Nat.gcd 2 2) = 2 := by norm_num

/-- Os mdc's das bases de todas as soluções com expoentes `> 2`. -/
def Mdcs : Set ℕ := {g | ∃ a b c x y z : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
  a ^ x + b ^ y = c ^ z ∧ g = Nat.gcd a (Nat.gcd b c)}

/-- `g*`: o menor mdc entre as soluções. -/
noncomputable def gEstrela : ℕ := sInf Mdcs

theorem dois_mem : 2 ∈ Mdcs := ⟨2, 2, 2, 3, 3, 4, by norm_num⟩

theorem tres_mem : 3 ∈ Mdcs := ⟨3, 6, 3, 3, 3, 5, by norm_num⟩

/-- `g* ≤ 2`, incondicionalmente. -/
theorem gEstrela_le_dois : gEstrela ≤ 2 := Nat.sInf_le dois_mem

/-- **Beal ⟺ `g* = 2`.** -/
theorem beal_iff_gEstrela : BealConjecture ↔ gEstrela = 2 := by
  rw [beal_iff_gcdLowerBound]
  constructor
  · intro h
    refine le_antisymm gEstrela_le_dois (le_csInf ⟨2, dois_mem⟩ ?_)
    rintro g ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, he, rfl⟩
    exact h a b c x y z ha hb hc hx hy hz he
  · intro h a b c x y z ha hb hc hx hy hz he
    have hmem : Nat.gcd a (Nat.gcd b c) ∈ Mdcs := ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, he, rfl⟩
    have := Nat.sInf_le hmem
    unfold gEstrela at h
    omega

/-- **Exatamente uma base par** numa solução dois a dois coprima. -/
theorem exatamente_uma_par {a b c x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (h : a ^ x + b ^ y = c ^ z) :
    (Even a ∧ ¬ Even b ∧ ¬ Even c) ∨ (¬ Even a ∧ Even b ∧ ¬ Even c) ∨
      (¬ Even a ∧ ¬ Even b ∧ Even c) := by
  have hpar : (Even (a ^ x) ↔ Even (b ^ y)) ↔ Even (c ^ z) := by rw [← Nat.even_add, h]
  rw [Nat.even_pow' hx, Nat.even_pow' hy, Nat.even_pow' hz] at hpar
  have two_even : ∀ {m n : ℕ}, Nat.Coprime m n → Even m → Even n → False := by
    intro m n hmn hm hn
    have := Nat.dvd_gcd (even_iff_two_dvd.1 hm) (even_iff_two_dvd.1 hn)
    rw [hmn.gcd_eq_one] at this
    norm_num at this
  by_cases ha : Even a <;> by_cases hb : Even b <;> by_cases hc : Even c
  · exact (two_even hab ha hb).elim
  · exact (two_even hab ha hb).elim
  · exact (two_even hac ha hc).elim
  · exact Or.inl ⟨ha, hb, hc⟩
  · exact (two_even hbc hb hc).elim
  · exact Or.inr (Or.inl ⟨ha, hb, hc⟩)
  · exact Or.inr (Or.inr ⟨ha, hb, hc⟩)
  · exact absurd (hpar.1 (iff_of_false ha hb)) hc

theorem sq_mod_oito {m : ℕ} (hm : Odd m) : m ^ 2 % 8 = 1 := by
  have h : m % 2 = 1 := Nat.odd_iff.1 hm
  have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
  rcases this with h8 | h8 | h8 | h8 <;> simp [Nat.pow_mod, h8]

theorem pow_par_mod_oito {m k : ℕ} (hm : Odd m) (hk : Even k) : m ^ k % 8 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul, Nat.pow_mod, sq_mod_oito hm]; simp

theorem pow_impar_mod_oito {m k : ℕ} (hm : Odd m) (hk : Odd k) : m ^ k % 8 = m % 8 := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, sq_mod_oito hm]; simp

theorem oito_dvd_pow {c z : ℕ} (hc : Even c) (hz : 3 ≤ z) : 8 ∣ c ^ z := by
  have h1 : 2 ^ z ∣ c ^ z := pow_dvd_pow_of_dvd (even_iff_two_dvd.1 hc) z
  have h2 : 2 ^ 3 ∣ 2 ^ z := pow_dvd_pow 2 hz
  exact (by norm_num : (8 : ℕ) = 2 ^ 3) ▸ h2.trans h1

theorem quatro_dvd_pow {c z : ℕ} (hc : Even c) (hz : 2 ≤ z) : 4 ∣ c ^ z := by
  have h1 : 2 ^ z ∣ c ^ z := pow_dvd_pow_of_dvd (even_iff_two_dvd.1 hc) z
  have h2 : 2 ^ 2 ∣ 2 ^ z := pow_dvd_pow 2 hz
  exact (by norm_num : (4 : ℕ) = 2 ^ 2) ▸ h2.trans h1

/-- **Módulo 8**: com `a, b` ímpares, `c` par e `z ≥ 3`, os expoentes `x, y` não são ambos pares. -/
theorem mod8_expoentes_pares {a b c x y z : ℕ} (ha : Odd a) (hb : Odd b) (hc : Even c)
    (hx : Even x) (hy : Even y) (hz : 3 ≤ z) : a ^ x + b ^ y ≠ c ^ z := by
  intro h
  have h1 := pow_par_mod_oito ha hx
  have h2 := pow_par_mod_oito hb hy
  have h3 := oito_dvd_pow hc hz
  generalize a ^ x = A at *
  generalize b ^ y = B at *
  generalize c ^ z = C at *
  omega

/-- **Módulo 8**: com `a, b, x, y` ímpares, `c` par e `z ≥ 3`, vale `8 ∣ a + b`. -/
theorem mod8_expoentes_impares {a b c x y z : ℕ} (ha : Odd a) (hb : Odd b) (hc : Even c)
    (hx : Odd x) (hy : Odd y) (hz : 3 ≤ z) (h : a ^ x + b ^ y = c ^ z) : 8 ∣ a + b := by
  have h1 := pow_impar_mod_oito ha hx
  have h2 := pow_impar_mod_oito hb hy
  have h3 := oito_dvd_pow hc hz
  generalize a ^ x = A at *
  generalize b ^ y = B at *
  generalize c ^ z = C at *
  omega

/-- **Módulo 4**: com `a, b` ímpares, `c` par, `z ≥ 2` e `x` par, então `y` é ímpar e `b ≡ 3 (mod 4)`. -/
theorem mod4_x_par {a b c x y z : ℕ} (ha : Odd a) (hb : Odd b) (hc : Even c) (hz : 2 ≤ z)
    (hx : Even x) (h : a ^ x + b ^ y = c ^ z) : Odd y ∧ b % 4 = 3 := by
  have h1 := pow_par_mod_oito ha hx
  have h3 := quatro_dvd_pow hc hz
  have hyo : Odd y := by
    by_contra hy
    rw [Nat.not_odd_iff_even] at hy
    have h2 := pow_par_mod_oito hb hy
    generalize a ^ x = A at *
    generalize b ^ y = B at *
    generalize c ^ z = C at *
    omega
  refine ⟨hyo, ?_⟩
  have h2 := pow_impar_mod_oito hb hyo
  generalize a ^ x = A at *
  generalize b ^ y = B at *
  generalize c ^ z = C at *
  omega

end ATK.BealFiltros

#print axioms ATK.BealFiltros.exemplo_mdc_tres
#print axioms ATK.BealFiltros.exemplo_mdc_dois
#print axioms ATK.BealFiltros.dois_mem
#print axioms ATK.BealFiltros.tres_mem
#print axioms ATK.BealFiltros.gEstrela_le_dois
#print axioms ATK.BealFiltros.beal_iff_gEstrela
#print axioms ATK.BealFiltros.exatamente_uma_par
#print axioms ATK.BealFiltros.sq_mod_oito
#print axioms ATK.BealFiltros.pow_par_mod_oito
#print axioms ATK.BealFiltros.pow_impar_mod_oito
#print axioms ATK.BealFiltros.oito_dvd_pow
#print axioms ATK.BealFiltros.quatro_dvd_pow
#print axioms ATK.BealFiltros.mod8_expoentes_pares
#print axioms ATK.BealFiltros.mod8_expoentes_impares
#print axioms ATK.BealFiltros.mod4_x_par
