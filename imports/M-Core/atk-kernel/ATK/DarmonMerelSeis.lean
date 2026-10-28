import ATK.DarmonMerelReducao
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# ATK — Ponte B8 (Darmon–Merel): o expoente `6` no caso `C²`

`A⁶ + B⁶ ≠ C²` para `A, B > 0` coprimos (Euler). A prova usa só a Mathlib:

1. um dos dois é par (`A⁶ + B⁶ ≡ 2 (mód 4)` não é quadrado); digamos `A` ímpar, `B = 2B₁`;
2. `(A³, B³, C)` é uma tripla pitagórica primitiva: `A³ = M² − N²`, `B³ = 2MN`, `M > N > 0`
   coprimos de paridades opostas (`PythagoreanTriple.coprime_classification'`);
3. `M − N` e `M + N` são coprimos com produto `A³`, logo cubos `s³`, `t³` (`cubo`); e
   `MN = 4B₁³` com o fator par igual a `4u³` (`par_cubo`);
4. se `M = 4u³`, `s³ + t³ = 2M = (2u)³`; se `N = 4u³`, `s³ + (2u)³ = t³` — ambos contradizem
   FLT(3) (`fermatLastTheoremThree`, Mathlib).

Com `ATK.DarmonMerelReducao.darmonMerel_iff`, a ponte B8 passa a equivaler aos casos `C²` com
`n = 9` ou `n` primo `≥ 5` e `C³` com `n = 4` ou `n` primo `≥ 5` (`darmonMerel_iff_reduzido`).
B8 continua `PUBLICADA_NAO_FORMALIZADA`.
-/

namespace ATK.DarmonMerelSeis

open ATK.DarmonMerelReducao ATK.BealDarmonMerel

/-- Fatores coprimos de um cubo em `ℕ` são cubos. -/
theorem cubo {a b c : ℕ} (h : Nat.Coprime a b) (he : a * b = c ^ 3) : ∃ d, a = d ^ 3 :=
  exists_eq_pow_of_mul_eq_pow (by rw [Nat.isUnit_iff]; exact h) he

/-- Se `o` é ímpar, coprimo com `e`, e `o·e = 4B³`, então `e = 4u³`. -/
theorem par_cubo {o e B : ℕ} (ho : Odd o) (hc : Nat.Coprime o e) (h : o * e = 4 * B ^ 3) :
    ∃ u, e = 4 * u ^ 3 := by
  have h2o : Nat.Coprime 2 o := Nat.coprime_two_left.mpr ho
  have h4o : Nat.Coprime 4 o := by
    have := Nat.Coprime.pow_left 2 h2o
    norm_num at this
    exact this
  have h4 : 4 ∣ e := by
    apply h4o.dvd_of_dvd_mul_left
    exact ⟨B ^ 3, h⟩
  obtain ⟨e₂, rfl⟩ := h4
  have h' : e₂ * o = B ^ 3 := by
    have : 4 * (e₂ * o) = 4 * B ^ 3 := by rw [← h]; ring
    omega
  have hc' : Nat.Coprime e₂ o :=
    (Nat.Coprime.coprime_dvd_right (Dvd.intro_left 4 rfl) hc).symm
  obtain ⟨u, hu⟩ := cubo hc' h'
  exact ⟨u, by rw [hu]⟩

/-- O caso `A` ímpar. -/
theorem seis_impar {A B C : ℕ} (hA : Odd A) (hB : 0 < B) (hAB : Nat.Coprime A B)
    (h : A ^ 6 + B ^ 6 = C ^ 2) : False := by
  -- `B` é par (mód 4)
  have hBe : Even B := by
    by_contra hBo
    rw [Nat.not_even_iff_odd] at hBo
    have hA4 : A % 4 = 1 ∨ A % 4 = 3 := by obtain ⟨k, rfl⟩ := hA; omega
    have hB4 : B % 4 = 1 ∨ B % 4 = 3 := by obtain ⟨k, rfl⟩ := hBo; omega
    have hC4 : C % 4 = 0 ∨ C % 4 = 1 ∨ C % 4 = 2 ∨ C % 4 = 3 := by omega
    have hm : (A ^ 6 + B ^ 6) % 4 = C ^ 2 % 4 := by rw [h]
    rw [Nat.add_mod, Nat.pow_mod A, Nat.pow_mod B, Nat.pow_mod C] at hm
    rcases hA4 with h1 | h1 <;> rcases hB4 with h2 | h2 <;>
      rcases hC4 with h3 | h3 | h3 | h3 <;> rw [h1, h2, h3] at hm <;> norm_num at hm
  obtain ⟨B₁, hB₁⟩ := hBe
  -- tripla pitagórica primitiva `(A³, B³, C)`
  have hC : 0 < C := by
    rcases Nat.eq_zero_or_pos C with rfl | hC
    · have : 0 < A ^ 6 + B ^ 6 := by positivity
      rw [h] at this
      norm_num at this
    · exact hC
  have hpt : PythagoreanTriple ((A : ℤ) ^ 3) ((B : ℤ) ^ 3) (C : ℤ) := by
    unfold PythagoreanTriple
    have : ((A ^ 6 + B ^ 6 : ℕ) : ℤ) = ((C ^ 2 : ℕ) : ℤ) := by rw [h]
    push_cast at this
    linear_combination this
  have hgcd : Int.gcd ((A : ℤ) ^ 3) ((B : ℤ) ^ 3) = 1 := by
    have : ((A : ℤ) ^ 3) = ((A ^ 3 : ℕ) : ℤ) := by push_cast; rfl
    have h2 : ((B : ℤ) ^ 3) = ((B ^ 3 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, h2, Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow 3 3 hAB
  have hpar : (A : ℤ) ^ 3 % 2 = 1 := by
    have : Odd ((A : ℤ) ^ 3) := by exact_mod_cast hA.pow
    exact Int.odd_iff.mp this
  obtain ⟨m, n, hx, hy, -, hmn, hpar2, hm0⟩ :=
    PythagoreanTriple.coprime_classification' hpt hgcd hpar (by exact_mod_cast hC)
  -- `m > n > 0`
  have hBpos : (0 : ℤ) < (B : ℤ) ^ 3 := by positivity
  have hApos : (0 : ℤ) < (A : ℤ) ^ 3 := by
    have : 0 < A := hA.pos
    positivity
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0] at hy; simp at hy; linarith
  have hnpos : 0 < n := by
    by_contra hn
    push Not at hn
    have : 2 * m * n ≤ 0 := by nlinarith
    linarith
  have hnm : n < m := by
    by_contra hc
    push Not at hc
    have : m ^ 2 - n ^ 2 ≤ 0 := by nlinarith
    linarith
  obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hnpos.le
  have hNM : N < M := by exact_mod_cast hnm
  have hN0 : 0 < N := by exact_mod_cast hnpos
  -- de volta a `ℕ`
  have hx' : (M - N) * (M + N) = A ^ 3 := by
    have : (((M - N) * (M + N) : ℕ) : ℤ) = ((A ^ 3 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hNM.le]
      linear_combination -hx
    exact_mod_cast this
  have hy' : 2 * M * N = B ^ 3 := by
    have : ((2 * M * N : ℕ) : ℤ) = ((B ^ 3 : ℕ) : ℤ) := by
      push_cast
      linear_combination -hy
    exact_mod_cast this
  have hcop : Nat.Coprime M N := by
    rw [Int.gcd_natCast_natCast] at hmn
    exact hmn
  have hparN : (M % 2 = 0 ∧ N % 2 = 1) ∨ (M % 2 = 1 ∧ N % 2 = 0) := by omega
  -- `M − N` e `M + N` são coprimos, logo cubos
  have hcop2 : Nat.Coprime (M - N) (M + N) := by
    have h1 : Nat.gcd (M - N) (M + N) ∣ 2 * M := by
      have := Nat.dvd_add (Nat.gcd_dvd_left (M - N) (M + N)) (Nat.gcd_dvd_right (M - N) (M + N))
      rwa [show M - N + (M + N) = 2 * M by omega] at this
    have h2 : Nat.gcd (M - N) (M + N) ∣ 2 * N := by
      have := Nat.dvd_sub (Nat.gcd_dvd_right (M - N) (M + N)) (Nat.gcd_dvd_left (M - N) (M + N))
      rwa [show M + N - (M - N) = 2 * N by omega] at this
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.gcd_mul_left, hcop, mul_one] at h3
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h4 | h4
    · exact h4
    · exfalso
      have h5 := Nat.gcd_dvd_right (M - N) (M + N)
      rw [h4] at h5
      omega
  obtain ⟨s, hs⟩ := cubo hcop2 hx'
  obtain ⟨t, ht⟩ := cubo hcop2.symm (by rw [mul_comm]; exact hx')
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    omega
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    omega
  have hMN : M * N = 4 * B₁ ^ 3 := by
    have : 2 * (M * N) = 2 * (4 * B₁ ^ 3) := by
      rw [← mul_assoc, hy', hB₁]; ring
    omega
  rcases hparN with ⟨hM2, hN2⟩ | ⟨hM2, hN2⟩
  · -- `M = 4u³`: `s³ + t³ = 2M = (2u)³`
    obtain ⟨u, hu⟩ := par_cubo (Nat.odd_iff.mpr hN2)
      hcop.symm (by rw [mul_comm]; exact hMN)
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
      omega
    apply fermatLastTheoremThree s t (2 * u) hs0 ht0 (by positivity)
    rw [← hs, ← ht]
    have : M - N + (M + N) = 2 * M := by omega
    rw [this, hu]
    ring
  · -- `N = 4u³`: `s³ + (2u)³ = t³`
    obtain ⟨u, hu⟩ := par_cubo (Nat.odd_iff.mpr hM2) hcop hMN
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
      omega
    apply fermatLastTheoremThree s (2 * u) t hs0 (by positivity) ht0
    rw [← hs, ← ht]
    have : M + N = M - N + 2 * N := by omega
    rw [this, hu]
    ring

/-- **`A⁶ + B⁶ ≠ C²`** para `A, B > 0` coprimos (Euler), a partir de FLT(3) da Mathlib e da
classificação das triplas pitagóricas. -/
theorem dmSq_seis : DMSq 6 := by
  intro A B C hA hB hAB h
  rcases Nat.even_or_odd A with hAe | hAo
  · rcases Nat.even_or_odd B with hBe | hBo
    · have h2 : 2 ∣ Nat.gcd A B := Nat.dvd_gcd (even_iff_two_dvd.mp hAe) (even_iff_two_dvd.mp hBe)
      rw [hAB] at h2
      omega
    · exact seis_impar hBo hA hAB.symm (by rw [add_comm]; exact h)
  · exact seis_impar hAo hB hAB h

/-- **A ponte B8 reduzida de novo**: com `n = 6` provado, `DarmonMerel` equivale aos casos `C²` com
`n = 9` ou primo `≥ 5` e `C³` com `n = 4` ou primo `≥ 5`. -/
theorem darmonMerel_iff_reduzido :
    DarmonMerel ↔ (DMSq 9 ∧ ∀ p, p.Prime → 5 ≤ p → DMSq p) ∧
      (DMCube 4 ∧ ∀ p, p.Prime → 5 ≤ p → DMCube p) := by
  rw [darmonMerel_iff]
  constructor
  · rintro ⟨⟨-, h9, hp⟩, hc⟩
    exact ⟨⟨h9, hp⟩, hc⟩
  · rintro ⟨⟨h9, hp⟩, hc⟩
    exact ⟨⟨dmSq_seis, h9, hp⟩, hc⟩

end ATK.DarmonMerelSeis

#print axioms ATK.DarmonMerelSeis.cubo
#print axioms ATK.DarmonMerelSeis.par_cubo
#print axioms ATK.DarmonMerelSeis.seis_impar
#print axioms ATK.DarmonMerelSeis.dmSq_seis
#print axioms ATK.DarmonMerelSeis.darmonMerel_iff_reduzido
