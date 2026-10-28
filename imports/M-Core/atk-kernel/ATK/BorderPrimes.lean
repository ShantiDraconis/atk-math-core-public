import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Tactic.NormNum.Prime

/-!
# ATK — Primos de borda (`pi-border-primes`) e as leis L1–L4

O repositório `pi-border-primes` define o primo de borda de um número `C` como `C + k_min`, com
`k_min = min {k > 0 | C + k primo}`, e usa quatro "leis" L1–L4 como filtros. Aqui:

* `L1_impar`, `L2_soma_digitos`, `L3_ultimo_digito`, `L4_mod_seis` — as quatro leis como
  teoremas, e `roda_30`, que mostra que todas são consequência de uma só:
  `p mod 30 ∈ {1, 7, 11, 13, 17, 19, 23, 29}` para `p > 5`. São filtros de resíduo; não dizem nada
  sobre a distribuição dos primos além disso.
* `kMin`, `borda_primo`, `kMin_minimo` — o primo de borda existe para todo `C` e `k_min` é
  realmente o menor.
* `kMin_le_bertrand` — **cota incondicional**: `k_min(C) ≤ C` (postulado de Bertrand, Mathlib).
* `borda_pi100T`, `borda_pi314T` — certificados no kernel: `k_min = 11` para `C = 3095295560` e
  `C = 8178269490`. Atenção: o repositório calcula com os **10 últimos dígitos** de π (essas
  bases), não com o truncamento inteiro `⌊π·10^(N−1)⌋` de 10¹⁴ dígitos; os certificados valem
  para esses números de 10 dígitos, e os dígitos de π são dado externo.

Ligação com RH: `k_min(C)` é limitado pela lacuna entre primos após `C`. Incondicionalmente,
Bertrand dá `k_min ≤ C` (provado aqui) e Baker–Harman–Pintz dá `C^0,525` para `C` grande; sob RH,
Cramér (1920) dá `O(√C · log C)`; a conjectura de Cramér prevê `O(log² C)`, compatível com o
`k_min = 11` observado. Essas cotas condicionais não estão na Mathlib. **CLOSED_MATH continua false.**
-/

namespace ATK.BorderPrimes

/-! ## Leis L1–L4 -/

/-- **L1**: todo primo `p > 2` é ímpar. -/
theorem L1_impar {p : ℕ} (hp : p.Prime) (h : 2 < p) : p % 2 = 1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))

/-- **L2**: para todo primo `p > 3`, a soma dos dígitos não é múltipla de 3. -/
theorem L2_soma_digitos {p : ℕ} (hp : p.Prime) (h : 3 < p) : (Nat.digits 10 p).sum % 3 ≠ 0 := by
  intro h0
  have h3 : 3 ∣ p := (Nat.three_dvd_iff p).mpr (Nat.dvd_of_mod_eq_zero h0)
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
  omega

/-- `p` primo maior que `q` primo não é múltiplo de `q`. -/
theorem nao_divide {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : q < p) : ¬ q ∣ p := by
  intro hd
  have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hd
  omega

/-- **L3**: para todo primo `p > 5`, o último dígito é 1, 3, 7 ou 9. -/
theorem L3_ultimo_digito {p : ℕ} (hp : p.Prime) (h : 5 < p) :
    p % 10 = 1 ∨ p % 10 = 3 ∨ p % 10 = 7 ∨ p % 10 = 9 := by
  have h2 := nao_divide hp Nat.prime_two (by omega)
  have h5 := nao_divide hp Nat.prime_five h
  omega

/-- **L4**: para todo primo `p > 3`, `p mod 6 ∈ {1, 5}`. -/
theorem L4_mod_seis {p : ℕ} (hp : p.Prime) (h : 3 < p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 := nao_divide hp Nat.prime_two (by omega)
  have h3 := nao_divide hp Nat.prime_three h
  omega

/-- **Roda de 30**: L1–L4 são consequências de `p mod 30 ∈ {1,7,11,13,17,19,23,29}`. -/
theorem roda_30 {p : ℕ} (hp : p.Prime) (h : 5 < p) :
    p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨
      p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
  have h2 := nao_divide hp Nat.prime_two (by omega)
  have h3 := nao_divide hp Nat.prime_three (by omega)
  have h5 := nao_divide hp Nat.prime_five h
  have hlt : p % 30 < 30 := Nat.mod_lt _ (by norm_num)
  generalize hr : p % 30 = r at hlt ⊢
  interval_cases r <;> omega

/-! ## Primo de borda -/

/-- Para todo `C` existe `k > 0` com `C + k` primo. -/
theorem existe_borda (C : ℕ) : ∃ k, 0 < k ∧ (C + k).Prime := by
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (C + 1)
  exact ⟨p - C, by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩

/-- `k_min(C)`: o menor `k > 0` com `C + k` primo. -/
def kMin (C : ℕ) : ℕ := Nat.find (existe_borda C)

theorem kMin_pos (C : ℕ) : 0 < kMin C := (Nat.find_spec (existe_borda C)).1

/-- O primo de borda `C + k_min(C)` é primo. -/
theorem borda_primo (C : ℕ) : (C + kMin C).Prime := (Nat.find_spec (existe_borda C)).2

/-- Minimalidade: nenhum `0 < k < k_min(C)` dá primo. -/
theorem kMin_minimo {C k : ℕ} (hk : 0 < k) (hlt : k < kMin C) : ¬ (C + k).Prime :=
  fun hp => Nat.find_min (existe_borda C) hlt ⟨hk, hp⟩

/-- **Cota incondicional (Bertrand)**: `k_min(C) ≤ C` para `C ≥ 1`. -/
theorem kMin_le_bertrand {C : ℕ} (hC : C ≠ 0) : kMin C ≤ C := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul C hC
  have hk : 0 < p - C ∧ (C + (p - C)).Prime := ⟨by omega, by rwa [Nat.add_sub_cancel' hlt.le]⟩
  exact (Nat.find_min' (existe_borda C) hk).trans (by omega)

set_option maxRecDepth 100000 in
/-- **Certificado Pi_100T** (base de 10 dígitos `3095295560`): `k_min = 11`, primo `3095295571`. -/
theorem borda_pi100T : kMin 3095295560 = 11 := by
  rw [kMin, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rintro n hn ⟨hpos, hprime⟩
  interval_cases n <;> norm_num at hprime

set_option maxRecDepth 100000 in
/-- **Certificado Pi_314T** (base de 10 dígitos `8178269490`): `k_min = 11`, primo `8178269501`. -/
theorem borda_pi314T : kMin 8178269490 = 11 := by
  rw [kMin, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rintro n hn ⟨hpos, hprime⟩
  interval_cases n <;> norm_num at hprime

end ATK.BorderPrimes

#print axioms ATK.BorderPrimes.L1_impar
#print axioms ATK.BorderPrimes.L2_soma_digitos
#print axioms ATK.BorderPrimes.nao_divide
#print axioms ATK.BorderPrimes.L3_ultimo_digito
#print axioms ATK.BorderPrimes.L4_mod_seis
#print axioms ATK.BorderPrimes.roda_30
#print axioms ATK.BorderPrimes.existe_borda
#print axioms ATK.BorderPrimes.kMin_pos
#print axioms ATK.BorderPrimes.borda_primo
#print axioms ATK.BorderPrimes.kMin_minimo
#print axioms ATK.BorderPrimes.kMin_le_bertrand
#print axioms ATK.BorderPrimes.borda_pi100T
#print axioms ATK.BorderPrimes.borda_pi314T
