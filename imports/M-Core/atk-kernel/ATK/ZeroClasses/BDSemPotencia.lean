import ATK.ZeroClasses.BDTaxaPiso
import ATK.ContracaoDN

/-!
# Sem lei de potência para `D_N` (B1 fraca, `c` arbitrário) e a contração refutada sem o piso citado (rodada 84)

A barreira B1 (o piso de Burnol/BBLS, `D_N ≥ (C − o(1))/log N`) entra no ATK como hipótese citada (`PisoLog`).
A rodada 84 dá uma forma fraca dela **sem hipóteses e para `c` arbitrário**:

  **`TaxaDN (½) κ ⟹ κ ≤ 0`**   (`sem_taxa_meio_DN`).

Para isso, transporta-se a taxa para `σ′ = ½ + h` (`taxaDN_mono`). Lá `Θ < σ′` (`taxaDN_pos`) e
`κ ≤ (2σ′ + 3)(σ′ − Θ)/Θ ≤ 10h` (`taxaDN_teto`). Com `h → 0`, sai `κ ≤ 0`.

* **`DN_sem_potencia`**: o `D_N` de Báez-Duarte não é `O(N^{−δ})` para nenhum `δ > 0`.
* **`contracao_impossivel_incond`**: não existe `q < 1` com `D_{2N} ≤ q D_N` a partir de algum `N₀`. Uma contração
  daria `D_N ≪ N^{−log₂(1/q)}`. É `ContracaoDN.contracao_impossivel` sem a hipótese `PisoLog`.
* `sem_taxa_Teta`: em `σ = Θ` (se `Θ < 1`) também não há taxa positiva. Com o teto da rodada 83, a taxa máxima vai a
  `0` quando `σ ↓ Θ`.

Classificação (rodada 84): **parcial** (B1 sem a taxa `1/log N`; o piso de Burnol para `c` arbitrário segue
BUILD_PENDING). RH continua OPEN_MATH.
-/

open Filter Topology

namespace ATK.ZeroClasses.BDSemPotencia

open ATK.Conditional.Riemann (DN DN_nonneg)
open ATK.RiemannConcrete (DN_antitone DN_le_DN_zero DN_zero_le_one)
open ATK.ZeroClasses.BDPonderado (DNσ DNσ_meio)
open ATK.ZeroClasses.BDTheta (Teta meio_le_Teta TaxaDN)
open ATK.ZeroClasses.BDTaxaPiso (taxaDN_mono taxaDN_pos taxaDN_teto)

/-- **Sem taxa de potência em `σ = ½`** (B1 fraca, `c` arbitrário): `TaxaDN (½) κ ⟹ κ ≤ 0`. -/
theorem sem_taxa_meio_DN {κ : ℝ} (h : TaxaDN (1 / 2) κ) : κ ≤ 0 := by
  by_contra hκ
  push Not at hκ
  have hT12 := meio_le_Teta
  have hT0 : 0 < Teta := by linarith
  set hh : ℝ := min (1 / 4) (κ / 20) with hhdef
  have hh0 : 0 < hh := lt_min (by norm_num) (by positivity)
  have hh1 : hh ≤ 1 / 4 := min_le_left _ _
  have hh2 : hh ≤ κ / 20 := min_le_right _ _
  have hσ' : (1 : ℝ) / 2 ≤ 1 / 2 + hh := by linarith
  have hσ'1 : 1 / 2 + hh < 1 := by linarith
  have ht := taxaDN_mono (by norm_num) hσ' hσ'1 h
  have hT := taxaDN_pos (by linarith) hσ'1 hκ ht
  have h1 := taxaDN_teto hT hσ'1 ht
  have h2 : (2 * (1 / 2 + hh) + 3) * (1 / 2 + hh - Teta) / Teta ≤ κ / 2 := by
    rw [div_le_iff₀ hT0]
    have ha : 2 * (1 / 2 + hh) + 3 ≤ 5 := by linarith
    have hb : 1 / 2 + hh - Teta ≤ hh := by linarith
    have hc : 0 ≤ 1 / 2 + hh - Teta := by linarith
    have hd : (2 * (1 / 2 + hh) + 3) * (1 / 2 + hh - Teta) ≤ 5 * hh :=
      mul_le_mul ha hb hc (by norm_num)
    nlinarith
  linarith

/-- **B1 fraca para o `D_N` de Báez-Duarte**: não existe `δ > 0` com `D_N ≤ K N^{−δ}` para todo `N ≥ 1`. -/
theorem DN_sem_potencia {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → DN N ≤ K * (N : ℝ) ^ (-δ) := by
  rintro ⟨K, hK⟩
  have h : TaxaDN (1 / 2) δ := by
    intro δ' hδ'
    refine ⟨max K 0, fun N hN => ?_⟩
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [DNσ_meio]
    calc DN N ≤ K * (N : ℝ) ^ (-δ) := hK N hN
      _ ≤ max K 0 * (N : ℝ) ^ (-δ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ max K 0 * (N : ℝ) ^ (-δ') :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNr (by linarith)) (le_max_right _ _)
  exact absurd (sem_taxa_meio_DN h) (not_le.mpr hδ)

/-- **A contração por duplicação é impossível**, sem o piso citado de BBLS/Burnol. -/
theorem contracao_impossivel_incond :
    ¬ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, DN (2 * N) ≤ q * DN N := by
  rintro ⟨q, hq0, hq1, N₀, hc⟩
  set q' : ℝ := max q (1 / 2) with hq'
  have hq'0 : 0 < q' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq'1 : q' < 1 := max_lt hq1 (by norm_num)
  have hc' : ∀ N ≥ N₀, DN (2 * N) ≤ q' * DN N := fun N hN =>
    (hc N hN).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (DN_nonneg N))
  set κ : ℝ := -Real.logb 2 q' with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith [Real.logb_neg one_lt_two hq'0 hq'1]
  have hq'κ : q' = (2 : ℝ) ^ (-κ) := by
    rw [hκ, neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hq'0]
  apply DN_sem_potencia hκ0
  set M : ℕ := max N₀ 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMN₀ : N₀ ≤ M := le_max_left _ _
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hM0 : (0 : ℝ) < M := by linarith
  refine ⟨max (DN M * (2 * (M : ℝ)) ^ κ) ((M : ℝ) ^ κ), fun N hN => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNκ : 0 < (N : ℝ) ^ (-κ) := Real.rpow_pos_of_pos hN0 _
  rcases le_or_gt M N with hMN | hMN
  · -- `N ≥ M`: `2^k M ≤ N < 2^{k+1} M`
    set k : ℕ := Nat.log 2 (N / M) with hk
    have hdiv : 1 ≤ N / M := (Nat.one_le_div_iff (by omega)).mpr hMN
    have hk1 : 2 ^ k * M ≤ N := by
      have := Nat.pow_log_le_self 2 (by omega : N / M ≠ 0)
      calc 2 ^ k * M ≤ N / M * M := Nat.mul_le_mul_right M this
        _ ≤ N := Nat.div_mul_le_self N M
    have hk2 : N < 2 ^ (k + 1) * M := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N / M)
      exact (Nat.div_lt_iff_lt_mul (by omega)).mp this
    have hD1 : DN N ≤ DN (2 ^ k * M) := DN_antitone hk1
    have hD2 := ATK.ContracaoDN.iter_contracao hc' hq'0.le hMN₀ k
    -- `q'^k = (2^k)^{−κ} ≤ (N/(2M))^{−κ} = (2M)^κ N^{−κ}`
    have hpk : q' ^ k = ((2 : ℝ) ^ k) ^ (-κ) := by
      rw [hq'κ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num), mul_comm]
    have h2k : (N : ℝ) / (2 * M) ≤ (2 : ℝ) ^ k := by
      rw [div_le_iff₀ (by positivity)]
      have : ((N : ℕ) : ℝ) < ((2 ^ (k + 1) * M : ℕ) : ℝ) := by exact_mod_cast hk2
      push_cast at this
      rw [pow_succ] at this
      linarith
    have hNd : 0 < (N : ℝ) / (2 * M) := by positivity
    have h3 : ((2 : ℝ) ^ k) ^ (-κ) ≤ ((N : ℝ) / (2 * M)) ^ (-κ) :=
      Real.rpow_le_rpow_of_nonpos hNd h2k (by linarith)
    have h4 : ((N : ℝ) / (2 * M)) ^ (-κ) = (2 * (M : ℝ)) ^ κ * (N : ℝ) ^ (-κ) := by
      rw [Real.div_rpow hN0.le (by positivity), Real.rpow_neg (x := 2 * (M : ℝ)) (by positivity) κ,
        div_inv_eq_mul, mul_comm]
    have hDM : 0 ≤ DN M := DN_nonneg M
    calc DN N ≤ DN (2 ^ k * M) := hD1
      _ ≤ q' ^ k * DN M := hD2
      _ ≤ ((N : ℝ) / (2 * M)) ^ (-κ) * DN M := by
          rw [hpk]
          exact mul_le_mul_of_nonneg_right h3 hDM
      _ = DN M * (2 * (M : ℝ)) ^ κ * (N : ℝ) ^ (-κ) := by rw [h4]; ring
      _ ≤ max (DN M * (2 * (M : ℝ)) ^ κ) ((M : ℝ) ^ κ) * (N : ℝ) ^ (-κ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hNκ.le
  · -- `N < M`: `D_N ≤ D_0 ≤ 1 ≤ M^κ N^{−κ}`
    have hNM : (N : ℝ) ≤ M := by exact_mod_cast hMN.le
    have h1 : DN N ≤ 1 := (DN_le_DN_zero N).trans DN_zero_le_one
    have h2 : 1 ≤ (M : ℝ) ^ κ * (N : ℝ) ^ (-κ) := by
      rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hN0 _), one_mul]
      exact Real.rpow_le_rpow hN0.le hNM hκ0.le
    calc DN N ≤ 1 := h1
      _ ≤ (M : ℝ) ^ κ * (N : ℝ) ^ (-κ) := h2
      _ ≤ max (DN M * (2 * (M : ℝ)) ^ κ) ((M : ℝ) ^ κ) * (N : ℝ) ^ (-κ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hNκ.le

/-- **Sem taxa em `σ = Θ`**: se `Θ < 1`, `TaxaDN Θ κ ⟹ κ ≤ 0`; com `taxaDN_teto`, a taxa máxima vai a `0` quando
`σ ↓ Θ`. -/
theorem sem_taxa_Teta {κ : ℝ} (hT1 : Teta < 1) (h : TaxaDN Teta κ) : κ ≤ 0 := by
  by_contra hκ
  push Not at hκ
  have hT0 : 0 < Teta := by linarith [meio_le_Teta]
  exact lt_irrefl _ (taxaDN_pos hT0 hT1 hκ h)

end ATK.ZeroClasses.BDSemPotencia

#print axioms ATK.ZeroClasses.BDSemPotencia.sem_taxa_meio_DN
#print axioms ATK.ZeroClasses.BDSemPotencia.DN_sem_potencia
#print axioms ATK.ZeroClasses.BDSemPotencia.contracao_impossivel_incond
#print axioms ATK.ZeroClasses.BDSemPotencia.sem_taxa_Teta
