import ATK.ZeroClasses.BDPisoL1

/-!
# Burnol restrito: `D_N ≥ c/(A log N + B)` na classe `‖c‖₁ ≤ N^A`, e um critério de RH num único `σ` (rodada 80)

A barreira B1 de `fronteira/RH_frontier.md` (o piso de Burnol `D_N ≥ (C − o(1))/log N`) é um teorema citado no ATK.
Aqui ela fica provada na classe `‖c‖₁ ≤ N^A`, pelo argumento da rodada 79 com o zero **na** reta do peso.

Se `ζ(ρ) = 0` com `Re ρ = σ ∈ (0, 1)`, a integral do meio é `∫_ε^1 dt/t = log(1/ε)` (`J_reta`), e com
`ε^σ ≍ 1/(1 + ‖c‖₁)` sai

  **`‖res‖²_σ ≥ C/(log(1 + ‖c‖₁) + B)`**   (`piso_reta`).

Consequências:
* **`burnol_L1`**: em `σ = ½`, pelos zeros de Hardy, `D_N^{(N^A)} ≥ C/(A log N + B)` para `N ≥ 1`. É Burnol na
  classe restrita, com o `D_N` de Báez-Duarte (`DNσ_meio`).
* `taxaL_reta`: um zero na reta `Re s = σ` impede qualquer taxa de potência na classe restrita.
* **`taxaL_pos`**: para `0 < σ < 1`, `κ > 0` e `A ≥ 0`, a hipótese `TaxaL σ A κ` dá `Θ < σ` e `Θ(κ + 2A) ≤ 2Aσ`.
  Os três casos são `σ < Θ` (`piso_abaixo`), `σ = Θ` (zeros com `Re ρ → σ` ou na reta) e `σ > Θ` (rodada 79).
  Uma taxa `ℓ¹` positiva num único `σ` certifica o semiplano sem zeros `Re s > 2Aσ/(κ + 2A)`.
* **`rh_of_taxaL`**: se `TaxaL σ₀ 1 (4σ₀ − 2)` para **um** `σ₀ ∈ (½, 1)`, então RH. Sob RH, o molificador dá
  `2σ₀ − 1` (rodada 79): a lacuna entre `2σ₀ − 1` e `4σ₀ − 2` é o fator `1/Θ`.

Classificação (rodada 80): **parcial** (B1 na classe `‖c‖₁ ≤ N^A`; Burnol para `c` arbitrário segue
BUILD_PENDING) e **reformulação** (o critério num `σ`). RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology Metric Asymptotics
open scoped Real

namespace ATK.ZeroClasses.BDBurnolL1

open ATK.BaezDuarteBridge (res tailS mellin_res norm_mellin_le integral_tail_weighted)
open ATK.ZeroClasses.BDPonderado (Wσ DNσ DNσ_nonneg Wσ_nonneg tail_sq_le)
open ATK.ZeroClasses.BDTheta (Teta meio_le_Teta re_le_Teta existe_zero piso_abaixo rh_iff_Teta)
open ATK.ZeroClasses.BDPisoL1 (head0_le mid_le DNσL DNσL_le DNσ_le_DNσL TaxaL taxaL_le_zero taxaL_Teta)

/-! ## 1. O piso com o zero na reta do peso -/

/-- `∫_ε^1 t^{2(σ−σ)−1} dt = −log ε`. -/
theorem J_reta {σ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ t in Ioc ε 1, t ^ (2 * (σ - σ) - 1) = -Real.log ε := by
  have e : ∀ t ∈ Ioc ε 1, t ^ (2 * (σ - σ) - 1) = t⁻¹ := by
    intro t ht
    rw [show 2 * (σ - σ) - 1 = (-1 : ℝ) by ring, Real.rpow_neg_one]
  rw [setIntegral_congr_fun measurableSet_Ioc e, ← intervalIntegral.integral_of_le hε1,
    integral_inv_of_pos hε zero_lt_one, one_div, Real.log_inv]

/-- **A desigualdade-chave na reta**: se `ζ(s) = 0` com `Re s = σ ∈ (0, 1)`, então para `0 < ε ≤ 1` e `λ > 0`,
`1/|s| ≤ (1 + ‖c‖₁) ε^σ/σ + (λW + (1 − log ε)/λ)/2 + √((2 − 2σ)W)/(1 − σ)`. -/
theorem key_reta {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {s : ℂ} (hsσ : s.re = σ)
    (hz : riemannZeta s = 0) {ε l : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 0 < l) :
    1 / ‖s‖ ≤ (1 + ∑ k : Fin N, |c k|) * (ε ^ σ / σ) +
      (l * Wσ σ c + (1 - Real.log ε) / l) / 2 +
      Real.sqrt ((2 - 2 * σ) * Wσ σ c) / (1 - σ) := by
  have hs0 : 0 < s.re := by rw [hsσ]; exact hσ0
  have hs1 : s.re < 1 := by rw [hsσ]; exact hσ1
  obtain ⟨hconv, hval⟩ := mellin_res c hs0 hs1 hz
  have hnorm := norm_mellin_le (res c) s
  rw [hval, norm_div, norm_one] at hnorm
  have hw : IntegrableOn (fun t => t ^ (s.re - 1) * |res c t|) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.norm hconv) (fun t ht => ?_) measurableSet_Ioi
    simp only
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hsσ] at hw
  have hsplit : ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * |res c t| =
      (∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * |res c t|) +
        ∫ t in Ioi (1 : ℝ), t ^ (σ - 1) * |res c t| := by
    have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2)
    have hu := setIntegral_union hdisj measurableSet_Ioi (hw.mono_set Ioc_subset_Ioi_self)
      (hw.mono_set (Ioi_subset_Ioi zero_le_one))
    rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
    exact hu
  have hsplit2 : ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * |res c t| =
      (∫ t in Ioc (0 : ℝ) ε, t ^ (σ - 1) * |res c t|) +
        ∫ t in Ioc ε 1, t ^ (σ - 1) * |res c t| := by
    have hdisj : Disjoint (Ioc (0 : ℝ) ε) (Ioc ε 1) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)
    have h01 : Ioc (0 : ℝ) ε ⊆ Ioi 0 := Ioc_subset_Ioi_self
    have h02 : Ioc ε 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hε.le)
    have hu := setIntegral_union hdisj measurableSet_Ioc (hw.mono_set h01) (hw.mono_set h02)
    rw [Ioc_union_Ioc_eq_Ioc hε.le hε1] at hu
    exact hu
  have hhead := head0_le c hσ0 hε
  have hmid := mid_le c hσ0 hσ1 hε hε1 hl (β := σ)
    (hw.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hε.le)))
  rw [J_reta hε hε1] at hmid
  have hmid' : ∫ t in Ioc ε 1, t ^ (σ - 1) * |res c t| ≤ (l * Wσ σ c + (1 - Real.log ε) / l) / 2 := by
    refine hmid.trans ?_
    have : -Real.log ε / l ≤ (1 - Real.log ε) / l := div_le_div_of_nonneg_right (by linarith) hl.le
    linarith
  have htail := integral_tail_weighted c hσ1
  have hS : |tailS c| ≤ Real.sqrt ((2 - 2 * σ) * Wσ σ c) := Real.abs_le_sqrt (tail_sq_le c hσ0 hσ1)
  have h1σ : 0 < 1 - σ := by linarith
  have hS' : |tailS c| / (1 - σ) ≤ Real.sqrt ((2 - 2 * σ) * Wσ σ c) / (1 - σ) :=
    div_le_div_of_nonneg_right hS h1σ.le
  rw [hsσ] at hnorm
  calc 1 / ‖s‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * |res c t| := hnorm
    _ = _ := by rw [hsplit, hsplit2]
    _ ≤ _ := by
        rw [htail]
        linarith

/-- **O piso na reta**: se `ζ(ρ) = 0` com `Re ρ = σ ∈ (0, 1)`, há `C, B > 0` com
`‖res‖²_σ ≥ C/(log(1 + ‖c‖₁) + B)` para todo `N` e todo `c`. -/
theorem piso_reta {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {s : ℂ} (hsσ : s.re = σ) (hz : riemannZeta s = 0) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ {N : ℕ} (c : Fin N → ℝ),
      C / (Real.log (1 + ∑ k : Fin N, |c k|) + B) ≤ Wσ σ c := by
  have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hsσ; linarith
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  set r : ℝ := 1 / (2 * ‖s‖) with hr
  have hr0 : 0 < r := by positivity
  set m0 : ℝ := min 1 (r * σ) with hm0
  have hm00 : 0 < m0 := lt_min one_pos (mul_pos hr0 hσ0)
  have hm01 : m0 ≤ 1 := min_le_left _ _
  have hlm0 : Real.log m0 ≤ 0 := Real.log_nonpos hm00.le hm01
  have h2σ : 0 < 2 - 2 * σ := by linarith
  have h1σ : 0 < 1 - σ := by linarith
  set C₀ : ℝ := min (3 * r ^ 2 / 8) ((3 * r * (1 - σ) / 8) ^ 2 / (2 - 2 * σ)) with hC₀
  have hC₀0 : 0 < C₀ := lt_min (by positivity) (div_pos (by positivity) h2σ)
  refine ⟨C₀ * σ, σ - Real.log m0, mul_pos hC₀0 hσ0, by linarith, fun {N} c => ?_⟩
  set L : ℝ := 1 + ∑ k : Fin N, |c k| with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ ∑ k : Fin N, |c k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  have hL0 : 0 < L := by linarith
  set W : ℝ := Wσ σ c with hW
  have hW0 : 0 ≤ W := Wσ_nonneg σ c
  set m : ℝ := min 1 (r * σ / L) with hm
  have hm0' : 0 < m := lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  set ε : ℝ := m ^ σ⁻¹ with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hm0' _
  have hε1 : ε ≤ 1 := Real.rpow_le_one hm0'.le hm1 (inv_nonneg.mpr hσ0.le)
  have hεσ : ε ^ σ = m := Real.rpow_inv_rpow hm0'.le hσ0.ne'
  have hlε : Real.log ε ≤ 0 := Real.log_nonpos hε0.le hε1
  set J₁ : ℝ := 1 - Real.log ε with hJ₁
  have hJ1 : 1 ≤ J₁ := by linarith
  have hJ0 : 0 < J₁ := by linarith
  set l : ℝ := 2 * J₁ / r with hl
  have hl0 : 0 < l := by positivity
  have hkey := key_reta c hσ0 hσ1 hsσ hz hε0 hε1 hl0
  rw [← hJ₁, ← hW, ← hL] at hkey
  have hhead : L * (ε ^ σ / σ) ≤ r := by
    rw [hεσ]
    have : m ≤ r * σ / L := min_le_right _ _
    rw [mul_div_assoc', div_le_iff₀ hσ0]
    rw [le_div_iff₀ hL0] at this
    linarith
  have hJl : J₁ / l = r / 2 := by
    rw [hl]
    field_simp
  have hlW : l * W / 2 = J₁ / r * W := by
    rw [hl]
    field_simp
  have h2r : 1 / ‖s‖ = 2 * r := by
    rw [hr]
    field_simp
  set Q : ℝ := Real.sqrt ((2 - 2 * σ) * W) / (1 - σ) with hQ
  have hmain : 3 * r / 4 ≤ J₁ / r * W + Q := by
    have e : (l * W + J₁ / l) / 2 = J₁ / r * W + r / 4 := by
      rw [hJl, add_div, hlW]
      ring
    rw [e, h2r] at hkey
    linarith
  have hWge : C₀ / J₁ ≤ W := by
    rcases le_or_gt (3 * r / 8) (J₁ / r * W) with hA | hA
    · have hW1 : 3 * r ^ 2 / 8 / J₁ ≤ W := by
        rw [div_le_iff₀ hJ0]
        rw [div_mul_eq_mul_div, le_div_iff₀ hr0] at hA
        nlinarith
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hJ0.le).trans hW1
    · have hQ' : 3 * r / 8 ≤ Q := by linarith
      rw [hQ, le_div_iff₀ h1σ] at hQ'
      have hsq : (3 * r / 8 * (1 - σ)) ^ 2 ≤ (2 - 2 * σ) * W := by
        have h0 : 0 ≤ 3 * r / 8 * (1 - σ) := by positivity
        calc (3 * r / 8 * (1 - σ)) ^ 2 ≤ Real.sqrt ((2 - 2 * σ) * W) ^ 2 := pow_le_pow_left₀ h0 hQ' 2
          _ = (2 - 2 * σ) * W := Real.sq_sqrt (mul_nonneg h2σ.le hW0)
      have hW1 : (3 * r * (1 - σ) / 8) ^ 2 / (2 - 2 * σ) ≤ W := by
        rw [div_le_iff₀ h2σ]
        have e : (3 * r * (1 - σ) / 8) = 3 * r / 8 * (1 - σ) := by ring
        rw [e]
        linarith
      calc C₀ / J₁ ≤ C₀ := div_le_self hC₀0.le hJ1
        _ ≤ _ := min_le_right _ _
        _ ≤ W := hW1
  -- `J₁ ≤ (log L − log m0)/σ + 1`
  have hmm : m0 / L ≤ m := by
    apply le_min
    · rw [div_le_one hL0]
      exact hm01.trans hL1
    · exact div_le_div_of_nonneg_right (min_le_right _ _) hL0.le
  have hlogm : Real.log m0 - Real.log L ≤ Real.log m := by
    rw [← Real.log_div hm00.ne' hL0.ne']
    exact Real.log_le_log (by positivity) hmm
  have hlogε : Real.log ε = σ⁻¹ * Real.log m := by rw [hε, Real.log_rpow hm0']
  have hJle : J₁ ≤ (Real.log L + (σ - Real.log m0)) / σ := by
    rw [hJ₁, hlogε, le_div_iff₀ hσ0]
    have : σ⁻¹ * Real.log m * σ = Real.log m := by field_simp
    nlinarith
  have hD : 0 < Real.log L + (σ - Real.log m0) := by
    have := Real.log_nonneg hL1
    linarith
  calc C₀ * σ / (Real.log L + (σ - Real.log m0)) = C₀ / ((Real.log L + (σ - Real.log m0)) / σ) := by
        field_simp
    _ ≤ C₀ / J₁ := div_le_div_of_nonneg_left hC₀0.le hJ0 hJle
    _ ≤ W := hWge

/-- O piso na reta na classe `‖c‖₁ ≤ L`: `D_N^{(L)}(σ) ≥ C/(log(1 + L) + B)`. -/
theorem piso_DNσL_reta {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {s : ℂ} (hsσ : s.re = σ)
    (hz : riemannZeta s = 0) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ (L : ℝ) (N : ℕ), 0 ≤ L → C / (Real.log (1 + L) + B) ≤ DNσL σ L N := by
  obtain ⟨C, B, hC0, hB0, hC⟩ := piso_reta hσ0 hσ1 hsσ hz
  refine ⟨C, B, hC0, hB0, fun L N hL => ?_⟩
  have : Nonempty {c : Fin N → ℝ // ∑ k, |c k| ≤ L} := ⟨⟨0, by simpa using hL⟩⟩
  refine le_ciInf fun c => le_trans ?_ (hC c.1)
  have h0 : 0 ≤ ∑ k, |c.1 k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hl0 : 0 ≤ Real.log (1 + ∑ k, |c.1 k|) := Real.log_nonneg (by linarith)
  apply div_le_div_of_nonneg_left hC0.le (by linarith)
  have := Real.log_le_log (by linarith) (by linarith [c.2] : 1 + ∑ k, |c.1 k| ≤ 1 + L)
  linarith

/-! ## 2. Burnol restrito -/

/-- `log(1 + N^A) ≤ log 2 + A log N` para `N ≥ 1`, `A ≥ 0`. -/
theorem log_um_add_le {A : ℝ} (hA : 0 ≤ A) {N : ℕ} (hN : 1 ≤ N) :
    Real.log (1 + (N : ℝ) ^ A) ≤ Real.log 2 + A * Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNA : 1 ≤ (N : ℝ) ^ A := Real.one_le_rpow hNr hA
  have h1 : Real.log (1 + (N : ℝ) ^ A) ≤ Real.log (2 * (N : ℝ) ^ A) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) (by linarith), Real.log_rpow hN0] at h1
  exact h1

/-- **Burnol na classe `‖c‖₁ ≤ N^A`**: em `σ = ½` há `C, B > 0` com `D_N^{(N^A)} ≥ C/(A log N + B)` para todo
`N ≥ 1` (pelos zeros de Hardy na reta crítica). -/
theorem burnol_L1 {A : ℝ} (hA : 0 ≤ A) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N →
      C / (A * Real.log N + B) ≤ DNσL (1 / 2) ((N : ℝ) ^ A) N := by
  obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  obtain ⟨C, B, hC0, hB0, hC⟩ :=
    piso_DNσL_reta (σ := 1 / 2) (by norm_num) (by norm_num) (ATK.ZeroClasses.Omega.re_zero_reta γ) hγ
  refine ⟨C, Real.log 2 + B, hC0, by positivity, fun N hN => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNA : 1 ≤ (N : ℝ) ^ A := Real.one_le_rpow hNr hA
  have h := hC ((N : ℝ) ^ A) N (by linarith)
  refine le_trans ?_ h
  have hlog := log_um_add_le hA hN
  have hl0 : 0 ≤ Real.log (1 + (N : ℝ) ^ A) := Real.log_nonneg (by linarith)
  exact div_le_div_of_nonneg_left hC0.le (by linarith) (by linarith)

/-! ## 3. Taxas `ℓ¹` positivas certificam semiplanos -/

/-- **Um zero na reta do peso impede taxa de potência**: se `ζ(ρ) = 0` com `Re ρ = σ ∈ (0, 1)`, então
`TaxaL σ A κ ⟹ κ ≤ 0`. -/
theorem taxaL_reta {σ A κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hA : 0 ≤ A) {s : ℂ} (hsσ : s.re = σ)
    (hz : riemannZeta s = 0) (hT : TaxaL σ A κ) : κ ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨K, hK⟩ := hT (κ / 2) (by linarith)
  obtain ⟨C, B, hC0, hB0, hC⟩ := piso_DNσL_reta hσ0 hσ1 hsσ hz
  set B' : ℝ := Real.log 2 + B with hB'
  have hB'0 : 0 < B' := by rw [hB']; positivity
  have hlim : Tendsto (fun x : ℝ => (A * Real.log x + B') * x ^ (-(κ / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (κ / 2)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by linarith)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun x : ℝ => x ^ (-(κ / 2))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by linarith)
    have := (h1.const_mul A).add (h2.const_mul B')
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
    ring
  have hlimN := hlim.comp tendsto_natCast_atTop_atTop
  have hK1 : 0 < |K| + 1 := by positivity
  obtain ⟨N, hNs, hN1⟩ :=
    ((hlimN.eventually (gt_mem_nhds (div_pos hC0 hK1))).and (eventually_ge_atTop 1)).exists
  simp only [Function.comp_apply] at hNs
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hD : 0 < A * Real.log N + B' := by have := mul_nonneg hA hlogN; linarith
  have hfl := hC ((N : ℝ) ^ A) N (Real.rpow_nonneg hN0.le _)
  have hlog := log_um_add_le hA hN1
  have hl0 : 0 ≤ Real.log (1 + (N : ℝ) ^ A) := Real.log_nonneg (by linarith [Real.rpow_nonneg hN0.le A])
  have h1 : C / (A * Real.log N + B') ≤ K * (N : ℝ) ^ (-(κ / 2)) :=
    ((div_le_div_of_nonneg_left hC0.le (by linarith) (by linarith)).trans hfl).trans (hK N hN1)
  rw [div_le_iff₀ hD] at h1
  have hf0 : 0 ≤ (A * Real.log N + B') * (N : ℝ) ^ (-(κ / 2)) :=
    mul_nonneg hD.le (Real.rpow_nonneg hN0.le _)
  have h2 : K * (N : ℝ) ^ (-(κ / 2)) * (A * Real.log N + B') ≤
      (|K| + 1) * ((A * Real.log N + B') * (N : ℝ) ^ (-(κ / 2))) := by
    have : K * (N : ℝ) ^ (-(κ / 2)) * (A * Real.log N + B') = K * ((A * Real.log N + B') * (N : ℝ) ^ (-(κ / 2))) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hf0
  have h3 : (|K| + 1) * ((A * Real.log N + B') * (N : ℝ) ^ (-(κ / 2))) < C := by
    rw [lt_div_iff₀ hK1] at hNs
    linarith
  linarith

/-- **Sem taxa de potência em `σ = ½`** na classe `‖c‖₁ ≤ N^A` (B1 restrita): `TaxaL (½) A κ ⟹ κ ≤ 0`. -/
theorem sem_taxa_meio {A κ : ℝ} (hA : 0 ≤ A) (hT : TaxaL (1 / 2) A κ) : κ ≤ 0 := by
  obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  exact taxaL_reta (by norm_num) (by norm_num) hA (ATK.ZeroClasses.Omega.re_zero_reta γ) hγ hT

/-- **Uma taxa `ℓ¹` positiva certifica um semiplano**: para `0 < σ < 1`, `A ≥ 0`, `κ > 0`, a hipótese
`TaxaL σ A κ` dá `Θ < σ` e `Θ (κ + 2A) ≤ 2Aσ`; logo `ζ ≠ 0` em `Re s > 2Aσ/(κ + 2A)`. -/
theorem taxaL_pos {σ A κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hA : 0 ≤ A) (hκ : 0 < κ) (hT : TaxaL σ A κ) :
    Teta < σ ∧ Teta * (κ + 2 * A) ≤ 2 * A * σ := by
  have hreta : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≠ σ := fun ρ hρ h => by
    have := taxaL_reta hσ0 hσ1 hA h hρ hT
    linarith
  have hT12 := meio_le_Teta
  have hTσ : Teta < σ := by
    rcases lt_trichotomy σ Teta with h | h | h
    · exfalso
      have hp := piso_abaixo hσ0 h
      obtain ⟨K, hK⟩ := hT (κ / 2) (by linarith)
      have hlim : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-(κ / 2))) atTop (𝓝 0) := by
        have := ((tendsto_rpow_neg_atTop (by linarith : 0 < κ / 2)).comp
          tendsto_natCast_atTop_atTop).const_mul K
        simpa using this
      obtain ⟨N, hNs, hN1⟩ := ((hlim.eventually (gt_mem_nhds hp)).and (eventually_ge_atTop 1)).exists
      have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
      have h1 : ⨅ M, DNσ σ M ≤ DNσ σ N := ciInf_le ⟨0, fun _ ⟨M, hM⟩ => hM ▸ DNσ_nonneg σ M⟩ N
      have h2 := DNσ_le_DNσL (σ := σ) (Real.rpow_nonneg hN0 A) N
      have h3 := hK N hN1
      linarith
    · exfalso
      rcases eq_or_lt_of_le hT12 with h12 | h12
      · obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
        exact hreta _ hγ (by rw [ATK.ZeroClasses.Omega.re_zero_reta, h, h12])
      · have hk : 0 < κ + 2 * A := by linarith
        set θs : ℝ := 2 * A * σ / (κ + 2 * A) with hθs
        have hθsk : θs * (κ + 2 * A) = 2 * A * σ := by rw [hθs]; field_simp
        have hθsσ : θs < σ := by
          by_contra hc
          push Not at hc
          have := mul_le_mul_of_nonneg_right hc hk.le
          nlinarith
        set θ' : ℝ := max (1 / 2) ((θs + σ) / 2) with hθ'
        have hθ'σ : θ' < σ := max_lt (by linarith) (by linarith)
        obtain ⟨ρ, hρ, hρθ⟩ := existe_zero (le_max_left _ _) (by rw [← h]; exact hθ'σ)
        have hρle : ρ.re ≤ σ := h ▸ re_le_Teta hρ
        have hρlt : ρ.re < σ := lt_of_le_of_ne hρle (hreta ρ hρ)
        have hρ0 : 0 < ρ.re := by linarith [le_max_left (1 / 2 : ℝ) ((θs + σ) / 2)]
        have hb := taxaL_le_zero hσ0 hσ1 hA hρ0 hρlt hρ hT
        rw [mul_div_assoc', le_div_iff₀ hρ0] at hb
        have hθρ : θs < ρ.re := by linarith [le_max_right (1 / 2 : ℝ) ((θs + σ) / 2)]
        have := mul_lt_mul_of_pos_right hθρ hk
        nlinarith
    · exact h
  exact ⟨hTσ, taxaL_Teta hTσ hσ1 hA hT⟩

/-- **O teto de `Θ`**: uma taxa `ℓ¹` positiva em `σ` dá `Θ ≤ 2Aσ/(κ + 2A)`. -/
theorem Teta_le_de_taxa {σ A κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hT : TaxaL σ A κ) : Teta ≤ 2 * A * σ / (κ + 2 * A) := by
  rw [le_div_iff₀ (by linarith)]
  exact (taxaL_pos hσ0 hσ1 hA hκ hT).2

/-- **RH num único `σ₀`**: se `TaxaL σ₀ 1 (4σ₀ − 2)` para algum `σ₀ ∈ (½, 1)`, então RH. -/
theorem rh_of_taxaL {σ₀ : ℝ} (hσ : 1 / 2 < σ₀) (hσ1 : σ₀ < 1) (hT : TaxaL σ₀ 1 (4 * σ₀ - 2)) :
    RiemannHypothesis := by
  obtain ⟨-, h⟩ := taxaL_pos (by linarith) hσ1 zero_le_one (by linarith) hT
  apply rh_iff_Teta.mpr
  have h12 := meio_le_Teta
  refine le_antisymm ?_ h12
  nlinarith

end ATK.ZeroClasses.BDBurnolL1

#print axioms ATK.ZeroClasses.BDBurnolL1.J_reta
#print axioms ATK.ZeroClasses.BDBurnolL1.key_reta
#print axioms ATK.ZeroClasses.BDBurnolL1.piso_reta
#print axioms ATK.ZeroClasses.BDBurnolL1.piso_DNσL_reta
#print axioms ATK.ZeroClasses.BDBurnolL1.burnol_L1
#print axioms ATK.ZeroClasses.BDBurnolL1.log_um_add_le
#print axioms ATK.ZeroClasses.BDBurnolL1.taxaL_reta
#print axioms ATK.ZeroClasses.BDBurnolL1.sem_taxa_meio
#print axioms ATK.ZeroClasses.BDBurnolL1.taxaL_pos
#print axioms ATK.ZeroClasses.BDBurnolL1.Teta_le_de_taxa
#print axioms ATK.ZeroClasses.BDBurnolL1.rh_of_taxaL
