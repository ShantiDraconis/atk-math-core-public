import ATK.ZeroClasses.BDNormaL1

/-!
# O teto da taxa para `c` arbitrário: `2(σ − Θ) ≤ κ(σ) ≤ (2σ + 3)(σ − Θ)/Θ` (rodada 83)

A questão Q2(iii) de `fronteira/RH_frontier.md` pede o teto `κ(σ) ≤ 2(σ − Θ)` para a taxa de `D_N(σ)` sobre
**todos** os coeficientes. Esta rodada prova esse teto **a menos de uma constante**:

  **`κ(σ) ≤ (2σ + 3)(σ − Θ)/Θ`**   para `Θ < σ < 1`   (`taxaDN_teto`).

Como `D_N(σ) ≤ ‖res_0‖²_σ = 1/(2σ) ≤ 1` (`Wσ_zero`), os quase-minimizantes têm `‖res_c‖²_σ ≤ 1`. Pela rodada 82,
eles estão na classe `‖c‖₁ ≤ K N^{σ+3/2+2η}`, onde `D_N(σ) = D_N^{(L)}(σ)` (`DNσL_eq`). Daí `TaxaDN σ κ ⟹ TaxaL σ A κ`
para todo `A > σ + 3/2` (`taxaDN_L`), e o piso da rodada 79 dá `Θ(κ + 2A) ≤ 2Aσ`.

Consequências:
* `Wσ_mono`, `DNσ_mono`, `taxaDN_mono`: `D_N(σ′) ≤ (1 + (1 − σ)/(1 − σ′)) D_N(σ)` para `σ ≤ σ′ < 1`, e taxas passam
  para a direita;
* **`taxaDN_pos`**: `TaxaDN σ κ` com `κ > 0` e `0 < σ < 1` dá `Θ < σ`. Os casos `σ < Θ` e `σ = Θ` são excluídos por
  `piso_abaixo` e pela monotonia;
* **`Teta_le_de_taxaDN`**: `Θ ≤ (2σ + 3)σ/(κ + 2σ + 3)`. Uma taxa positiva num único `σ` certifica um semiplano sem
  zeros;
* **`rh_of_taxaDN`**: `TaxaDN σ₀ ((2σ₀ + 3)(2σ₀ − 1))` num único `σ₀ ∈ (½, 1)` dá RH;
* **`sanduiche_DN`**: `2(σ − Θ) ≤ κ(σ) ≤ (2σ + 3)(σ − Θ)/Θ`; sob RH (`taxaDN_RH`),
  `2σ − 1 ≤ κ(σ) ≤ (2σ + 3)(2σ − 1)`.

Classificação (rodada 83): **parcial** (Q2(iii) a menos do fator `(2σ + 3)/(2Θ) ∈ (2, 5)`; o teto exato
`2(σ − Θ)` segue OPEN_MATH). RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.BDTaxaPiso

open ATK.BaezDuarteBridge (res tailS res_of_gt_one)
open ATK.RiemannFaithful (chi_of_mem chi_of_gt_one)
open ATK.ZeroClasses.BDPonderado (Wσ DNσ DNσ_nonneg Wσ_nonneg integrable_w tail_sq_le res_sq_w_gt_one)
open ATK.ZeroClasses.QuasiRH (SemZeros)
open ATK.ZeroClasses.BDTheta (Teta meio_le_Teta Teta_le_um semZeros_Teta piso_abaixo rh_iff_Teta TaxaDN taxa_Teta)
open ATK.ZeroClasses.BDPisoL1 (DNσL DNσL_le DNσ_le_DNσL TaxaL taxaL_Teta)
open ATK.ZeroClasses.BDNormaL1 (norma_l1_le)

/-! ## 1. `‖res_0‖²_σ = 1/(2σ)` e a monotonia em `σ` -/

/-- `‖res_0‖²_σ = ‖χ‖²_σ = 1/(2σ)`. -/
theorem Wσ_zero {σ : ℝ} (hσ : 0 < σ) (N : ℕ) : Wσ σ (0 : Fin N → ℝ) = 1 / (2 * σ) := by
  unfold Wσ
  have h : ∀ t ∈ Ioi (0 : ℝ), res (0 : Fin N → ℝ) t ^ 2 * t ^ (2 * σ - 1) =
      (Ioc (0 : ℝ) 1).indicator (fun t => t ^ (2 * σ - 1)) t := by
    intro t ht
    simp only [res, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    by_cases h1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
      rw [chi_of_mem hm, Set.indicator_of_mem hm]
      ring
    · rw [chi_of_gt_one (not_le.mp h1), Set.indicator_of_notMem (fun h => h1 h.2)]
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi h, setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr Ioc_subset_Ioi_self, ATK.BaezDuarteBridge.integral_rpow_Ioc (by linarith)]
  ring_nf

/-- **Monotonia em `σ`**: para `0 < σ ≤ σ′ < 1`, `‖res‖²_{σ′} ≤ (1 + (1 − σ)/(1 − σ′)) ‖res‖²_σ`. -/
theorem Wσ_mono {σ σ' : ℝ} (hσ0 : 0 < σ) (hσσ : σ ≤ σ') (hσ1 : σ' < 1) {N : ℕ} (c : Fin N → ℝ) :
    Wσ σ' c ≤ (1 + (1 - σ) / (1 - σ')) * Wσ σ c := by
  have hσ'0 : 0 < σ' := by linarith
  have hσ1' : σ < 1 := by linarith
  have hI : IntegrableOn (fun t => res c t ^ 2 * t ^ (2 * σ' - 1)) (Ioi 0) := integrable_w c hσ'0 hσ1
  have hI0 : IntegrableOn (fun t => res c t ^ 2 * t ^ (2 * σ - 1)) (Ioi 0) := integrable_w c hσ0 hσ1'
  have hsplit : Wσ σ' c = (∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 * t ^ (2 * σ' - 1)) +
      ∫ t in Ioi (1 : ℝ), res c t ^ 2 * t ^ (2 * σ' - 1) := by
    unfold Wσ
    have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2)
    have hu := setIntegral_union hdisj measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self)
      (hI.mono_set (Ioi_subset_Ioi zero_le_one))
    rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
    exact hu
  have h1 : ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 * t ^ (2 * σ' - 1) ≤ Wσ σ c := by
    calc ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 * t ^ (2 * σ' - 1)
        ≤ ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 * t ^ (2 * σ - 1) := by
          refine setIntegral_mono_on (hI.mono_set Ioc_subset_Ioi_self) (hI0.mono_set Ioc_subset_Ioi_self)
            measurableSet_Ioc fun t ht => ?_
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith))
            (sq_nonneg _)
      _ ≤ Wσ σ c := by
          unfold Wσ
          exact setIntegral_mono_set hI0
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
              mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _)))
            Ioc_subset_Ioi_self.eventuallyLE
  have h2 : ∫ t in Ioi (1 : ℝ), res c t ^ 2 * t ^ (2 * σ' - 1) = tailS c ^ 2 / (2 - 2 * σ') := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t ht => res_sq_w_gt_one c σ' ht, integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    have e : 2 * σ' - 3 + 1 = -(2 - 2 * σ') := by ring
    have h2' : 2 - 2 * σ' ≠ 0 := by intro h; linarith
    rw [e]
    field_simp
  have hS := tail_sq_le c hσ0 hσ1'
  have h3 : tailS c ^ 2 / (2 - 2 * σ') ≤ (1 - σ) / (1 - σ') * Wσ σ c := by
    rw [div_le_iff₀ (by linarith)]
    have hne : (1 - σ') ≠ 0 := by intro h; linarith
    have e : (1 - σ) / (1 - σ') * Wσ σ c * (2 - 2 * σ') = (2 - 2 * σ) * Wσ σ c := by
      field_simp
      try ring
    rw [e]
    exact hS
  rw [hsplit, h2]
  have := Wσ_nonneg σ c
  nlinarith

/-- `D_N(σ′) ≤ (1 + (1 − σ)/(1 − σ′)) D_N(σ)`. -/
theorem DNσ_mono {σ σ' : ℝ} (hσ0 : 0 < σ) (hσσ : σ ≤ σ') (hσ1 : σ' < 1) (N : ℕ) :
    DNσ σ' N ≤ (1 + (1 - σ) / (1 - σ')) * DNσ σ N := by
  have hC : 0 < 1 + (1 - σ) / (1 - σ') := by
    have : 0 ≤ (1 - σ) / (1 - σ') := div_nonneg (by linarith) (by linarith)
    linarith
  have hb : BddBelow (Set.range fun c : Fin N → ℝ => Wσ σ' c) :=
    ⟨0, fun _ ⟨c', hc'⟩ => hc' ▸ Wσ_nonneg σ' c'⟩
  rw [← div_le_iff₀' hC]
  refine le_ciInf fun c => ?_
  rw [div_le_iff₀' hC]
  exact (ciInf_le hb c).trans (Wσ_mono hσ0 hσσ hσ1 c)

/-- Taxas passam para a direita: `TaxaDN σ κ ⟹ TaxaDN σ′ κ` para `σ ≤ σ′ < 1`. -/
theorem taxaDN_mono {σ σ' κ : ℝ} (hσ0 : 0 < σ) (hσσ : σ ≤ σ') (hσ1 : σ' < 1) (h : TaxaDN σ κ) :
    TaxaDN σ' κ := by
  intro δ hδ
  obtain ⟨K, hK⟩ := h δ hδ
  refine ⟨(1 + (1 - σ) / (1 - σ')) * K, fun N hN => ?_⟩
  have hC : 0 ≤ 1 + (1 - σ) / (1 - σ') := by
    have : 0 ≤ (1 - σ) / (1 - σ') := div_nonneg (by linarith) (by linarith)
    linarith
  calc DNσ σ' N ≤ (1 + (1 - σ) / (1 - σ')) * DNσ σ N := DNσ_mono hσ0 hσσ hσ1 N
    _ ≤ (1 + (1 - σ) / (1 - σ')) * (K * (N : ℝ) ^ (-δ)) := mul_le_mul_of_nonneg_left (hK N hN) hC
    _ = _ := by ring

/-! ## 2. Os quase-minimizantes estão na classe `ℓ¹` -/

/-- **`D_N^{(L)}(σ) = D_N(σ)`** para `L ≥ K N^{σ+3/2+2η}` (sob `SemZeros θ`, `θ < σ < 1`). -/
theorem DNσL_eq {θ σ η : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ : θ < σ) (hσ1 : σ < 1)
    (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ L : ℝ, K * (N : ℝ) ^ (σ + 3 / 2 + 2 * η) ≤ L →
      DNσL σ L N = DNσ σ N := by
  obtain ⟨K, hK0, hK⟩ := norma_l1_le hZ hθ hθ1 hσ hσ1 hη
  refine ⟨K, hK0, fun N hN L hL => ?_⟩
  have hσ0 : 0 < σ := by linarith
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  refine le_antisymm ?_ (DNσ_le_DNσL hL0 N)
  have hW0 : Wσ σ (0 : Fin N → ℝ) ≤ 1 := by
    rw [Wσ_zero hσ0, div_le_one (by positivity)]
    linarith
  have hz : DNσL σ L N ≤ 1 := (DNσL_le 0 (by simpa using hL0)).trans hW0
  show DNσL σ L N ≤ ⨅ c : Fin N → ℝ, Wσ σ c
  refine le_ciInf fun c => ?_
  by_cases hc : Wσ σ c ≤ 1
  · exact DNσL_le c ((hK N hN c hc).trans hL)
  · push Not at hc
    linarith

/-- **`TaxaDN σ κ ⟹ TaxaL σ A κ`** para todo `A > σ + 3/2` (sob `SemZeros θ`, `θ < σ < 1`). -/
theorem taxaDN_L {θ σ κ A : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ : θ < σ) (hσ1 : σ < 1)
    (hA : σ + 3 / 2 < A) (h : TaxaDN σ κ) : TaxaL σ A κ := by
  set η : ℝ := (A - (σ + 3 / 2)) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set A0 : ℝ := σ + 3 / 2 + 2 * η with hA0
  have hA0A : A0 < A := by rw [hA0, hη]; linarith
  obtain ⟨K, hK0, hKeq⟩ := DNσL_eq hZ hθ hθ1 hσ hσ1 hη0
  have hσ0 : 0 < σ := by linarith
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (A - A0)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop K)
  intro δ hδ
  obtain ⟨K', hK'⟩ := h δ hδ
  set M : ℝ := ((max N0 1 : ℕ) : ℝ) with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast le_max_right N0 1
  refine ⟨max K' (max 1 (M ^ δ)), fun N hN => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0r : (0 : ℝ) < N := by linarith
  have hpos : 0 < (N : ℝ) ^ (-δ) := Real.rpow_pos_of_pos hN0r _
  rcases le_or_gt N0 N with hNN | hNN
  · -- `N ≥ N0`: `N^A ≥ K N^{A0}`
    have h1 : K * (N : ℝ) ^ A0 ≤ (N : ℝ) ^ A := by
      have h2 := hN0 N hNN
      have e : (N : ℝ) ^ A = (N : ℝ) ^ (A - A0) * (N : ℝ) ^ A0 := by
        rw [← Real.rpow_add hN0r]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    rw [hKeq N hN _ h1]
    exact (hK' N hN).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
  · -- `N < N0`: `D_N^{(N^A)} ≤ ‖res_0‖² ≤ 1 ≤ max(…) N^{−δ}`
    have hW0 : Wσ σ (0 : Fin N → ℝ) ≤ 1 := by
      rw [Wσ_zero hσ0, div_le_one (by positivity)]
      linarith
    have hz : DNσL σ ((N : ℝ) ^ A) N ≤ 1 :=
      (DNσL_le 0 (by simpa using Real.rpow_nonneg hN0r.le A)).trans hW0
    refine hz.trans ?_
    have hNM : (N : ℝ) ≤ M := by
      rw [hM]
      exact_mod_cast le_trans hNN.le (le_max_left N0 1)
    rcases le_or_gt δ 0 with hδ0 | hδ0
    · have h1 : 1 ≤ (N : ℝ) ^ (-δ) := Real.one_le_rpow hNr (by linarith)
      have h2 : 1 ≤ max K' (max 1 (M ^ δ)) := le_trans (le_max_left _ _) (le_max_right _ _)
      nlinarith
    · have h1 : M ^ (-δ) ≤ (N : ℝ) ^ (-δ) := Real.rpow_le_rpow_of_nonpos hN0r hNM (by linarith)
      have h2 : M ^ δ ≤ max K' (max 1 (M ^ δ)) := le_trans (le_max_right _ _) (le_max_right _ _)
      have h3 : M ^ δ * M ^ (-δ) = 1 := by
        rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
      have hMd : 0 ≤ M ^ δ := by positivity
      have hMd' : 0 ≤ M ^ (-δ) := by positivity
      calc (1 : ℝ) = M ^ δ * M ^ (-δ) := h3.symm
        _ ≤ max K' (max 1 (M ^ δ)) * (N : ℝ) ^ (-δ) := mul_le_mul h2 h1 hMd' (le_trans hMd h2)

/-! ## 3. O teto da taxa -/

/-- **O teto para `c` arbitrário**: para `Θ < σ < 1`, `TaxaDN σ κ ⟹ κ ≤ (2σ + 3)(σ − Θ)/Θ`. -/
theorem taxaDN_teto {σ κ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (h : TaxaDN σ κ) :
    κ ≤ (2 * σ + 3) * (σ - Teta) / Teta := by
  have hT12 := meio_le_Teta
  have hT0 : 0 < Teta := by linarith
  have hA : ∀ A, σ + 3 / 2 < A → Teta * (κ + 2 * A) ≤ 2 * A * σ := fun A hA =>
    taxaL_Teta hσ hσ1 (by linarith) (taxaDN_L semZeros_Teta hT12 (by linarith) hσ hσ1 hA h)
  rw [le_div_iff₀ hT0]
  by_contra hc
  push Not at hc
  set g : ℝ := κ * Teta - (2 * σ + 3) * (σ - Teta) with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hsT : 0 < σ - Teta := by linarith
  set A : ℝ := σ + 3 / 2 + g / (4 * (σ - Teta)) with hAdef
  have hq : 0 < g / (4 * (σ - Teta)) := by positivity
  have hA' : σ + 3 / 2 < A := by rw [hAdef]; linarith
  have h1 := hA A hA'
  have e : 2 * A * (σ - Teta) = (2 * σ + 3) * (σ - Teta) + g / 2 := by
    rw [hAdef]
    field_simp
    ring
  nlinarith

/-- **Uma taxa positiva certifica `Θ < σ`**: `TaxaDN σ κ` com `κ > 0`, `0 < σ < 1` dá `Θ < σ`. -/
theorem taxaDN_pos {σ κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hκ : 0 < κ) (h : TaxaDN σ κ) : Teta < σ := by
  rcases lt_trichotomy σ Teta with hlt | heq | hgt
  · exfalso
    have hp := piso_abaixo hσ0 hlt
    obtain ⟨K, hK⟩ := h (κ / 2) (by linarith)
    have hlim : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-(κ / 2))) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : 0 < κ / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul K
      simpa using this
    obtain ⟨N, hNs, hN1⟩ := ((hlim.eventually (gt_mem_nhds hp)).and (eventually_ge_atTop 1)).exists
    have h1 : ⨅ M, DNσ σ M ≤ DNσ σ N := ciInf_le ⟨0, fun _ ⟨M, hM⟩ => hM ▸ DNσ_nonneg σ M⟩ N
    have h3 := hK N hN1
    linarith
  · exfalso
    have hT12 := meio_le_Teta
    have hT0 : 0 < Teta := by linarith
    set hh : ℝ := min ((1 - Teta) / 2) (κ * Teta / 10) with hhdef
    have hh0 : 0 < hh := lt_min (by linarith) (by positivity)
    have hh1 : hh ≤ (1 - Teta) / 2 := min_le_left _ _
    have hh2 : hh ≤ κ * Teta / 10 := min_le_right _ _
    have hσ' : Teta < Teta + hh := by linarith
    have hσ'1 : Teta + hh < 1 := by linarith
    have ht := taxaDN_mono hσ0 (by rw [heq]; linarith) hσ'1 h
    have h1 := taxaDN_teto hσ' hσ'1 ht
    have h2 : (2 * (Teta + hh) + 3) * (Teta + hh - Teta) / Teta ≤ κ / 2 := by
      rw [div_le_iff₀ hT0]
      have : 2 * (Teta + hh) + 3 ≤ 5 := by linarith
      nlinarith
    linarith
  · exact hgt

/-- **O teto de `Θ`**: `TaxaDN σ κ` com `κ > 0` dá `Θ ≤ (2σ + 3)σ/(κ + 2σ + 3)`. -/
theorem Teta_le_de_taxaDN {σ κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hκ : 0 < κ) (h : TaxaDN σ κ) :
    Teta ≤ (2 * σ + 3) * σ / (κ + 2 * σ + 3) := by
  have hT := taxaDN_pos hσ0 hσ1 hκ h
  have h1 := taxaDN_teto hT hσ1 h
  have hT0 : 0 < Teta := by linarith [meio_le_Teta]
  rw [le_div_iff₀ hT0] at h1
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **RH num único `σ₀`, para `c` arbitrário**: `TaxaDN σ₀ ((2σ₀ + 3)(2σ₀ − 1))` para algum `σ₀ ∈ (½, 1)` dá RH. -/
theorem rh_of_taxaDN {σ₀ : ℝ} (hσ : 1 / 2 < σ₀) (hσ1 : σ₀ < 1)
    (h : TaxaDN σ₀ ((2 * σ₀ + 3) * (2 * σ₀ - 1))) : RiemannHypothesis := by
  have hκ : 0 < (2 * σ₀ + 3) * (2 * σ₀ - 1) := by nlinarith
  have h1 := Teta_le_de_taxaDN (by linarith) hσ1 hκ h
  apply rh_iff_Teta.mpr
  refine le_antisymm ?_ meio_le_Teta
  have e : (2 * σ₀ + 3) * σ₀ / ((2 * σ₀ + 3) * (2 * σ₀ - 1) + 2 * σ₀ + 3) = 1 / 2 := by
    rw [div_eq_iff (by nlinarith)]
    ring
  rw [e] at h1
  exact h1

/-- **O sanduíche para `c` arbitrário**: para `Θ < σ < 1`, a taxa `2(σ − Θ)` é atingida e nenhuma taxa passa de
`(2σ + 3)(σ − Θ)/Θ`. -/
theorem sanduiche_DN {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    TaxaDN σ (2 * (σ - Teta)) ∧ ∀ κ : ℝ, TaxaDN σ κ → κ ≤ (2 * σ + 3) * (σ - Teta) / Teta :=
  ⟨taxa_Teta hσ hσ1, fun _ h => taxaDN_teto hσ hσ1 h⟩

/-- **Sob RH**: `2σ − 1 ≤ κ(σ) ≤ (2σ + 3)(2σ − 1)` para `σ ∈ (½, 1)`. -/
theorem taxaDN_RH (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    TaxaDN σ (2 * σ - 1) ∧ ∀ κ : ℝ, TaxaDN σ κ → κ ≤ (2 * σ + 3) * (2 * σ - 1) := by
  have hT := rh_iff_Teta.mp hRH
  have h := sanduiche_DN (σ := σ) (by rw [hT]; exact hσ) hσ1
  rw [hT] at h
  refine ⟨?_, fun κ hκ => ?_⟩
  · have e : 2 * (σ - 1 / 2) = 2 * σ - 1 := by ring
    rw [← e]
    exact h.1
  · have := h.2 κ hκ
    have e : (2 * σ + 3) * (σ - 1 / 2) / (1 / 2) = (2 * σ + 3) * (2 * σ - 1) := by ring
    rw [e] at this
    exact this

end ATK.ZeroClasses.BDTaxaPiso

#print axioms ATK.ZeroClasses.BDTaxaPiso.Wσ_zero
#print axioms ATK.ZeroClasses.BDTaxaPiso.Wσ_mono
#print axioms ATK.ZeroClasses.BDTaxaPiso.DNσ_mono
#print axioms ATK.ZeroClasses.BDTaxaPiso.taxaDN_mono
#print axioms ATK.ZeroClasses.BDTaxaPiso.DNσL_eq
#print axioms ATK.ZeroClasses.BDTaxaPiso.taxaDN_L
#print axioms ATK.ZeroClasses.BDTaxaPiso.taxaDN_teto
#print axioms ATK.ZeroClasses.BDTaxaPiso.taxaDN_pos
#print axioms ATK.ZeroClasses.BDTaxaPiso.Teta_le_de_taxaDN
#print axioms ATK.ZeroClasses.BDTaxaPiso.rh_of_taxaDN
#print axioms ATK.ZeroClasses.BDTaxaPiso.sanduiche_DN
#print axioms ATK.ZeroClasses.BDTaxaPiso.taxaDN_RH
