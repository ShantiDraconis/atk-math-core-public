import ATK.ZeroClasses.BDDesloc

/-!
# Báez-Duarte ponderado com taxa: `D_N(σ) ≪ N^{−2δ}` sob semiplano sem zeros (rodada 75)

Fecha a questão Q2(ii) de `fronteira/RH_frontier.md`. Para `½ ≤ θ < 1` e `SemZeros θ` (`ζ ≠ 0` em `Re s > θ`):

  **`D_N(σ) ≤ K N^{−2δ}` para todo `0 < δ < σ − θ`**, `θ < σ < 1`   (`DNσ_taxa`),

onde `D_N(σ) = inf_c ∫_0^∞ (χ − Σ_{k≤N} c_k {1/(kt)})² t^{2σ−1} dt` (rodada 59). Ou seja, `κ(σ) ≥ 2(σ − θ)`.
Junto com a suficiência da rodada 59 (`inf_N D_N(σ) = 0 ⟹ SemZeros σ`), sai o **critério de semiplano**

  **`SemZeros θ ⟺ ∀ σ ∈ (θ, 1), inf_N D_N(σ) = 0`**   (`semZeros_iff_DNσ`),

e, em `θ = ½`, **RH ⟺ `D_N(σ) → 0` para todo `σ ∈ (½, 1)`** (`rh_iff_DNσ`), agora com a taxa
`D_N(σ) ≪ N^{−2δ}`, `δ < σ − ½`, sob RH (`DNσ_taxa_RH`). As peças:

* `norm_zeta_linha`: sob `SemZeros θ`, `|ζ(σ + iτ)| ≤ C(1 + |τ|)^η` na reta `Re s = σ ∈ (θ, 1)` — o ramo de `log ζ` e
  Borel–Carathéodory da rodada 57 (`QuasiRH.norm_L_le`), com `exp(Re L)` no lugar de `exp(−Re L)`;
* `1 − ζ(s)A_N(s) = ζ(s)(1/ζ(s) − A_N(s))` e a cota da rodada 74 (`molif_cota`):
  `|1 − ζA_N| ≤ C K N^{−δ}(1 + |τ|)^{1/4}`; com `|s| ≥ σ(1 + |τ|)/2`, o integrando espectral da rodada 73 fica
  `≤ (const) N^{−2δ}(1 + |τ|)^{−3/2}`, integrável.

O expoente `2(σ − θ)` é o que a fronteira pedia em (ii); o piso ponderado (iii), `κ(σ) ≤ 2(σ − Θ)`, segue OPEN_MATH.
Nenhum semiplano sem zeros é dado: `SemZeros θ` é OPEN_MATH para todo `θ < 1`.

Classificação (rodada 75): **reformulação** (critério de Nyman–Beurling–Báez-Duarte para semiplanos, com taxa de
potência). RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.BDTaxa

open ATK.ZeroClasses.BDPonderado (DNσ DNσ_nonneg semZeros_of_DNσ)
open ATK.ZeroClasses.BDEspectral (aN DNσ_le_molif)
open ATK.ZeroClasses.BDDesloc (molif_cota)
open ATK.ZeroClasses.QuasiRH (SemZeros cθ existe_log_zeta norm_L_le exp_young semZeros_meio_iff)
open ATK.RHLogZeta (F F_eq young θ₂ θ₂_bounds)

/-! ## 1. `ζ` na reta `Re s = σ` sob `SemZeros θ` -/

/-- **Sob `SemZeros θ`**: `|ζ(σ + iτ)| ≤ C(1 + |τ|)^η` para `θ < σ < 1`. -/
theorem norm_zeta_linha {θ σ η : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ : θ < σ)
    (hσ1 : σ < 1) (hη : 0 < η) :
    ∃ C, 0 < C ∧ ∀ τ : ℝ, ‖riemannZeta ((σ : ℂ) + τ * I)‖ ≤ C * (1 + |τ|) ^ η := by
  set δ := σ - θ with hδdef
  have hδ : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hθ₂ := θ₂_bounds hδ hδ1
  obtain ⟨K, hK⟩ := young (A := (10 / δ) ^ θ₂ δ) (θ := θ₂ δ) (η := η)
    (Real.rpow_nonneg (by positivity) _) hθ₂.1 hθ₂.2 hη
  have hcont : ContinuousOn (fun τ : ℝ => riemannZeta ((σ : ℂ) + τ * I)) (Icc (-4) 4) := by
    intro τ _
    have hne : (σ : ℂ) + τ * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hc : Continuous (fun τ : ℝ => (σ : ℂ) + τ * I) := by fun_prop
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun τ : ℝ => (σ : ℂ) + τ * I)
      (differentiableAt_riemannZeta hne).continuousAt hc.continuousAt).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set C₁ := Real.exp (η + K) * 12 ^ η with hC₁
  set C := max (max C₀ 1) C₁ with hCdef
  have hC1 : 1 ≤ C := (le_max_right C₀ 1).trans (le_max_left _ _)
  have hCC₀ : C₀ ≤ C := (le_max_left C₀ 1).trans (le_max_left _ _)
  have hCC₁ : C₁ ≤ C := le_max_right _ _
  refine ⟨C, by linarith, fun τ => ?_⟩
  have h1 : 1 ≤ (1 + |τ|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg τ]) hη.le
  have hCpos : 0 ≤ C := by linarith
  rcases le_or_gt |τ| 4 with h4 | h4
  · have := hC₀ τ ⟨(abs_le.mp h4).1, (abs_le.mp h4).2⟩
    calc ‖riemannZeta ((σ : ℂ) + τ * I)‖ ≤ C₀ := this
      _ ≤ C := hCC₀
      _ ≤ C * (1 + |τ|) ^ η := le_mul_of_one_le_right hCpos h1
  · have ht : 4 ≤ |τ| := h4.le
    obtain ⟨L, hL0, hLe, hLd⟩ := existe_log_zeta hZ hθ hθ1 ht
    set s : ℂ := (σ : ℂ) + τ * I with hsdef
    have hsc : s - cθ θ τ = ((σ - (5 / 2 + θ) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [cθ, hsdef]
    have hz : ‖s - cθ θ τ‖ ≤ 5 / 2 - δ := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hsmem : s ∈ ball (cθ θ τ) (5 / 2) := by
      rw [mem_ball, dist_eq_norm]
      linarith
    have hLs := norm_L_le hZ hθ hθ1 ht hδ hδ1 hL0 hLe hLd hz
    rw [← hLe s hsmem, Complex.norm_exp]
    calc Real.exp (L s).re ≤ Real.exp ‖L s‖ := Real.exp_le_exp.mpr (Complex.re_le_norm _)
      _ ≤ Real.exp ((10 * (Real.log (2 * (|τ| + 6)) + 1) / δ) ^ θ₂ δ) := Real.exp_le_exp.mpr hLs
      _ ≤ Real.exp (η + K) * (12 ^ η * (1 + |τ|) ^ η) := exp_young hδ hη hθ₂.1 hK
      _ = C₁ * (1 + |τ|) ^ η := by rw [hC₁]; ring
      _ ≤ C * (1 + |τ|) ^ η := by gcongr

/-! ## 2. A taxa -/

/-- **`D_N(σ) ≤ K N^{−2δ}`** sob `SemZeros θ`, para `0 < δ`, `θ + δ < σ < 1`. -/
theorem DNσ_taxa {θ σ δ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ1 : σ < 1)
    (hδ0 : 0 < δ) (hδ : θ + δ < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → DNσ σ N ≤ K * (N : ℝ) ^ (-(2 * δ)) := by
  have hσ0 : 0 < σ := by linarith
  have hδ1 : δ < 1 := by linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := molif_cota hZ hθ hθ1 hδ0 hδ1 hδ hσ1 (η := 1 / 8) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := norm_zeta_linha hZ hθ hθ1 (by linarith) hσ1 (η := 1 / 8) (by norm_num)
  have hI : Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) := integrable_one_add_norm (by simp; norm_num)
  set I₀ : ℝ := ∫ τ : ℝ, (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) with hI₀
  have hI0 : 0 ≤ I₀ := integral_nonneg fun τ => by positivity
  set B : ℝ := (2 * C * K₁ / σ) ^ 2 with hB
  refine ⟨(2 * π)⁻¹ * (B * I₀), by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (DNσ_le_molif hσ0 hσ1 hN).trans ?_
  -- a cota pontual
  have hpt : ∀ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) * LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) /
      ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ (B * (N : ℝ) ^ (-(2 * δ))) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
    intro τ
    set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hsdef
    have hsre : s.re = σ := by simp [hsdef]
    have hsim : s.im = τ := by simp [hsdef]
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hsre, one_re] at this
      linarith
    have hζ : riemannZeta s ≠ 0 := hZ s (by rw [hsre]; linarith)
    have hζF : riemannZeta s * F s = 1 := by rw [F_eq hs1, mul_inv_cancel₀ hζ]
    have e1 : 1 - riemannZeta s * LSeries (aN N) s = -(riemannZeta s * (LSeries (aN N) s - F s)) := by
      linear_combination -hζF
    have hy : (0 : ℝ) < 1 + |τ| := by positivity
    have hs : σ * (1 + |τ|) / 2 ≤ ‖s‖ := by
      have a1 := abs_re_le_norm s
      have a2 := abs_im_le_norm s
      rw [hsre, abs_of_pos hσ0] at a1
      rw [hsim] at a2
      nlinarith [abs_nonneg τ]
    have hnum : ‖1 - riemannZeta s * LSeries (aN N) s‖ ≤
        C * K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 4 : ℝ) := by
      rw [e1, norm_neg, norm_mul]
      have h1 := hC τ
      have h2 := hK₁ N hN τ
      have hp : (1 + |τ|) ^ (1 / 8 : ℝ) * (1 + |τ|) ^ (1 / 8 : ℝ) = (1 + |τ|) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hy]
        norm_num
      calc ‖riemannZeta s‖ * ‖LSeries (aN N) s - F s‖
          ≤ (C * (1 + |τ|) ^ (1 / 8 : ℝ)) * (K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 8 : ℝ)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = C * K₁ * (N : ℝ) ^ (-δ) * ((1 + |τ|) ^ (1 / 8 : ℝ) * (1 + |τ|) ^ (1 / 8 : ℝ)) := by ring
        _ = C * K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 4 : ℝ) := by rw [hp]
    have hq : ‖(1 - riemannZeta s * LSeries (aN N) s) / s‖ ≤
        2 * C * K₁ / σ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (-(3 / 4 : ℝ)) := by
      rw [norm_div]
      have hsp : 0 < σ * (1 + |τ|) / 2 := by positivity
      have hp : (1 + |τ|) ^ (1 / 4 : ℝ) / (σ * (1 + |τ|) / 2) = 2 / σ * (1 + |τ|) ^ (-(3 / 4 : ℝ)) := by
        have e : (1 + |τ|) ^ (-(3 / 4 : ℝ)) = (1 + |τ|) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hy]
          norm_num
        rw [e, Real.rpow_neg_one]
        field_simp
      calc ‖1 - riemannZeta s * LSeries (aN N) s‖ / ‖s‖
          ≤ C * K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 4 : ℝ) / (σ * (1 + |τ|) / 2) :=
            div_le_div₀ (by positivity) hnum hsp hs
        _ = C * K₁ * (N : ℝ) ^ (-δ) * ((1 + |τ|) ^ (1 / 4 : ℝ) / (σ * (1 + |τ|) / 2)) := by ring
        _ = 2 * C * K₁ / σ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (-(3 / 4 : ℝ)) := by rw [hp]; ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have hN2 : ((N : ℝ) ^ (-δ)) ^ 2 = (N : ℝ) ^ (-(2 * δ)) := by
      rw [← Real.rpow_mul_natCast hN0.le]
      congr 1
      push_cast
      ring
    have hy2 : ((1 + |τ|) ^ (-(3 / 4 : ℝ))) ^ 2 = (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.norm_eq_abs, ← Real.rpow_mul_natCast hy.le]
      congr 1
      push_cast
      ring
    calc ‖(1 - riemannZeta s * LSeries (aN N) s) / s‖ ^ 2
        ≤ (2 * C * K₁ / σ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (-(3 / 4 : ℝ))) ^ 2 := hsq
      _ = (2 * C * K₁ / σ) ^ 2 * ((N : ℝ) ^ (-δ)) ^ 2 * ((1 + |τ|) ^ (-(3 / 4 : ℝ))) ^ 2 := by ring
      _ = (B * (N : ℝ) ^ (-(2 * δ))) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by rw [hN2, hy2, hB]
  have hint : ∫ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) * LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) /
      ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ (B * (N : ℝ) ^ (-(2 * δ))) * I₀ := by
    rw [hI₀, ← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun τ => by positivity) (hI.const_mul _) (ae_of_all _ hpt)
  calc (2 * π)⁻¹ * ∫ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) *
        LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) / ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2
      ≤ (2 * π)⁻¹ * ((B * (N : ℝ) ^ (-(2 * δ))) * I₀) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (2 * π)⁻¹ * (B * I₀) * (N : ℝ) ^ (-(2 * δ)) := by ring

/-! ## 3. Consequências -/

/-- Sob `SemZeros θ`, **`D_N(σ) → 0`** para todo `σ ∈ (θ, 1)`. -/
theorem DNσ_tendsto {θ σ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ : θ < σ)
    (hσ1 : σ < 1) : Tendsto (DNσ σ) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := DNσ_taxa hZ hθ hθ1 hσ1 (δ := (σ - θ) / 2) (by linarith) (by linarith)
  have hg : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-(2 * ((σ - θ) / 2)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := 2 * ((σ - θ) / 2)) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    simpa using h.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun N => DNσ_nonneg σ N) ?_ hg
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact hK N hN

theorem iInf_DNσ_eq_zero {θ σ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ : θ < σ)
    (hσ1 : σ < 1) : ⨅ N, DNσ σ N = 0 := by
  have hbdd : BddBelow (Set.range (DNσ σ)) := ⟨0, fun _ ⟨N, hN⟩ => hN ▸ DNσ_nonneg σ N⟩
  exact le_antisymm (ge_of_tendsto' (DNσ_tendsto hZ hθ hθ1 hσ hσ1) fun N => ciInf_le hbdd N)
    (le_ciInf fun N => DNσ_nonneg σ N)

/-- **O critério de semiplano**: `SemZeros θ ⟺ ∀ σ ∈ (θ, 1), inf_N D_N(σ) = 0`, para `½ ≤ θ < 1`. -/
theorem semZeros_iff_DNσ {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ σ : ℝ, θ < σ → σ < 1 → ⨅ N, DNσ σ N = 0 := by
  constructor
  · intro hZ σ hσ hσ1
    exact iInf_DNσ_eq_zero hZ hθ hθ1 hσ hσ1
  · intro h s hs
    rcases le_or_gt 1 s.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1
    · have hσ : θ < (θ + s.re) / 2 := by linarith
      have hσ1 : (θ + s.re) / 2 < 1 := by linarith
      exact semZeros_of_DNσ (by linarith) hσ1 (h _ hσ hσ1) s (by linarith)

/-- **RH ⟺ `inf_N D_N(σ) = 0` para todo `σ ∈ (½, 1)`**. -/
theorem rh_iff_DNσ : RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → ⨅ N, DNσ σ N = 0 := by
  rw [← semZeros_meio_iff]
  exact semZeros_iff_DNσ le_rfl (by norm_num)

/-- **Sob RH**: `D_N(σ) ≤ K N^{−2δ}` para `0 < δ < σ − ½`. -/
theorem DNσ_taxa_RH (hRH : RiemannHypothesis) {σ δ : ℝ} (hσ1 : σ < 1) (hδ0 : 0 < δ) (hδ : 1 / 2 + δ < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → DNσ σ N ≤ K * (N : ℝ) ^ (-(2 * δ)) :=
  DNσ_taxa (semZeros_meio_iff.mpr hRH) le_rfl (by norm_num) hσ1 hδ0 hδ

end ATK.ZeroClasses.BDTaxa

#print axioms ATK.ZeroClasses.BDTaxa.norm_zeta_linha
#print axioms ATK.ZeroClasses.BDTaxa.DNσ_taxa
#print axioms ATK.ZeroClasses.BDTaxa.DNσ_tendsto
#print axioms ATK.ZeroClasses.BDTaxa.iInf_DNσ_eq_zero
#print axioms ATK.ZeroClasses.BDTaxa.semZeros_iff_DNσ
#print axioms ATK.ZeroClasses.BDTaxa.rh_iff_DNσ
#print axioms ATK.ZeroClasses.BDTaxa.DNσ_taxa_RH
