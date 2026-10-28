import ATK.MellinPlancherel
import ATK.BLEulerMaclaurin

/-!
# Bohr–Landau, passo 3 — a cauda de Euler–Maclaurin em L² (Plancherel de Mellin)

Para `σ > 0` e `N ≥ 1`, com `I_N(s) = ∫_N^∞ t^{−s−1}{t} dt`:

  **`∫_ℝ |I_N(σ + iτ)|² dτ ≤ π N^{−2σ}/σ`** (`cauda_L2`), e o integrando é integrável.

Prova: `I_N(σ − iτ) = 𝓜f(1/2 + iτ)` com `f(t) = 𝟙_{t>N} t^{−σ−1/2}{t}`; o Plancherel de Mellin do
kernel (`ATK.MellinPlancherel.integral_norm_sq_eq_mellin`) dá `∫|𝓜f|² = 2π∫|f|²`, e
`∫|f|² ≤ ∫_N^∞ t^{−2σ−1} = N^{−2σ}/(2σ)`.
-/

open Complex Set MeasureTheory Real FourierTransform

namespace ATK.BLCauda

open ATK.BLEulerMaclaurin ATK.MellinPlancherel

/-- `f(t) = 𝟙_{t>N} t^{−σ−1/2}{t}`. -/
noncomputable def fN (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  Set.indicator (Ioi (N : ℝ)) (fun u : ℝ => ((u ^ (-σ - 1 / 2) * Int.fract u : ℝ) : ℂ)) t

theorem norm_fN_le (σ : ℝ) (N : ℕ) (t : ℝ) :
    ‖fN σ N t‖ ≤ Set.indicator (Ioi (N : ℝ)) (fun u : ℝ => u ^ (-σ - 1 / 2)) t := by
  unfold fN
  by_cases ht : t ∈ Ioi (N : ℝ)
  · have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) (le_of_lt ht)
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0 _) (Int.fract_nonneg _))]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht0 _) (Int.fract_lt_one _).le
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, norm_zero]

theorem measurable_fN (σ : ℝ) (N : ℕ) : Measurable (fN σ N) := by
  unfold fN
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact Complex.measurable_ofReal.comp ((measurable_id.pow_const _).mul measurable_fract)

theorem mellinConvergent_fN {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    MellinConvergent (fN σ N) ((1 / 2 : ℝ) : ℂ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold MellinConvergent
  have hdom : IntegrableOn (fun t : ℝ => Set.indicator (Ioi (N : ℝ)) (fun u : ℝ => u ^ (-σ - 1)) t)
      (Ioi 0) := by
    refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_ |>.integrableOn
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  refine Integrable.mono' hdom ?_ ?_
  · exact (((Complex.measurable_ofReal.pow_const _).smul (measurable_fN σ N))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    have hre : (((1 / 2 : ℝ) : ℂ) - 1).re = -1 / 2 := by norm_num
    rw [hre]
    by_cases htN : t ∈ Ioi (N : ℝ)
    · have := norm_fN_le σ N t
      rw [Set.indicator_of_mem htN] at this ⊢
      calc t ^ (-1 / 2 : ℝ) * ‖fN σ N t‖ ≤ t ^ (-1 / 2 : ℝ) * t ^ (-σ - 1 / 2) :=
            mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht.le _)
        _ = t ^ (-σ - 1) := by
            rw [← Real.rpow_add ht]; congr 1; ring
    · rw [Set.indicator_of_notMem htN]
      unfold fN; rw [Set.indicator_of_notMem htN, norm_zero, mul_zero]

theorem integrableOn_sq_fN {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun t => ‖fN σ N t‖ ^ 2) (Ioi 0) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hdom : IntegrableOn (fun t : ℝ => Set.indicator (Ioi (N : ℝ)) (fun u : ℝ => u ^ (-2 * σ - 1)) t)
      (Ioi 0) := by
    refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_ |>.integrableOn
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  refine Integrable.mono' hdom ((measurable_fN σ N).norm.pow_const 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases htN : t ∈ Ioi (N : ℝ)
  · have ht0 : 0 < t := hN0.trans htN
    have := norm_fN_le σ N t
    rw [Set.indicator_of_mem htN] at this ⊢
    calc ‖fN σ N t‖ ^ 2 ≤ (t ^ (-σ - 1 / 2)) ^ 2 := by gcongr
      _ = t ^ (-2 * σ - 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; congr 1; push_cast; ring
  · rw [Set.indicator_of_notMem htN]; unfold fN; rw [Set.indicator_of_notMem htN]; simp

/-- `∫_0^∞ |f|² ≤ N^{−2σ}/(2σ)`. -/
theorem integral_sq_fN_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    ∫ t in Ioi (0 : ℝ), ‖fN σ N t‖ ^ 2 ≤ (N : ℝ) ^ (-2 * σ) / (2 * σ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : IntegrableOn (fun u : ℝ => u ^ (-2 * σ - 1)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  calc ∫ t in Ioi (0 : ℝ), ‖fN σ N t‖ ^ 2
      ≤ ∫ t in Ioi (0 : ℝ), Set.indicator (Ioi (N : ℝ)) (fun u : ℝ => u ^ (-2 * σ - 1)) t := by
        refine setIntegral_mono_on (integrableOn_sq_fN hσ hN)
          ((integrable_indicator_iff measurableSet_Ioi).mpr hint).integrableOn measurableSet_Ioi
          fun t ht => ?_
        by_cases htN : t ∈ Ioi (N : ℝ)
        · have := norm_fN_le σ N t
          rw [Set.indicator_of_mem htN] at this ⊢
          calc ‖fN σ N t‖ ^ 2 ≤ (t ^ (-σ - 1 / 2)) ^ 2 := by gcongr
            _ = t ^ (-2 * σ - 1) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring
        · rw [Set.indicator_of_notMem htN]; unfold fN; rw [Set.indicator_of_notMem htN]; simp
    _ = ∫ t in Ioi (N : ℝ), t ^ (-2 * σ - 1) := by
        rw [setIntegral_indicator measurableSet_Ioi,
          Set.inter_eq_right.mpr (Ioi_subset_Ioi hN0.le)]
    _ = (N : ℝ) ^ (-2 * σ) / (2 * σ) := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hN0]
        have e : -2 * σ - 1 + 1 = -2 * σ := by ring
        rw [e]; field_simp

/-- `I_N(σ − iτ) = 𝓜f(1/2 + iτ)`. -/
theorem cauda_eq_mellin (σ : ℝ) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    cauda N ((σ : ℂ) - (τ : ℂ) * I) = mellin (fN σ N) (1 / 2 + (τ : ℂ) * I) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cauda mellin
  have hpt : ∀ t : ℝ, (t : ℂ) ^ (1 / 2 + (τ : ℂ) * I - 1) • fN σ N t =
      Set.indicator (Ioi (N : ℝ))
        (fun u : ℝ => (u : ℂ) ^ (-((σ : ℂ) - (τ : ℂ) * I) - 1) * ((Int.fract u : ℝ) : ℂ)) t := by
    intro t
    unfold fN
    by_cases htN : t ∈ Ioi (N : ℝ)
    · have ht0 : 0 < t := hN0.trans htN
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      rw [Set.indicator_of_mem htN, Set.indicator_of_mem htN, smul_eq_mul]
      push_cast
      rw [Complex.ofReal_cpow ht0.le, ← mul_assoc, ← cpow_add _ _ htc]
      congr 2
      push_cast; ring
    · rw [Set.indicator_of_notMem htN, Set.indicator_of_notMem htN, smul_zero]
  simp_rw [hpt]
  rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr (Ioi_subset_Ioi hN0.le)]

/-- O lado de Fourier tem quadrado integrável; logo `τ ↦ |𝓜f(1/2+iτ)|²` é integrável. -/
theorem integrable_sq_mellin {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun τ : ℝ => ‖mellin (fN σ N) (1 / 2 + (τ : ℂ) * I)‖ ^ 2) := by
  have hg1 : Integrable (lado (fN σ N)) := integrable_lado (mellinConvergent_fN hσ hN)
  have hsq : Integrable (fun u => ‖lado (fN σ N) u‖ ^ 2) := by
    have h := (integrableOn_Ioi_iff (fun t => ‖fN σ N t‖ ^ 2)).mp (integrableOn_sq_fN hσ hN)
    simpa [norm_sq_lado] using h
  have hg2 : MemLp (lado (fN σ N)) 2 :=
    (memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable).mpr hsq
  have hF : MemLp (𝓕 (lado (fN σ N))) 2 := ATK.PlancherelL1L2.memLp_two_fourier hg1 hg2
  have hFi : Integrable (fun ξ => ‖𝓕 (lado (fN σ N)) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hcomp : Integrable (fun ξ : ℝ =>
      (fun τ : ℝ => ‖mellin (fN σ N) (1 / 2 + (τ : ℂ) * I)‖ ^ 2) ((2 * π) * ξ)) := by
    refine hFi.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_lado]
  have h2pi : (2 * π) ≠ 0 := by positivity
  exact (integrable_comp_mul_left_iff _ h2pi).mp hcomp

/-- **A cauda em L²**: `∫_ℝ |I_N(σ+iτ)|² dτ ≤ π N^{−2σ}/σ`, com integrando integrável. -/
theorem cauda_L2 {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun τ : ℝ => ‖cauda N ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2) ∧
      ∫ τ : ℝ, ‖cauda N ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ π * (N : ℝ) ^ (-2 * σ) / σ := by
  have hfun : (fun τ : ℝ => ‖cauda N ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2) =
      fun τ : ℝ => (fun τ' : ℝ => ‖mellin (fN σ N) (1 / 2 + (τ' : ℂ) * I)‖ ^ 2) (-τ) := by
    funext τ
    simp only
    rw [← cauda_eq_mellin σ hN (-τ)]
    push_cast; ring_nf
  have hint := integrable_sq_mellin hσ hN
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hint.comp_neg
  · rw [hfun, integral_neg_eq_self (fun τ' : ℝ => ‖mellin (fN σ N) (1 / 2 + (τ' : ℂ) * I)‖ ^ 2)]
    have hP := integral_norm_sq_eq_mellin (mellinConvergent_fN hσ hN) (integrableOn_sq_fN hσ hN)
    have hb := integral_sq_fN_le hσ hN
    have hpi : 0 < 2 * π := by positivity
    have e : ∫ τ : ℝ, ‖mellin (fN σ N) (1 / 2 + (τ : ℂ) * I)‖ ^ 2 =
        2 * π * ∫ t in Ioi (0 : ℝ), ‖fN σ N t‖ ^ 2 := by
      rw [hP, ← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]
    rw [e]
    calc 2 * π * ∫ t in Ioi (0 : ℝ), ‖fN σ N t‖ ^ 2 ≤ 2 * π * ((N : ℝ) ^ (-2 * σ) / (2 * σ)) :=
          mul_le_mul_of_nonneg_left hb hpi.le
      _ = π * (N : ℝ) ^ (-2 * σ) / σ := by field_simp

end ATK.BLCauda

#print axioms ATK.BLCauda.mellinConvergent_fN
#print axioms ATK.BLCauda.integral_sq_fN_le
#print axioms ATK.BLCauda.cauda_eq_mellin
#print axioms ATK.BLCauda.integrable_sq_mellin
#print axioms ATK.BLCauda.cauda_L2
#print axioms ATK.BLCauda.norm_fN_le
#print axioms ATK.BLCauda.measurable_fN
#print axioms ATK.BLCauda.integrableOn_sq_fN
