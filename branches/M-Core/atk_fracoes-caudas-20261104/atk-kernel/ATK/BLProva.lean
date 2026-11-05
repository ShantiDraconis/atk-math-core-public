import ATK.BLJensen
import ATK.BLMediaZeta
import ATK.BohrLandau
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# Bohr–Landau, passo 6 — a prova incondicional de `N(1/2 + δ, T) = O(T)`

**`bohrLandau : TeoremaBohrLandau`**, sem `sorry` e sem axiomas novos.

Para `0 < δ ≤ 1/4`, `h = δ/2`, `R = 3/2 − δ/2`, `r = 3/2 − 3δ/4` e centro `c_y = 2 + iy` (`y ≥ 2`):

1. todo zero com `Re ρ > 1/2 + δ` e `|Im ρ − y| ≤ h` está em `closedBall c_y r` (`zeros_na_bola`);
2. Jensen em média (`BLJensen.ncard_zeros_zeta_le`) + `log x ≤ x²` + `|ζ(2 + iy)| ≥ 2 − π²/6`
   (`zeta_dois_lb`) dão `#S_y · log(R/r) ≤ média(|ζ|², c_y, R) + L₀` (`jensen_y`);
3. integra-se em `y ∈ [2, T+1]`: cada zero de altura `≥ 3` contribui com `2h = δ`, e por Fubini
   `∫ média(|ζ|²) dy = (2π)⁻¹ ∫_θ ∫_y |ζ(σ_θ + i(y + R sen θ))|² ≤ M (T + 3)`, com
   `σ_θ = 2 + R cos θ ∈ [1/2 + δ/2, 4]` (`BLMediaZeta.media_zeta`);
4. os zeros de altura `≤ 3` são finitos (`todos_finite`).
-/

open Complex Set MeasureTheory Filter Metric

namespace ATK.BLProva

open ATK.BohrLandau ATK.BLJensen ATK.BLMediaZeta ATK.ZetaSimetria

/-- `circleMap` em coordenadas reais. -/
theorem circleMap_coord (y R θ : ℝ) :
    circleMap (2 + (y : ℂ) * I) R θ =
      ((2 + R * Real.cos θ : ℝ) : ℂ) + ((y + R * Real.sin θ : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  · simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem log_le_sq (x : ℝ) (hx : 0 ≤ x) : Real.log x ≤ x ^ 2 := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]; simp
  · have := Real.log_le_sub_one_of_pos h
    nlinarith [sq_nonneg (x - 1)]

theorem dois_menos_pos : 0 < 2 - Real.pi ^ 2 / 6 := by
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

theorem dois_menos_le_one : 2 - Real.pi ^ 2 / 6 ≤ 1 := by
  nlinarith [Real.pi_gt_three]

/-- **Cota inferior** `|ζ(2 + iy)| ≥ 2 − π²/6`. -/
theorem zeta_dois_lb (y : ℝ) : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta (2 + (y : ℂ) * I)‖ := by
  set s : ℂ := 2 + (y : ℂ) * I with hs
  have hre : s.re = 2 := by simp [hs]
  have hs1 : 1 < s.re := by rw [hre]; norm_num
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    simp only [hf, norm_div, norm_one]
    have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega), hre]
    push_cast
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hR : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hsum : Summable (fun n => ‖f n‖) := by
    have : (fun n => ‖f n‖) = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := funext hnorm
    rw [this]; exact hR.summable
  have hfs : Summable f := hsum.of_norm
  have hf0 : f 0 = 1 := by simp [hf]
  have htail : ∑' n, ‖f (n + 1)‖ = Real.pi ^ 2 / 6 - 1 := by
    have h1 := hsum.tsum_eq_zero_add
    have h2 : ∑' n, ‖f n‖ = Real.pi ^ 2 / 6 := by
      have : (fun n => ‖f n‖) = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := funext hnorm
      rw [this]; exact hR.tsum_eq
    rw [hf0, norm_one] at h1
    linarith
  have hle : ‖∑' n, f (n + 1)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    rw [← htail]
    exact norm_tsum_le_tsum_norm ((summable_nat_add_iff 1).mpr hsum)
  have hzeta : riemannZeta s = 1 + ∑' n, f (n + 1) := by
    rw [hz]; change ∑' n, f n = _; rw [hfs.tsum_eq_zero_add, hf0]
  rw [hzeta]
  have h := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 1)))
  rw [norm_neg, sub_neg_eq_add, norm_one] at h
  linarith

/-- Os zeros de `Re > 1/2 + δ`, `|Im − y| ≤ δ/2` estão no disco fechado de raio `3/2 − 3δ/4`. -/
theorem zeros_na_bola {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) {y : ℝ} {ρ : ℂ}
    (h1 : 1 / 2 + δ < ρ.re) (h2 : ρ.re < 1) (h3 : |ρ.im - y| ≤ δ / 2) :
    ρ ∈ closedBall (2 + (y : ℂ) * I) (3 / 2 - 3 * δ / 4) := by
  rw [mem_closedBall, dist_eq_norm]
  have hr : 0 < 3 / 2 - 3 * δ / 4 := by linarith
  have hsq : ‖ρ - (2 + (y : ℂ) * I)‖ ^ 2 ≤ (3 / 2 - 3 * δ / 4) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_im, add_im, mul_im,
      re_ofNat, im_ofNat]
    have ha : (ρ.im - y) ^ 2 ≤ (δ / 2) ^ 2 := by
      have := abs_le.mp h3; nlinarith
    nlinarith
  nlinarith [norm_nonneg (ρ - (2 + (y : ℂ) * I))]

/-- **Jensen num centro `2 + iy`**. -/
theorem jensen_y {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) {y : ℝ} (hy : 2 ≤ y) {S : Set ℂ}
    (hS : S.Finite)
    (hSz : ∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 1 / 2 + δ < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - y| ≤ δ / 2) :
    (S.ncard : ℝ) * Real.log ((3 / 2 - δ / 2) / (3 / 2 - 3 * δ / 4)) ≤
      Real.circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + (y : ℂ) * I) (3 / 2 - δ / 2) -
        Real.log (2 - Real.pi ^ 2 / 6) := by
  set c : ℂ := 2 + (y : ℂ) * I with hc
  set R : ℝ := 3 / 2 - δ / 2 with hR
  set r : ℝ := 3 / 2 - 3 * δ / 4 with hr
  have r_pos : 0 < r := by rw [hr]; linarith
  have r_lt : r < R := by rw [hr, hR]; linarith
  have R_pos : 0 < R := r_pos.trans r_lt
  have h1 : (1 : ℂ) ∉ closedBall c R := by
    intro h
    rw [mem_closedBall, dist_eq_norm] at h
    have := Complex.abs_im_le_norm (1 - c)
    have him : (1 - c).im = -y := by simp [hc]
    rw [him, abs_neg, abs_of_pos (by linarith)] at this
    linarith
  have hc0 : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [hc])
  have hSb : S ⊆ closedBall c r := fun ρ hρ => by
    obtain ⟨-, a, b, d⟩ := hSz ρ hρ
    exact zeros_na_bola hδ hδ1 a b d
  have hJ := ncard_zeros_zeta_le r_pos r_lt h1 hc0 hS hSb (fun ρ hρ => (hSz ρ hρ).1)
  -- média de log ≤ média de |ζ|²
  have hsph : sphere c |R| ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz hz1
    apply h1
    rw [Set.mem_singleton_iff] at hz1
    rw [← hz1]
    rw [abs_of_pos R_pos] at hz
    exact sphere_subset_closedBall hz
  have han : AnalyticOnNhd ℂ riemannZeta (sphere c |R|) :=
    analyticOn_riemannZeta.mono hsph
  have hlogI : CircleIntegrable (fun z => Real.log ‖riemannZeta z‖) c R :=
    han.meromorphicOn.circleIntegrable_log_norm
  have hsqI : CircleIntegrable (fun z => ‖riemannZeta z‖ ^ 2) c R := by
    apply ContinuousOn.circleIntegrable'
    intro z hz
    exact ((han z hz).continuousAt.norm.pow 2).continuousWithinAt
  have hmono := Real.circleAverage_mono hlogI hsqI fun z _ => log_le_sq _ (norm_nonneg _)
  have hlb : Real.log (2 - Real.pi ^ 2 / 6) ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log dois_menos_pos (zeta_dois_lb y)
  linarith

/-- O integrando de Fubini, em coordenadas. -/
noncomputable def H (R y θ : ℝ) : ℝ :=
  ‖riemannZeta (((2 + R * Real.cos θ : ℝ) : ℂ) + ((y + R * Real.sin θ : ℝ) : ℂ) * I)‖ ^ 2

theorem cA_eq (y R : ℝ) :
    Real.circleAverage (fun z => ‖riemannZeta z‖ ^ 2) (2 + (y : ℂ) * I) R =
      (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), H R y θ := by
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp only [circleMap_coord, H]

theorem H_nonneg (R y θ : ℝ) : 0 ≤ H R y θ := sq_nonneg _

/-- **Fubini**: `∫_{[2,T+1]} média(|ζ|², 2+iy, R) dy ≤ M (T + 3)`, e a média é integrável em `y`. -/
theorem fubini_media {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) {M : ℝ}
    (hM : ∀ σ : ℝ, 1 / 2 + δ / 2 ≤ σ → σ ≤ 4 → ∀ Y : ℝ, 1 ≤ Y →
      ∫ t in (1 / 2 : ℝ)..Y, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ M * Y)
    {T : ℝ} (hT : 2 ≤ T) :
    IntegrableOn (fun y => (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), H (3 / 2 - δ / 2) y θ)
        (Icc 2 (T + 1)) ∧
      ∫ y in Icc 2 (T + 1), (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), H (3 / 2 - δ / 2) y θ
        ≤ M * (T + 3) := by
  set R : ℝ := 3 / 2 - δ / 2 with hR
  have hR0 : 0 < R := by linarith
  have hR1 : R ≤ 3 / 2 := by linarith
  have hcont : ContinuousOn (Function.uncurry (H R)) (Icc 2 (T + 1) ×ˢ Icc 0 (2 * Real.pi)) := by
    intro p hp
    have hin : Continuous (fun p : ℝ × ℝ =>
        ((2 + R * Real.cos p.2 : ℝ) : ℂ) + ((p.1 + R * Real.sin p.2 : ℝ) : ℂ) * I) := by fun_prop
    have hne : ((2 + R * Real.cos p.2 : ℝ) : ℂ) + ((p.1 + R * Real.sin p.2 : ℝ) : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [Complex.sin_ofReal_re] at this
      have hs := Real.neg_one_le_sin p.2
      have hy := hp.1.1
      nlinarith
    have hζ : ContinuousAt (fun z => ‖riemannZeta z‖ ^ 2)
        (((2 + R * Real.cos p.2 : ℝ) : ℂ) + ((p.1 + R * Real.sin p.2 : ℝ) : ℂ) * I) :=
      (differentiableAt_riemannZeta hne).continuousAt.norm.pow 2
    have hca : ContinuousAt (fun q : ℝ × ℝ => ‖riemannZeta (((2 + R * Real.cos q.2 : ℝ) : ℂ) +
        ((q.1 + R * Real.sin q.2 : ℝ) : ℂ) * I)‖ ^ 2) p :=
      ContinuousAt.comp (g := fun z => ‖riemannZeta z‖ ^ 2)
        (f := fun q : ℝ × ℝ => ((2 + R * Real.cos q.2 : ℝ) : ℂ) + ((q.1 + R * Real.sin q.2 : ℝ) : ℂ) * I)
        hζ hin.continuousAt
    exact hca.continuousWithinAt
  have hint : Integrable (Function.uncurry (H R))
      ((volume.restrict (Icc 2 (T + 1))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono le_rfl Ioc_subset_Icc_self)
  refine ⟨(hint.integral_prod_left).const_mul _, ?_⟩
  have hinner : ∀ θ : ℝ, ∫ y in Icc 2 (T + 1), H R y θ ≤ M * (T + 3) := by
    intro θ
    have hc1 := Real.neg_one_le_cos θ
    have hc2 := Real.cos_le_one θ
    have hs1 := Real.neg_one_le_sin θ
    have hs2 := Real.sin_le_one θ
    have hσ0 : 1 / 2 + δ / 2 ≤ 2 + R * Real.cos θ := by nlinarith
    have hσ4 : 2 + R * Real.cos θ ≤ 4 := by nlinarith
    have hd1 : -R ≤ R * Real.sin θ := by nlinarith
    have hd2 : R * Real.sin θ ≤ R := by nlinarith
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hcomp : (∫ y in (2 : ℝ)..T + 1, H R y θ) =
        ∫ t in (2 + R * Real.sin θ)..(T + 1 + R * Real.sin θ),
          ‖riemannZeta (((2 + R * Real.cos θ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      intervalIntegral.integral_comp_add_right
        (fun t => ‖riemannZeta (((2 + R * Real.cos θ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        (R * Real.sin θ)
    rw [hcomp]
    calc ∫ t in (2 + R * Real.sin θ)..(T + 1 + R * Real.sin θ),
          ‖riemannZeta (((2 + R * Real.cos θ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ ∫ t in (1 / 2 : ℝ)..(T + 3),
          ‖riemannZeta (((2 + R * Real.cos θ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
          intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Filter.Eventually.of_forall fun t => sq_nonneg _)
            (intervalIntegrable_sq _ (by norm_num) (by linarith))
      _ ≤ M * (T + 3) := hM _ hσ0 hσ4 (T + 3) (by linarith)
  have hswap := integral_integral_swap hint
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  rw [integral_const_mul, hswap]
  have hle : ∫ θ in Ioc 0 (2 * Real.pi), ∫ y in Icc 2 (T + 1), H R y θ ≤
      ∫ θ in Ioc 0 (2 * Real.pi), M * (T + 3) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => integral_nonneg fun y => H_nonneg R y θ)
      (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall hinner)
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, sub_zero] at hle
  calc (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), ∫ y in Icc 2 (T + 1), H R y θ
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * (M * (T + 3))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = M * (T + 3) := by field_simp

/-- **Bohr–Landau para `0 < δ ≤ 1/4`.** -/
theorem bohrLandau_pequeno {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ((direita (1 / 2 + δ) T).ncard : ℝ) ≤ C * T := by
  obtain ⟨M, hM0, hM⟩ := media_zeta (σ0 := 1 / 2 + δ / 2) (by linarith) (by linarith)
  have hr0 : 0 < 3 / 2 - 3 * δ / 4 := by linarith
  have hlam0 : 0 < Real.log ((3 / 2 - δ / 2) / (3 / 2 - 3 * δ / 4)) :=
    Real.log_pos ((one_lt_div hr0).mpr (by linarith))
  set lam : ℝ := Real.log ((3 / 2 - δ / 2) / (3 / 2 - 3 * δ / 4)) with hlam
  have hL00 : 0 ≤ -Real.log (2 - Real.pi ^ 2 / 6) := by
    have := Real.log_nonpos dois_menos_pos.le dois_menos_le_one
    linarith
  set L0 : ℝ := -Real.log (2 - Real.pi ^ 2 / 6) with hL0
  have hN30 : (0 : ℝ) ≤ ((todos 3).ncard : ℝ) := Nat.cast_nonneg _
  refine ⟨((todos 3).ncard : ℝ) + (5 * M / 2 + L0) / (lam * δ), fun T hT => ?_⟩
  set A : Finset ℂ :=
    (todos_finite T).toFinset.filter (fun ρ => 1 / 2 + δ < ρ.re ∧ 3 ≤ ρ.im) with hA
  -- decomposição: alturas `≤ 3` e `≥ 3`
  have hdec : ((direita (1 / 2 + δ) T).ncard : ℝ) ≤ ((todos 3).ncard : ℝ) + A.card := by
    have hsub : direita (1 / 2 + δ) T ⊆ todos 3 ∪ (A : Set ℂ) := by
      rintro ρ ⟨hz, hre, him0, himT⟩
      by_cases h3 : ρ.im ≤ 3
      · exact Or.inl ⟨hz, him0, h3⟩
      · right
        rw [Finset.mem_coe, hA, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨hz, him0, himT⟩, hre, by linarith⟩
    have := (Set.ncard_le_ncard hsub ((todos_finite 3).union A.finite_toSet)).trans
      (Set.ncard_union_le _ _)
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  -- cada zero de altura `≥ 3` contribui com `δ`
  have hφint : ∀ ρ : ℂ, Integrable
      (Set.indicator (Icc (ρ.im - δ / 2) (ρ.im + δ / 2)) (fun _ => (1 : ℝ)))
      (volume.restrict (Icc 2 (T + 1))) := fun ρ =>
    (continuous_const.integrableOn_Icc).indicator measurableSet_Icc
  have hφval : ∀ ρ ∈ A, ∫ y in Icc 2 (T + 1),
      Set.indicator (Icc (ρ.im - δ / 2) (ρ.im + δ / 2)) (fun _ => (1 : ℝ)) y = δ := by
    intro ρ hρ
    rw [hA, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨-, -, hle⟩, -, h3⟩ := hρ
    have hsub : Icc (ρ.im - δ / 2) (ρ.im + δ / 2) ⊆ Icc 2 (T + 1) :=
      Icc_subset_Icc (by linarith) (by linarith)
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
      measureReal_restrict_apply measurableSet_Icc, inter_eq_left.mpr hsub,
      Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hgint : Integrable (fun y => ∑ ρ ∈ A,
      Set.indicator (Icc (ρ.im - δ / 2) (ρ.im + δ / 2)) (fun _ => (1 : ℝ)) y)
      (volume.restrict (Icc 2 (T + 1))) :=
    integrable_finset_sum A fun ρ _ => hφint ρ
  have hgval : ∫ y in Icc 2 (T + 1), ∑ ρ ∈ A,
      Set.indicator (Icc (ρ.im - δ / 2) (ρ.im + δ / 2)) (fun _ => (1 : ℝ)) y = A.card * δ := by
    rw [integral_finset_sum A fun ρ _ => hφint ρ, Finset.sum_congr rfl hφval, Finset.sum_const,
      nsmul_eq_mul]
  -- Jensen em cada altura
  obtain ⟨hFint, hFbound⟩ := fubini_media hδ hδ1 hM hT
  have hpt : ∀ y ∈ Icc 2 (T + 1), (∑ ρ ∈ A,
      Set.indicator (Icc (ρ.im - δ / 2) (ρ.im + δ / 2)) (fun _ => (1 : ℝ)) y) * lam ≤
      (2 * Real.pi)⁻¹ * (∫ θ in Ioc 0 (2 * Real.pi), H (3 / 2 - δ / 2) y θ) + L0 := by
    intro y hy
    set Sy : Finset ℂ := A.filter (fun ρ => y ∈ Icc (ρ.im - δ / 2) (ρ.im + δ / 2)) with hSy
    have hgy : (∑ ρ ∈ A, Set.indicator (Icc (ρ.im - δ / 2) (ρ.im + δ / 2))
        (fun _ => (1 : ℝ)) y) = Sy.card := by
      rw [hSy, Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun ρ _ => ?_
      by_cases hm : y ∈ Icc (ρ.im - δ / 2) (ρ.im + δ / 2)
      · simp [hm]
      · simp [hm]
    have hJ := jensen_y hδ hδ1 hy.1 (S := (Sy : Set ℂ)) Sy.finite_toSet (by
      intro ρ hρ
      rw [Finset.mem_coe, hSy, Finset.mem_filter] at hρ
      obtain ⟨hρA, hy1, hy2⟩ := hρ
      rw [hA, Finset.mem_filter, Set.Finite.mem_toFinset] at hρA
      obtain ⟨⟨⟨hz, -, h1⟩, -, -⟩, hre, -⟩ := hρA
      exact ⟨hz, hre, h1, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
    rw [Set.ncard_coe_finset, cA_eq] at hJ
    rw [hgy]
    linarith
  have hFL : IntegrableOn (fun y => (2 * Real.pi)⁻¹ *
      (∫ θ in Ioc 0 (2 * Real.pi), H (3 / 2 - δ / 2) y θ) + L0) (Icc 2 (T + 1)) :=
    hFint.add (continuous_const.integrableOn_Icc)
  have hmono := setIntegral_mono_on (hgint.mul_const lam) hFL measurableSet_Icc hpt
  rw [integral_mul_const, hgval, integral_add hFint (continuous_const.integrableOn_Icc),
    setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hmono
  -- aritmética final
  have hpos : 0 < lam * δ := mul_pos hlam0 hδ
  have h1 : (A.card : ℝ) * (lam * δ) ≤ (5 * M / 2 + L0) * T := by nlinarith
  have hcard : (A.card : ℝ) ≤ (5 * M / 2 + L0) / (lam * δ) * T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith
  have hN3T : ((todos 3).ncard : ℝ) ≤ ((todos 3).ncard : ℝ) * T := by nlinarith
  nlinarith

/-- **Teorema de Bohr–Landau (1914), incondicional**: `N(1/2 + δ, T) = O(T)` para todo `δ > 0`. -/
theorem bohrLandau : TeoremaBohrLandau := by
  intro δ hδ
  by_cases hδ1 : δ ≤ 1 / 4
  · exact bohrLandau_pequeno hδ hδ1
  · obtain ⟨C, hC⟩ := bohrLandau_pequeno (δ := 1 / 4) (by norm_num) le_rfl
    refine ⟨C, fun T hT => le_trans ?_ (hC T hT)⟩
    have hsub : direita (1 / 2 + δ) T ⊆ direita (1 / 2 + 1 / 4) T :=
      fun ρ ⟨hz, hre, h0, h1⟩ => ⟨hz, by linarith, h0, h1⟩
    exact_mod_cast Set.ncard_le_ncard hsub ((todos_finite T).subset (direita_subset _ T))

/-- O lado esquerdo também é `O(T)` (pela reflexão `ρ ↦ 1 − ρ̄`). -/
theorem bohrLandau_esquerda (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ((esquerda (1 / 2 - δ) T).ncard : ℝ) ≤ C * T := by
  obtain ⟨C, hC⟩ := bohrLandau δ hδ
  exact ⟨C, fun T hT => by rw [← simetria_contagem]; exact hC T hT⟩

/-- **Fora da faixa `|Re ρ − 1/2| ≤ δ`** há no máximo `O(T)` zeros até a altura `T`. -/
theorem fora_da_faixa (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      ((direita (1 / 2 + δ) T).ncard : ℝ) + (esquerda (1 / 2 - δ) T).ncard ≤ C * T := by
  obtain ⟨C, hC⟩ := bohrLandau δ hδ
  refine ⟨2 * C, fun T hT => ?_⟩
  rw [← simetria_contagem]
  have := hC T hT
  linarith

/-- **Condicional, agora só em B10**: crescimento de `N(T)` ⇒ quase todos os zeros perto de `1/2`. -/
theorem densidade_de_crescimento (hN : CrescimentoN) : Densidade :=
  densidade_de_bohrLandau bohrLandau hN

/-- **Zeros isolados**: toda sequência de zeros **distintos** de `ζ` vai para o infinito; não há
acúmulo em ponto finito (em particular, nenhuma sequência de zeros exatos converge para um ponto). -/
theorem zeros_escapam {ρ : ℕ → ℂ} (hinj : Function.Injective ρ)
    (hz : ∀ n, riemannZeta (ρ n) = 0) : Tendsto (fun n => ‖ρ n‖) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  have hK := (isCompact_closedBall (0 : ℂ) B).inter_riemannZetaZeros_finite
  have hpre : {n | ρ n ∈ closedBall (0 : ℂ) B ∩ riemannZetaZeros}.Finite :=
    hK.preimage hinj.injOn
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hpre.compl_mem_cofinite] with n hn
  by_contra h
  push Not at h
  exact hn ⟨by rw [mem_closedBall, dist_zero_right]; exact h.le, hz n⟩

end ATK.BLProva

#print axioms ATK.BLProva.zeta_dois_lb
#print axioms ATK.BLProva.zeros_na_bola
#print axioms ATK.BLProva.jensen_y
#print axioms ATK.BLProva.cA_eq
#print axioms ATK.BLProva.fubini_media
#print axioms ATK.BLProva.bohrLandau_pequeno
#print axioms ATK.BLProva.bohrLandau
#print axioms ATK.BLProva.bohrLandau_esquerda
#print axioms ATK.BLProva.fora_da_faixa
#print axioms ATK.BLProva.densidade_de_crescimento
#print axioms ATK.BLProva.zeros_escapam
#print axioms ATK.BLProva.circleMap_coord
#print axioms ATK.BLProva.log_le_sq
#print axioms ATK.BLProva.dois_menos_pos
#print axioms ATK.BLProva.dois_menos_le_one
#print axioms ATK.BLProva.H_nonneg
