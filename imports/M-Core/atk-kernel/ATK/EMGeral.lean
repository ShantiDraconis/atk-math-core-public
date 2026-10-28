import ATK.BLEulerMaclaurin
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler–Maclaurin de ordem arbitrária para `ζ`, com resto explícito

Para `0 < Re s`, `s ≠ 1`, `N ≥ 1`, `M ≥ 1`:

  `ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − N^{−s}/2
          + Σ_{j=2}^{M} (B_j / j!)·(s)_{j−1}·N^{−s−j+1} − ((s)_M / M!)·J_M(s)`,

com `J_M(s) = ∫_N^∞ P_M(t) t^{−s−M} dt`, `P_M(t) = B_M({t})` (Bernoulli periódico) e
`|J_M(s)| ≤ C_M · N^{1−σ−M}/(σ+M−1)`, `C_M = Σ_i |B_i|·C(M,i)` (`abs_bernoulliFun_le`).

* `passo_unidade`: integração por partes em `[n, n+1]`;
* `recorrencia`: `J_k = −B_{k+1}N^{−s−k}/(k+1) + (s+k)/(k+1)·J_{k+1}`;
* **`zeta_EM`**: a fórmula acima; **`norm_zeta_sub_EM_le`**: o resto.
-/

open Complex Set MeasureTheory Filter Topology intervalIntegral

namespace ATK.EMGeral

open ATK.BLEulerMaclaurin

/-- Bernoulli periódico `P_k(t) = B_k({t})`. -/
noncomputable def perB (k : ℕ) (t : ℝ) : ℝ := bernoulliFun k (Int.fract t)

/-- Cota de `|B_k|` em `[0, 1]`. -/
noncomputable def Cb (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), |(bernoulli i : ℝ)| * (k.choose i : ℝ)

theorem bernoulliFun_eq_sum (k : ℕ) (x : ℝ) :
    bernoulliFun k x = ∑ i ∈ Finset.range (k + 1), (bernoulli i : ℝ) * (k.choose i : ℝ) * x ^ (k - i) := by
  rw [bernoulliFun, Polynomial.eval_map, Polynomial.bernoulli, Polynomial.eval₂_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval₂_monomial]
  simp

theorem abs_bernoulliFun_le (k : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |bernoulliFun k x| ≤ Cb k := by
  rw [bernoulliFun_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg h0 _), Nat.abs_cast]
  have hx : x ^ (k - i) ≤ 1 := pow_le_one₀ h0 h1
  have ha : 0 ≤ |(bernoulli i : ℝ)| * (k.choose i : ℝ) := by positivity
  nlinarith

theorem Cb_nonneg (k : ℕ) : 0 ≤ Cb k := Finset.sum_nonneg fun _ _ => by positivity

theorem abs_perB_le (k : ℕ) (t : ℝ) : |perB k t| ≤ Cb k :=
  abs_bernoulliFun_le k (Int.fract_nonneg t) (Int.fract_lt_one t).le

theorem measurable_perB (k : ℕ) : Measurable (perB k) :=
  (continuous_bernoulliFun k).measurable.comp measurable_fract

/-- `P_k(t) = B_k(t − n)` em `[n, n+1)`. -/
theorem perB_eq {k : ℕ} {n : ℕ} {t : ℝ} (h1 : (n : ℝ) ≤ t) (h2 : t < n + 1) :
    perB k t = bernoulliFun k (t - n) := by
  unfold perB
  congr 1
  rw [Int.fract, show (⌊t⌋ : ℝ) = n by
    have : ⌊t⌋ = (n : ℤ) := by rw [Int.floor_eq_iff]; push_cast; exact ⟨h1, h2⟩
    rw [this]; push_cast; ring]

/-- O resto `J_k(s) = ∫_N^∞ P_k(t) t^{−s−k} dt`. -/
noncomputable def J (N k : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (N : ℝ), ((perB k t : ℝ) : ℂ) * (t : ℂ) ^ (-s - k)

theorem integrableOn_J {s : ℂ} {k N : ℕ} (hσ : 1 < s.re + k) (hN : 1 ≤ N) :
    IntegrableOn (fun t : ℝ => ((perB k t : ℝ) : ℂ) * (t : ℂ) ^ (-s - k)) (Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : IntegrableOn (fun t : ℝ => Cb k * t ^ (-s.re - k)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _
  refine hg.mono' ?_ ?_
  · refine (((Complex.measurable_ofReal.comp (measurable_perB k)).aestronglyMeasurable).mul ?_)
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := hN0.trans ht
    exact (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 ht0)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hN0.trans ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - (k : ℂ)).re = -s.re - k := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (abs_perB_le k t) (Real.rpow_nonneg ht0.le _)

/-- **Cota do resto**: `|J_k(s)| ≤ C_k N^{1−σ−k}/(σ+k−1)`. -/
theorem norm_J_le {s : ℂ} {k N : ℕ} (hσ : 1 < s.re + k) (hN : 1 ≤ N) :
    ‖J N k s‖ ≤ Cb k * (N : ℝ) ^ (1 - s.re - k) / (s.re + k - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : IntegrableOn (fun t : ℝ => Cb k * t ^ (-s.re - k)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _
  unfold J
  calc ‖∫ t in Ioi (N : ℝ), ((perB k t : ℝ) : ℂ) * (t : ℂ) ^ (-s - k)‖
      ≤ ∫ t in Ioi (N : ℝ), ‖((perB k t : ℝ) : ℂ) * (t : ℂ) ^ (-s - k)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (N : ℝ), Cb k * t ^ (-s.re - k) := by
        refine setIntegral_mono_on (integrableOn_J hσ hN).norm hg measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hN0.trans ht
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - (k : ℂ)).re = -s.re - k := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (abs_perB_le k t) (Real.rpow_nonneg ht0.le _)
    _ = Cb k * (N : ℝ) ^ (1 - s.re - k) / (s.re + k - 1) := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0]
        have e : -s.re - k + 1 = 1 - s.re - k := by ring
        rw [e]
        have h2 : -(N : ℝ) ^ (1 - s.re - k) / (1 - s.re - k) =
            (N : ℝ) ^ (1 - s.re - k) / (s.re + k - 1) := by
          rw [neg_div, ← div_neg]; congr 1; ring
        rw [h2, mul_div_assoc]

theorem continuousOn_cpow_pos (c : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ c) (Set.uIcc a b) := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : 0 < t := ha.trans_le ht.1
  exact (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
    (Complex.ofReal_mem_slitPlane.2 ht0)).continuousWithinAt

/-- **Integração por partes em `[n, n+1]`** (`k ≥ 1`, `σ > 0`). -/
theorem passo_unidade {s : ℂ} (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in (n : ℝ)..(n + 1), ((perB k t : ℝ) : ℂ) * (t : ℂ) ^ (-s - k) =
      (bernoulli (k + 1) : ℂ) / (k + 1) * (((n : ℂ) + 1) ^ (-s - k) - (n : ℂ) ^ (-s - k)) +
      (s + k) / (k + 1) *
        ∫ t in (n : ℝ)..(n + 1), ((perB (k + 1) t : ℝ) : ℂ) * (t : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hae : ∀ j : ℕ, ∀ c : ℂ, ∀ᵐ t ∂volume, t ∈ Set.uIoc (n : ℝ) (n + 1) →
      ((perB j t : ℝ) : ℂ) * (t : ℂ) ^ c = ((bernoulliFun j (t - n) : ℝ) : ℂ) * (t : ℂ) ^ c := by
    intro j c
    have hfin : ∀ᵐ t ∂volume, t ≠ (n : ℝ) + 1 := by
      have : volume ({(n : ℝ) + 1} : Set ℝ) = 0 := Real.volume_singleton
      filter_upwards [compl_mem_ae_iff.mpr this] with t ht
      simpa using ht
    filter_upwards [hfin] with t hne ht
    rw [Set.uIoc_of_le hle] at ht
    rw [perB_eq ht.1.le (lt_of_le_of_ne ht.2 hne)]
  rw [intervalIntegral.integral_congr_ae (hae k _), intervalIntegral.integral_congr_ae (hae (k + 1) _)]
  have hpos : ∀ t ∈ Set.uIcc (n : ℝ) (n + 1), 0 < t := by
    intro t ht; rw [Set.uIcc_of_le hle] at ht; linarith [ht.1]
  have hr : (-s - k : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hU : ∀ t ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-s - k)) ((-s - k) * (t : ℂ) ^ (-s - k - 1)) t :=
    fun t ht => hasDerivAt_ofReal_cpow_const (hpos t ht).ne' hr
  have hV : ∀ t ∈ Set.uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun t : ℝ => ((bernoulliFun (k + 1) (t - n) / (k + 1) : ℝ) : ℂ))
        ((bernoulliFun k (t - n) : ℝ) : ℂ) t := by
    intro t _
    have h3 : HasDerivAt (fun x : ℝ => bernoulliFun (k + 1) (x - n) / (k + 1))
        (bernoulliFun k (t - n)) t := by
      have h := (antideriv_bernoulliFun k (t - n)).comp t ((hasDerivAt_id t).sub_const (n : ℝ))
      simp only [Function.comp_def, id_eq, mul_one] at h
      exact h
    exact h3.ofReal_comp
  have hU' : IntervalIntegrable (fun t : ℝ => (-s - k) * (t : ℂ) ^ (-s - k - 1)) volume (n : ℝ) (n + 1) :=
    ((continuousOn_cpow_pos _ hn0 hle).const_smul (-s - k)).intervalIntegrable
  have hV' : IntervalIntegrable (fun t : ℝ => ((bernoulliFun k (t - n) : ℝ) : ℂ)) volume (n : ℝ) (n + 1) :=
    (by fun_prop : Continuous fun t : ℝ => ((bernoulliFun k (t - n) : ℝ) : ℂ)).intervalIntegrable _ _
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hV hU' hV'
  have hcomm : (∫ t in (n : ℝ)..(n + 1), ((bernoulliFun k (t - n) : ℝ) : ℂ) * (t : ℂ) ^ (-s - k)) =
      ∫ t in (n : ℝ)..(n + 1), (t : ℂ) ^ (-s - k) * ((bernoulliFun k (t - n) : ℝ) : ℂ) := by
    congr 1; funext t; ring
  have hlast : (∫ t in (n : ℝ)..(n + 1), (-s - k) * (t : ℂ) ^ (-s - k - 1) *
      ((bernoulliFun (k + 1) (t - n) / (k + 1) : ℝ) : ℂ)) =
      (-s - k) / (k + 1) * ∫ t in (n : ℝ)..(n + 1),
        ((bernoulliFun (k + 1) (t - n) : ℝ) : ℂ) * (t : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t
    have e : -s - (k : ℂ) - 1 = -s - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e]; push_cast; field_simp
  have hk1 : k + 1 ≠ 1 := by omega
  have hb1 : bernoulliFun (k + 1) ((n : ℝ) + 1 - n) = bernoulli (k + 1) := by
    rw [add_sub_cancel_left, bernoulliFun_endpoints_eq_of_ne_one hk1, bernoulliFun_eval_zero]
  have hb0 : bernoulliFun (k + 1) ((n : ℝ) - n) = bernoulli (k + 1) := by
    rw [sub_self, bernoulliFun_eval_zero]
  rw [hcomm, ibp, hlast, hb1, hb0]
  push_cast
  ring

/-- **Recorrência**: `J_k = −B_{k+1}N^{−s−k}/(k+1) + (s+k)/(k+1)·J_{k+1}`. -/
theorem recorrencia {s : ℂ} (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) :
    J N k s = -((bernoulli (k + 1) : ℂ) / (k + 1)) * (N : ℂ) ^ (-s - k) +
      (s + k) / (k + 1) * J N (k + 1) s := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfi := integrableOn_J (s := s) (k := k) (by linarith) hN
  have hgi := integrableOn_J (s := s) (k := k + 1) (by push_cast; linarith) hN
  set a : ℕ → ℝ := fun i => ((N + i : ℕ) : ℝ) with ha
  have ha0 : a 0 = N := by simp [ha]
  have haN : ∀ i, (N : ℝ) ≤ a i := fun i => by simp [ha]
  have hsucc : ∀ i, a (i + 1) = ((N + i : ℕ) : ℝ) + 1 := fun i => by simp [ha]; ring
  have hint : ∀ {F : ℝ → ℂ}, IntegrableOn F (Ioi (N : ℝ)) → ∀ i,
      IntervalIntegrable F volume (a i) (a (i + 1)) := by
    intro F hF i
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by rw [hsucc]; simp [ha])]
    exact hF.mono_set (fun t ht => lt_of_le_of_lt (haN i) ht.1)
  have hfin : ∀ m : ℕ, ∫ t in (N : ℝ)..a m, ((perB k t : ℝ) : ℂ) * (t : ℂ) ^ (-s - k) =
      (bernoulli (k + 1) : ℂ) / (k + 1) * (((N + m : ℕ) : ℂ) ^ (-s - k) - (N : ℂ) ^ (-s - k)) +
      (s + k) / (k + 1) *
        ∫ t in (N : ℝ)..a m, ((perB (k + 1) t : ℝ) : ℂ) * (t : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) := by
    intro m
    rw [← ha0, ← intervalIntegral.sum_integral_adjacent_intervals (fun i _ => hint hfi i),
      ← intervalIntegral.sum_integral_adjacent_intervals (fun i _ => hint hgi i)]
    have hstep : ∀ i, ∫ t in a i..a (i + 1), ((perB k t : ℝ) : ℂ) * (t : ℂ) ^ (-s - k) =
        (bernoulli (k + 1) : ℂ) / (k + 1) *
          (((N + (i + 1) : ℕ) : ℂ) ^ (-s - k) - ((N + i : ℕ) : ℂ) ^ (-s - k)) +
        (s + k) / (k + 1) *
          ∫ t in a i..a (i + 1), ((perB (k + 1) t : ℝ) : ℂ) * (t : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) := by
      intro i
      rw [hsucc]
      have := passo_unidade hs hk (n := N + i) (by omega)
      rw [show ((N + (i + 1) : ℕ) : ℂ) = ((N + i : ℕ) : ℂ) + 1 by push_cast; ring]
      exact this
    simp_rw [hstep]
    have htel : ∑ i ∈ Finset.range m,
        (((N + (i + 1) : ℕ) : ℂ) ^ (-s - k) - ((N + i : ℕ) : ℂ) ^ (-s - k)) =
        ((N + m : ℕ) : ℂ) ^ (-s - k) - ((N + 0 : ℕ) : ℂ) ^ (-s - k) :=
      Finset.sum_range_sub (fun i => ((N + i : ℕ) : ℂ) ^ (-s - k)) m
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htel]
    simp [ha0]
  have hta : Tendsto a atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun m => Nat.le_add_left m N) tendsto_id)
  have hlimL := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hfi hta
  have hlimG := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hgi hta
  have hpow : Tendsto (fun m : ℕ => ((N + m : ℕ) : ℂ) ^ (-s - k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ m : ℕ, ‖((N + m : ℕ) : ℂ) ^ (-s - k)‖ = a m ^ (-(s.re + k)) := by
      intro m
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      simp [ha]; ring_nf
    simp_rw [e]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < s.re + k)).comp hta
  have hR := ((hpow.sub (tendsto_const_nhds (x := (N : ℂ) ^ (-s - k)))).const_mul ((bernoulli (k + 1) : ℂ) / (k + 1))).add
    (hlimG.const_mul ((s + k) / (k + 1)))
  have hL : Tendsto (fun m : ℕ => (bernoulli (k + 1) : ℂ) / (k + 1) *
      (((N + m : ℕ) : ℂ) ^ (-s - k) - (N : ℂ) ^ (-s - k)) + (s + k) / (k + 1) *
      ∫ t in (N : ℝ)..a m, ((perB (k + 1) t : ℝ) : ℂ) * (t : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)))
      atTop (𝓝 (J N k s)) := hlimL.congr hfin
  have := tendsto_nhds_unique hL hR
  rw [this]
  unfold J
  ring

/-- Fatorial ascendente `(s)_m = s(s+1)⋯(s+m−1)`. -/
noncomputable def poch (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => poch s m * (s + m)

/-- A parte explícita de Euler–Maclaurin de ordem `M`. -/
noncomputable def EM (N M : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2 +
    ∑ j ∈ Finset.Ico 2 (M + 1),
      (bernoulli j : ℂ) / (j.factorial : ℂ) * poch s (j - 1) * (N : ℂ) ^ (-s - ((j - 1 : ℕ) : ℂ))

/-- `I_N(s) = J_1(s) + N^{−s}/(2s)`. -/
theorem cauda_eq_J {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    cauda N s = J N 1 s + (N : ℂ) ^ (-s) / (2 * s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have h1 := integrableOn_J (s := s) (k := 1) (by push_cast; linarith) hN
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) hN0
  have hpt : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) =
      ((perB 1 t : ℝ) : ℂ) * (t : ℂ) ^ (-s - ((1 : ℕ) : ℂ)) + (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1) := by
    intro t
    simp only [perB, bernoulliFun_one, Nat.cast_one]
    push_cast; ring
  unfold cauda J
  simp_rw [hpt]
  rw [integral_add h1 (h2.const_mul _), MeasureTheory.integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) hN0]
  have e : -s - 1 + 1 = -s := by ring
  rw [e, Complex.ofReal_natCast]
  field_simp

/-- **Euler–Maclaurin de ordem `M`** para `ζ`. -/
theorem zeta_EM {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) {M : ℕ} (hM : 1 ≤ M) :
    riemannZeta s = EM N M s - poch s M / (M.factorial : ℂ) * J N M s := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  induction M, hM using Nat.le_induction with
  | base =>
    rw [zeta_eq hs hs1 N hN, cauda_eq_J hs hN]
    unfold EM
    simp [poch]
    field_simp
    ring
  | succ M hM ih =>
    rw [ih, recorrencia hs hM hN]
    unfold EM
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ M + 1)]
    simp only [Nat.add_sub_cancel, poch, Nat.factorial_succ]
    push_cast
    have hM0 : ((M.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    have hM1 : (M : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    field_simp
    ring

/-- **Resto de Euler–Maclaurin**: `|ζ(s) − EM_M| ≤ |(s)_M|/M! · C_M · N^{1−σ−M}/(σ+M−1)`. -/
theorem norm_zeta_sub_EM_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) {M : ℕ}
    (hM : 1 ≤ M) :
    ‖riemannZeta s - EM N M s‖ ≤
      ‖poch s M‖ / (M.factorial : ℝ) * (Cb M * (N : ℝ) ^ (1 - s.re - M) / (s.re + M - 1)) := by
  rw [zeta_EM hs hs1 hN hM, sub_sub_cancel_left, norm_neg, norm_mul, norm_div, Complex.norm_natCast]
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  exact mul_le_mul_of_nonneg_left (norm_J_le (by linarith) hN) (by positivity)

end ATK.EMGeral

#print axioms ATK.EMGeral.abs_bernoulliFun_le
#print axioms ATK.EMGeral.perB_eq
#print axioms ATK.EMGeral.integrableOn_J
#print axioms ATK.EMGeral.norm_J_le
#print axioms ATK.EMGeral.passo_unidade
#print axioms ATK.EMGeral.recorrencia
#print axioms ATK.EMGeral.cauda_eq_J
#print axioms ATK.EMGeral.zeta_EM
#print axioms ATK.EMGeral.norm_zeta_sub_EM_le
#print axioms ATK.EMGeral.bernoulliFun_eq_sum
#print axioms ATK.EMGeral.Cb_nonneg
#print axioms ATK.EMGeral.abs_perB_le
#print axioms ATK.EMGeral.measurable_perB
#print axioms ATK.EMGeral.continuousOn_cpow_pos
