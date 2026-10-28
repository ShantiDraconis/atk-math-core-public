import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ATK.RHLogZeta
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# ATK — Fórmula de Perron suavizada e deslocamento de contorno

Para `k(u) = max(1 − u, 0)` e `K(z) = 1/(z(z+1))` (a transformada de Mellin de `k` em `Re z > 0`,
e a de `k − 1` em `−1 < Re z < 0`), a inversão de Mellin da Mathlib dá

  `k(x) = (1/2π) ∫ x^(−(1+iy)) K(1+iy) dy`   (`perron_kk`),

e com o teorema de Cauchy para retângulos da Mathlib (`desloca`) a soma suavizada

  `A_N(w) = Σ_{n ≤ N} μ(n) (1 − n/N) n^(−w)`

satisfaz, sob RH e para `Re w = 1/2 + ε`,

  `A_N(w) − 1/ζ(w) = (1/2π) ∫ N^(−θ+iy) F(w − θ + iy) K(−θ + iy) dy`   (`θ = ε/2`),

donde `‖A_N(w) − 1/ζ(w)‖ ≤ C N^(−ε/2) (1 + |Im w|)^η` (`norm_AN_sub_le`), com `η` arbitrário
(`ATK.RHLogZeta.norm_F_le`).
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace ATK.PerronSuave

/-! ## Deslocamento de contorno entre retas verticais -/

/-- **Deslocamento de contorno**: se `f` é contínua na faixa fechada `a ≤ Re ≤ b`, holomorfa no
interior fora de um conjunto enumerável, integrável nas duas retas e pequena nos segmentos
horizontais de altura `±T` (`T → ∞`), então as integrais nas duas retas coincidem. -/
theorem desloca {f : ℂ → ℂ} {a b : ℝ} (hab : a < b) {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (re ⁻¹' Icc a b))
    (hd : ∀ z ∈ re ⁻¹' Ioo a b \ s, DifferentiableAt ℂ f z)
    (ha : Integrable (fun y : ℝ => f (a + y * I)))
    (hb : Integrable (fun y : ℝ => f (b + y * I)))
    (hdecay : ∀ η > 0, ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc a b,
      ‖f (x + T * I)‖ ≤ η ∧ ‖f (x + ((-T : ℝ) : ℂ) * I)‖ ≤ η) :
    ∫ y : ℝ, f (a + y * I) = ∫ y : ℝ, f (b + y * I) := by
  have hrect : ∀ T : ℝ, 0 < T →
      (∫ x : ℝ in a..b, f (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in a..b, f (x + T * I)) +
        I • (∫ y : ℝ in -T..T, f (b + y * I)) - I • (∫ y : ℝ in -T..T, f (a + y * I)) = 0 := by
    intro T hT
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f
      (a + ((-T : ℝ) : ℂ) * I) (b + T * I) s hs ?_ ?_
    · simpa using h
    · refine hc.mono ?_
      intro z hz
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
        mul_one, sub_self, add_zero] at hz
      show z.re ∈ Icc a b
      rw [uIcc_of_le hab.le] at hz
      exact hz.1
    · intro z hz
      refine hd z ⟨?_, hz.2⟩
      have h1 := hz.1
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
        mul_one, sub_self, add_zero, min_eq_left hab.le, max_eq_right hab.le] at h1
      exact h1.1
  -- integrais verticais convergem
  have hVa : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (a + y * I)) atTop
      (𝓝 (∫ y : ℝ, f (a + y * I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (b + y * I)) atTop
      (𝓝 (∫ y : ℝ, f (b + y * I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  -- integrais horizontais tendem a zero
  have hH : Tendsto (fun T : ℝ => (∫ x : ℝ in a..b, f (x + ((-T : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in a..b, f (x + T * I))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    have hη' : 0 < η / (2 * (b - a) + 1) := by
      have : 0 < 2 * (b - a) + 1 := by linarith
      positivity
    obtain ⟨T₀, hT₀⟩ := (hdecay _ hη').exists_forall_of_atTop
    refine ⟨T₀, fun T hT => ?_⟩
    rw [dist_zero_right]
    have hbd := hT₀ T hT
    have h1 : ‖∫ x : ℝ in a..b, f (x + ((-T : ℝ) : ℂ) * I)‖ ≤ η / (2 * (b - a) + 1) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
        rw [uIoc_of_le hab.le] at hx
        exact (hbd x ⟨le_of_lt hx.1, hx.2⟩).2)
    have h2 : ‖∫ x : ℝ in a..b, f (x + T * I)‖ ≤ η / (2 * (b - a) + 1) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
        rw [uIoc_of_le hab.le] at hx
        exact (hbd x ⟨le_of_lt hx.1, hx.2⟩).1)
    rw [abs_of_pos (by linarith)] at h1 h2
    have h3 : η / (2 * (b - a) + 1) * (b - a) < η / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    calc ‖(∫ x : ℝ in a..b, f (x + ((-T : ℝ) : ℂ) * I)) - ∫ x : ℝ in a..b, f (x + T * I)‖
        ≤ ‖∫ x : ℝ in a..b, f (x + ((-T : ℝ) : ℂ) * I)‖ + ‖∫ x : ℝ in a..b, f (x + T * I)‖ :=
          norm_sub_le _ _
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring
  -- `I • (Vb − Va) = −(H₋ − H₊)` eventualmente, e passa ao limite
  have hlim1 : Tendsto (fun T : ℝ => I • (∫ y : ℝ in -T..T, f (b + y * I)) -
      I • (∫ y : ℝ in -T..T, f (a + y * I))) atTop
      (𝓝 (I • (∫ y : ℝ, f (b + y * I)) - I • (∫ y : ℝ, f (a + y * I)))) :=
    (hVb.const_smul I).sub (hVa.const_smul I)
  have hlim2 : Tendsto (fun T : ℝ => I • (∫ y : ℝ in -T..T, f (b + y * I)) -
      I • (∫ y : ℝ in -T..T, f (a + y * I))) atTop (𝓝 0) := by
    have hneg := hH.neg
    rw [neg_zero] at hneg
    refine hneg.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have := hrect T hT
    simp only [smul_eq_mul] at this ⊢
    linear_combination -this
  have heq := tendsto_nhds_unique hlim1 hlim2
  have : I • ((∫ y : ℝ, f (b + y * I)) - ∫ y : ℝ, f (a + y * I)) = 0 := by
    rw [smul_sub]; exact heq
  rcases smul_eq_zero.mp this with h | h
  · exact absurd h I_ne_zero
  · exact (sub_eq_zero.mp h).symm

/-! ## O núcleo `k(u) = max(1 − u, 0)` e `K(z) = 1/(z(z+1))` -/

/-- `k(u) = max(1 − u, 0)`. -/
noncomputable def kk (u : ℝ) : ℝ := max (1 - u) 0

/-- `K(z) = 1/(z(z+1))`. -/
noncomputable def KK (z : ℂ) : ℂ := 1 / (z * (z + 1))

theorem continuous_kk : Continuous kk := (continuous_const.sub continuous_id).max continuous_const

theorem kk_of_le_one {u : ℝ} (hu : u ≤ 1) : kk u = 1 - u := max_eq_left (by linarith)

theorem kk_of_one_le {u : ℝ} (hu : 1 ≤ u) : kk u = 0 := max_eq_right (by linarith)

theorem kk_nonneg (u : ℝ) : 0 ≤ kk u := le_max_right _ _

theorem kk_le_one {u : ℝ} (hu : 0 ≤ u) : kk u ≤ 1 := max_le (by linarith) zero_le_one

/-- `∫₀¹ x^r = 1/(r+1)` (`Re r > −1`). -/
theorem integral_zero_one_cpow {r : ℂ} (hr : -1 < r.re) :
    (∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ r) = 1 / (r + 1) := by
  rw [integral_cpow (Or.inl hr)]
  have hr1 : r + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  simp [Complex.zero_cpow hr1]

theorem integrableOn_cpow_Ioc {r : ℂ} (hr : -1 < r.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ r) (Ioc 0 1) := by
  have := (intervalIntegrable_cpow' (a := 0) (b := 1) hr)
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this

theorem cpow_eq_mul_self {t : ℂ} (ht : t ≠ 0) (z : ℂ) : t ^ z = t ^ (z - 1) * t := by
  conv_lhs => rw [show z = (z - 1) + 1 by ring]
  rw [Complex.cpow_add _ _ ht, Complex.cpow_one]

theorem intervalIntegrable_cpow01 {r : ℂ} (hr : -1 < r.re) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume 0 1 :=
  intervalIntegrable_cpow' hr

/-- **Mellin de `k`**: `∫₀^∞ k(u) u^(z−1) du = 1/(z(z+1))` para `Re z > 0`. -/
theorem mellin_kk {z : ℂ} (hz : 0 < z.re) : mellin (fun u => ((kk u : ℝ) : ℂ)) z = KK z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; exact lt_irrefl 0 hz
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun t ht => by
      have h1 : 1 < t := by
        rcases ht with ⟨h0, hn⟩
        by_contra hc; exact hn ⟨h0, not_lt.mp hc⟩
      beta_reduce
      rw [kk_of_one_le h1.le]; simp)]
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ => (t : ℂ) ^ (z - 1) - (t : ℂ) ^ z)
    (fun t ht => by
      simp only
      rw [kk_of_le_one ht.2, smul_eq_mul]
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
      rw [cpow_eq_mul_self ht0 z]
      push_cast; ring)]
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (intervalIntegrable_cpow01 (by simp; linarith))
      (intervalIntegrable_cpow01 (by linarith)),
    integral_zero_one_cpow (by simp; linarith), integral_zero_one_cpow (by linarith), KK]
  rw [sub_add_cancel]
  field_simp
  ring

theorem mellinConvergent_kk {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun u => ((kk u : ℝ) : ℂ)) z := by
  unfold MellinConvergent
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := Ioc 0 1) ?_ measurableSet_Ioi ?_
  · refine ((integrableOn_cpow_Ioc (r := z - 1) (by simp; linarith)).sub
      (integrableOn_cpow_Ioc (r := z) (by linarith))).congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]
    rw [kk_of_le_one ht.2, smul_eq_mul]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    rw [cpow_eq_mul_self ht0 z]
    push_cast; ring
  · intro t ht
    have h1 : 1 < t := by
      rcases ht with ⟨h0, hn⟩
      by_contra hc; exact hn ⟨h0, not_lt.mp hc⟩
    beta_reduce
    rw [kk_of_one_le h1.le]; simp

/-- **Mellin de `k − 1`**: `∫₀^∞ (k(u) − 1) u^(z−1) du = 1/(z(z+1))` para `−1 < Re z < 0`. -/
theorem mellin_kk_sub {z : ℂ} (hz1 : -1 < z.re) (hz2 : z.re < 0) :
    mellin (fun u => ((kk u - 1 : ℝ) : ℂ)) z = KK z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz2; exact lt_irrefl 0 hz2
  have hz1' : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  unfold mellin
  have hA : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • ((kk t - 1 : ℝ) : ℂ)) (Ioc 0 1) := by
    refine (integrableOn_cpow_Ioc (r := z) hz1).neg.congr_fun (fun t ht => ?_) measurableSet_Ioc
    try simp only [Pi.neg_apply]
    rw [kk_of_le_one ht.2, smul_eq_mul]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    rw [cpow_eq_mul_self ht0 z]
    push_cast; ring
  have hB : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • ((kk t - 1 : ℝ) : ℂ)) (Ioi 1) := by
    refine (integrableOn_Ioi_cpow_of_lt (a := z - 1) (by simp; linarith) zero_lt_one).neg.congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    try simp only [Pi.neg_apply]
    rw [kk_of_one_le (le_of_lt ht), smul_eq_mul]
    push_cast; ring
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi hA hB]
  have h1 : (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (z - 1) • ((kk t - 1 : ℝ) : ℂ)) = -(1 / (z + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ => -((t : ℂ) ^ z)) (fun t ht => by
      simp only
      rw [kk_of_le_one ht.2, smul_eq_mul]
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
      rw [cpow_eq_mul_self ht0 z]
      push_cast; ring)]
    rw [MeasureTheory.integral_neg, ← intervalIntegral.integral_of_le zero_le_one, integral_zero_one_cpow hz1]
  have h2 : (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) • ((kk t - 1 : ℝ) : ℂ)) = 1 / z := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => -((t : ℂ) ^ (z - 1)))
      (fun t ht => by
        simp only
        rw [kk_of_one_le (le_of_lt ht), smul_eq_mul]
        push_cast; ring)]
    rw [MeasureTheory.integral_neg, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    simp only [ofReal_one, sub_add_cancel, one_cpow]
    ring
  rw [h1, h2, KK]
  field_simp
  ring

theorem mellinConvergent_kk_sub {z : ℂ} (hz1 : -1 < z.re) (hz2 : z.re < 0) :
    MellinConvergent (fun u => ((kk u - 1 : ℝ) : ℂ)) z := by
  unfold MellinConvergent
  have hA : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • ((kk t - 1 : ℝ) : ℂ)) (Ioc 0 1) := by
    refine (integrableOn_cpow_Ioc (r := z) hz1).neg.congr_fun (fun t ht => ?_) measurableSet_Ioc
    try simp only [Pi.neg_apply]
    rw [kk_of_le_one ht.2, smul_eq_mul]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    rw [cpow_eq_mul_self ht0 z]
    push_cast; ring
  have hB : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • ((kk t - 1 : ℝ) : ℂ)) (Ioi 1) := by
    refine (integrableOn_Ioi_cpow_of_lt (a := z - 1) (by simp; linarith) zero_lt_one).neg.congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    try simp only [Pi.neg_apply]
    rw [kk_of_one_le (le_of_lt ht), smul_eq_mul]
    push_cast; ring
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hA.union hB

/-! ## `K` nas retas verticais e a inversão de Mellin -/

theorem norm_KK (z : ℂ) : ‖KK z‖ = 1 / (‖z‖ * ‖z + 1‖) := by
  rw [KK, norm_div, norm_one, norm_mul]

theorem sq_norm_line (σ y : ℝ) : ‖((σ : ℂ) + y * I)‖ ^ 2 = σ ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring

theorem le_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb two_ne_zero).mp h

/-- `‖K(σ + iy)‖ ≤ (2/m)/(1 + y²)` se `|σ| ≥ m`, `|σ + 1| ≥ 1/2` e `0 < m ≤ 1`. -/
theorem norm_KK_le {σ m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hσ : m ≤ |σ|) (hσ1 : 1 / 2 ≤ |σ + 1|)
    (y : ℝ) : ‖KK (σ + y * I)‖ ≤ 2 / m / (1 + y ^ 2) := by
  rw [norm_KK]
  have h1 : m * √(1 + y ^ 2) ≤ ‖((σ : ℂ) + y * I)‖ := by
    refine le_of_sq_le (by positivity) (norm_nonneg _) ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), sq_norm_line]
    have : m ^ 2 ≤ σ ^ 2 := by
      have := mul_le_mul hσ hσ hm.le (abs_nonneg σ)
      rw [← sq, ← sq, sq_abs] at this; exact this
    have hm2 : m ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hm2 (sq_nonneg y)]
  have h2 : 1 / 2 * √(1 + y ^ 2) ≤ ‖((σ : ℂ) + y * I) + 1‖ := by
    refine le_of_sq_le (by positivity) (norm_nonneg _) ?_
    have : ((σ : ℂ) + y * I) + 1 = ((σ + 1 : ℝ) : ℂ) + y * I := by push_cast; ring
    rw [this, mul_pow, Real.sq_sqrt (by positivity), sq_norm_line]
    have : 1 / 4 ≤ (σ + 1) ^ 2 := by
      have := mul_le_mul hσ1 hσ1 (by norm_num) (abs_nonneg _)
      rw [← sq, ← sq, sq_abs] at this; linarith
    nlinarith [sq_nonneg y]
  have hs : 0 < √(1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hprod : m / 2 * (1 + y ^ 2) ≤ ‖((σ : ℂ) + y * I)‖ * ‖((σ : ℂ) + y * I) + 1‖ := by
    calc m / 2 * (1 + y ^ 2) = (m * √(1 + y ^ 2)) * (1 / 2 * √(1 + y ^ 2)) := by
          rw [show m * √(1 + y ^ 2) * (1 / 2 * √(1 + y ^ 2)) = m / 2 * (√(1 + y ^ 2)) ^ 2 by ring,
            Real.sq_sqrt (by positivity)]
      _ ≤ _ := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  have hpos : 0 < m / 2 * (1 + y ^ 2) := by positivity
  rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hprod) (by positivity)]
  calc 1 * (1 + y ^ 2) = 2 / m * (m / 2 * (1 + y ^ 2)) := by field_simp
    _ ≤ 2 / m * (‖((σ : ℂ) + y * I)‖ * ‖((σ : ℂ) + y * I) + 1‖) := by gcongr

theorem continuous_KK_line {σ : ℝ} (hσ0 : σ ≠ 0) (hσ1 : σ + 1 ≠ 0) :
    Continuous (fun y : ℝ => KK (σ + y * I)) := by
  unfold KK
  refine continuous_const.div (by fun_prop) (fun y => ?_)
  refine mul_ne_zero (fun h => hσ0 ?_) (fun h => hσ1 ?_)
  · have := congrArg Complex.re h; simpa using this
  · have := congrArg Complex.re h; simpa using this

theorem integrable_KK_line {σ m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hσ : m ≤ |σ|)
    (hσ1 : 1 / 2 ≤ |σ + 1|) : Integrable (fun y : ℝ => KK (σ + y * I)) := by
  have hσ0 : σ ≠ 0 := fun h => by rw [h, abs_zero] at hσ; linarith
  have hσ1' : σ + 1 ≠ 0 := fun h => by rw [h, abs_zero] at hσ1; linarith
  refine ((integrable_inv_one_add_sq).const_mul (2 / m)).mono'
    (continuous_KK_line hσ0 hσ1').aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [← div_eq_mul_inv]
  exact norm_KK_le hm hm1 hσ hσ1 y

/-- **Perron (inversão de Mellin)**: `k(x) = (1/2π) ∫ x^(−(1+iy)) K(1+iy) dy`. -/
theorem perron_kk {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, (x : ℂ) ^ (-(1 + y * I)) * KK (1 + y * I) = kk x := by
  have hinv := mellinInv_mellin_eq (σ := 1) (f := fun u => ((kk u : ℝ) : ℂ)) hx
    (mellinConvergent_kk (by simp)) ?_ (continuous_ofReal.comp continuous_kk).continuousAt
  · unfold mellinInv at hinv
    rw [Complex.real_smul] at hinv
    rw [← hinv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [ofReal_one, smul_eq_mul]
    rw [mellin_kk (by simp)]
  · show Integrable (fun y : ℝ => mellin (fun u => ((kk u : ℝ) : ℂ)) ((1 : ℝ) + y * I))
    refine (integrable_KK_line (σ := 1) (m := 1) one_pos le_rfl (by norm_num)
      (by norm_num)).congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [mellin_kk (by simp)]

/-- `∫ K(1 + iy) dy = 0` (`k(1) = 0`). -/
theorem integral_KK_um : ∫ y : ℝ, KK (1 + y * I) = 0 := by
  have h := perron_kk (x := 1) one_pos
  rw [kk_of_one_le le_rfl] at h
  simp only [ofReal_one, one_cpow, one_mul, ofReal_zero] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exfalso
    have : (1 / (2 * π) : ℝ) ≠ 0 := by positivity
    exact this (by exact_mod_cast h')
  · exact h'

/-- `∫ K(−θ + iy) dy = −2π` para `0 < θ ≤ 1/2` (`k(1) − 1 = −1`). -/
theorem integral_KK_neg {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 2) :
    ∫ y : ℝ, KK (-θ + y * I) = -(2 * π) := by
  have hre1 : -1 < ((-θ : ℝ) : ℂ).re := by simp; linarith
  have hre2 : ((-θ : ℝ) : ℂ).re < 0 := by simp; linarith
  have hinv := mellinInv_mellin_eq (σ := -θ) (f := fun u => ((kk u - 1 : ℝ) : ℂ)) one_pos
    (mellinConvergent_kk_sub hre1 hre2) ?_
    ((continuous_ofReal.comp (continuous_kk.sub continuous_const)).continuousAt)
  · unfold mellinInv at hinv
    rw [Complex.real_smul, kk_of_one_le le_rfl] at hinv
    have hint : (∫ y : ℝ, ((1 : ℝ) : ℂ) ^ (-(((-θ : ℝ) : ℂ) + y * I)) •
        mellin (fun u => ((kk u - 1 : ℝ) : ℂ)) (((-θ : ℝ) : ℂ) + y * I)) =
        ∫ y : ℝ, KK (-θ + y * I) := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [ofReal_one, one_cpow, one_smul]
      rw [mellin_kk_sub (by simp; linarith) (by simp; linarith)]
      push_cast; ring_nf
    rw [hint] at hinv
    have h2pi : ((1 / (2 * π) : ℝ) : ℂ) ≠ 0 := by
      have : (1 / (2 * π) : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have : ∫ y : ℝ, KK (-θ + y * I) = ((0 - 1 : ℝ) : ℂ) / ((1 / (2 * π) : ℝ) : ℂ) := by
      rw [eq_div_iff h2pi, mul_comm]; exact hinv
    rw [this]
    push_cast
    field_simp
    all_goals norm_num
  · show Integrable (fun y : ℝ => mellin (fun u => ((kk u - 1 : ℝ) : ℂ)) (((-θ : ℝ) : ℂ) + y * I))
    refine (integrable_KK_line (σ := -θ) (m := θ) hθ (by linarith)
      (by rw [abs_neg, abs_of_pos hθ]) (by rw [abs_of_pos (by linarith)]; linarith)).congr
      (Eventually.of_forall fun y => ?_)
    simp only
    rw [mellin_kk_sub (by simp; linarith) (by simp; linarith)]

/-! ## A soma suavizada como integral na reta `Re = 1` -/

/-- Soma suavizada `A_N(w) = Σ_{n ≤ N} μ(n) k(n/N) n^(−w)`. -/
noncomputable def AN (N : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (ArithmeticFunction.moebius (n + 1) : ℂ) * (kk ((n + 1 : ℝ) / N) : ℂ) *
    ((n + 1 : ℕ) : ℂ) ^ (-w)

/-- `Σ μ(n+1)/(n+1)^z = 1/ζ(z)` para `Re z > 1`. -/
theorem hasSum_moebius {z : ℂ} (hz : 1 < z.re) :
    HasSum (fun n : ℕ => LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) z (n + 1))
      (riemannZeta z)⁻¹ := by
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) z :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hz
  have hL : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) z = (riemannZeta z)⁻¹ := by
    have := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hz
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz] at this
    exact eq_inv_of_mul_eq_one_right this
  have h1 := (hasSum_nat_add_iff' 1).mpr hsum.LSeriesHasSum
  simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero, hL] at h1
  exact h1

theorem cpow_quociente {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℂ) :
    ((a / b : ℝ) : ℂ) ^ u = (a : ℂ) ^ u * ((b : ℂ) ^ u)⁻¹ := by
  rw [div_eq_mul_inv, ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hb.le),
    ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hb.le]; exact
      Real.pi_ne_zero.symm)]

/-- O integrando de Perron em `x > 0`. -/
theorem integrable_perron {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => (x : ℂ) ^ (-(1 + y * I)) * KK (1 + y * I)) := by
  have hK := integrable_KK_line (σ := 1) (m := 1) one_pos le_rfl (by norm_num) (by norm_num)
  have hK' : Integrable (fun y : ℝ => KK (1 + y * I)) := by simpa using hK
  refine (hK'.norm.const_mul x⁻¹).mono' ?_ (Eventually.of_forall fun y => ?_)
  · refine (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
    · have := continuous_KK_line (σ := 1) one_ne_zero (by norm_num)
      simpa using this
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [neg_re, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, Real.rpow_neg_one]
    exact le_rfl

/-- O termo `n` da soma, como integral na reta `Re = 1`. -/
theorem integral_termo {N : ℕ} (hN : 0 < N) (n : ℕ) (w : ℂ) :
    ∫ y : ℝ, (N : ℂ) ^ (1 + y * I) *
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (w + (1 + y * I)) (n + 1) *
      KK (1 + y * I) =
    ((2 * π : ℝ) : ℂ) * ((ArithmeticFunction.moebius (n + 1) : ℂ) * (kk ((n + 1 : ℝ) / N) : ℂ) *
      ((n + 1 : ℕ) : ℂ) ^ (-w)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (0 : ℝ) < (n + 1 : ℝ) / N := by positivity
  have hP := perron_kk hx
  have hn0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpt : ∀ y : ℝ, (N : ℂ) ^ (1 + y * I) *
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (w + (1 + y * I)) (n + 1) *
      KK (1 + y * I) = ((ArithmeticFunction.moebius (n + 1) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-w)) *
      ((((n + 1 : ℝ) / N : ℝ) : ℂ) ^ (-(1 + y * I)) * KK (1 + y * I)) := by
    intro y
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), cpow_quociente (by positivity) hNr]
    have e1 : ((n + 1 : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have e2 : ((N : ℝ) : ℂ) = (N : ℂ) := by norm_cast
    rw [e1, e2, Complex.cpow_add _ _ hn0, Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_neg,
      inv_inv]
    have h1 : ((n + 1 : ℕ) : ℂ) ^ w ≠ 0 := fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have h2 : ((n + 1 : ℕ) : ℂ) ^ (1 + y * I) ≠ 0 :=
      fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    field_simp
  rw [integral_congr_ae (Eventually.of_forall hpt), MeasureTheory.integral_const_mul]
  have h2pi : ((2 * π : ℝ) : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul]; field_simp; simp
  have hI : ∫ y : ℝ, (((n + 1 : ℝ) / N : ℝ) : ℂ) ^ (-(1 + y * I)) * KK (1 + y * I) =
      ((2 * π : ℝ) : ℂ) * (kk ((n + 1 : ℝ) / N) : ℂ) := by
    rw [← hP, ← mul_assoc, h2pi, one_mul]
  rw [hI]
  ring

/-- **Perron para a soma suavizada**: para `Re w > 0`,
`A_N(w) = (1/2π) ∫ N^(1+iy) ζ(w+1+iy)⁻¹ K(1+iy) dy`. -/
theorem AN_eq_integral {N : ℕ} (hN : 0 < N) {w : ℂ} (hw : 0 < w.re) :
    AN N w = ((1 / (2 * π) : ℝ) : ℂ) *
      ∫ y : ℝ, (N : ℂ) ^ (1 + y * I) * (riemannZeta (w + (1 + y * I)))⁻¹ * KK (1 + y * I) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : ℕ → ℝ → ℂ := fun n y => (N : ℂ) ^ (1 + y * I) *
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (w + (1 + y * I)) (n + 1) *
      KK (1 + y * I) with hgdef
  have hK := integrable_KK_line (σ := 1) (m := 1) one_pos le_rfl (by norm_num) (by norm_num)
  have hK' : Integrable (fun y : ℝ => KK (1 + y * I)) := by simpa using hK
  have hnorm : ∀ n y, ‖g n y‖ ≤ N * ((n + 1 : ℝ) ^ (w.re + 1))⁻¹ * ‖KK (1 + y * I)‖ := by
    intro n y
    simp only [hgdef, norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos hN, LSeries.norm_term_eq]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, add_re, one_re, mul_re, ofReal_re, I_re,
      mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, Real.rpow_one]
    have hmu : ‖(ArithmeticFunction.moebius (n + 1) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ (w.re + 1) := by positivity
    push_cast
    rw [div_eq_mul_inv]
    gcongr
    calc ‖(ArithmeticFunction.moebius (n + 1) : ℂ)‖ * (((n : ℝ) + 1) ^ (w.re + 1))⁻¹
        ≤ 1 * (((n : ℝ) + 1) ^ (w.re + 1))⁻¹ := by gcongr
      _ = _ := one_mul _
  have hint : ∀ n, Integrable (g n) := by
    intro n
    have hx : (0 : ℝ) < (n + 1 : ℝ) / N := by positivity
    have hn0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    refine ((integrable_perron hx).const_mul ((ArithmeticFunction.moebius (n + 1) : ℂ) *
      ((n + 1 : ℕ) : ℂ) ^ (-w))).congr (Eventually.of_forall fun y => ?_)
    simp only [hgdef]
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), cpow_quociente (by positivity) hNr]
    have e1 : ((n + 1 : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have e2 : ((N : ℝ) : ℂ) = (N : ℂ) := by norm_cast
    rw [e1, e2, Complex.cpow_add _ _ hn0, Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_neg,
      inv_inv]
    have h1 : ((n + 1 : ℕ) : ℂ) ^ w ≠ 0 := fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have h2 : ((n + 1 : ℕ) : ℂ) ^ (1 + y * I) ≠ 0 :=
      fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    field_simp
  have hsumm : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (w.re + 1))⁻¹) := by
    have := (Real.summable_nat_rpow_inv (p := w.re + 1)).mpr (by linarith)
    have h2 := (summable_nat_add_iff 1).mpr this
    simpa using h2
  have hsum : Summable (fun n => ∫ y, ‖g n y‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _)
      (fun n => ?_) ((hsumm.mul_left (N * ∫ y : ℝ, ‖KK (1 + y * I)‖)))
    calc ∫ y, ‖g n y‖ ≤ ∫ y : ℝ, N * ((n + 1 : ℝ) ^ (w.re + 1))⁻¹ * ‖KK (1 + y * I)‖ :=
          MeasureTheory.integral_mono (hint n).norm (hK'.norm.const_mul _) (hnorm n)
      _ = N * (∫ y : ℝ, ‖KK (1 + y * I)‖) * ((n + 1 : ℝ) ^ (w.re + 1))⁻¹ := by
          rw [MeasureTheory.integral_const_mul]; ring
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hpt : ∀ y : ℝ, ∑' n, g n y =
      (N : ℂ) ^ (1 + y * I) * (riemannZeta (w + (1 + y * I)))⁻¹ * KK (1 + y * I) := by
    intro y
    have hre : 1 < (w + (1 + y * I)).re := by simp; linarith
    simp only [hgdef]
    rw [tsum_mul_right, tsum_mul_left, (hasSum_moebius hre).tsum_eq]
  have hfin : ∑' n, ∫ y, g n y = ((2 * π : ℝ) : ℂ) * AN N w := by
    simp only [hgdef]
    simp_rw [integral_termo hN]
    rw [tsum_mul_left, AN]
    congr 1
    refine tsum_eq_sum (fun n hn => ?_)
    rw [Finset.mem_range, not_lt] at hn
    have h1 : 1 ≤ (n + 1 : ℝ) / N := by
      rw [le_div_iff₀ hNr, one_mul]; exact_mod_cast (Nat.le_succ_of_le hn)
    rw [kk_of_one_le h1]
    simp
  rw [← funext hpt, ← hswap, hfin, ← mul_assoc, ← ofReal_mul]
  have : 1 / (2 * π) * (2 * π) = 1 := by field_simp
  rw [this, ofReal_one, one_mul]

/-! ## Deslocamento até `Re = −ε/2` e a cota do erro (sob RH) -/

open ATK.RHLogZeta

/-- `φ(z) = N^z F(w + z)` (`F = 1/ζ` fora de `1`). -/
noncomputable def phi (N : ℕ) (w z : ℂ) : ℂ := (N : ℂ) ^ z * F (w + z)

/-- A parte holomorfa `H(z) = (φ(z) − φ(0))/(z(z+1))`, com a singularidade em `0` removida. -/
noncomputable def H1 (N : ℕ) (w z : ℂ) : ℂ := dslope (phi N w) 0 z / (z + 1)

theorem phi_zero (N : ℕ) (w : ℂ) : phi N w 0 = F w := by simp [phi]

theorem H1_eq {N : ℕ} {w z : ℂ} (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    H1 N w z = phi N w z * KK z - F w * KK z := by
  rw [H1, dslope_of_ne _ hz, slope_def_field, phi_zero, KK]
  field_simp
  ring

theorem differentiableAt_phi (hRH : RiemannHypothesis) {N : ℕ} (hN : 0 < N) {w z : ℂ}
    (hz : 1 / 2 < (w + z).re) : DifferentiableAt ℂ (phi N w) z := by
  unfold phi
  refine DifferentiableAt.mul ?_ ?_
  · exact differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))
  · exact (differentiableAt_F hRH hz).comp z ((differentiableAt_const w).add differentiableAt_id)

theorem differentiableAt_H1 (hRH : RiemannHypothesis) {N : ℕ} (hN : 0 < N) {w z : ℂ}
    (hw : 1 / 2 < w.re) (hz : 1 / 2 < (w + z).re) (hz1 : z + 1 ≠ 0) :
    DifferentiableAt ℂ (H1 N w) z := by
  set U : Set ℂ := {u | 1 / 2 < (w + u).re} with hU
  have hUo : IsOpen U :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.add continuous_id))
  have hd : DifferentiableOn ℂ (phi N w) U :=
    fun u hu => (differentiableAt_phi hRH hN hu).differentiableWithinAt
  have h0 : U ∈ 𝓝 (0 : ℂ) := hUo.mem_nhds (by simp [hU]; linarith)
  have hds := (differentiableOn_dslope h0).mpr hd
  exact ((hds z hz).differentiableAt (hUo.mem_nhds hz)).div
    (differentiableAt_id.add_const 1) hz1

theorem norm_phi_le {N : ℕ} (hN : 0 < N) {w : ℂ} {ε CF η : ℝ}
    (hF : ∀ s : ℂ, 1 / 2 + ε / 2 ≤ s.re → ‖F s‖ ≤ CF * (1 + |s.im|) ^ η) (hη : 0 ≤ η)
    (hCF : 0 ≤ CF) {z : ℂ} (hz : 1 / 2 + ε / 2 ≤ (w + z).re) :
    ‖phi N w z‖ ≤ (N : ℝ) ^ z.re * ((CF * (1 + |w.im|) ^ η) * (1 + |z.im|) ^ η) := by
  have h1 : ‖F (w + z)‖ ≤ CF * (1 + |w.im|) ^ η * (1 + |z.im|) ^ η := by
    refine (hF _ hz).trans ?_
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity)]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hη) hCF
    rw [add_im]
    have := abs_add_le w.im z.im
    nlinarith [abs_nonneg w.im, abs_nonneg z.im]
  unfold phi
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem peso_le {η : ℝ} (y : ℝ) : (1 + |y|) ^ η / (1 + y ^ 2) ≤ 2 * (1 + |y|) ^ (-(2 - η)) := by
  have h1 : 0 < 1 + |y| := by positivity
  have h2 : (1 + |y|) ^ (-(2 - η)) = (1 + |y|) ^ η / (1 + |y|) ^ 2 := by
    rw [show -(2 - η) = η - 2 by ring, Real.rpow_sub h1, Real.rpow_two]
  have h3 : (1 + |y|) ^ 2 ≤ 2 * (1 + y ^ 2) := by
    nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
  have h4 : 0 ≤ (1 + |y|) ^ η := by positivity
  rw [h2]
  have h5 : 1 / (1 + y ^ 2) ≤ 2 / (1 + |y|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  calc (1 + |y|) ^ η / (1 + y ^ 2) = (1 + |y|) ^ η * (1 / (1 + y ^ 2)) := by ring
    _ ≤ (1 + |y|) ^ η * (2 / (1 + |y|) ^ 2) := mul_le_mul_of_nonneg_left h5 h4
    _ = 2 * ((1 + |y|) ^ η / (1 + |y|) ^ 2) := by ring

theorem re_linha (σ y : ℝ) : ((σ : ℂ) + y * I).re = σ := by simp

theorem im_linha (σ y : ℝ) : ((σ : ℂ) + y * I).im = y := by simp

/-- Cota do integrando `φ K` numa reta vertical. -/
theorem norm_linha_le {N : ℕ} (hN : 0 < N) {w : ℂ} {ε CF η : ℝ}
    (hF : ∀ s : ℂ, 1 / 2 + ε / 2 ≤ s.re → ‖F s‖ ≤ CF * (1 + |s.im|) ^ η) (hη : 0 ≤ η)
    (hCF : 0 ≤ CF) {σ m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hσ : m ≤ |σ|) (hσ1 : 1 / 2 ≤ |σ + 1|)
    (hσw : 1 / 2 + ε / 2 ≤ w.re + σ) (y : ℝ) :
    ‖phi N w (σ + y * I) * KK (σ + y * I)‖ ≤
      (N : ℝ) ^ σ * (CF * (1 + |w.im|) ^ η) * (4 / m) * (1 + |y|) ^ (-(2 - η)) := by
  rw [norm_mul]
  have h1 := norm_phi_le hN hF hη hCF (w := w) (z := σ + y * I) (by rw [add_re, re_linha]; exact hσw)
  rw [re_linha, im_linha] at h1
  have h2 := norm_KK_le hm hm1 hσ hσ1 y
  have h3 := peso_le (η := η) y
  have hA : 0 ≤ (N : ℝ) ^ σ * (CF * (1 + |w.im|) ^ η) * (2 / m) := by positivity
  calc ‖phi N w (σ + y * I)‖ * ‖KK (σ + y * I)‖
      ≤ ((N : ℝ) ^ σ * ((CF * (1 + |w.im|) ^ η) * (1 + |y|) ^ η)) * (2 / m / (1 + y ^ 2)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (N : ℝ) ^ σ * (CF * (1 + |w.im|) ^ η) * (2 / m) * ((1 + |y|) ^ η / (1 + y ^ 2)) := by
        ring
    _ ≤ (N : ℝ) ^ σ * (CF * (1 + |w.im|) ^ η) * (2 / m) * (2 * (1 + |y|) ^ (-(2 - η))) :=
        mul_le_mul_of_nonneg_left h3 hA
    _ = _ := by ring

theorem integrable_peso {η : ℝ} (hη1 : η < 1) :
    Integrable (fun y : ℝ => (1 + |y|) ^ (-(2 - η))) := by
  have hI := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2 - η) (by simp; linarith)
  simpa only [Real.norm_eq_abs] using hI

theorem continuous_phi_linha (hRH : RiemannHypothesis) {N : ℕ} (hN : 0 < N) {w : ℂ} {σ : ℝ}
    (hσw : 1 / 2 < w.re + σ) : Continuous (fun y : ℝ => phi N w (σ + y * I)) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hd := differentiableAt_phi hRH hN (w := w) (z := σ + y * I) (by rw [add_re, re_linha]; exact hσw)
  exact ContinuousAt.comp (g := phi N w) (f := fun y : ℝ => (σ : ℂ) + y * I) hd.continuousAt
    (by fun_prop)

theorem integrable_linha (hRH : RiemannHypothesis) {N : ℕ} (hN : 0 < N) {w : ℂ} {ε CF η : ℝ}
    (hε : 0 < ε) (hF : ∀ s : ℂ, 1 / 2 + ε / 2 ≤ s.re → ‖F s‖ ≤ CF * (1 + |s.im|) ^ η)
    (hη : 0 ≤ η) (hη1 : η < 1) (hCF : 0 ≤ CF) {σ m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hσ : m ≤ |σ|) (hσ1 : 1 / 2 ≤ |σ + 1|) (hσw : 1 / 2 + ε / 2 ≤ w.re + σ) :
    Integrable (fun y : ℝ => phi N w (σ + y * I) * KK (σ + y * I)) := by
  have hσ0 : σ ≠ 0 := fun h => by rw [h, abs_zero] at hσ; linarith
  have hσ1' : σ + 1 ≠ 0 := fun h => by rw [h, abs_zero] at hσ1; linarith
  refine ((integrable_peso hη1).const_mul
    ((N : ℝ) ^ σ * (CF * (1 + |w.im|) ^ η) * (4 / m))).mono' ?_
    (Eventually.of_forall fun y => norm_linha_le hN hF hη hCF hm hm1 hσ hσ1 hσw y)
  exact ((continuous_phi_linha hRH hN (by linarith)).mul
    (continuous_KK_line hσ0 hσ1')).aestronglyMeasurable

/-- Cota de `H` nos segmentos horizontais. -/
theorem norm_H1_le {N : ℕ} (hN : 0 < N) {w : ℂ} {ε CF η : ℝ}
    (hF : ∀ s : ℂ, 1 / 2 + ε / 2 ≤ s.re → ‖F s‖ ≤ CF * (1 + |s.im|) ^ η) (hη : 0 ≤ η)
    (hη1 : η ≤ 1) (hCF : 0 ≤ CF) {x t : ℝ} (hx1 : x ≤ 1) (hxw : 1 / 2 + ε / 2 ≤ w.re + x)
    (ht : 1 ≤ |t|) :
    ‖H1 N w (x + t * I)‖ ≤ (2 * N * (CF * (1 + |w.im|) ^ η) + ‖F w‖) / |t| := by
  set z : ℂ := x + t * I with hzdef
  have hzim : z.im = t := im_linha x t
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at hzim; rw [← hzim, abs_zero] at ht; linarith
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    rw [add_im, hzim, one_im, add_zero, zero_im] at this
    rw [this, abs_zero] at ht; linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 < |t| := by linarith
  set A := CF * (1 + |w.im|) ^ η with hA
  have hA0 : 0 ≤ A := by positivity
  set K := 2 * N * A + ‖F w‖ with hK
  have hK0 : 0 ≤ K := by positivity
  have hphi := norm_phi_le hN hF hη hCF (w := w) (z := z) (by rw [add_re, re_linha]; exact hxw)
  rw [re_linha, hzim] at hphi
  have hNx : (N : ℝ) ^ x ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hNr hx1
    rwa [Real.rpow_one] at this
  have hTη : (1 + |t|) ^ η ≤ 1 + |t| := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t] : (1 : ℝ) ≤ 1 + |t|) hη1
    rwa [Real.rpow_one] at this
  have hP : ‖phi N w z - F w‖ ≤ K * |t| := by
    calc ‖phi N w z - F w‖ ≤ ‖phi N w z‖ + ‖F w‖ := norm_sub_le _ _
      _ ≤ (N : ℝ) * (A * (1 + |t|)) + ‖F w‖ := by
          gcongr
          refine hphi.trans ?_
          exact mul_le_mul hNx (mul_le_mul_of_nonneg_left hTη hA0) (by positivity) (by positivity)
      _ ≤ K * |t| := by
          rw [hK]
          have := norm_nonneg (F w)
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ N) hA0) (by linarith : (0 : ℝ) ≤ |t| - 1)]
  have hd : |t| * |t| ≤ ‖z‖ * ‖z + 1‖ := by
    have h1 : |t| ≤ ‖z‖ := by rw [← hzim]; exact Complex.abs_im_le_norm z
    have h2 : |t| ≤ ‖z + 1‖ := by
      have := Complex.abs_im_le_norm (z + 1)
      rwa [add_im, hzim, one_im, add_zero] at this
    exact mul_le_mul h1 h2 ht0.le (norm_nonneg _)
  rw [H1_eq hz0 hz1, ← sub_mul, norm_mul, norm_KK, mul_one_div,
    div_le_div_iff₀ (by nlinarith) ht0]
  nlinarith [mul_le_mul_of_nonneg_right hP ht0.le, mul_le_mul_of_nonneg_left hd hK0]

/-- **Deslocamento de contorno**: sob RH, para `Re w = 1/2 + ε` (`0 < ε ≤ 1/4`),
`A_N(w) = 1/ζ(w) + (1/2π) ∫ φ(−ε/2 + iy) K(−ε/2 + iy) dy` (aqui com `F(w) = 1/ζ(w)`). -/
theorem desloca_AN (hRH : RiemannHypothesis) {N : ℕ} (hN : 0 < N) {ε CF η : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 4) (hη : 0 ≤ η) (hη1 : η < 1) (hCF : 0 ≤ CF)
    (hF : ∀ s : ℂ, 1 / 2 + ε / 2 ≤ s.re → ‖F s‖ ≤ CF * (1 + |s.im|) ^ η) {w : ℂ}
    (hw : w.re = 1 / 2 + ε) :
    AN N w = F w + ((1 / (2 * π) : ℝ) : ℂ) *
      ∫ y : ℝ, phi N w ((-(ε / 2) : ℝ) + y * I) * KK ((-(ε / 2) : ℝ) + y * I) := by
  set θ := ε / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by linarith
  -- as duas retas
  have hl1 : Integrable (fun y : ℝ => phi N w ((1 : ℝ) + y * I) * KK ((1 : ℝ) + y * I)) :=
    integrable_linha hRH hN hε hF hη hη1 hCF (σ := 1) (m := 1) one_pos le_rfl (by norm_num)
      (by norm_num) (by rw [hw]; linarith)
  have hl2 : Integrable (fun y : ℝ => phi N w ((-θ : ℝ) + y * I) * KK ((-θ : ℝ) + y * I)) :=
    integrable_linha hRH hN hε hF hη hη1 hCF (σ := -θ) (m := θ) hθ0 (by linarith)
      (by rw [abs_neg, abs_of_pos hθ0]) (by rw [abs_of_pos (by linarith)]; linarith)
      (by rw [hw]; linarith)
  have hK1 : Integrable (fun y : ℝ => KK ((1 : ℝ) + y * I)) :=
    integrable_KK_line (σ := 1) (m := 1) one_pos le_rfl (by norm_num) (by norm_num)
  have hK2 : Integrable (fun y : ℝ => KK ((-θ : ℝ) + y * I)) :=
    integrable_KK_line (σ := -θ) (m := θ) hθ0 (by linarith) (by rw [abs_neg, abs_of_pos hθ0])
      (by rw [abs_of_pos (by linarith)]; linarith)
  have hHeq : ∀ σ : ℝ, σ ≠ 0 → σ + 1 ≠ 0 → ∀ y : ℝ, H1 N w (σ + y * I) =
      phi N w (σ + y * I) * KK (σ + y * I) - F w * KK (σ + y * I) := by
    intro σ hσ hσ1 y
    refine H1_eq (fun h => hσ ?_) (fun h => hσ1 ?_)
    · have := congrArg Complex.re h; rwa [re_linha, zero_re] at this
    · have := congrArg Complex.re h; rwa [add_re, re_linha, one_re, zero_re] at this
  have hθne : -θ ≠ 0 := by linarith
  have hθne1 : -θ + 1 ≠ 0 := by linarith
  have hH1int : Integrable (fun y : ℝ => H1 N w ((1 : ℝ) + y * I)) :=
    (hl1.sub (hK1.const_mul (F w))).congr
      (Eventually.of_forall fun y => (hHeq 1 one_ne_zero (by norm_num) y).symm)
  have hH2int : Integrable (fun y : ℝ => H1 N w ((-θ : ℝ) + y * I)) :=
    (hl2.sub (hK2.const_mul (F w))).congr
      (Eventually.of_forall fun y => (hHeq (-θ) hθne hθne1 y).symm)
  -- o deslocamento
  have hshift := desloca (f := H1 N w) (a := -θ) (b := 1) (by linarith) (s := ∅) countable_empty
    (fun z hz => by
      have hz' : z.re ∈ Icc (-θ) 1 := hz
      refine (differentiableAt_H1 hRH hN (by rw [hw]; linarith) (by rw [add_re, hw]; linarith [hz'.1])
        (fun h => ?_)).continuousAt.continuousWithinAt
      have := congrArg Complex.re h
      rw [add_re, one_re, zero_re] at this; linarith [hz'.1])
    (fun z hz => by
      have hz' : z.re ∈ Ioo (-θ) 1 := hz.1
      refine differentiableAt_H1 hRH hN (by rw [hw]; linarith) (by rw [add_re, hw]; linarith [hz'.1])
        (fun h => ?_)
      have := congrArg Complex.re h
      rw [add_re, one_re, zero_re] at this; linarith [hz'.1])
    hH2int hH1int ?_
  swap
  · intro η' hη'
    set K := 2 * N * (CF * (1 + |w.im|) ^ η) + ‖F w‖ with hK
    have hK0 : 0 ≤ K := by positivity
    filter_upwards [eventually_ge_atTop (max 1 (K / η'))] with T hT
    have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
    have hTK : K / η' ≤ T := (le_max_right _ _).trans hT
    have hT0 : 0 < T := by linarith
    have hfin : K / T ≤ η' := by
      rw [div_le_iff₀ hT0]; rw [div_le_iff₀ hη'] at hTK; linarith
    intro x hx
    have hxw : 1 / 2 + ε / 2 ≤ w.re + x := by rw [hw]; linarith [hx.1]
    constructor
    · have := norm_H1_le hN hF hη hη1.le hCF hx.2 hxw (t := T) (by rw [abs_of_pos hT0]; exact hT1)
      rw [abs_of_pos hT0] at this
      exact this.trans hfin
    · have := norm_H1_le hN hF hη hη1.le hCF hx.2 hxw (t := -T)
        (by rw [abs_neg, abs_of_pos hT0]; exact hT1)
      rw [abs_neg, abs_of_pos hT0] at this
      exact this.trans hfin
  -- as integrais de `H` nas duas retas
  have hI1 : ∫ y : ℝ, H1 N w ((1 : ℝ) + y * I) =
      ∫ y : ℝ, phi N w ((1 : ℝ) + y * I) * KK ((1 : ℝ) + y * I) := by
    rw [integral_congr_ae (Eventually.of_forall (hHeq 1 one_ne_zero (by norm_num))),
      MeasureTheory.integral_sub hl1 (hK1.const_mul _), MeasureTheory.integral_const_mul]
    have : ∫ y : ℝ, KK ((1 : ℝ) + y * I) = 0 := by simpa using integral_KK_um
    rw [this, mul_zero, sub_zero]
  have hI2 : ∫ y : ℝ, H1 N w ((-θ : ℝ) + y * I) =
      (∫ y : ℝ, phi N w ((-θ : ℝ) + y * I) * KK ((-θ : ℝ) + y * I)) + 2 * π * F w := by
    rw [integral_congr_ae (Eventually.of_forall (hHeq (-θ) hθne hθne1)),
      MeasureTheory.integral_sub hl2 (hK2.const_mul _), MeasureTheory.integral_const_mul]
    have : ∫ y : ℝ, KK ((-θ : ℝ) + y * I) = -(2 * π) := by
      simpa only [ofReal_neg] using integral_KK_neg hθ0 hθ1
    rw [this]; ring
  -- a reta `Re = 1`
  have hAN := AN_eq_integral hN (w := w) (by rw [hw]; linarith)
  have hline : ∫ y : ℝ, (N : ℂ) ^ (1 + y * I) * (riemannZeta (w + (1 + y * I)))⁻¹ * KK (1 + y * I) =
      ∫ y : ℝ, phi N w ((1 : ℝ) + y * I) * KK ((1 : ℝ) + y * I) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hne : w + (1 + y * I) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, hw] at this
      linarith
    simp only [phi, ofReal_one]
    rw [F_eq hne]
  rw [hAN, hline, ← hI1, ← hshift, hI2, mul_add]
  have h2pi : ((1 / (2 * π) : ℝ) : ℂ) * (2 * π * F w) = F w := by
    push_cast; field_simp
  rw [h2pi, add_comm]

/-- **Erro da soma suavizada (sob RH)**: para `0 < ε ≤ 1/4` e `0 < η < 1` existe `C` com
`‖A_N(w) − 1/ζ(w)‖ ≤ C N^(−ε/2) (1 + |Im w|)^η` em toda a reta `Re w = 1/2 + ε`, para todo
`N ≥ 1`. -/
theorem norm_AN_sub_le (hRH : RiemannHypothesis) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hη : 0 < η) (hη1 : η < 1) :
    ∃ C, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ w : ℂ, w.re = 1 / 2 + ε →
      ‖AN N w - (riemannZeta w)⁻¹‖ ≤ C * (N : ℝ) ^ (-(ε / 2)) * (1 + |w.im|) ^ η := by
  obtain ⟨CF, hCF, hF⟩ := norm_F_le hRH (δ := ε / 2) (η := η) (by linarith) (by linarith) hη
  set Iη := ∫ y : ℝ, (1 + |y|) ^ (-(2 - η)) with hIη
  have hIη0 : 0 ≤ Iη := integral_nonneg fun y => by positivity
  set C := 1 / (2 * π) * CF * (4 / (ε / 2)) * Iη + 1 with hC
  refine ⟨C, by positivity, fun N hN w hw => ?_⟩
  have hw1 : w ≠ 1 := by
    intro h; rw [h, one_re] at hw; linarith
  have hθ0 : 0 < ε / 2 := by positivity
  rw [← F_eq hw1, desloca_AN hRH hN hε hε1 hη.le hη1 hCF.le hF hw, add_sub_cancel_left, norm_mul]
  have hc : ‖((1 / (2 * π) : ℝ) : ℂ)‖ = 1 / (2 * π) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hc]
  set A := CF * (1 + |w.im|) ^ η with hA
  have hbound := norm_linha_le hN hF hη.le hCF.le (w := w) (σ := -(ε / 2)) (m := ε / 2) hθ0
    (by linarith) (by rw [abs_neg, abs_of_pos hθ0]) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [hw]; linarith)
  have hint := ((integrable_peso hη1).const_mul ((N : ℝ) ^ (-(ε / 2)) * A * (4 / (ε / 2))))
  have hle := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [MeasureTheory.integral_const_mul] at hle
  have hA0 : 0 ≤ A := by positivity
  have hN0 : 0 ≤ (N : ℝ) ^ (-(ε / 2)) := by positivity
  have hW : 0 ≤ (1 + |w.im|) ^ η := by positivity
  calc 1 / (2 * π) * ‖∫ y : ℝ, phi N w ((-(ε / 2) : ℝ) + y * I) * KK ((-(ε / 2) : ℝ) + y * I)‖
      ≤ 1 / (2 * π) * ((N : ℝ) ^ (-(ε / 2)) * A * (4 / (ε / 2)) * Iη) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (1 / (2 * π) * CF * (4 / (ε / 2)) * Iη) * (N : ℝ) ^ (-(ε / 2)) * (1 + |w.im|) ^ η := by
        rw [hA]; ring
    _ ≤ C * (N : ℝ) ^ (-(ε / 2)) * (1 + |w.im|) ^ η := by
        gcongr
        rw [hC]; linarith

end ATK.PerronSuave

#print axioms ATK.PerronSuave.desloca
#print axioms ATK.PerronSuave.continuous_kk
#print axioms ATK.PerronSuave.kk_of_le_one
#print axioms ATK.PerronSuave.kk_of_one_le
#print axioms ATK.PerronSuave.kk_nonneg
#print axioms ATK.PerronSuave.kk_le_one
#print axioms ATK.PerronSuave.integral_zero_one_cpow
#print axioms ATK.PerronSuave.integrableOn_cpow_Ioc
#print axioms ATK.PerronSuave.cpow_eq_mul_self
#print axioms ATK.PerronSuave.intervalIntegrable_cpow01
#print axioms ATK.PerronSuave.mellin_kk
#print axioms ATK.PerronSuave.mellinConvergent_kk
#print axioms ATK.PerronSuave.mellin_kk_sub
#print axioms ATK.PerronSuave.mellinConvergent_kk_sub
#print axioms ATK.PerronSuave.norm_KK
#print axioms ATK.PerronSuave.sq_norm_line
#print axioms ATK.PerronSuave.le_of_sq_le
#print axioms ATK.PerronSuave.norm_KK_le
#print axioms ATK.PerronSuave.continuous_KK_line
#print axioms ATK.PerronSuave.integrable_KK_line
#print axioms ATK.PerronSuave.perron_kk
#print axioms ATK.PerronSuave.integral_KK_um
#print axioms ATK.PerronSuave.integral_KK_neg
#print axioms ATK.PerronSuave.hasSum_moebius
#print axioms ATK.PerronSuave.cpow_quociente
#print axioms ATK.PerronSuave.integrable_perron
#print axioms ATK.PerronSuave.integral_termo
#print axioms ATK.PerronSuave.AN_eq_integral
#print axioms ATK.PerronSuave.phi_zero
#print axioms ATK.PerronSuave.H1_eq
#print axioms ATK.PerronSuave.differentiableAt_phi
#print axioms ATK.PerronSuave.differentiableAt_H1
#print axioms ATK.PerronSuave.norm_phi_le
#print axioms ATK.PerronSuave.peso_le
#print axioms ATK.PerronSuave.re_linha
#print axioms ATK.PerronSuave.im_linha
#print axioms ATK.PerronSuave.norm_linha_le
#print axioms ATK.PerronSuave.integrable_peso
#print axioms ATK.PerronSuave.continuous_phi_linha
#print axioms ATK.PerronSuave.integrable_linha
#print axioms ATK.PerronSuave.norm_H1_le
#print axioms ATK.PerronSuave.desloca_AN
#print axioms ATK.PerronSuave.norm_AN_sub_le
