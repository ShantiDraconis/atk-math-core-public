import ATK.ZeroClasses.ChebyshevSuave
import Mathlib.NumberTheory.Chebyshev

/-!
# O teorema dos números primos com o erro de de la Vallée Poussin (rodada 54)

**Teorema** (Hadamard, de la Vallée Poussin 1896; erro de de la Vallée Poussin 1899).

  `|ψ(x) − x| ≤ K x e^{−b√log x}`   para `x` grande   (**`psi_tnp`**),

com `ψ = Chebyshev.psi` da Mathlib; em particular `ψ(x)/x → 1` (`tendsto_psi_div`) e `θ(x)/x → 1`
(`tendsto_theta_div`). A Mathlib tem `ψ`, `θ` e as cotas de Chebyshev, mas não o TNP.

A prova tira a suavização da rodada 53 (`chebyshev_suave`): com `ψ₁(y) = y·Ssm(y) = Σ_{n ≤ y} Λ(n)(y − n)`
(`mul_Ssm_eq`), a monotonia de `ψ` dá `h ψ(y) ≤ ψ₁(y + h) − ψ₁(y) ≤ h ψ(y + h)` (`incremento`), e com
`ψ₁(y) = y²/2 + O(y² η²)` em `[x/2, 2x]` e `h = ηx`,

  `x − 2,5 ηx ≤ ψ(x) ≤ x + 5,5 ηx`,   `η = √(2K log x)·e^{−(a/4)√log x}`.

Classificação (rodada 54): **consequência** — o TNP com erro, incondicional; não é RH (RH equivale a
`ψ(x) = x + O(x^{1/2+ε})`, rodada 51 para `M(x)`). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.PNT

open Chebyshev ArithmeticFunction

/-! ## 1. A soma `ψ₁` e o incremento -/

theorem Ssm_ext {y : ℝ} (hy : 0 < y) {N : ℕ} (hN : ⌊y⌋₊ + 1 ≤ N) :
    Ssm y = ∑ n ∈ Finset.range N, vonMangoldt n * ATK.PerronSuave.kk (n / y) := by
  unfold Ssm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun n hn hn' => ?_
  rw [Finset.mem_range, not_lt] at hn'
  have h1 : 1 ≤ (n : ℝ) / y := by
    rw [le_div_iff₀ hy, one_mul]
    have := Nat.lt_floor_add_one y
    have hn2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at hn2
    linarith
  rw [ATK.PerronSuave.kk_of_one_le h1, mul_zero]

theorem mul_kk {y : ℝ} (hy : 0 < y) (n : ℝ) : y * ATK.PerronSuave.kk (n / y) = max (y - n) 0 := by
  unfold ATK.PerronSuave.kk
  rw [mul_max_of_nonneg _ _ hy.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ hy.ne']

/-- `ψ₁(y) = y·Ssm(y) = Σ_{n < N} Λ(n)·max(y − n, 0)`. -/
theorem mul_Ssm_eq {y : ℝ} (hy : 0 < y) {N : ℕ} (hN : ⌊y⌋₊ + 1 ≤ N) :
    y * Ssm y = ∑ n ∈ Finset.range N, vonMangoldt n * max (y - n) 0 := by
  rw [Ssm_ext hy hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← mul_kk hy n]
  ring

theorem psi_eq_range (y : ℝ) {N : ℕ} (hN : N = ⌊y⌋₊ + 1) :
    ψ y = ∑ n ∈ Finset.range N, vonMangoldt n := by
  rw [psi_eq_sum_Icc, hN]
  congr 1
  ext n
  simp

/-- **O incremento**: `h ψ(y) ≤ ψ₁(y + h) − ψ₁(y) ≤ h ψ(y + h)`. -/
theorem incremento {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    h * ψ y ≤ (y + h) * Ssm (y + h) - y * Ssm y ∧
      (y + h) * Ssm (y + h) - y * Ssm y ≤ h * ψ (y + h) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊y + h⌋₊ + 1 := ⟨_, rfl⟩
  have hNy : ⌊y⌋₊ + 1 ≤ N := by
    rw [hN]
    have := Nat.floor_le_floor (show y ≤ y + h by linarith)
    omega
  have hyh : 0 < y + h := by linarith
  rw [mul_Ssm_eq hyh (le_of_eq hN.symm), mul_Ssm_eq hy hNy, ← Finset.sum_sub_distrib]
  have hdiff : ∀ n : ℕ, 0 ≤ max (y + h - n) 0 - max (y - n) 0 ∧ max (y + h - n) 0 - max (y - n) 0 ≤ h := by
    intro n
    constructor
    · have : max (y - n) 0 ≤ max (y + h - n) 0 := max_le_max (by linarith) le_rfl
      linarith
    · rcases le_total (y - n) 0 with h1 | h1
      · rw [max_eq_right h1]
        rcases le_total (y + h - n) 0 with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; linarith
      · rw [max_eq_left h1, max_eq_left (by linarith)]
        linarith
  constructor
  · rw [psi_eq_range y rfl, Finset.mul_sum]
    calc ∑ n ∈ Finset.range (⌊y⌋₊ + 1), h * vonMangoldt n
        = ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
            (vonMangoldt n * max (y + h - n) 0 - vonMangoldt n * max (y - n) 0) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_range] at hn
          have hny : (n : ℝ) ≤ y := by
            have h1 : n ≤ ⌊y⌋₊ := Nat.lt_succ_iff.mp hn
            exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hy.le)
          rw [max_eq_left (by linarith), max_eq_left (by linarith)]
          ring
      _ ≤ ∑ n ∈ Finset.range N,
            (vonMangoldt n * max (y + h - n) 0 - vonMangoldt n * max (y - n) 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNy)
            fun n _ _ => ?_
          rw [← mul_sub]
          exact mul_nonneg vonMangoldt_nonneg (hdiff n).1
  · rw [psi_eq_range (y + h) hN, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← mul_sub, mul_comm h]
    exact mul_le_mul_of_nonneg_left (hdiff n).2 vonMangoldt_nonneg

/-! ## 2. O TNP com erro -/

/-- `t ≤ (1/c) e^{ct}` para `c > 0`. -/
theorem le_exp_mul {t c : ℝ} (hc : 0 < c) : t ≤ 1 / c * Real.exp (c * t) := by
  have h := Real.add_one_le_exp (c * t)
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  nlinarith

/-- **O teorema dos números primos com o erro de de la Vallée Poussin**:
existem `b > 0` e `K` com `|ψ(x) − x| ≤ K x e^{−b√log x}` para `x` grande. -/
theorem psi_tnp : ∃ b > 0, ∃ K : ℝ, ∀ᶠ x in atTop,
    |ψ x - x| ≤ K * x * Real.exp (-(b * Real.sqrt (Real.log x))) := by
  obtain ⟨a, ha, K₀, hK₀, x₀, hx₀, hS⟩ := chebyshev_suave
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = K₀ + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; linarith
  -- a cota em `[x/2, 2x]`
  have hS' : ∀ y : ℝ, x₀ ≤ y → |y * Ssm y - y ^ 2 / 2| ≤
      y ^ 2 * (K * Real.log y * Real.exp (-(a * Real.sqrt (Real.log y)))) := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hy1 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have h := hS y hy
    have e : y * Ssm y - y ^ 2 / 2 = y * (Ssm y - y / 2) := by ring
    rw [e, abs_mul, abs_of_pos hy0]
    have hE := Real.exp_pos (-(a * Real.sqrt (Real.log y)))
    calc y * |Ssm y - y / 2| ≤ y * (K₀ * y * Real.log y * Real.exp (-(a * Real.sqrt (Real.log y)))) :=
          mul_le_mul_of_nonneg_left h hy0.le
      _ ≤ y * (K * y * Real.log y * Real.exp (-(a * Real.sqrt (Real.log y)))) := by
          gcongr
          rw [hK]; linarith
      _ = y ^ 2 * (K * Real.log y * Real.exp (-(a * Real.sqrt (Real.log y)))) := by ring
  -- `η(x) = √(2K log x)·e^{−(a/4)√log x}`
  set η : ℝ → ℝ := fun x => Real.sqrt (2 * K * Real.log x) * Real.exp (-(a / 4 * Real.sqrt (Real.log x)))
    with hη
  have hηB : ∀ x : ℝ, 1 ≤ x → η x ≤ Real.sqrt (2 * K) * (8 / a) *
      Real.exp (-(a / 8 * Real.sqrt (Real.log x))) := by
    intro x hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt (Real.log x) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact Real.sqrt_nonneg _
    simp only [hη]
    rw [← ht, Real.sqrt_mul (by positivity), ← ht]
    have h1 := le_exp_mul (t := t) (c := a / 8) (by positivity)
    have e1 : Real.exp (a / 8 * t) * Real.exp (-(a / 4 * t)) = Real.exp (-(a / 8 * t)) := by
      rw [← Real.exp_add]; ring_nf
    have hs0 : 0 ≤ Real.sqrt (2 * K) := Real.sqrt_nonneg _
    have hE0 : 0 ≤ Real.exp (-(a / 4 * t)) := (Real.exp_pos _).le
    calc Real.sqrt (2 * K) * t * Real.exp (-(a / 4 * t))
        ≤ Real.sqrt (2 * K) * (1 / (a / 8) * Real.exp (a / 8 * t)) * Real.exp (-(a / 4 * t)) := by
          gcongr
      _ = Real.sqrt (2 * K) * (8 / a) * Real.exp (-(a / 8 * t)) := by
          rw [mul_assoc (Real.sqrt (2 * K)), mul_assoc, e1]; field_simp
  have hηsq : ∀ x : ℝ, 1 ≤ x → η x ^ 2 = 2 * K * Real.log x * Real.exp (-(a / 2 * Real.sqrt (Real.log x))) := by
    intro x hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    simp only [hη]
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  -- `η → 0`
  have hlim : Tendsto (fun x : ℝ => Real.sqrt (2 * K) * (8 / a) *
      Real.exp (-(a / 8 * Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
    have h2 : Tendsto (fun x : ℝ => a / 8 * Real.sqrt (Real.log x)) atTop atTop :=
      h1.const_mul_atTop (by positivity)
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h2).const_mul (Real.sqrt (2 * K) * (8 / a))
    rw [mul_zero] at h3
    exact h3
  refine ⟨a / 8, by positivity, 5.5 * (Real.sqrt (2 * K) * (8 / a)), ?_⟩
  have hev : ∀ᶠ x : ℝ in atTop, Real.sqrt (2 * K) * (8 / a) *
      Real.exp (-(a / 8 * Real.sqrt (Real.log x))) ≤ 1 / 2 :=
    (tendsto_order.mp hlim).2 (1 / 2) (by norm_num) |>.mono fun _ h => h.le
  filter_upwards [hev, eventually_ge_atTop (max (2 * x₀) 16)] with x hB hx
  have hx16 : 16 ≤ x := (le_max_right _ _).trans hx
  have hxx₀ : 2 * x₀ ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  -- a cota uniforme em `[x/2, 2x]`
  have hunif : ∀ y : ℝ, x / 2 ≤ y → y ≤ 2 * x → |y * Ssm y - y ^ 2 / 2| ≤ y ^ 2 * η x ^ 2 := by
    intro y hy1 hy2
    have hy0 : 0 < y := by linarith
    have hyx₀ : x₀ ≤ y := by linarith
    refine (hS' y hyx₀).trans ?_
    rw [hηsq x hx1]
    have hy1' : 1 ≤ y := by linarith
    have hl1 : Real.log y ≤ 2 * Real.log x := by
      rw [← Real.log_rpow hx0]
      refine Real.log_le_log hy0 ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith
    have hl2 : Real.log x / 4 ≤ Real.log y := by
      have h := Real.log_le_log (by linarith) hy1
      rw [Real.log_div hx0.ne' (by norm_num)] at h
      have h16 : 4 * Real.log 2 ≤ Real.log x := by
        rw [← Real.log_rpow (by norm_num)]
        exact Real.log_le_log (by positivity) (by norm_num; linarith)
      linarith
    have hsq : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log y) := by
      have : Real.sqrt (Real.log x / 4) = Real.sqrt (Real.log x) / 2 := by
        rw [Real.sqrt_div' _ (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [← this]
      exact Real.sqrt_le_sqrt hl2
    have hexp : Real.exp (-(a * Real.sqrt (Real.log y))) ≤ Real.exp (-(a / 2 * Real.sqrt (Real.log x))) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hly : 0 ≤ Real.log y := Real.log_nonneg hy1'
    have hy2' : 0 ≤ y ^ 2 := sq_nonneg y
    calc y ^ 2 * (K * Real.log y * Real.exp (-(a * Real.sqrt (Real.log y))))
        ≤ y ^ 2 * (K * (2 * Real.log x) * Real.exp (-(a / 2 * Real.sqrt (Real.log x)))) := by
          gcongr
      _ = y ^ 2 * (2 * K * Real.log x * Real.exp (-(a / 2 * Real.sqrt (Real.log x)))) := by ring
  -- o passo `h = ηx`
  have hη0 : 0 < η x := by
    simp only [hη]
    exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)
  have hηh : η x ≤ 1 / 2 := (hηB x hx1).trans hB
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = η x * x := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hhx : h ≤ x / 2 := by rw [hh]; nlinarith
  -- cota superior
  have hup : ψ x ≤ x + 5.5 * (η x * x) := by
    have hinc := (incremento hx0 hh0).1
    have h1 := hunif (x + h) (by linarith) (by linarith)
    have h2 := hunif x (by linarith) (by linarith)
    have h1' := (abs_le.mp h1).2
    have h2' := (abs_le.mp h2).1
    have hsq : (x + h) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    have hkey : h * ψ x ≤ h * (x + 5.5 * (η x * x)) := by
      have e : h * (x + 5.5 * (η x * x)) = x * h + h ^ 2 / 2 + 5 * x ^ 2 * η x ^ 2 := by
        rw [hh]; ring
      rw [e]
      nlinarith [sq_nonneg (η x)]
    exact le_of_mul_le_mul_left hkey hh0
  -- cota inferior
  have hlo : x - 5.5 * (η x * x) ≤ ψ x := by
    have hxh : 0 < x - h := by linarith
    have hinc := (incremento hxh hh0).2
    rw [sub_add_cancel] at hinc
    have h1 := hunif x (by linarith) (by linarith)
    have h2 := hunif (x - h) (by linarith) (by linarith)
    have h1' := (abs_le.mp h1).1
    have h2' := (abs_le.mp h2).2
    have hsq : (x - h) ^ 2 ≤ x ^ 2 := by nlinarith
    have hkey : h * (x - 5.5 * (η x * x)) ≤ h * ψ x := by
      have e : h * (x - 5.5 * (η x * x)) = x * h - h ^ 2 / 2 - 5 * x ^ 2 * η x ^ 2 := by
        rw [hh]; ring
      rw [e]
      nlinarith [sq_nonneg (η x)]
    exact le_of_mul_le_mul_left hkey hh0
  have habs : |ψ x - x| ≤ 5.5 * (η x * x) := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |ψ x - x| ≤ 5.5 * (η x * x) := habs
    _ ≤ 5.5 * (Real.sqrt (2 * K) * (8 / a) * Real.exp (-(a / 8 * Real.sqrt (Real.log x))) * x) := by
        gcongr
        exact hηB x hx1
    _ = 5.5 * (Real.sqrt (2 * K) * (8 / a)) * x * Real.exp (-(a / 8 * Real.sqrt (Real.log x))) := by ring

/-- **TNP**: `ψ(x)/x → 1`. -/
theorem tendsto_psi_div : Tendsto (fun x => ψ x / x) atTop (𝓝 1) := by
  obtain ⟨b, hb, K, hK⟩ := psi_tnp
  have hlim : Tendsto (fun x : ℝ => K * Real.exp (-(b * Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => b * Real.sqrt (Real.log x)) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hb
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
    rwa [mul_zero] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hK, eventually_gt_atTop 0] with x hx hx0
  rw [Real.norm_eq_abs, show ψ x / x - 1 = (ψ x - x) / x by field_simp, abs_div, abs_of_pos hx0,
    div_le_iff₀ hx0]
  calc |ψ x - x| ≤ K * x * Real.exp (-(b * Real.sqrt (Real.log x))) := hx
    _ = K * Real.exp (-(b * Real.sqrt (Real.log x))) * x := by ring

/-- `θ(x)/x → 1`. -/
theorem tendsto_theta_div : Tendsto (fun x => θ x / x) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  have h0 : Tendsto (fun x : ℝ => (ψ x - θ x) / x) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => |C| * (Real.sqrt x)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul |C|
      rwa [mul_zero] at this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx0
    have h1 := hC x
    have h2 := theta_le_psi x
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_of_nonneg (by linarith), div_le_iff₀ hx0]
    calc ψ x - θ x ≤ C * Real.sqrt x := h1
      _ ≤ |C| * Real.sqrt x := by gcongr; exact le_abs_self C
      _ = |C| * (Real.sqrt x)⁻¹ * x := by rw [mul_assoc, inv_mul_eq_div, Real.div_sqrt]
  have := tendsto_psi_div.sub h0
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  field_simp
  ring


/-! ## 3. O TNP para `π(x)` -/

/-- `∫₂^x log 4/log²t dt ≤ log 4 (√x/log²2 + 4x/log²x)` para `x ≥ 4`. -/
theorem integral_inv_log_sq_le {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in (2 : ℝ)..x, Real.log 4 / Real.log t ^ 2 ≤
      Real.log 4 * (Real.sqrt x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) := by
  have hs2 : 2 ≤ Real.sqrt x := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsx : Real.sqrt x ≤ x := by
    have h1 : 1 ≤ Real.sqrt x := by linarith
    have := le_mul_of_one_le_left (Real.sqrt_nonneg x) h1
    rwa [Real.mul_self_sqrt (by linarith)] at this
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcont : ContinuousOn (fun t : ℝ => Real.log 4 / Real.log t ^ 2) (Icc 2 x) := by
    refine continuousOn_const.div (ContinuousOn.pow (Real.continuousOn_log.mono fun t ht => ?_) 2)
      fun t ht => ?_
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
    · exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
  have hi1 : IntervalIntegrable (fun t : ℝ => Real.log 4 / Real.log t ^ 2) volume 2 (Real.sqrt x) :=
    (hcont.mono (Icc_subset_Icc le_rfl hsx)).intervalIntegrable_of_Icc hs2
  have hi2 : IntervalIntegrable (fun t : ℝ => Real.log 4 / Real.log t ^ 2) volume (Real.sqrt x) x :=
    (hcont.mono (Icc_subset_Icc hs2 le_rfl)).intervalIntegrable_of_Icc hsx
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have h1 : ‖∫ t in (2 : ℝ)..Real.sqrt x, Real.log 4 / Real.log t ^ 2‖ ≤
      Real.log 4 / Real.log 2 ^ 2 * |Real.sqrt x - 2| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le hs2] at ht
    have ht2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  have hlsx : Real.log (Real.sqrt x) = Real.log x / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have h2 : ‖∫ t in Real.sqrt x..x, Real.log 4 / Real.log t ^ 2‖ ≤
      Real.log 4 / (Real.log x / 2) ^ 2 * |x - Real.sqrt x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le hsx] at ht
    have ht2 : Real.log x / 2 ≤ Real.log t := by
      rw [← hlsx]; exact Real.log_le_log (by linarith) ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  have hA : ∫ t in (2 : ℝ)..Real.sqrt x, Real.log 4 / Real.log t ^ 2 ≤
      Real.log 4 / Real.log 2 ^ 2 * Real.sqrt x := by
    have := (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ h1)
    rw [abs_of_nonneg (by linarith)] at this
    have hp : 0 ≤ Real.log 4 / Real.log 2 ^ 2 := by positivity
    nlinarith
  have hB : ∫ t in Real.sqrt x..x, Real.log 4 / Real.log t ^ 2 ≤
      Real.log 4 * (4 * x / Real.log x ^ 2) := by
    have := (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ h2)
    rw [abs_of_nonneg (by linarith)] at this
    have e : Real.log 4 / (Real.log x / 2) ^ 2 * (x - Real.sqrt x) ≤ Real.log 4 * (4 * x / Real.log x ^ 2) := by
      rw [div_pow, div_div_eq_mul_div]
      have hpos : 0 < Real.log x ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos, mul_div_assoc', div_mul_cancel₀ _ hpos.ne']
      have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      nlinarith
    linarith
  have e : Real.log 4 * (Real.sqrt x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) =
      Real.log 4 / Real.log 2 ^ 2 * Real.sqrt x + Real.log 4 * (4 * x / Real.log x ^ 2) := by ring
  rw [e]
  linarith

/-- **O teorema dos números primos**: `π(x) log x / x → 1`. -/
theorem tendsto_primeCounting :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) := by
  -- `I(x) log x / x → 0`
  set I : ℝ → ℝ := fun x => ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2) with hI
  have hIle : ∀ x : ℝ, 4 ≤ x → 0 ≤ I x ∧
      I x ≤ Real.log 4 * (Real.sqrt x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := by linarith
    have hf : IntervalIntegrable (fun t => θ t / (t * Real.log t ^ 2)) volume 2 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx2).mpr (integrableOn_theta_div_id_mul_log_sq x)
    have hcont : ContinuousOn (fun t : ℝ => Real.log 4 / Real.log t ^ 2) (Icc 2 x) := by
      refine continuousOn_const.div (ContinuousOn.pow (Real.continuousOn_log.mono fun t ht => ?_) 2)
        fun t ht => ?_
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
      · exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
    have hg : IntervalIntegrable (fun t : ℝ => Real.log 4 / Real.log t ^ 2) volume 2 x :=
      hcont.intervalIntegrable_of_Icc hx2
    constructor
    · refine intervalIntegral.integral_nonneg hx2 fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      exact div_nonneg (theta_nonneg t) (by positivity)
    · refine (intervalIntegral.integral_mono_on hx2 hf hg fun t ht => ?_).trans
        (integral_inv_log_sq_le hx)
      have ht0 : 0 < t := by linarith [ht.1]
      have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have hθ := theta_le_log4_mul_x ht0.le
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc θ t * Real.log t ^ 2 ≤ (Real.log 4 * t) * Real.log t ^ 2 := by gcongr
        _ = Real.log 4 * (t * Real.log t ^ 2) := by ring
  have hlim0 : Tendsto (fun x : ℝ => I x * Real.log x / x) atTop (𝓝 0) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- `log x/√x → 0` e `1/log x → 0`
    have hA : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.sqrt_eq_rpow]
    have hB : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hC := ((hA.const_mul (Real.log 4 / Real.log 2 ^ 2)).add (hB.const_mul (Real.log 4 * 4)))
    rw [mul_zero, mul_zero, add_zero] at hC
    refine squeeze_zero' ?_ ?_ hC
    · filter_upwards [eventually_ge_atTop 4] with x hx
      have hx0 : 0 < x := by linarith
      exact div_nonneg (mul_nonneg (hIle x hx).1 (Real.log_nonneg (by linarith))) hx0.le
    · filter_upwards [eventually_ge_atTop 4] with x hx
      have hx0 : 0 < x := by linarith
      have hlx : 0 < Real.log x := Real.log_pos (by linarith)
      have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
      obtain ⟨h0, h1⟩ := hIle x hx
      rw [div_le_iff₀ hx0]
      calc I x * Real.log x ≤ Real.log 4 * (Real.sqrt x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) *
            Real.log x := by gcongr
        _ = (Real.log 4 / Real.log 2 ^ 2 * (Real.log x / Real.sqrt x) +
              Real.log 4 * 4 * (Real.log x)⁻¹) * x := by
            have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
            have hlx' := hlx.ne'
            have hsx' := hsx.ne'
            generalize hA : Real.log x = A at hlx' ⊢
            generalize hs : Real.sqrt x = s at hsq hsx' ⊢
            subst hsq
            field_simp
  have hθ := tendsto_theta_div
  have hsum := hθ.add hlim0
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 4] with x hx
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hπ := primeCounting_eq_theta_div_log_add_integral hx2
  rw [hπ]
  simp only [hI]
  field_simp

end ATK.ZeroClasses.PNT

#print axioms ATK.ZeroClasses.PNT.Ssm_ext
#print axioms ATK.ZeroClasses.PNT.mul_kk
#print axioms ATK.ZeroClasses.PNT.mul_Ssm_eq
#print axioms ATK.ZeroClasses.PNT.psi_eq_range
#print axioms ATK.ZeroClasses.PNT.incremento
#print axioms ATK.ZeroClasses.PNT.le_exp_mul
#print axioms ATK.ZeroClasses.PNT.psi_tnp
#print axioms ATK.ZeroClasses.PNT.tendsto_psi_div
#print axioms ATK.ZeroClasses.PNT.tendsto_theta_div
#print axioms ATK.ZeroClasses.PNT.integral_inv_log_sq_le
#print axioms ATK.ZeroClasses.PNT.tendsto_primeCounting
