import ATK.ZeroClasses.LittlewoodSoma
import ATK.ZeroClasses.Unilateral

/-!
# Littlewood, parte 3: a montagem (rodada 92)

**O teorema de Littlewood (1914)**, sem hipóteses (`littlewood`):

  `ψ(x) − x = Ω±(√x log log log x)`,

isto é, existe `c > 0` tal que `ψ(x) − x ≤ −c√x log log log x` e `ψ(x) − x ≥ c√x log log log x` para `x`
arbitrariamente grandes. Fecha o plano das rodadas 89–91.

* §1 `resto_le`: o resto de `formula_psi` é `|R(u, τ)| ≤ (K/τ)e^{−u/2}` (`0 < τ ≤ 1`, `u ≥ 0`), com
  `integral_abs_gauss` (`∫ |y|e^{−τy²} = 1/τ`) e `integral_gaussian`.
* §2 `integral_forcada` (sob RH): com `τ = A₀/T²` e `n` que alinha os zeros de `|γ| ≤ 3T`,
  `∫ k_τ(v)F(n ± 1/T − v) dv` fica `∓ c log T` a menos de `C₁ + εΣ + R` (limite de `soma_forcada`).
* §3 `log_N_le`: `log(n + 2) ≤ C_G T^{3/2}` para `n ≤ ⌈T²⌉ Q^K`, `Q = ⌈(1 + log 3T)²⌉`, `K = #{|γ| ≤ 3T}`.
* §4 `F_grande` (sob RH): para `T` grande há `y ≥ T² − 2` com `log y ≤ T²` e `F(y) ≤ −c log T`, e outro com
  `F(y) ≥ c log T`. É a localização da rodada 90 com `ε = 2π/Q` (`εΣ ≤ 2πC`), `|R| ≤ 1` e o termo
  `8B(1 + 2u²)e^{1 − T²/(4A₀)} ≤ ½`.
* §5 `F_omega_RH`, `littlewood_RH` (sob RH); `littlewood_nao_RH` (se RH falha, `Θ > ½` e a rodada 87 dá
  `ψ(x) − x = Ω±(x^θ)` com `½ < θ < Θ`, que domina `√x log log log x`); e `littlewood`, por casos.

Classificação: **consequência** (formalização de um teorema conhecido; Littlewood 1914, Ingham cap. V,
Montgomery–Vaughan §15.1). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.LittlewoodMontagem

open ATK.ZeroClasses.ExplicitaGauss (Wg pw Fw kg)
open ATK.ZeroClasses.ExplicitaT (Zfin mem_Zfin)
open ATK.ZeroClasses.LittlewoodBase (Fpsi)

/-! ## 1. O resto `R(u, τ)` com constante explícita em `τ` -/

/-- O resto da fórmula `formula_psi`: `e^{−5u/2 + 25τ/4}/2 − e^{−u/2 + τ/4} log 2π + Re E`. -/
noncomputable def Resto (u τ : ℝ) : ℝ :=
  Real.exp (-(5 / 2) * u + τ * (25 / 4)) / 2 - Real.exp (-(1 / 2) * u + τ * (1 / 4)) * Real.log (2 * π) +
    ((1 / (2 * π : ℂ)) * ∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)).re

theorem integral_abs_gauss {τ : ℝ} (hτ : 0 < τ) : ∫ y : ℝ, |y| * Real.exp (-τ * y ^ 2) = 1 / τ := by
  have h1 : ∫ y : ℝ, |y| * Real.exp (-τ * y ^ 2) = 2 * ∫ x in Ioi (0 : ℝ), x * Real.exp (-τ * x ^ 2) := by
    have := integral_comp_abs (f := fun x : ℝ => x * Real.exp (-τ * x ^ 2))
    simp only [sq_abs] at this
    exact this
  rw [h1]
  have h2 := integral_mul_cexp_neg_mul_sq (b := (τ : ℂ)) (by simpa using hτ)
  have h3 : ∫ r : ℝ in Ioi 0, (r : ℂ) * cexp (-(τ : ℂ) * (r : ℂ) ^ 2) =
      ((∫ r : ℝ in Ioi 0, r * Real.exp (-τ * r ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    push_cast
    rfl
  rw [h3] at h2
  have h4 : (∫ r : ℝ in Ioi 0, r * Real.exp (-τ * r ^ 2)) = (2 * τ)⁻¹ := by exact_mod_cast h2
  rw [h4]
  field_simp

/-- **O resto é `O(e^{−u/2}/τ)`**: `|R(u, τ)| ≤ (K/τ) e^{−u/2}` para `0 < τ ≤ 1` e `u ≥ 0`. -/
theorem resto_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ u τ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ u →
    |Resto u τ| ≤ K / τ * Real.exp (-(u / 2)) := by
  obtain ⟨c₀, hc₀⟩ := ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
  obtain ⟨B, hB0, hB⟩ := ATK.ZeroClasses.ExplicitaLimite.digamma_esq
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  set a := c₀ + B + 13 with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨Real.exp (25 / 4) + 2 * Real.exp (1 / 4) + Real.exp 9 * (2 * a + 1), by positivity,
    fun u τ hτ hτ1 hu => ?_⟩
  have hpi := Real.pi_pos
  -- a reta esquerda
  have hi2 : Integrable fun y : ℝ => |y| * Real.exp (-τ * y ^ 2) := by
    simpa using ATK.ZeroClasses.ExplicitaGauss.integrable_G hτ 0
  have hE : ‖∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      Real.exp (-3 * u + 9 * τ) * (2 / 5) * (a * √(π / τ) + 1 / τ) := by
    calc ‖∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)‖
        ≤ ∫ y : ℝ, Real.exp (-3 * u + 9 * τ) * (2 / 5) *
            (a * Real.exp (-τ * y ^ 2) + |y| * Real.exp (-τ * y ^ 2)) :=
          norm_integral_le_of_norm_le ((ATK.ZeroClasses.ExplicitaGauss.integrable_G hτ a).const_mul _)
            (Eventually.of_forall fun y => ATK.ZeroClasses.ExplicitaGauss.norm_esq_pt hc₀ hB u τ y)
      _ = Real.exp (-3 * u + 9 * τ) * (2 / 5) * (a * √(π / τ) + 1 / τ) := by
          rw [integral_const_mul, integral_add ((integrable_exp_neg_mul_sq hτ).const_mul a) hi2,
            integral_const_mul, integral_gaussian, integral_abs_gauss hτ]
  have hsq : √(π / τ) ≤ 2 / τ := by
    rw [show (2 / τ) = √((2 / τ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [div_pow, div_le_div_iff₀ hτ (by positivity)]
    nlinarith [Real.pi_lt_four]
  have hinv : 1 ≤ 1 / τ := by rw [le_div_iff₀ hτ]; linarith
  have hE' : ‖((1 / (2 * π : ℂ)) * ∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I))‖ ≤
      Real.exp 9 * (2 * a + 1) / τ * Real.exp (-(u / 2)) := by
    rw [norm_mul]
    have hn : ‖(1 / (2 * π : ℂ))‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hpi]
    rw [hn]
    have hx1 : Real.exp (-3 * u + 9 * τ) ≤ Real.exp 9 * Real.exp (-(u / 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hx0 : 0 ≤ a * √(π / τ) + 1 / τ := by positivity
    calc 1 / (2 * π) * ‖∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)‖
        ≤ 1 / (2 * π) * (Real.exp (-3 * u + 9 * τ) * (2 / 5) * (a * √(π / τ) + 1 / τ)) := by gcongr
      _ ≤ 1 * (Real.exp 9 * Real.exp (-(u / 2)) * 1 * (a * (2 / τ) + 1 / τ)) := by
        gcongr
        · rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
        · norm_num
      _ = Real.exp 9 * (2 * a + 1) / τ * Real.exp (-(u / 2)) := by ring
  have h1 : Real.exp (-(5 / 2) * u + τ * (25 / 4)) / 2 ≤ Real.exp (25 / 4) * Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    have : Real.exp (-(5 / 2) * u + τ * (25 / 4)) ≤ Real.exp (25 / 4 + -(u / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have : 0 < Real.exp (-(5 / 2) * u + τ * (25 / 4)) := Real.exp_pos _
    linarith
  have h2 : Real.exp (-(1 / 2) * u + τ * (1 / 4)) * Real.log (2 * π) ≤
      2 * Real.exp (1 / 4) * Real.exp (-(u / 2)) := by
    have hl := ATK.ZeroClasses.ExplicitaLimite.log_dois_pi_lt
    have hl0 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have : Real.exp (-(1 / 2) * u + τ * (1 / 4)) ≤ Real.exp (1 / 4) * Real.exp (-(u / 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc Real.exp (-(1 / 2) * u + τ * (1 / 4)) * Real.log (2 * π)
        ≤ Real.exp (1 / 4) * Real.exp (-(u / 2)) * 2 := by gcongr
      _ = 2 * Real.exp (1 / 4) * Real.exp (-(u / 2)) := by ring
  have h3 := (Complex.abs_re_le_norm ((1 / (2 * π : ℂ)) *
    ∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I))).trans hE'
  have h1' : 0 ≤ Real.exp (-(5 / 2) * u + τ * (25 / 4)) / 2 := by positivity
  have h2' : 0 ≤ Real.exp (-(1 / 2) * u + τ * (1 / 4)) * Real.log (2 * π) :=
    mul_nonneg (Real.exp_pos _).le (Real.log_nonneg (by linarith [Real.pi_gt_three]))
  have hexp0 : 0 ≤ Real.exp (-(u / 2)) := (Real.exp_pos _).le
  unfold Resto
  rw [abs_le]
  have key : Real.exp (25 / 4) * Real.exp (-(u / 2)) + 2 * Real.exp (1 / 4) * Real.exp (-(u / 2)) +
      Real.exp 9 * (2 * a + 1) / τ * Real.exp (-(u / 2)) ≤
      (Real.exp (25 / 4) + 2 * Real.exp (1 / 4) + Real.exp 9 * (2 * a + 1)) / τ * Real.exp (-(u / 2)) := by
    have e : (Real.exp (25 / 4) + 2 * Real.exp (1 / 4) + Real.exp 9 * (2 * a + 1)) / τ * Real.exp (-(u / 2)) =
        (Real.exp (25 / 4) + 2 * Real.exp (1 / 4)) * (1 / τ) * Real.exp (-(u / 2)) +
          Real.exp 9 * (2 * a + 1) / τ * Real.exp (-(u / 2)) := by ring
    rw [e]
    have : (Real.exp (25 / 4) + 2 * Real.exp (1 / 4)) * Real.exp (-(u / 2)) ≤
        (Real.exp (25 / 4) + 2 * Real.exp (1 / 4)) * (1 / τ) * Real.exp (-(u / 2)) := by
      have hp : 0 ≤ (Real.exp (25 / 4) + 2 * Real.exp (1 / 4)) * Real.exp (-(u / 2)) := by positivity
      nlinarith
    linarith
  constructor <;> linarith [abs_le.mp h3]

/-! ## 2. Do limite à integral gaussiana de `F` -/

open ATK.ZeroClasses.LittlewoodSoma (A₀ um_le_A₀)

theorem formula_psi_resto {τ : ℝ} (hτ : 0 < τ) (u : ℝ) : ∃ T : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 6 ≤ T k ∧ T k ≤ k + 7) ∧
    Tendsto (fun k => ∑ ρ ∈ Zfin (T k), (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg u τ) ρ).re) atTop
      (𝓝 (-(∫ v, kg τ v * Fpsi (u - v)) + Resto u τ)) := by
  obtain ⟨T, hT, h⟩ := ATK.ZeroClasses.LittlewoodBase.formula_psi hτ u
  refine ⟨T, hT, ?_⟩
  convert h using 2
  unfold Resto
  ring

/-- **A integral gaussiana de `F` forçada** (sob RH): para `T` grande e `n` que alinha os zeros com
`|γ| ≤ 3T` a menos de `ε`, com `τ = A₀/T²`,
`∫ k_τ(v)F(n + 1/T − v) dv ≤ −c log T + C₁ + εΣ + R` e `∫ k_τ(v)F(n − 1/T − v) dv ≥ c log T − C₁ − εΣ + R`. -/
theorem integral_forcada (hRH : RiemannHypothesis) : ∃ c C₁ : ℝ, 0 < c ∧ ∀ᶠ T in atTop,
    ∀ n ε : ℝ, (∀ ρ ∈ Zfin (3 * T), ∃ k : ℤ, |n * ρ.im - 2 * π * k| ≤ ε) →
      (∫ v, kg (A₀ / T ^ 2) v * Fpsi (n + 1 / T - v)) ≤ -(c * Real.log T) + C₁ +
          ε * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ + Resto (n + 1 / T) (A₀ / T ^ 2) ∧
      c * Real.log T - C₁ - ε * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ +
          Resto (n - 1 / T) (A₀ / T ^ 2) ≤ ∫ v, kg (A₀ / T ^ 2) v * Fpsi (n - 1 / T - v) := by
  obtain ⟨c, C₁, hc, hev⟩ := ATK.ZeroClasses.LittlewoodSoma.soma_forcada hRH
  refine ⟨c, C₁, hc, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with T hT hT0 n ε hal
  have hA := um_le_A₀
  have hτ : 0 < A₀ / T ^ 2 := by positivity
  obtain ⟨Tk, hTk, hlim⟩ := formula_psi_resto hτ (n + 1 / T)
  obtain ⟨Tk', hTk', hlim'⟩ := formula_psi_resto hτ (n - 1 / T)
  have hev3 : ∀ T'' : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 6 ≤ T'' k ∧ T'' k ≤ k + 7) →
      ∀ᶠ k in atTop, 3 * T ≤ T'' k := fun T'' hT'' =>
    eventually_atTop.mpr ⟨⌈3 * T⌉₊, fun k hk => by
      have h1 : 3 * T ≤ (k : ℝ) := (Nat.ceil_le.mp hk)
      linarith [(hT'' k).1]⟩
  constructor
  · have hge := ge_of_tendsto hlim ((hev3 Tk hTk).mono fun k hk => (hT n ε (Tk k) hk hal).1)
    linarith
  · have hle := le_of_tendsto hlim' ((hev3 Tk' hTk').mono fun k hk => (hT n ε (Tk' k) hk hal).2)
    linarith

/-! ## 3. O tamanho de `u`: `log(n + 2) ≤ C_G T^{3/2}` para `n ≤ ⌈T²⌉ Q^K` -/

/-- A precisão do alinhamento, `Q(T) = ⌈(1 + log 3T)²⌉`. -/
noncomputable def Qa (T : ℝ) : ℕ := ⌈(1 + Real.log (3 * T)) ^ 2⌉₊

theorem um_le_Qa {T : ℝ} (hT : 1 ≤ T) : 1 ≤ Qa T := by
  unfold Qa
  have : 0 ≤ Real.log (3 * T) := Real.log_nonneg (by linarith)
  exact Nat.one_le_ceil_iff.mpr (by positivity)

theorem log_N_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 3 ≤ T → ∀ n : ℕ,
    n ≤ ⌈T ^ 2⌉₊ * Qa T ^ (Zfin (3 * T)).card → Real.log ((n : ℝ) + 2) ≤ C * (T ^ (1 / 4 : ℝ)) ^ 6 := by
  have hl0 := ATK.ZeroClasses.SomaZeros.l0_pos
  have ha0 := ATK.ZeroClasses.SomaZeros.one_le_a0
  set C := 11 + 168 * (ATK.ZeroClasses.SomaZeros.a0 + 6) / ATK.ZeroClasses.SomaZeros.l0 with hC
  refine ⟨C, by positivity, fun T hT n hn => ?_⟩
  have hT0 : 0 < T := by linarith
  set s := T ^ (1 / 4 : ℝ) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow (by linarith) (by norm_num)
  have hs4 : s ^ 4 = T := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  have hlogT : Real.log T ≤ 4 * s := by
    have := Real.log_le_rpow_div hT0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hs] at this
    linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  set K := (Zfin (3 * T)).card with hK
  set Q := Qa T with hQ
  have hQ1 : 1 ≤ Q := um_le_Qa (by linarith)
  have hn0 : 1 ≤ ⌈T ^ 2⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  set N := ⌈T ^ 2⌉₊ * Q ^ K with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- `log(n + 2) ≤ log 3 + log ⌈T²⌉ + K log Q`
  have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log 3 + Real.log (⌈T ^ 2⌉₊ : ℝ) + K * Real.log Q := by
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (⌈T ^ 2⌉₊ : ℝ) := by exact_mod_cast hn0
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
    calc Real.log ((n : ℝ) + 2) ≤ Real.log (3 * ((⌈T ^ 2⌉₊ : ℝ) * (Q : ℝ) ^ K)) := by
          apply Real.log_le_log (by positivity)
          have : (N : ℝ) = (⌈T ^ 2⌉₊ : ℝ) * (Q : ℝ) ^ K := by rw [hN]; push_cast; ring
          rw [← this]
          linarith
      _ = Real.log 3 + Real.log (⌈T ^ 2⌉₊ : ℝ) + K * Real.log Q := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hpos.ne' (by positivity),
            Real.log_pow]
          ring
  -- `log ⌈T²⌉ ≤ 1 + 8s`
  have h2 : Real.log (⌈T ^ 2⌉₊ : ℝ) ≤ 1 + 8 * s := by
    have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ T ^ 2)
    have hpos : (0 : ℝ) < (⌈T ^ 2⌉₊ : ℝ) := by exact_mod_cast hn0
    calc Real.log (⌈T ^ 2⌉₊ : ℝ) ≤ Real.log (2 * T ^ 2) :=
          Real.log_le_log hpos (by nlinarith)
      _ = Real.log 2 + 2 * Real.log T := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 1 + 8 * s := by
          have : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
          linarith
  -- `K ≤ 12T(a₀ + log(3T + 3))/l₀`
  have h3 : (K : ℝ) ≤ 4 * (3 * T) * ((ATK.ZeroClasses.SomaZeros.a0 + Real.log (3 * T + 3)) /
      ATK.ZeroClasses.SomaZeros.l0) :=
    (ATK.ZeroClasses.LittlewoodSoma.card_le_massa _ fun ρ hρ =>
      (ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin hρ).1).trans
      (ATK.ZeroClasses.LittlewoodSoma.massa_le_real (by linarith))
  -- `log Q ≤ 2(1 + log 3T)`
  have hL0 : 0 ≤ Real.log (3 * T) := Real.log_nonneg (by linarith)
  have h4 : Real.log Q ≤ 2 * (1 + Real.log (3 * T)) := by
    have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (1 + Real.log (3 * T)) ^ 2)
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
    calc Real.log Q ≤ Real.log ((2 + Real.log (3 * T)) ^ 2) := by
          apply Real.log_le_log hQpos
          rw [hQ, Qa]
          nlinarith
      _ = 2 * Real.log (2 + Real.log (3 * T)) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * (1 + Real.log (3 * T)) := by
          have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 2 + Real.log (3 * T))
          linarith
  have hl3 : Real.log (3 * T) ≤ 2 + 4 * s := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    have : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    linarith
  have hl6 : Real.log (3 * T + 3) ≤ 2 + 4 * s := by
    calc Real.log (3 * T + 3) ≤ Real.log (6 * T) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 6 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
      _ ≤ 2 + 4 * s := by
          have : Real.log 6 ≤ 2 := by
            rw [Real.log_le_iff_le_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
            have := Real.exp_one_gt_d9
            nlinarith
          linarith
  -- `K log Q ≤ (168(a₀ + 6)/l₀) s⁶`
  set a0 := ATK.ZeroClasses.SomaZeros.a0 with ha0d
  set l0 := ATK.ZeroClasses.SomaZeros.l0 with hl0d
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ1)
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  have h5 : (K : ℝ) * Real.log Q ≤ 168 * (a0 + 6) / l0 * s ^ 6 := by
    have hA : a0 + Real.log (3 * T + 3) ≤ (a0 + 6) * s := by nlinarith
    have hB : 2 * (1 + Real.log (3 * T)) ≤ 14 * s := by nlinarith
    have hK' : (K : ℝ) ≤ 12 * T * ((a0 + 6) * s / l0) := by
      calc (K : ℝ) ≤ 4 * (3 * T) * ((a0 + Real.log (3 * T + 3)) / l0) := h3
        _ ≤ 4 * (3 * T) * ((a0 + 6) * s / l0) := by gcongr
        _ = 12 * T * ((a0 + 6) * s / l0) := by ring
    calc (K : ℝ) * Real.log Q ≤ 12 * T * ((a0 + 6) * s / l0) * (14 * s) := by
          apply mul_le_mul hK' (h4.trans hB) hlogQ0 (by positivity)
      _ = 168 * (a0 + 6) / l0 * (s ^ 4 * s ^ 2) := by rw [← hs4]; ring
      _ = 168 * (a0 + 6) / l0 * s ^ 6 := by ring
  have hs6 : 1 ≤ s ^ 6 := one_le_pow₀ hs1
  have hss : s ≤ s ^ 6 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 6 := pow_le_pow_right₀ hs1 (by norm_num)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hKl : (K : ℝ) * Real.log Q = K * Real.log Q := rfl
  calc Real.log ((n : ℝ) + 2) ≤ Real.log 3 + Real.log (⌈T ^ 2⌉₊ : ℝ) + K * Real.log Q := h1
    _ ≤ 2 + (1 + 8 * s) + 168 * (a0 + 6) / l0 * s ^ 6 := by linarith
    _ ≤ C * s ^ 6 := by
        rw [hC]
        nlinarith

/-! ## 4. A montagem sob RH -/

theorem ev_pol (a b : ℝ) (hb : 0 < b) : ∀ᶠ T in atTop, a * (T ^ (1 / 4 : ℝ)) ^ 6 ≤ b * T ^ 2 := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop (max 1 (|a| / b))
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with T hs hT0
  set s := T ^ (1 / 4 : ℝ) with hsd
  have hs4 : s ^ 4 = T := by
    rw [hsd, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have hsa : |a| / b ≤ s := le_trans (le_max_right _ _) hs
  have hab : |a| ≤ b * s := by
    rw [div_le_iff₀ hb] at hsa
    linarith
  have hT2 : T ^ 2 = s ^ 8 := by rw [← hs4]; ring
  rw [hT2]
  have h6 : 0 ≤ s ^ 6 := by positivity
  have h78 : s * s ^ 6 ≤ s ^ 8 := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hs1 (by norm_num)
  calc a * s ^ 6 ≤ |a| * s ^ 6 := mul_le_mul_of_nonneg_right (le_abs_self a) h6
    _ ≤ b * s * s ^ 6 := mul_le_mul_of_nonneg_right hab h6
    _ = b * (s * s ^ 6) := by ring
    _ ≤ b * s ^ 8 := mul_le_mul_of_nonneg_left h78 hb.le

theorem ev_resto (K : ℝ) : ∀ᶠ T in atTop, K * T ^ 2 * Real.exp (-((T ^ 2 - 1) / 2)) ≤ 1 := by
  have hlim : Tendsto (fun T : ℝ => (T ^ 2 / 2) ^ 1 * Real.exp (-(T ^ 2 / 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      ((tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos)
  have hlim2 := hlim.const_mul (K * 2 * Real.exp (1 / 2))
  rw [mul_zero] at hlim2
  filter_upwards [hlim2.eventually (gt_mem_nhds one_pos)] with T hT
  have e : K * T ^ 2 * Real.exp (-((T ^ 2 - 1) / 2)) =
      K * 2 * Real.exp (1 / 2) * ((T ^ 2 / 2) ^ 1 * Real.exp (-(T ^ 2 / 2))) := by
    rw [show -((T ^ 2 - 1) / 2) = 1 / 2 + -(T ^ 2 / 2) by ring, Real.exp_add]
    ring
  rw [e]
  exact hT.le

theorem aux_sq {u n : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ n + 1) (hn : 0 ≤ n) : 1 + 2 * u ^ 2 ≤ 3 * (n + 2) ^ 2 := by
  nlinarith

theorem aux_abs (CG L s6 : ℝ) (hs6 : 1 ≤ s6) : 2 * CG * s6 + L + 2 ≤ (2 * CG + |L| + 2) * s6 := by
  have h1 := le_abs_self L
  have h0 := abs_nonneg L
  nlinarith

/-- **`F` grande nos dois sentidos, sob RH**: para `T` grande há `y ≥ T² − 2` com `log y ≤ T²` e
`F(y) ≤ −c log T`, e outro com `F(y) ≥ c log T`. -/
theorem F_grande (hRH : RiemannHypothesis) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop,
    (∃ y : ℝ, T ^ 2 - 2 ≤ y ∧ Real.log y ≤ T ^ 2 ∧ Fpsi y ≤ -(c * Real.log T)) ∧
    (∃ y : ℝ, T ^ 2 - 2 ≤ y ∧ Real.log y ≤ T ^ 2 ∧ c * Real.log T ≤ Fpsi y) := by
  obtain ⟨c, C₁, hc, hev⟩ := integral_forcada hRH
  obtain ⟨B, hB0, hB⟩ := ATK.ZeroClasses.LittlewoodBase.Fpsi_le_RH hRH
  obtain ⟨Cn, hCn0, hCn⟩ := ATK.ZeroClasses.Explicita.soma_ordem_norm
  obtain ⟨K, hK0, hK⟩ := resto_le
  obtain ⟨CG, hCG0, hCG⟩ := log_N_le
  have hA := um_le_A₀
  have hpi := Real.pi_pos
  refine ⟨c / 2, by positivity, ?_⟩
  have e1 := ev_pol (2 * CG + |Real.log (24 * B + 1)| + 2) (1 / (4 * A₀)) (by positivity)
  have e2 := ev_pol CG 1 one_pos
  have e4 : ∀ᶠ T in atTop, C₁ + 2 * π * Cn + 3 ≤ c / 2 * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop (by positivity : 0 < c / 2)).eventually_ge_atTop _
  filter_upwards [hev, e1, e2, ev_resto K, e4, eventually_ge_atTop (3 : ℝ),
    eventually_ge_atTop (2 * A₀)] with T hT h1 h2 h3 h4 hT3 hTA
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hT2 : 2 * A₀ ≤ T ^ 2 := by nlinarith
  have hT9 : 9 ≤ T ^ 2 := by nlinarith
  set τ := A₀ / T ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 / 2 := by
    rw [hτ, div_le_iff₀ (by positivity)]
    linarith
  set s := T ^ (1 / 4 : ℝ) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hT1 (by norm_num)
  have hs6 : 1 ≤ s ^ 6 := one_le_pow₀ hs1
  set Q := Qa T with hQ
  have hQ1 : 1 ≤ Q := um_le_Qa hT1
  have hn₀1 : 1 ≤ ⌈T ^ 2⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  obtain ⟨n, hn1, hn2, hal⟩ := ATK.ZeroClasses.LittlewoodSoma.alinha T hn₀1 hQ1
  -- o erro de alinhamento é `≤ 2π C_n`
  have hSig : 2 * π / Q * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤ 2 * π * Cn := by
    have hS := hCn (3 * T) (by linarith) (Zfin (3 * T)) (fun ρ hρ =>
      ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin hρ)
    have hQr : (1 + Real.log (3 * T)) ^ 2 ≤ (Q : ℝ) := Nat.le_ceil _
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
    have hL : 0 ≤ (1 + Real.log (3 * T)) ^ 2 := by positivity
    calc 2 * π / Q * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖
        ≤ 2 * π / Q * (Cn * (1 + Real.log (3 * T)) ^ 2) := by gcongr
      _ = 2 * π * Cn * ((1 + Real.log (3 * T)) ^ 2 / Q) := by ring
      _ ≤ 2 * π * Cn * 1 := by
          gcongr
          rw [div_le_one hQpos]
          exact hQr
      _ = 2 * π * Cn := by ring
  obtain ⟨hI1, hI2⟩ := hT (n : ℝ) (2 * π / Q) hal
  -- `n ≥ T²` e `log(n + 2) ≤ CG s⁶ ≤ T²`
  have hnT : T ^ 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn1)
  have hlogn : Real.log ((n : ℝ) + 2) ≤ CG * s ^ 6 := hCG T hT3 n hn2
  have hlogn' : Real.log ((n : ℝ) + 2) ≤ T ^ 2 := by linarith
  have hiT : 1 / T ≤ 1 := by rw [div_le_one hT0]; exact hT1
  have hiT0 : 0 < 1 / T := by positivity
  -- o resto
  have hR : ∀ u : ℝ, T ^ 2 - 1 ≤ u → |Resto u τ| ≤ 1 := by
    intro u hu
    have hu0 : 0 ≤ u := by linarith
    refine (hK u τ hτ0 (by linarith) hu0).trans ?_
    have hKt : K / τ = K * T ^ 2 / A₀ := by rw [hτ]; field_simp
    have hex : Real.exp (-(u / 2)) ≤ Real.exp (-((T ^ 2 - 1) / 2)) := Real.exp_le_exp.mpr (by linarith)
    calc K / τ * Real.exp (-(u / 2)) ≤ K * T ^ 2 * Real.exp (-((T ^ 2 - 1) / 2)) := by
          rw [hKt]
          have : K * T ^ 2 / A₀ ≤ K * T ^ 2 := div_le_self (by positivity) hA
          exact mul_le_mul this hex (Real.exp_pos _).le (by positivity)
      _ ≤ 1 := h3
  -- o termo da localização
  have hX : ∀ u : ℝ, 0 ≤ u → u ≤ (n : ℝ) + 1 →
      8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) ≤ 1 / 2 := by
    intro u hu0 hu1
    have hn2p : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hsq : 1 + 2 * u ^ 2 ≤ 3 * Real.exp (2 * Real.log ((n : ℝ) + 2)) := by
      rw [show 2 * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ 2) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity)]
      exact aux_sq hu0 hu1 (Nat.cast_nonneg n)
    have h4τ : 1 / (4 * τ) = T ^ 2 / (4 * A₀) := by rw [hτ]; field_simp
    have hexp : 2 * Real.log ((n : ℝ) + 2) + (1 - 1 / (4 * τ)) ≤ -1 - Real.log (24 * B + 1) := by
      rw [h4τ]
      have habs := le_abs_self (Real.log (24 * B + 1))
      have : 2 * CG * s ^ 6 + Real.log (24 * B + 1) + 2 ≤ (2 * CG + |Real.log (24 * B + 1)| + 2) * s ^ 6 :=
        aux_abs CG _ _ hs6
      have h1' : (2 * CG + |Real.log (24 * B + 1)| + 2) * s ^ 6 ≤ T ^ 2 / (4 * A₀) := by
        rw [div_eq_mul_one_div, mul_comm (T ^ 2)]
        exact h1
      linarith
    have hB24 : 24 * B * Real.exp (-1 - Real.log (24 * B + 1)) ≤ 1 / 2 := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity)]
      have he : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.exp_one_gt_d9
        linarith
      have hfrac : 24 * B * (24 * B + 1)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        linarith
      calc 24 * B * (Real.exp (-1) * (24 * B + 1)⁻¹) = Real.exp (-1) * (24 * B * (24 * B + 1)⁻¹) := by ring
        _ ≤ 1 / 2 * 1 := mul_le_mul he hfrac (by positivity) (by norm_num)
        _ = 1 / 2 := by ring
    calc 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ))
        ≤ 8 * B * (3 * Real.exp (2 * Real.log ((n : ℝ) + 2))) * Real.exp (1 - 1 / (4 * τ)) := by gcongr
      _ = 24 * B * Real.exp (2 * Real.log ((n : ℝ) + 2) + (1 - 1 / (4 * τ))) := by
          rw [Real.exp_add]; ring
      _ ≤ 24 * B * Real.exp (-1 - Real.log (24 * B + 1)) := by gcongr
      _ ≤ 1 / 2 := hB24
  -- `L = c log T − C₁ − 2πC_n − 2 ≥ (c/2) log T + 1`
  have hcl : c * Real.log T = 2 * (c / 2 * Real.log T) := by ring
  have hcl0 : 0 ≤ c / 2 * Real.log T := by
    have := Real.log_nonneg hT1
    positivity
  set L := c * Real.log T - C₁ - 2 * π * Cn - 2 with hLd
  have hL0 : 0 ≤ L := by linarith
  constructor
  · -- `u = n + 1/T`: `F` muito negativo
    set u := (n : ℝ) + 1 / T with hu
    have hRu := abs_le.mp (hR u (by linarith))
    have hXu := hX u (by positivity) (by linarith)
    have hint : ∫ v, kg τ v * Fpsi (u - v) < -L - 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) := by
      linarith [hRu.2]
    obtain ⟨y, hy, hFy⟩ := ATK.ZeroClasses.LittlewoodBase.localiza_menos hτ0 hτ1 hB hL0 hint
    refine ⟨y, by linarith [hy.1], ?_, by linarith⟩
    have hy0 : 0 < y := by linarith [hy.1]
    calc Real.log y ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log hy0 (by linarith [hy.2])
      _ ≤ T ^ 2 := hlogn'
  · -- `u = n − 1/T`: `F` muito positivo
    set u := (n : ℝ) - 1 / T with hu
    have hRu := abs_le.mp (hR u (by linarith))
    have hXu := hX u (by linarith) (by linarith)
    have hint : L + 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) < ∫ v, kg τ v * Fpsi (u - v) := by
      linarith [hRu.1]
    obtain ⟨y, hy, hFy⟩ := ATK.ZeroClasses.LittlewoodBase.localiza_mais hτ0 hτ1 hB hL0 hint
    refine ⟨y, by linarith [hy.1], ?_, by linarith⟩
    have hy0 : 0 < y := by linarith [hy.1]
    calc Real.log y ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log hy0 (by linarith [hy.2])
      _ ≤ T ^ 2 := hlogn'

/-! ## 5. Littlewood: `ψ(x) − x = Ω±(√x log log log x)` -/

/-- **Sob RH**: `F(y) = Ω±(log log y)`, com `F(y) = (ψ(e^y) − e^y)e^{−y/2}`. -/
theorem F_omega_RH (hRH : RiemannHypothesis) : ∃ c : ℝ, 0 < c ∧
    (∀ Y : ℝ, ∃ y : ℝ, Y ≤ y ∧ Fpsi y ≤ -(c * Real.log (Real.log y))) ∧
    (∀ Y : ℝ, ∃ y : ℝ, Y ≤ y ∧ c * Real.log (Real.log y) ≤ Fpsi y) := by
  obtain ⟨c, hc, hev⟩ := F_grande hRH
  refine ⟨c / 2, by positivity, fun Y => ?_, fun Y => ?_⟩
  all_goals
    obtain ⟨T, hT, hT3⟩ := (hev.and (eventually_ge_atTop (|Y| + 3))).exists
    have hT1 : 1 ≤ T := by linarith [abs_nonneg Y]
    have hTT : T ≤ T ^ 2 := by nlinarith
    have hYT : Y ≤ T ^ 2 - 2 := by linarith [le_abs_self Y]
    have hll : ∀ y : ℝ, T ^ 2 - 2 ≤ y → Real.log y ≤ T ^ 2 →
        c / 2 * Real.log (Real.log y) ≤ c * Real.log T := by
      intro y hy hly
      have hy1 : 1 < y := by nlinarith [abs_nonneg Y]
      have hly0 : 0 < Real.log y := Real.log_pos hy1
      have h1 : Real.log (Real.log y) ≤ Real.log (T ^ 2) := Real.log_le_log hly0 hly
      rw [Real.log_pow] at h1
      push_cast at h1
      nlinarith
  · obtain ⟨y, hy, hly, hF⟩ := hT.1
    exact ⟨y, hYT.trans hy, by linarith [hll y hy hly]⟩
  · obtain ⟨y, hy, hly, hF⟩ := hT.2
    exact ⟨y, hYT.trans hy, by linarith [hll y hy hly]⟩

/-- **Littlewood sob RH**: `ψ(x) − x = Ω±(√x log log log x)`. -/
theorem littlewood_RH (hRH : RiemannHypothesis) : ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      Chebyshev.psi x - x ≤ -(c * √x * Real.log (Real.log (Real.log x)))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * √x * Real.log (Real.log (Real.log x)) ≤ Chebyshev.psi x - x) := by
  obtain ⟨c, hc, h1, h2⟩ := F_omega_RH hRH
  have key : ∀ y : ℝ, Chebyshev.psi (Real.exp y) - Real.exp y = Fpsi y * √(Real.exp y) := by
    intro y
    unfold Fpsi
    rw [← Real.exp_half, mul_assoc, ← Real.exp_add]
    simp
  have hx : ∀ X y : ℝ, |X| ≤ y → X ≤ Real.exp y := fun X y h => by
    linarith [Real.add_one_le_exp y, le_abs_self X]
  refine ⟨c, hc, fun X => ?_, fun X => ?_⟩
  · obtain ⟨y, hy, hF⟩ := h1 |X|
    refine ⟨Real.exp y, hx X y hy, ?_⟩
    rw [key, Real.log_exp]
    have hs : 0 ≤ √(Real.exp y) := Real.sqrt_nonneg _
    calc Fpsi y * √(Real.exp y) ≤ -(c * Real.log (Real.log y)) * √(Real.exp y) :=
          mul_le_mul_of_nonneg_right hF hs
      _ = -(c * √(Real.exp y) * Real.log (Real.log y)) := by ring
  · obtain ⟨y, hy, hF⟩ := h2 |X|
    refine ⟨Real.exp y, hx X y hy, ?_⟩
    rw [key, Real.log_exp]
    have hs : 0 ≤ √(Real.exp y) := Real.sqrt_nonneg _
    calc c * √(Real.exp y) * Real.log (Real.log y) = c * Real.log (Real.log y) * √(Real.exp y) := by ring
      _ ≤ Fpsi y * √(Real.exp y) := mul_le_mul_of_nonneg_right hF hs

/-- `log log log N ≤ log N` para `N ≥ 3`. -/
theorem logloglog_le {x : ℝ} (hx : 3 ≤ x) : Real.log (Real.log (Real.log x)) ≤ Real.log x := by
  have h1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg h1
  calc Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := Real.log_le_self h2
    _ ≤ Real.log x := Real.log_le_self (by linarith)

/-- `√x log log log x ≤ (1/ε)(x + 1)^{½ + ε}` para `x ≥ 3`, `0 < ε`. -/
theorem raiz_le_pot {x ε : ℝ} (hx : 3 ≤ x) (hε : 0 < ε) :
    √x * Real.log (Real.log (Real.log x)) ≤ 1 / ε * (x + 1) ^ (1 / 2 + ε) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_le_rpow_div hx0.le hε
  have hll := logloglog_le hx
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  calc √x * Real.log (Real.log (Real.log x)) ≤ √x * (x ^ ε / ε) :=
        mul_le_mul_of_nonneg_left (hll.trans hl) hs
    _ = 1 / ε * x ^ (1 / 2 + ε) := by
        rw [Real.rpow_add hx0, Real.sqrt_eq_rpow]
        ring
    _ ≤ 1 / ε * (x + 1) ^ (1 / 2 + ε) := by
        gcongr
        linarith

open ATK.ZeroClasses.BDTheta (Teta meio_le_Teta rh_iff_Teta) in
/-- **Littlewood sem RH**: se RH falha, `ψ(x) − x = Ω±(√x log log log x)` com constante `1`
(rodada 87: `ψ(x) − x = Ω±(x^θ)` para `θ < Θ`, e `Θ > ½`). -/
theorem littlewood_nao_RH (h : ¬ RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      Chebyshev.psi x - x ≤ -(1 * √x * Real.log (Real.log (Real.log x)))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      1 * √x * Real.log (Real.log (Real.log x)) ≤ Chebyshev.psi x - x) := by
  have hT : 1 / 2 < Teta := lt_of_le_of_ne meio_le_Teta (fun he => h (rh_iff_Teta.mpr he.symm))
  set θ := (1 / 2 + Teta) / 2 with hθ
  have hθ1 : 1 / 2 < θ := by rw [hθ]; linarith
  have hθ2 : θ < Teta := by rw [hθ]; linarith
  set ε := θ - 1 / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hθε : θ = 1 / 2 + ε := by rw [hε]; ring
  refine ⟨fun X => ?_, fun X => ?_⟩
  · set X' := max X 3 with hX'
    obtain ⟨N, hN⟩ := ATK.ZeroClasses.Unilateral.psi_omega_menos (by linarith) hθ2 (1 / ε) X'
    have hpos : 0 ≤ 1 / ε * ((N : ℝ) + 1) ^ θ := by positivity
    have hNX : X' < (N : ℝ) := by
      by_contra hle
      push Not at hle
      have := Chebyshev.psi_nonneg (N : ℝ)
      linarith
    have hN3 : 3 ≤ (N : ℝ) := by linarith [le_max_right X 3]
    refine ⟨N, by linarith [le_max_left X 3], ?_⟩
    have hr := raiz_le_pot hN3 hε0
    rw [← hθε] at hr
    have hX3 : 3 ≤ X' := le_max_right X 3
    linarith
  · set X' := max X 3 with hX'
    obtain ⟨N, hN⟩ := ATK.ZeroClasses.Unilateral.psi_omega_mais (by linarith) hθ2 (1 / ε)
      (Chebyshev.psi X')
    have hpos : 0 ≤ 1 / ε * ((N : ℝ) + 1) ^ θ := by positivity
    have hNX : X' < (N : ℝ) := by
      by_contra hle
      push Not at hle
      have h1 := Chebyshev.psi_mono hle
      have h2 : (0 : ℝ) ≤ N := N.cast_nonneg
      linarith
    have hN3 : 3 ≤ (N : ℝ) := by linarith [le_max_right X 3]
    refine ⟨N, by linarith [le_max_left X 3], ?_⟩
    have hr := raiz_le_pot hN3 hε0
    rw [← hθε] at hr
    have hp0 := Chebyshev.psi_nonneg X'
    linarith

/-- **O teorema de Littlewood (1914)**: `ψ(x) − x = Ω±(√x log log log x)`, sem hipóteses. -/
theorem littlewood : ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      Chebyshev.psi x - x ≤ -(c * √x * Real.log (Real.log (Real.log x)))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * √x * Real.log (Real.log (Real.log x)) ≤ Chebyshev.psi x - x) := by
  by_cases hRH : RiemannHypothesis
  · exact littlewood_RH hRH
  · exact ⟨1, one_pos, littlewood_nao_RH hRH⟩

end ATK.ZeroClasses.LittlewoodMontagem

#print axioms ATK.ZeroClasses.LittlewoodMontagem.integral_abs_gauss
#print axioms ATK.ZeroClasses.LittlewoodMontagem.resto_le
#print axioms ATK.ZeroClasses.LittlewoodMontagem.formula_psi_resto
#print axioms ATK.ZeroClasses.LittlewoodMontagem.integral_forcada
#print axioms ATK.ZeroClasses.LittlewoodMontagem.um_le_Qa
#print axioms ATK.ZeroClasses.LittlewoodMontagem.log_N_le
#print axioms ATK.ZeroClasses.LittlewoodMontagem.ev_pol
#print axioms ATK.ZeroClasses.LittlewoodMontagem.ev_resto
#print axioms ATK.ZeroClasses.LittlewoodMontagem.aux_sq
#print axioms ATK.ZeroClasses.LittlewoodMontagem.aux_abs
#print axioms ATK.ZeroClasses.LittlewoodMontagem.F_grande
#print axioms ATK.ZeroClasses.LittlewoodMontagem.F_omega_RH
#print axioms ATK.ZeroClasses.LittlewoodMontagem.littlewood_RH
#print axioms ATK.ZeroClasses.LittlewoodMontagem.logloglog_le
#print axioms ATK.ZeroClasses.LittlewoodMontagem.raiz_le_pot
#print axioms ATK.ZeroClasses.LittlewoodMontagem.littlewood_nao_RH
#print axioms ATK.ZeroClasses.LittlewoodMontagem.littlewood
