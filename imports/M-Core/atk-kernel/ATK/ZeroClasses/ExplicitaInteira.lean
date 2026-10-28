import ATK.ZeroClasses.ExplicitaReal

/-!
# A fórmula explícita em `x` inteiro: `ψ₀` (rodada 78)

A rodada 77 deu a fórmula explícita para `x > 1` não inteiro. Em `x = N` inteiro o degrau de Perron vale `½` no
termo `n = N` e a fórmula usa `ψ₀(N) = ψ(N) − Λ(N)/2`:

  **`lim_{T → ∞} Σ_{|γ| ≤ T} m_ρ N^ρ/ρ = N − ψ₀(N) − log 2π − ½ log(1 − N^{−2})`**   (`formula_explicita_T_N`).

* `integral_um_div`: `∫_{−T}^{T} dt/(c + it) = 2 arctan(T/c)`;
* `perron_zero`: `|perron 0 c T − ½| ≤ c/(πT)` (o termo `n = N`);
* `abs_log_ge_N`: `|log(N/n)| ≥ 1/(N + 1)` para `n ≠ N`;
* `perron_LSeries_N`, `perron_psi0`: Perron truncada em `x = N` com constante `N + 1 + c`;
* `explicita_k_N`, `formula_explicita_N`, `formula_explicita_T_N`: a cadeia das rodadas 70–72 e 77;
* `psiZero`, `formula_explicita_T_real`: com a rodada 77, **a fórmula vale para todo `x > 1`**,
  `lim_{T → ∞} Σ_{|γ| ≤ T} m_ρ x^ρ/ρ = x − ψ₀(x) − log 2π − ½ log(1 − x^{−2})`.

Classificação (rodada 78): **consequência**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.ExplicitaInteira

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret)
open ATK.ZeroClasses.Perron (perron perron_degrau)
open ATK.ZeroClasses.PerronD (soma_perron summable_um termo norm_term_le_um)
open ATK.ZeroClasses.PsiRH (Fx px norm_Fx fL norm_fL_le term_fL_neg LSeries_fL tsum_um_le)
open ATK.ZeroClasses.ExplicitaLimite
open ATK.ZeroClasses.ExplicitaReal (epsx epsx_tendsto)
open ATK.ZeroClasses.SomaZeros (a0 l0 l0_pos)

/-! ## 1. O termo `n = x` de Perron -/

/-- **`∫_{−T}^{T} dt/(c + it) = 2 arctan(T/c)`** para `c > 0`. -/
theorem integral_um_div {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∫ t in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I) = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
  have hne : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := fun t h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hD : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((Real.arctan (t / c) : ℝ) : ℂ) -
      I / 2 * ((Real.log (c ^ 2 + t ^ 2) : ℝ) : ℂ)) ((1 : ℂ) / ((c : ℂ) + t * I)) t := by
    intro t
    have hq : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
    have h1 : HasDerivAt (fun t : ℝ => Real.arctan (t / c)) (1 / (1 + (t / c) ^ 2) * (1 / c)) t := by
      exact (Real.hasDerivAt_arctan (t / c)).comp t ((hasDerivAt_id t).div_const c)
    have h2 : HasDerivAt (fun t : ℝ => Real.log (c ^ 2 + t ^ 2)) ((2 * t) / (c ^ 2 + t ^ 2)) t := by
      have h := ((hasDerivAt_pow 2 t).const_add (c ^ 2)).log hq.ne'
      convert h using 1
      norm_num
    have h3 := (h1.ofReal_comp).sub (h2.ofReal_comp.const_mul (I / 2))
    convert h3 using 1
    have e1 : 1 / (1 + (t / c) ^ 2) * (1 / c) = c / (c ^ 2 + t ^ 2) := by
      field_simp
      try ring
    rw [e1]
    have hq' : ((c ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [div_eq_iff (hne t)]
    symm
    have hc2 : ((c : ℂ) - t * I) * ((c : ℂ) + t * I) = ((c ^ 2 + t ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    calc (((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) - I / 2 * ((2 * t / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) *
          ((c : ℂ) + t * I)
        = ((c : ℂ) - t * I) * ((c : ℂ) + t * I) / ((c ^ 2 + t ^ 2 : ℝ) : ℂ) := by
          push_cast
          field_simp
          try ring
      _ = 1 := by rw [hc2, div_self hq']
  have hcont : Continuous fun t : ℝ => (1 : ℂ) / ((c : ℂ) + t * I) :=
    continuous_const.div (by fun_prop) hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t) (hcont.intervalIntegrable _ _)]
  have ha : Real.arctan (-T / c) = -Real.arctan (T / c) := by
    rw [neg_div, Real.arctan_neg]
  have hl : Real.log (c ^ 2 + (-T) ^ 2) = Real.log (c ^ 2 + T ^ 2) := by
    rw [neg_sq]
  simp only [ha, hl]
  push_cast
  ring

/-- **O termo `n = x`**: `|perron 0 c T − ½| ≤ c/(πT)`. -/
theorem perron_zero {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖perron 0 c T - 1 / 2‖ ≤ c / (π * T) := by
  have e : perron 0 c T = (2 * π : ℂ)⁻¹ * ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
    unfold perron
    rw [← integral_um_div hc T]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  have hTc : 0 < T / c := div_pos hT hc
  have hat := Real.arctan_inv_of_pos hTc
  rw [inv_div] at hat
  have hle := Real.arctan_le_self (div_pos hc hT).le
  have hge : 0 ≤ Real.arctan (c / T) := by
    have := Real.arctan_strictMono.monotone (div_pos hc hT).le
    rwa [Real.arctan_zero] at this
  have e2 : perron 0 c T - 1 / 2 = ((-(Real.arctan (c / T) / π)) : ℝ) := by
    rw [e]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hat]
    push_cast
    field_simp
    ring
  rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ Real.pi_pos (by positivity)]
  have : Real.arctan (c / T) * T ≤ c := by
    calc Real.arctan (c / T) * T ≤ c / T * T := mul_le_mul_of_nonneg_right hle hT.le
      _ = c := by field_simp
  nlinarith [Real.pi_pos]

/-- **`|log(N/n)| ≥ 1/(N + 1)`** para `n ≠ 0`, `n ≠ N`. -/
theorem abs_log_ge_N {N n : ℕ} (hN : N ≠ 0) (hn : n ≠ 0) (hnN : n ≠ N) :
    1 / ((N : ℝ) + 1) ≤ |Real.log ((N : ℝ) / n)| := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rcases lt_or_gt_of_ne hnN with h | h
  · -- n ≤ N − 1: log(N/n) ≥ 1 − n/N ≥ 1/N
    have h1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast h
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hN0 hn0)
    rw [inv_div] at hl
    have h2 : 1 / ((N : ℝ) + 1) ≤ 1 - n / N := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < N + 1)]
      rw [sub_mul, div_mul_eq_mul_div, one_mul]
      have : (n : ℝ) * (N + 1) / N = n + n / N := by field_simp
      rw [this]
      have : (n : ℝ) / N < 1 := (div_lt_one hN0).mpr (by linarith)
      linarith
    have hp : 0 < 1 / ((N : ℝ) + 1) := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- n ≥ N + 1: log(n/N) ≥ 1 − N/n ≥ 1/(N + 1)
    have h1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast h
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hN0)
    rw [inv_div] at hl
    have h2 : 1 / ((N : ℝ) + 1) ≤ 1 - N / n := by
      rw [show (1 : ℝ) - N / n = (n - N) / n by field_simp]
      rw [div_le_div_iff₀ (by positivity) hn0]
      nlinarith
    have hlog : Real.log ((N : ℝ) / n) = -Real.log ((n : ℝ) / N) := by
      rw [← Real.log_inv, inv_div]
    have hp : 0 < 1 / ((N : ℝ) + 1) := by positivity
    rw [hlog, abs_neg, abs_of_nonneg (by linarith)]
    linarith

/-- **Perron truncada em `x = N` inteiro** com `|f| ≤ 1`: o degrau vale `½` no termo `n = N`,
`|Σ_{n<N} f(n) n^{−s} + f(N) N^{−s}/2 − (1/2π) ∫_{−T}^{T} F(s + c + it) x^{c+it}/(c + it) dt| ≤
x^c (x + 1 + c) ζ(σ + c)/(πT)`. -/
theorem perron_LSeries_N {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : (N : ℝ) = x)
    {s : ℂ} {c T : ℝ} (hc : 0 < c) (hsc : 1 < s.re + c) (hT : 0 < T) :
    ‖(∑ n ∈ Finset.range N, LSeries.term f s n + LSeries.term f s N / 2) -
      (2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I)‖ ≤
      x ^ c * (x + 1 + c) / (π * T) *
        ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ := by
  have hZ := summable_um (σ := s.re + c) hsc
  have hA := soma_perron (T := T) hf hx hc hsc
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
    linarith
  set w : ℕ → ℂ := fun n => if n < N then 1 else if n = N then 1 / 2 else 0 with hw
  have hB : HasSum (fun n => LSeries.term f s n * w n)
      (∑ n ∈ Finset.range N, LSeries.term f s n + LSeries.term f s N / 2) := by
    have h0 : ∀ n ∉ Finset.range (N + 1), LSeries.term f s n * w n = 0 := by
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      have h1 : ¬ n < N := by omega
      have h2 : n ≠ N := by omega
      simp [hw, h1, h2]
    have hsum : ∑ n ∈ Finset.range (N + 1), LSeries.term f s n * w n =
        ∑ n ∈ Finset.range N, LSeries.term f s n + LSeries.term f s N / 2 := by
      rw [Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_range] at hn
        simp [hw, hn]
      · simp [hw]
        ring
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero h0
  have hE : HasSum (fun n => LSeries.term f s n * (w n - perron (Real.log (x / n)) c T))
      ((∑ n ∈ Finset.range N, LSeries.term f s n + LSeries.term f s N / 2) -
        (2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
          ((c : ℂ) + t * I)) := by
    convert hB.sub hA using 1
    funext n
    ring
  refine hE.norm_le_of_bounded (hZ.hasSum.mul_left (x ^ c * (x + 1 + c) / (π * T))) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hπT : 0 < π * T := mul_pos Real.pi_pos hT
  have h2 : ‖LSeries.term f s n‖ * Real.exp (c * Real.log (x / n)) ≤
      ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c := by
    have e := termo f s (c : ℂ) hx n
    have := congrArg norm e
    rw [norm_mul, norm_mul, ← ofReal_mul, norm_exp_ofReal, norm_cpow_eq_rpow_re_of_pos hx, ofReal_re] at this
    rw [this]
    have h := norm_term_le_um hf (s + c) n
    have hre : (s + (c : ℂ)).re = s.re + c := by simp
    rw [hre] at h
    exact mul_le_mul_of_nonneg_right h (Real.rpow_pos_of_pos hx c).le
  have hK : 0 ≤ ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c := by positivity
  rcases eq_or_ne n N with rfl | hnN
  · -- o termo `n = N`: `log(x/N) = 0`, degrau `½`
    have hl : Real.log (x / n) = 0 := by
      rw [hN, div_self hx.ne', Real.log_one]
    have hwN : w n = 1 / 2 := by simp [hw]
    rw [hl, mul_zero, Real.exp_zero, mul_one] at h2
    have hz := perron_zero hc hT
    calc ‖LSeries.term f s n * (w n - perron (Real.log (x / n)) c T)‖
        = ‖LSeries.term f s n‖ * ‖perron 0 c T - 1 / 2‖ := by
          rw [hl, hwN, norm_mul, norm_sub_rev]
      _ ≤ (‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c) * (c / (π * T)) :=
          mul_le_mul h2 hz (norm_nonneg _) hK
      _ ≤ (‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c) * ((x + 1 + c) / (π * T)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact div_le_div_of_nonneg_right (by linarith) hπT.le
      _ = x ^ c * (x + 1 + c) / (π * T) * ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ := by
          ring
  · -- `n ≠ N`: `|log(x/n)| ≥ 1/(x + 1)` e o degrau é `0` ou `1`
    have hab := abs_log_ge_N hN0 hn hnN
    rw [hN] at hab
    have hp : 0 < 1 / (x + 1) := by positivity
    have hL : Real.log (x / n) ≠ 0 := fun h => by
      rw [h, abs_zero] at hab
      linarith
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hwn : w n = if 0 < Real.log (x / n) then 1 else 0 := by
      rcases lt_or_gt_of_ne hnN with h | h
      · have hpos : 0 < Real.log (x / n) := by
          apply Real.log_pos
          rw [one_lt_div hn0, ← hN]
          exact_mod_cast h
        simp [hw, h, hpos]
      · have hneg : Real.log (x / n) < 0 := by
          apply Real.log_neg (div_pos hx hn0)
          rw [div_lt_one hn0, ← hN]
          exact_mod_cast h
        have h1 : ¬ n < N := by omega
        simp [hw, h1, hnN, not_lt.mpr hneg.le]
    have h1 := perron_degrau hL hc hT
    have h3 : 1 / |Real.log (x / n)| ≤ x + 1 := by
      rw [one_div_le (abs_pos.mpr hL) (by linarith), ]
      exact hab
    calc ‖LSeries.term f s n * (w n - perron (Real.log (x / n)) c T)‖
        = ‖LSeries.term f s n‖ *
          ‖perron (Real.log (x / n)) c T - (if 0 < Real.log (x / n) then (1 : ℂ) else 0)‖ := by
          rw [hwn, norm_mul, norm_sub_rev]
      _ ≤ ‖LSeries.term f s n‖ * (Real.exp (c * Real.log (x / n)) / (π * T * |Real.log (x / n)|)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖LSeries.term f s n‖ * Real.exp (c * Real.log (x / n))) * (1 / |Real.log (x / n)|) /
            (π * T) := by ring
      _ ≤ (‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c) * (x + 1 + c) / (π * T) := by
          apply div_le_div_of_nonneg_right _ hπT.le
          exact mul_le_mul h2 (h3.trans (by linarith)) (by positivity) hK
      _ = x ^ c * (x + 1 + c) / (π * T) * ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ := by
          ring

/-! ## 2. `ψ₀` -/

/-- **`ψ₀(N) = ψ(N) − Λ(N)/2`**: a média dos limites laterais de `ψ` em `N`. -/
noncomputable def psi0 (N : ℕ) : ℝ := Chebyshev.psi N - ArithmeticFunction.vonMangoldt N / 2

theorem soma_fL_N (η : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, LSeries.term (fL η) (-(η : ℂ)) n + LSeries.term (fL η) (-(η : ℂ)) N / 2 =
      ((η * psi0 N : ℝ) : ℂ) := by
  simp_rw [term_fL_neg]
  unfold psi0
  rw [ATK.ZeroClasses.PNT.psi_eq_range (N : ℝ) (N := N + 1) (by simp), Finset.sum_range_succ]
  push_cast
  rw [← Finset.mul_sum]
  ring

/-- **Perron para `ψ₀`**: `η |ψ₀(N) − (1/2π) ∫ F(c + it) dt| ≤ x^c(x + 1 + c)/(πT) · 8/(c − η − 1)`, `x = N`. -/
theorem perron_psi0 {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : (N : ℝ) = x)
    {η c T : ℝ} (hη : 0 < η) (hc1 : 1 < c - η) (hc2 : c - η ≤ 2) (hT : 0 < T) :
    η * ‖(psi0 N : ℂ) - (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)‖ ≤
      x ^ c * (x + 1 + c) / (π * T) * (8 / (c - η - 1)) := by
  have hc0 : 0 < c := by linarith
  have hsc : 1 < (-(η : ℂ)).re + c := by
    rw [neg_re, ofReal_re]
    linarith
  have hP := perron_LSeries_N (f := fL η) (norm_fL_le hη) hx hN (s := -(η : ℂ)) (c := c) (T := T) hc0 hsc hT
  have hint : ∫ t in (-T)..T, LSeries (fL η) (-(η : ℂ) + ((c : ℂ) + t * I)) *
      (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) =
      (η : ℂ) * ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) *
        (-logDeriv riemannZeta ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : 1 < ((c : ℂ) + t * I).re := by simp; linarith
    simp only [LSeries_fL η hre]
    ring
  rw [soma_fL_N, hint] at hP
  have hσ' : (-(η : ℂ)).re + c = c - η := by rw [neg_re, ofReal_re]; ring
  rw [hσ'] at hP
  have htsum := tsum_um_le (σ := c - η) hc1 hc2
  have hpos : 0 ≤ x ^ c * (x + 1 + c) / (π * T) := by
    positivity
  have e : ((η * psi0 N : ℝ) : ℂ) - (2 * π : ℂ)⁻¹ * ((η : ℂ) *
      ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)) =
      (η : ℂ) * ((psi0 N : ℂ) - (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)) := by
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη] at hP
  calc _ ≤ _ := hP
    _ ≤ _ := mul_le_mul_of_nonneg_left htsum hpos

/-! ## 3. A fórmula explícita em `x = N` -/

/-- **A fórmula explícita com erro, `x = N` inteiro**: para `N ≥ 2` e cada `k`, há uma altura boa `T ∈ [k + 6, k + 7]`
com `‖Σ_{|γ|≤T} m_ρ N^ρ/ρ − (N + Σ_{n<k+7} N^{−2(n+1)}/(2(n+1)) − log 2π − ψ₀(N))‖ ≤ ε_k`. -/
theorem explicita_k_N {x : ℝ} {N : ℕ} (hx : 1 < x) (hN : (N : ℝ) = x) :
    ∃ C₁ c₀ B : ℝ, ∀ k : ℕ, ∃ T : ℝ, (k : ℝ) + 6 ≤ T ∧ T ≤ k + 7 ∧
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ riemannZeta u = 0 ∧ 0 < u.re ∧ |u.im| ≤ T) ∧
      ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px x u -
        ((x : ℂ) + ∑ n ∈ Finset.range (k + 7), (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) -
          (Real.log (2 * π) : ℂ) - (psi0 N : ℂ))‖ ≤ epsx x ((x + 1 + 2)) C₁ c₀ B k := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := ATK.ZeroClasses.Explicita.altura_boa
  obtain ⟨c₀, hc₀⟩ := ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
  obtain ⟨B, hB0, hB⟩ := digamma_esq
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  refine ⟨C₁, c₀, B, fun k => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  obtain ⟨T, hT1, hT2', hgood⟩ := hC₁ ((k : ℝ) + 6) (by linarith)
  have hT2 : T ≤ k + 7 := by linarith
  have hT0 : 0 < T := by linarith
  have hT6 : 6 ≤ T := by linarith
  have hKr : ((k + 7 : ℕ) : ℝ) = (k : ℝ) + 7 := by push_cast; ring
  have hK1 : 1 ≤ k + 7 := by omega
  have hbd : ∀ s : ℂ, 0 < s.re → s.re < 1 → (s.im = -T ∨ s.im = T) → riemannZeta s ≠ 0 := by
    intro s h0 h1 him
    have := (hgood s.re h0 (by linarith) s.im him.symm).1
    rwa [Complex.re_add_im] at this
  obtain ⟨S, hS, hbordo⟩ :=
    ATK.ZeroClasses.FormulaExplicita.bordo_largo hx0 (c := 2) (by norm_num) hT0 (k + 7) hbd
  refine ⟨T, hT1, hT2, S, fun u => ?_, ?_⟩
  · rw [hS u]
    constructor
    · rintro ⟨huR, hz, hre⟩
      have him := (mem_reProdIm.mp huR).2
      change u.im ∈ [[-T, T]] at him
      rw [uIcc_of_le (by linarith)] at him
      exact ⟨hz, hre, abs_le.mpr ⟨him.1, him.2⟩⟩
    · rintro ⟨hz, hre, him⟩
      have hu1 : u.re < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
      refine ⟨mem_reProdIm.mpr ⟨?_, ?_⟩, hz, hre⟩
      · change u.re ∈ [[-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2), 2]]
        rw [uIcc_of_le (by rw [hKr]; linarith)]
        exact ⟨by rw [hKr]; linarith, by linarith⟩
      · change u.im ∈ [[-T, T]]
        rw [uIcc_of_le (by linarith)]
        exact abs_le.mp him
  · set R : ℂ := ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px x u with hR
    set Q : ℂ := ∑ n ∈ Finset.range (k + 7), (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1))
      with hQ
    set ℓ : ℂ := (Real.log (2 * π) : ℂ) with hℓ
    set Bh : ℂ := ∫ u in (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2))..2, Fx x ((u : ℂ) + ((-T : ℝ) : ℂ) * I)
      with hBh
    set Tp : ℂ := ∫ u in (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2))..2, Fx x ((u : ℂ) + (T : ℂ) * I) with hTp
    set Vc : ℂ := ∫ t in (-T)..T, (x : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) *
      (-logDeriv riemannZeta (((2 : ℝ) : ℂ) + t * I)) / (((2 : ℝ) : ℂ) + t * I) with hVc
    set Vl : ℂ := ∫ y in (-T)..T, Fx x (((-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2) : ℝ) : ℂ) + (y : ℂ) * I)
      with hVl
    have hunf : bordo (Fx x) ⟨-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2), -T⟩ ⟨2, T⟩ =
        Bh - Tp + I • Vc - I • Vl := rfl
    rw [hunf, smul_eq_mul, smul_eq_mul] at hbordo
    -- (1) Perron
    have hP := perron_psi0 hx0 hN (η := 1 / 2) (c := 2) (T := T) (by norm_num) (by norm_num) (by norm_num) hT0
    rw [← hVc] at hP
    have hPerron : ‖(psi0 N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤
        32 * x ^ (2 : ℝ) * ((x + 1 + 2)) / (π * ((k : ℝ) + 6)) := by
      have e16 : (8 : ℝ) / (2 - 1 / 2 - 1) = 16 := by norm_num
      rw [e16] at hP
      have h1 : ‖(psi0 N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤ 32 * x ^ (2 : ℝ) * ((x + 1 + 2)) / (π * T) := by
        have e : 32 * x ^ (2 : ℝ) * ((x + 1 + 2)) / (π * T) = 2 * (x ^ (2 : ℝ) * ((x + 1 + 2)) / (π * T) * 16) := by
          ring
        rw [e]
        linarith
      refine h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
      exact mul_le_mul_of_nonneg_left hT1 Real.pi_pos.le
    -- (2) o retângulo
    have h2 : I * (Vc - 2 * π * (x - R + Q - ℓ)) = Tp - Bh + I * Vl := by linear_combination hbordo
    have h3 : ‖Vc - 2 * π * (x - R + Q - ℓ)‖ ≤ ‖Bh‖ + ‖Tp‖ + ‖Vl‖ := by
      have h := congrArg norm h2
      rw [norm_mul, Complex.norm_I, one_mul] at h
      rw [h]
      have a1 := norm_add_le (Tp - Bh) (I * Vl)
      have a2 := norm_sub_le Tp Bh
      rw [norm_mul, Complex.norm_I, one_mul] at a1
      linarith
    have hπ : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hcont : ‖(2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ)‖ ≤ (‖Bh‖ + ‖Tp‖ + ‖Vl‖) / (2 * π) := by
      have e : (2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ) = (2 * π : ℂ)⁻¹ * (Vc - 2 * π * (x - R + Q - ℓ)) := by
        field_simp
      rw [e, norm_mul, norm_inv, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right h3 (by positivity)
    -- (3) as horizontais
    have hU0 : (0 : ℝ) ≤ 2 * ((k + 7 : ℕ) : ℝ) + 1 / 2 := by positivity
    have hl0 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
    have hA2 : 2 ≤ C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 20 := by
      have : 0 ≤ C₁ * Real.log (2 + T) ^ 2 := by positivity
      linarith
    have hhor : ∀ τ : ℝ, (τ = T ∨ τ = -T) →
        ‖∫ σ in (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2))..2, Fx x ((σ : ℂ) + τ * I)‖ ≤
          x ^ (2 : ℝ) * ((C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 20 - 2) / Real.log x +
            1 / Real.log x ^ 2) / T := by
      intro τ hτ
      have hτabs : |τ| = T := by
        rcases hτ with h | h <;> rw [h]
        · exact abs_of_pos hT0
        · rw [abs_neg]; exact abs_of_pos hT0
      exact hor_le hx hT0 hU0 hA2 hτabs fun σ _ hσ => logDeriv_hor hC₁0 hT6 hc₀ hgood hσ hτ
    have hBhb := hhor (-T) (Or.inr rfl)
    have hTpb := hhor T (Or.inl rfl)
    have hH : x ^ (2 : ℝ) * ((C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 20 - 2) / Real.log x +
        1 / Real.log x ^ 2) / T ≤ x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ +
          Real.log ((k : ℝ) + 9) + 18) / Real.log x + 1 / Real.log x ^ 2) / ((k : ℝ) + 6) := by
      have hlk : Real.log (2 + T) ≤ Real.log ((k : ℝ) + 9) := Real.log_le_log (by linarith) (by linarith)
      have hsq : Real.log (2 + T) ^ 2 ≤ Real.log ((k : ℝ) + 9) ^ 2 := pow_le_pow_left₀ hl0 hlk 2
      have hlk0 : 0 ≤ Real.log ((k : ℝ) + 9) := hl0.trans hlk
      have hn : C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 20 - 2 ≤
          C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18 := by
        have := mul_le_mul_of_nonneg_left hsq hC₁0
        linarith
      have hnum : (C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 20 - 2) / Real.log x +
          1 / Real.log x ^ 2 ≤ (C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18) /
            Real.log x + 1 / Real.log x ^ 2 := by
        have := div_le_div_of_nonneg_right hn hL.le
        linarith
      have hx2 : 0 ≤ x ^ (2 : ℝ) := by positivity
      have hpos : 0 ≤ x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18) /
          Real.log x + 1 / Real.log x ^ 2) := by
        have : 0 ≤ C₁ * Real.log ((k : ℝ) + 9) ^ 2 := by positivity
        have : 0 ≤ (C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18) / Real.log x :=
          div_nonneg (by linarith) hL.le
        positivity
      exact div_le_div₀ hpos (mul_le_mul_of_nonneg_left hnum hx2) (by positivity) hT1
    -- (4) a reta esquerda
    have hM0 : 0 ≤ c₀ + B + Real.log (2 + T) + 4 * ((k + 7 : ℕ) : ℝ) + 8 := by positivity
    have hU : (0 : ℝ) < 2 * ((k + 7 : ℕ) : ℝ) + 1 / 2 := by positivity
    have hVlb := esq_le hx hT0.le hU hM0 (fun y hy => by
      have h := logDeriv_esq_reta hc₀ hB hK1 y
      have : Real.log (2 + |y|) ≤ Real.log (2 + T) := Real.log_le_log (by positivity) (by linarith)
      linarith)
    have hVle : x ^ (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2)) * (c₀ + B + Real.log (2 + T) + 4 * ((k + 7 : ℕ) : ℝ) + 8) /
        (2 * ((k + 7 : ℕ) : ℝ) + 1 / 2) * (2 * T) ≤
        2 * ((k : ℝ) + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) * ((x ^ 2)⁻¹) ^ (k + 7) := by
      have hxU : x ^ (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2)) ≤ ((x ^ 2)⁻¹) ^ (k + 7) := by
        have h1 : x ^ (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2)) ≤ x ^ (-(2 * ((k + 7 : ℕ) : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
        have h2 : x ^ (-(2 * ((k + 7 : ℕ) : ℝ))) = ((x ^ 2)⁻¹) ^ (k + 7) := by
          rw [Real.rpow_neg hx0.le, show (2 * ((k + 7 : ℕ) : ℝ)) = ((2 * (k + 7) : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast, pow_mul, inv_pow]
        rw [h2] at h1
        exact h1
      have hlogT : Real.log (2 + T) ≤ T + 1 := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 2 + T)
        linarith
      have hMb : c₀ + B + Real.log (2 + T) + 4 * ((k + 7 : ℕ) : ℝ) + 8 ≤ c₀ + B + 10 + 5 * ((k : ℝ) + 7) := by
        rw [hKr]; linarith
      have hMU : (c₀ + B + Real.log (2 + T) + 4 * ((k + 7 : ℕ) : ℝ) + 8) / (2 * ((k + 7 : ℕ) : ℝ) + 1 / 2) ≤
          c₀ + B + Real.log (2 + T) + 4 * ((k + 7 : ℕ) : ℝ) + 8 :=
        div_le_self hM0 (by rw [hKr]; linarith)
      have hxs : 0 ≤ x ^ (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2)) := Real.rpow_nonneg hx0.le _
      have hr : 0 ≤ ((x ^ 2)⁻¹) ^ (k + 7) := by positivity
      calc x ^ (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2)) * (c₀ + B + Real.log (2 + T) + 4 * ((k + 7 : ℕ) : ℝ) + 8) /
            (2 * ((k + 7 : ℕ) : ℝ) + 1 / 2) * (2 * T)
          = x ^ (-(2 * ((k + 7 : ℕ) : ℝ) + 1 / 2)) * ((c₀ + B + Real.log (2 + T) + 4 * ((k + 7 : ℕ) : ℝ) + 8) /
            (2 * ((k + 7 : ℕ) : ℝ) + 1 / 2)) * (2 * T) := by ring
        _ ≤ ((x ^ 2)⁻¹) ^ (k + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) * (2 * ((k : ℝ) + 7)) := by
          apply mul_le_mul (mul_le_mul hxU (hMU.trans hMb) (div_nonneg hM0 hU.le) hr) (by linarith)
            (by linarith) (mul_nonneg hr (by linarith))
        _ = 2 * ((k : ℝ) + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) * ((x ^ 2)⁻¹) ^ (k + 7) := by ring
    -- (5) a soma
    have hfin : ‖R - (x + Q - ℓ - (psi0 N : ℂ))‖ ≤
        ‖(psi0 N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ + ‖(2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ)‖ := by
      have e : R - (x + Q - ℓ - (psi0 N : ℂ)) =
          ((psi0 N : ℂ) - (2 * π : ℂ)⁻¹ * Vc) + ((2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ)) := by ring
      rw [e]
      exact norm_add_le _ _
    have hsum : (‖Bh‖ + ‖Tp‖ + ‖Vl‖) / (2 * π) ≤
        (2 * (x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18) /
          Real.log x + 1 / Real.log x ^ 2) / ((k : ℝ) + 6)) +
          2 * ((k : ℝ) + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) * ((x ^ 2)⁻¹) ^ (k + 7)) / (2 * π) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    unfold epsx
    linarith

/-- **A fórmula explícita, `x = N` inteiro** (sem hipóteses): para `N ≥ 2`, ao longo de alturas boas
`T_k ∈ [k + 6, k + 7]`, `Σ_{|γ| ≤ T_k} m_ρ N^ρ/ρ → N − ψ₀(N) − log 2π − ½ log(1 − N^{−2})`. -/
theorem formula_explicita_N {x : ℝ} {N : ℕ} (hx : 1 < x) (hN : (N : ℝ) = x)
    : ∃ T : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 6 ≤ T k ∧ T k ≤ k + 7) ∧
    ∃ S : ℕ → Finset ℂ, (∀ k u, u ∈ S k ↔ riemannZeta u = 0 ∧ 0 < u.re ∧ |u.im| ≤ T k) ∧
      Tendsto (fun k => ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u) atTop
        (𝓝 ((x : ℂ) - psi0 N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))) := by
  obtain ⟨C₁, c₀, B, h⟩ := explicita_k_N hx hN
  choose T hT1 hT2 S hS hb using h
  refine ⟨T, fun k => ⟨hT1 k, hT2 k⟩, S, hS, ?_⟩
  have hQ := (ATK.ZeroClasses.ExplicitaLimite.triv_soma hx).comp (tendsto_add_atTop_nat 7)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hQ ⊢
  have hlim := (epsx_tendsto (P := (x + 1 + 2)) (C₁ := C₁) (c₀ := c₀) (B := B) hx).add hQ
  rw [zero_add] at hlim
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
  simp only [Function.comp_apply]
  set R : ℂ := ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u
  set Q : ℂ := ∑ n ∈ Finset.range (k + 7), (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1))
  have e : R - ((x : ℂ) - psi0 N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹)) =
      (R - ((x : ℂ) + Q - (Real.log (2 * π) : ℂ) - (psi0 N : ℂ))) +
        (Q - ((1 / 2 * -Real.log (1 - (x ^ 2)⁻¹) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hb k) le_rfl)

/-- **A fórmula explícita com `T → ∞`, `x = N` inteiro**: para `N ≥ 2`,
`Σ_{|γ| ≤ T} m_ρ N^ρ/ρ → N − ψ₀(N) − log 2π − ½ log(1 − N^{−2})` quando `T → ∞`. -/
theorem formula_explicita_T_N {x : ℝ} {N : ℕ} (hx : 1 < x) (hN : (N : ℝ) = x)
    :
    Tendsto (fun T : ℝ => ∑ ρ ∈ ATK.ZeroClasses.ExplicitaT.Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ) atTop
      (𝓝 ((x : ℂ) - psi0 N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))) := by
  obtain ⟨Tk, hTk, S, hS, hlim⟩ := formula_explicita_N hx hN
  have hSZ : ∀ k, S k = ATK.ZeroClasses.ExplicitaT.Zfin (Tk k) := fun k => by
    ext u
    rw [hS, ATK.ZeroClasses.ExplicitaT.mem_Zfin]
  have hx1 : 1 ≤ x := hx.le
  have hl0 := l0_pos
  set e : ℕ → ℝ := fun k => 2 * (4 * ((a0 + Real.log ((k : ℝ) + 9)) / l0) * (x / ((k : ℝ) + 6)))
    with he_def
  have he : Tendsto e atTop (𝓝 0) := by
    have := ((ATK.ZeroClasses.ExplicitaLimite.lim_log 0).const_mul (8 * a0 * x / l0)).add
      ((ATK.ZeroClasses.ExplicitaLimite.lim_log 1).const_mul (8 * x / l0))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    have hk : (k : ℝ) + 6 ≠ 0 := by positivity
    simp only [he_def, pow_zero, pow_one]
    field_simp
    ring
  rw [Metric.tendsto_atTop] at hlim he ⊢
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := hlim (ε / 2) (by linarith)
  obtain ⟨K₂, hK₂⟩ := he (ε / 2) (by linarith)
  refine ⟨(max K₁ K₂ : ℕ) + 6, fun T hT => ?_⟩
  have hT6 : (6 : ℝ) ≤ T := by
    have : (0 : ℝ) ≤ (max K₁ K₂ : ℕ) := Nat.cast_nonneg _
    linarith
  have hfl : max K₁ K₂ + 6 ≤ ⌊T⌋₊ := Nat.le_floor (by push_cast at hT ⊢; linarith)
  set k : ℕ := ⌊T⌋₊ - 6 with hk
  have hkr : (k : ℝ) = (⌊T⌋₊ : ℝ) - 6 := by
    rw [hk, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hk1 : (k : ℝ) + 6 ≤ T := by rw [hkr]; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ T)]
  have hk2 : T ≤ (k : ℝ) + 7 := by rw [hkr]; linarith [Nat.lt_floor_add_one T]
  have hkK : max K₁ K₂ ≤ k := by omega
  have hd := ATK.ZeroClasses.ExplicitaT.dif_le hx1 k hk1 hk2 (hTk k).1 (hTk k).2
  rw [← hSZ k] at hd
  have hA := hK₁ k (le_of_max_le_left hkK)
  have hB := hK₂ k (le_of_max_le_right hkK)
  rw [Real.dist_eq, sub_zero] at hB
  rw [dist_eq_norm] at hA ⊢
  have hBabs : e k < ε / 2 := (le_abs_self _).trans_lt hB
  calc ‖∑ ρ ∈ ATK.ZeroClasses.ExplicitaT.Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ -
        ((x : ℂ) - psi0 N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))‖
      ≤ ‖∑ ρ ∈ ATK.ZeroClasses.ExplicitaT.Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ -
          ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u‖ +
        ‖∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u -
          ((x : ℂ) - psi0 N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hd.trans hBabs.le) hA
    _ = ε := by ring

/-! ## 4. Todo `x > 1` -/

/-- **`ψ₀(x)`** para `x` real: `ψ(x)` fora dos inteiros e `ψ(N) − Λ(N)/2` em `x = N`. -/
noncomputable def psiZero (x : ℝ) : ℝ :=
  Chebyshev.psi x - if ((⌊x⌋₊ : ℕ) : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0

/-- **A fórmula explícita de Riemann–von Mangoldt para todo `x > 1`**:
`lim_{T → ∞} Σ_{|γ| ≤ T} m_ρ x^ρ/ρ = x − ψ₀(x) − log 2π − ½ log(1 − x^{−2})`. -/
theorem formula_explicita_T_real {x : ℝ} (hx : 1 < x) :
    Tendsto (fun T : ℝ => ∑ ρ ∈ ATK.ZeroClasses.ExplicitaT.Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ) atTop
      (𝓝 ((x : ℂ) - psiZero x - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))) := by
  have hx0 : 0 ≤ x := by linarith
  by_cases h : ((⌊x⌋₊ : ℕ) : ℝ) = x
  · have e : psiZero x = psi0 ⌊x⌋₊ := by
      unfold psiZero psi0
      simp [h]
    rw [e]
    exact formula_explicita_T_N hx h
  · have e : psiZero x = Chebyshev.psi x := by
      unfold psiZero
      simp [h]
    rw [e]
    have hfl := Nat.floor_le hx0
    have hfl1 := Nat.lt_floor_add_one x
    have ha : 0 < x - ⌊x⌋₊ := lt_of_le_of_ne (sub_nonneg.mpr hfl) (fun h' => h (by linarith))
    have hb : 0 < (⌊x⌋₊ : ℝ) + 1 - x := by linarith
    refine ATK.ZeroClasses.ExplicitaReal.formula_explicita_T_x (d := min (x - ⌊x⌋₊) ((⌊x⌋₊ : ℝ) + 1 - x)) hx
      (lt_min ha hb) ((min_le_left _ _).trans (by linarith)) fun n => ?_
    rcases le_or_gt n ⌊x⌋₊ with hn | hn
    · have hn' : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
      rw [abs_of_nonneg (by linarith)]
      exact (min_le_left _ _).trans (by linarith)
    · have hn' : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      rw [abs_of_neg (by linarith)]
      exact (min_le_right _ _).trans (by linarith)

end ATK.ZeroClasses.ExplicitaInteira

#print axioms ATK.ZeroClasses.ExplicitaInteira.integral_um_div
#print axioms ATK.ZeroClasses.ExplicitaInteira.perron_zero
#print axioms ATK.ZeroClasses.ExplicitaInteira.abs_log_ge_N
#print axioms ATK.ZeroClasses.ExplicitaInteira.perron_LSeries_N
#print axioms ATK.ZeroClasses.ExplicitaInteira.soma_fL_N
#print axioms ATK.ZeroClasses.ExplicitaInteira.perron_psi0
#print axioms ATK.ZeroClasses.ExplicitaInteira.explicita_k_N
#print axioms ATK.ZeroClasses.ExplicitaInteira.formula_explicita_N
#print axioms ATK.ZeroClasses.ExplicitaInteira.formula_explicita_T_N
#print axioms ATK.ZeroClasses.ExplicitaInteira.formula_explicita_T_real
