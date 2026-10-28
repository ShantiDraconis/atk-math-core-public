import ATK.ZeroClasses.ExplicitaT

/-!
# A fórmula explícita para `x` real (rodada 77)

As rodadas 71–72 deram a fórmula explícita em `x = N + ½`. Aqui ela vale para **todo `x > 1` não inteiro**:

  **`lim_{T → ∞} Σ_{|γ| ≤ T} m_ρ x^ρ/ρ = x − ψ(x) − log 2π − ½ log(1 − x^{−2})`**   (`formula_explicita_T_x`),

com `ψ(x) = Σ_{n ≤ x} Λ(n)` (para `x` não inteiro, `ψ₀(x) = ψ(x)`). O único ponto em que `x = N + ½` entrava era a
Perron truncada, pela cota `|log(x/n)| ≥ 1/(4x + 2)`; para `x` a distância `≥ d > 0` dos inteiros vale
`|log(x/n)| ≥ d/(2x + 2)` (`abs_log_ge_x`), e o resto da cadeia (rodadas 45, 64, 70–72) se repete com a constante de
Perron `(2x + 2)/d` no lugar de `4x + 2`:

* `perron_LSeries_x`, `perron_psi_x`: Perron truncada para `x` real;
* `epsx`, `epsx_tendsto`: o erro da altura `k` com constante de Perron `P`;
* `explicita_k_x`, `formula_explicita_x`: a fórmula com erro e o limite em alturas boas;
* `formula_explicita_T_x`: o limite com `T → ∞` qualquer.

Classificação (rodada 77): **consequência**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.ExplicitaReal

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret)
open ATK.ZeroClasses.Perron (perron perron_degrau)
open ATK.ZeroClasses.PerronD (soma_perron summable_um termo norm_term_le_um)
open ATK.ZeroClasses.PsiRH (Fx px norm_Fx fL norm_fL_le term_fL_neg LSeries_fL tsum_um_le)
open ATK.ZeroClasses.ExplicitaLimite
open ATK.ZeroClasses.SomaZeros (a0 l0 l0_pos)

/-! ## 1. Perron truncada para `x` real -/

/-- **`|log(x/n)| ≥ d/(2x + 2)`** se `|x − m| ≥ d` para todo inteiro `m ≥ 0`. -/
theorem abs_log_ge_x {x d : ℝ} (hx : 0 < x) (hd0 : 0 < d) (hd1 : d ≤ 1) (hd : ∀ n : ℕ, d ≤ |x - n|)
    {n : ℕ} (hn : n ≠ 0) : d / (2 * x + 2) ≤ |Real.log (x / n)| := by
  have hm : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  have hm0 : (0 : ℝ) < n := by linarith
  have hD : 0 < 2 * x + 2 := by linarith
  have hdn := hd n
  have hk : d / (2 * x + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]
    linarith
  rcases le_or_gt (n : ℝ) x with h | h
  · have hxn : d ≤ x - n := by rwa [abs_of_nonneg (by linarith)] at hdn
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx hm0)
    rw [inv_div] at hl
    have h2 : d / x ≤ 1 - n / x := by
      rw [show 1 - (n : ℝ) / x = (x - n) / x by field_simp]
      exact div_le_div_of_nonneg_right hxn hx.le
    have h3 : d / (2 * x + 2) ≤ d / x := div_le_div_of_nonneg_left hd0.le hx (by linarith)
    have hpos : 0 ≤ Real.log (x / n) := by
      have : 0 < d / x := by positivity
      linarith
    rw [abs_of_nonneg hpos]
    linarith
  · have hnx : d ≤ n - x := by rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at hdn
    have e : Real.log (x / n) = -Real.log (n / x) := by rw [← Real.log_inv, inv_div]
    have key : d / (2 * x + 2) ≤ Real.log (n / x) := by
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos hm0 hx)
      rw [inv_div] at hl
      rcases le_or_gt (n : ℝ) (2 * x + 2) with h2 | h2
      · have h4 : d / (2 * x + 2) ≤ 1 - x / n := by
          rw [show 1 - x / (n : ℝ) = (n - x) / n by field_simp]
          calc d / (2 * x + 2) ≤ d / n := div_le_div_of_nonneg_left hd0.le hm0 h2
            _ ≤ (n - x) / n := div_le_div_of_nonneg_right hnx hm0.le
        linarith
      · have h6 : Real.log 2 ≤ Real.log (n / x) :=
          Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hx]; linarith)
        have h7 := Real.log_two_gt_d9
        linarith
    have hk0 : 0 < d / (2 * x + 2) := by positivity
    rw [e, abs_neg, abs_of_nonneg (by linarith)]
    exact key

theorem log_ne_zero_x {x d : ℝ} (hx : 0 < x) (hd0 : 0 < d) (hd1 : d ≤ 1) (hd : ∀ n : ℕ, d ≤ |x - n|)
    {n : ℕ} (hn : n ≠ 0) : Real.log (x / n) ≠ 0 := by
  intro h
  have := abs_log_ge_x hx hd0 hd1 hd hn
  rw [h, abs_zero] at this
  have : 0 < d / (2 * x + 2) := by positivity
  linarith

theorem inv_abs_log_le_x {x d : ℝ} (hx : 0 < x) (hd0 : 0 < d) (hd1 : d ≤ 1) (hd : ∀ n : ℕ, d ≤ |x - n|)
    {n : ℕ} (hn : n ≠ 0) : 1 / |Real.log (x / n)| ≤ (2 * x + 2) / d := by
  rw [one_div_le (abs_pos.mpr (log_ne_zero_x hx hd0 hd1 hd hn)) (by positivity), one_div_div]
  exact abs_log_ge_x hx hd0 hd1 hd hn

theorem soma_fL_x (η x : ℝ) :
    ∑ n ∈ Finset.range (⌊x⌋₊ + 1), LSeries.term (fL η) (-(η : ℂ)) n =
      ((η * Chebyshev.psi x : ℝ) : ℂ) := by
  simp_rw [term_fL_neg]
  rw [ATK.ZeroClasses.PNT.psi_eq_range x (N := ⌊x⌋₊ + 1) rfl, Finset.mul_sum, Complex.ofReal_sum]

/-- **Perron truncada para `x` real** com `|f| ≤ 1`, `|x − n| ≥ d` para todo `n`:
`|Σ_{n ≤ N} f(n) n^{−s} − (1/2π) ∫_{−T}^{T} F(s + c + it) x^{c+it}/(c + it) dt| ≤ x^c ((2x + 2)/d) ζ(σ + c)/(πT)`. -/
theorem perron_LSeries_x {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {x d : ℝ} (hx : 0 < x) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hd : ∀ n : ℕ, d ≤ |x - n|) {s : ℂ} {c T : ℝ} (hc : 0 < c)
    (hsc : 1 < s.re + c) (hT : 0 < T) :
    ‖∑ n ∈ Finset.range (⌊x⌋₊ + 1), LSeries.term f s n -
      (2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I)‖ ≤
      x ^ c * ((2 * x + 2) / d) / (π * T) *
        ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ := by
  have hZ := summable_um (σ := s.re + c) hsc
  have hA := soma_perron (T := T) hf hx hc hsc
  -- o degrau como série finita
  have hB : HasSum (fun n => LSeries.term f s n * (if 0 < Real.log (x / n) then (1 : ℂ) else 0))
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), LSeries.term f s n) := by
    have h0 : ∀ n ∉ Finset.range (⌊x⌋₊ + 1),
        LSeries.term f s n * (if 0 < Real.log (x / n) then (1 : ℂ) else 0) = 0 := by
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      have hn0 : n ≠ 0 := by omega
      have hm0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have hneg : Real.log (x / n) < 0 := by
        apply Real.log_neg (div_pos hx hm0)
        rw [div_lt_one hm0]
        have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
        linarith [Nat.lt_floor_add_one x]
      simp [not_lt.mpr hneg.le]
    have hsum : ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        LSeries.term f s n * (if 0 < Real.log (x / n) then (1 : ℂ) else 0) =
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), LSeries.term f s n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have hm0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        have hpos : 0 < Real.log (x / n) := by
          rw [Finset.mem_range] at hn
          apply Real.log_pos
          rw [one_lt_div hm0]
          have h1 : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp hn
          have h2 : (n : ℝ) ≤ x := h1.trans (Nat.floor_le hx.le)
          have h3 := hd n
          rcases h2.lt_or_eq with h4 | h4
          · exact h4
          · rw [h4, sub_self, abs_zero] at h3
            linarith
        simp [hpos]
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero h0
  have hE : HasSum (fun n => LSeries.term f s n *
      ((if 0 < Real.log (x / n) then (1 : ℂ) else 0) - perron (Real.log (x / n)) c T))
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), LSeries.term f s n -
        (2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
          ((c : ℂ) + t * I)) := by
    convert hB.sub hA using 1
    funext n
    ring
  refine hE.norm_le_of_bounded (hZ.hasSum.mul_left (x ^ c * ((2 * x + 2) / d) / (π * T))) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hL := log_ne_zero_x hx hd0 hd1 hd hn
  have h1 := perron_degrau hL hc hT
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
  have h3 := inv_abs_log_le_x hx hd0 hd1 hd hn
  have hπT : 0 < π * T := mul_pos Real.pi_pos hT
  calc ‖LSeries.term f s n *
        ((if 0 < Real.log (x / n) then (1 : ℂ) else 0) - perron (Real.log (x / n)) c T)‖
      = ‖LSeries.term f s n‖ *
        ‖perron (Real.log (x / n)) c T - (if 0 < Real.log (x / n) then (1 : ℂ) else 0)‖ := by
        rw [norm_mul, norm_sub_rev]
    _ ≤ ‖LSeries.term f s n‖ * (Real.exp (c * Real.log (x / n)) / (π * T * |Real.log (x / n)|)) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (‖LSeries.term f s n‖ * Real.exp (c * Real.log (x / n))) * (1 / |Real.log (x / n)|) /
          (π * T) := by ring
    _ ≤ (‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c) * ((2 * x + 2) / d) / (π * T) := by
        apply div_le_div_of_nonneg_right _ hπT.le
        exact mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = x ^ c * ((2 * x + 2) / d) / (π * T) *
          ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ := by ring

/-- **Perron para `ψ`, `x` real**: `|ψ(x) − (1/2π) ∫ F(c + it) dt| ≤ x^c((2x + 2)/d)/(πT) · 8/((c − η − 1)η)`. -/
theorem perron_psi_x {x d : ℝ} (hx : 0 < x) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hd : ∀ n : ℕ, d ≤ |x - n|) {η c T : ℝ} (hη : 0 < η) (hc1 : 1 < c - η) (hc2 : c - η ≤ 2) (hT : 0 < T) :
    η * ‖(Chebyshev.psi x : ℂ) - (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)‖ ≤
      x ^ c * ((2 * x + 2) / d) / (π * T) * (8 / (c - η - 1)) := by
  have hc0 : 0 < c := by linarith
  have hsc : 1 < (-(η : ℂ)).re + c := by
    rw [neg_re, ofReal_re]
    linarith
  have hP := perron_LSeries_x (f := fL η) (norm_fL_le hη) hx hd0 hd1 hd (s := -(η : ℂ)) (c := c) (T := T) hc0 hsc hT
  have hint : ∫ t in (-T)..T, LSeries (fL η) (-(η : ℂ) + ((c : ℂ) + t * I)) *
      (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) =
      (η : ℂ) * ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) *
        (-logDeriv riemannZeta ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : 1 < ((c : ℂ) + t * I).re := by simp; linarith
    simp only [LSeries_fL η hre]
    ring
  rw [soma_fL_x, hint] at hP
  have hσ' : (-(η : ℂ)).re + c = c - η := by rw [neg_re, ofReal_re]; ring
  rw [hσ'] at hP
  have htsum := tsum_um_le (σ := c - η) hc1 hc2
  have hpos : 0 ≤ x ^ c * ((2 * x + 2) / d) / (π * T) := by
    positivity
  have e : ((η * Chebyshev.psi x : ℝ) : ℂ) - (2 * π : ℂ)⁻¹ * ((η : ℂ) *
      ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)) =
      (η : ℂ) * ((Chebyshev.psi x : ℂ) - (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)) := by
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη] at hP
  calc _ ≤ _ := hP
    _ ≤ _ := mul_le_mul_of_nonneg_left htsum hpos

/-! ## 2. A fórmula explícita -/

/-- O erro da altura `k` (Perron com constante `P`): Perron + as horizontais + a reta esquerda. -/
noncomputable def epsx (x P C₁ c₀ B : ℝ) (k : ℕ) : ℝ :=
  32 * x ^ (2 : ℝ) * P / (π * ((k : ℝ) + 6)) +
    (2 * (x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18) /
      Real.log x + 1 / Real.log x ^ 2) / ((k : ℝ) + 6)) +
      2 * ((k : ℝ) + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) * ((x ^ 2)⁻¹) ^ (k + 7)) / (2 * π)

theorem epsx_tendsto {x P C₁ c₀ B : ℝ} (hx : 1 < x) : Tendsto (epsx x P C₁ c₀ B) atTop (𝓝 0) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hL0 : Real.log x ≠ 0 := hL.ne'
  have h1 : Tendsto (fun k : ℕ => 32 * x ^ (2 : ℝ) * P / (π * ((k : ℝ) + 6))) atTop (𝓝 0) := by
    have := (ATK.ZeroClasses.ExplicitaLimite.lim_log 0).const_mul (32 * x ^ (2 : ℝ) * P / π)
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    simp only [pow_zero]
    rw [div_mul_div_comm, mul_one]
  have h2 : Tendsto (fun k : ℕ => x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ +
      Real.log ((k : ℝ) + 9) + 18) / Real.log x + 1 / Real.log x ^ 2) / ((k : ℝ) + 6)) atTop (𝓝 0) := by
    have := (((ATK.ZeroClasses.ExplicitaLimite.lim_log 2).const_mul (x ^ (2 : ℝ) * C₁ / Real.log x)).add
      ((ATK.ZeroClasses.ExplicitaLimite.lim_log 1).const_mul (x ^ (2 : ℝ) / Real.log x))).add
      ((ATK.ZeroClasses.ExplicitaLimite.lim_log 0).const_mul (x ^ (2 : ℝ) * ((c₀ + 18) / Real.log x + 1 / Real.log x ^ 2)))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    have hk : (k : ℝ) + 6 ≠ 0 := by positivity
    simp only [pow_zero, pow_one]
    field_simp
    ring
  have hr0 : 0 ≤ (x ^ 2)⁻¹ := by positivity
  have hr1 : (x ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have h3 : Tendsto (fun k : ℕ => 2 * ((k : ℝ) + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) *
      ((x ^ 2)⁻¹) ^ (k + 7)) atTop (𝓝 0) := by
    have := ((ATK.ZeroClasses.ExplicitaLimite.lim_geo 1 hr0 hr1).const_mul (2 * (c₀ + B + 10))).add ((ATK.ZeroClasses.ExplicitaLimite.lim_geo 2 hr0 hr1).const_mul 10)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    ring
  have := h1.add (((h2.const_mul 2).add h3).div_const (2 * π))
  simp only [mul_zero, add_zero, zero_div] at this
  exact this

/-- **A fórmula explícita com erro, `x` real**: para `x > 1` a distância `≥ d` dos inteiros e cada `k`, há uma altura boa
`T ∈ [k + 6, k + 7]` com `‖Σ_{|γ|≤T} m_ρ x^ρ/ρ − (x + Σ_{n<k+7} x^{−2(n+1)}/(2(n+1)) − log 2π − ψ(x))‖ ≤ ε_k`. -/
theorem explicita_k_x {x d : ℝ} (hx : 1 < x) (hd0 : 0 < d) (hd1 : d ≤ 1) (hd : ∀ n : ℕ, d ≤ |x - n|) :
    ∃ C₁ c₀ B : ℝ, ∀ k : ℕ, ∃ T : ℝ, (k : ℝ) + 6 ≤ T ∧ T ≤ k + 7 ∧
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ riemannZeta u = 0 ∧ 0 < u.re ∧ |u.im| ≤ T) ∧
      ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px x u -
        ((x : ℂ) + ∑ n ∈ Finset.range (k + 7), (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) -
          (Real.log (2 * π) : ℂ) - (Chebyshev.psi x : ℂ))‖ ≤ epsx x ((2 * x + 2) / d) C₁ c₀ B k := by
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
    have hP := perron_psi_x hx0 hd0 hd1 hd (η := 1 / 2) (c := 2) (T := T) (by norm_num) (by norm_num) (by norm_num) hT0
    rw [← hVc] at hP
    have hPerron : ‖(Chebyshev.psi x : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤
        32 * x ^ (2 : ℝ) * ((2 * x + 2) / d) / (π * ((k : ℝ) + 6)) := by
      have e16 : (8 : ℝ) / (2 - 1 / 2 - 1) = 16 := by norm_num
      rw [e16] at hP
      have h1 : ‖(Chebyshev.psi x : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤ 32 * x ^ (2 : ℝ) * ((2 * x + 2) / d) / (π * T) := by
        have e : 32 * x ^ (2 : ℝ) * ((2 * x + 2) / d) / (π * T) = 2 * (x ^ (2 : ℝ) * ((2 * x + 2) / d) / (π * T) * 16) := by
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
    have hfin : ‖R - (x + Q - ℓ - (Chebyshev.psi x : ℂ))‖ ≤
        ‖(Chebyshev.psi x : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ + ‖(2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ)‖ := by
      have e : R - (x + Q - ℓ - (Chebyshev.psi x : ℂ)) =
          ((Chebyshev.psi x : ℂ) - (2 * π : ℂ)⁻¹ * Vc) + ((2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ)) := by ring
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

/-- **A fórmula explícita, `x` real** (sem hipóteses): para `x > 1` não inteiro, ao longo de
alturas boas `T_k ∈ [k + 6, k + 7]`,
`Σ_{|γ| ≤ T_k} m_ρ x^ρ/ρ → x − ψ(x) − log 2π − ½ log(1 − x^{−2})`. -/
theorem formula_explicita_x {x d : ℝ} (hx : 1 < x) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hd : ∀ n : ℕ, d ≤ |x - n|) : ∃ T : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 6 ≤ T k ∧ T k ≤ k + 7) ∧
    ∃ S : ℕ → Finset ℂ, (∀ k u, u ∈ S k ↔ riemannZeta u = 0 ∧ 0 < u.re ∧ |u.im| ≤ T k) ∧
      Tendsto (fun k => ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u) atTop
        (𝓝 ((x : ℂ) - Chebyshev.psi x - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))) := by
  obtain ⟨C₁, c₀, B, h⟩ := explicita_k_x hx hd0 hd1 hd
  choose T hT1 hT2 S hS hb using h
  refine ⟨T, fun k => ⟨hT1 k, hT2 k⟩, S, hS, ?_⟩
  have hQ := (ATK.ZeroClasses.ExplicitaLimite.triv_soma hx).comp (tendsto_add_atTop_nat 7)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hQ ⊢
  have hlim := (epsx_tendsto (P := (2 * x + 2) / d) (C₁ := C₁) (c₀ := c₀) (B := B) hx).add hQ
  rw [zero_add] at hlim
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
  simp only [Function.comp_apply]
  set R : ℂ := ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u
  set Q : ℂ := ∑ n ∈ Finset.range (k + 7), (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1))
  have e : R - ((x : ℂ) - Chebyshev.psi x - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹)) =
      (R - ((x : ℂ) + Q - (Real.log (2 * π) : ℂ) - (Chebyshev.psi x : ℂ))) +
        (Q - ((1 / 2 * -Real.log (1 - (x ^ 2)⁻¹) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hb k) le_rfl)

/-- **A fórmula explícita com `T → ∞`, `x` real**: para `x > 1` com `|x − n| ≥ d > 0` para todo `n`,
`Σ_{|γ| ≤ T} m_ρ x^ρ/ρ → x − ψ(x) − log 2π − ½ log(1 − x^{−2})` quando `T → ∞`. -/
theorem formula_explicita_T_x {x d : ℝ} (hx : 1 < x) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hd : ∀ n : ℕ, d ≤ |x - n|) :
    Tendsto (fun T : ℝ => ∑ ρ ∈ ATK.ZeroClasses.ExplicitaT.Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ) atTop
      (𝓝 ((x : ℂ) - Chebyshev.psi x - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))) := by
  obtain ⟨Tk, hTk, S, hS, hlim⟩ := formula_explicita_x hx hd0 hd1 hd
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
        ((x : ℂ) - Chebyshev.psi x - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))‖
      ≤ ‖∑ ρ ∈ ATK.ZeroClasses.ExplicitaT.Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ -
          ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u‖ +
        ‖∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px x u -
          ((x : ℂ) - Chebyshev.psi x - Real.log (2 * π) - 1 / 2 * Real.log (1 - (x ^ 2)⁻¹))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hd.trans hBabs.le) hA
    _ = ε := by ring

end ATK.ZeroClasses.ExplicitaReal

#print axioms ATK.ZeroClasses.ExplicitaReal.abs_log_ge_x
#print axioms ATK.ZeroClasses.ExplicitaReal.log_ne_zero_x
#print axioms ATK.ZeroClasses.ExplicitaReal.inv_abs_log_le_x
#print axioms ATK.ZeroClasses.ExplicitaReal.soma_fL_x
#print axioms ATK.ZeroClasses.ExplicitaReal.perron_LSeries_x
#print axioms ATK.ZeroClasses.ExplicitaReal.perron_psi_x
#print axioms ATK.ZeroClasses.ExplicitaReal.epsx_tendsto
#print axioms ATK.ZeroClasses.ExplicitaReal.explicita_k_x
#print axioms ATK.ZeroClasses.ExplicitaReal.formula_explicita_x
#print axioms ATK.ZeroClasses.ExplicitaReal.formula_explicita_T_x
