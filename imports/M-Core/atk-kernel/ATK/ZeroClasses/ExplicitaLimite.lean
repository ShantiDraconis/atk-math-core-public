import ATK.ZeroClasses.ExplicitaResiduos
import ATK.ZeroClasses.VonKochRH

/-!
# A fórmula explícita de Riemann–von Mangoldt (rodada 71)

Segunda metade da fórmula explícita sem hipóteses (Davenport, cap. 17): as cotas no retângulo largo da rodada 70 e
o limite. Para `x = N + ½` (`N ≥ 1`), ao longo de alturas boas `T_k ∈ [k + 6, k + 7]`,

  **`Σ_{|γ| ≤ T_k} m_ρ x^ρ/ρ → x − ψ(N) − log 2π − ½ log(1 − x^{−2})`**   (`formula_explicita`),

`ρ` sobre os zeros não triviais com multiplicidade. As peças:

* **a tangente** fora do eixo real: `‖tan z‖ ≤ 2` se `|Im z| ≥ 1` (`norm_tan_le_dois`), `‖tan z‖ ≤ 1` se
  `sen² Re z ≤ cos² Re z` (`norm_tan_le_um`), pelas fórmulas `|sen z|² = sen² a + senh² b`, `|cos z|² = cos² a + senh² b`;
* **a digama à direita**: pela recorrência `ψ(z + n) = ψ(z) + Σ_{k<n} 1/(z + k)` (Mathlib), a cota da rodada 63 na
  faixa `0 < Re z ≤ 1` e compacidade em `½ + i[−3, 3]`: `‖ψ(s)‖ ≤ log(2 + |Im s|) + 11 + Re s/3` para `|Im s| ≥ 3`
  (`digamma_hor`) e `‖ψ(n + ½ + iy)‖ ≤ B + log(2 + |y|) + 2n` (`digamma_esq`);
* **`ζ′/ζ` à esquerda pela equação funcional** (`logDeriv_riemannZeta_one_sub` da Mathlib):
  `‖ζ′/ζ(w)‖ ≤ ‖ζ′/ζ(1 − w)‖ + 2 + ‖ψ(1 − w)‖ + 2‖tan(π(1 − w)/2)‖` em `Re w ≤ 0` (`logDeriv_esq_le`); daí
  `‖ζ′/ζ(σ ± iT)‖ ≤ A(T) − σ` nas horizontais (`logDeriv_hor`) e `O(K + log T)` na reta `Re w = −(2K + ½)`
  (`logDeriv_esq_reta`);
* as integrais: `∫_{−U}^2 x^σ(A − σ) dσ ≤ x²((A − 2)/log x + 1/log² x)` (`integral_exp_lin`), as horizontais
  `O(log² T/T)` (`hor_le`) e a reta esquerda `O(T x^{−U}(K + log T)/U)` (`esq_le`);
* Perron (rodada 64) na reta `Re s = 2` e `Σ_{n<K} x^{−2(n+1)}/(2(n+1)) → −½ log(1 − x^{−2})` (`triv_soma`).

Classificação (rodada 71): **ferramenta**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.ExplicitaLimite

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret)
open ATK.ZeroClasses.PsiRH (Fx px norm_Fx perron_psi)
open ATK.ZeroClasses.PerronD (xN)

/-! ## 1. A tangente fora do eixo real -/

theorem normSq_sin (z : ℂ) : normSq (sin z) = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [sin_add_mul_I, ← ofReal_sin, ← ofReal_cosh, ← ofReal_cos, ← ofReal_sinh]
  rw [show ((Real.sin z.re : ℂ) * (Real.cosh z.im : ℂ) + (Real.cos z.re : ℂ) * (Real.sinh z.im : ℂ) * I) =
      ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ) + ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * I by
    push_cast; ring]
  rw [normSq_add_mul_I]
  have h1 := Real.cosh_sq z.im
  have h2 := Real.sin_sq_add_cos_sq z.re
  linear_combination (Real.sin z.re) ^ 2 * h1 + (Real.sinh z.im) ^ 2 * h2

theorem normSq_cos (z : ℂ) : normSq (cos z) = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [cos_add_mul_I, ← ofReal_sin, ← ofReal_cosh, ← ofReal_cos, ← ofReal_sinh]
  rw [show ((Real.cos z.re : ℂ) * (Real.cosh z.im : ℂ) - (Real.sin z.re : ℂ) * (Real.sinh z.im : ℂ) * I) =
      ((Real.cos z.re * Real.cosh z.im : ℝ) : ℂ) + ((-(Real.sin z.re * Real.sinh z.im) : ℝ) : ℂ) * I by
    push_cast; ring]
  rw [normSq_add_mul_I]
  have h1 := Real.cosh_sq z.im
  have h2 := Real.sin_sq_add_cos_sq z.re
  linear_combination (Real.cos z.re) ^ 2 * h1 + (Real.sinh z.im) ^ 2 * h2

theorem norm_tan_le_of_sq {z : ℂ} {M : ℝ} (hM : 0 ≤ M) (hc : cos z ≠ 0)
    (h : normSq (sin z) ≤ M ^ 2 * normSq (cos z)) : ‖tan z‖ ≤ M := by
  rw [tan_eq_sin_div_cos, norm_div, div_le_iff₀ (norm_pos_iff.mpr hc)]
  have h1 : ‖sin z‖ ^ 2 ≤ (M * ‖cos z‖) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
    exact h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1

/-- **`‖tan z‖ ≤ 2` para `|Im z| ≥ 1`**. -/
theorem norm_tan_le_dois {z : ℂ} (h : 1 ≤ |z.im|) : ‖tan z‖ ≤ 2 := by
  have hs : 1 ≤ Real.sinh z.im ^ 2 := by
    have h0 : 1 ≤ |Real.sinh z.im| := by
      rw [Real.abs_sinh]
      exact h.trans (Real.self_le_sinh_iff.mpr (abs_nonneg _))
    have := one_le_pow₀ (n := 2) h0
    rwa [sq_abs] at this
  have hc : cos z ≠ 0 := by
    intro h0
    have := normSq_cos z
    rw [h0, map_zero] at this
    nlinarith [sq_nonneg (Real.cos z.re)]
  apply norm_tan_le_of_sq (by norm_num) hc
  rw [normSq_sin, normSq_cos]
  have := Real.sin_sq_le_one z.re
  nlinarith [sq_nonneg (Real.cos z.re)]

/-- **`‖tan z‖ ≤ 1` se `sen² Re z ≤ cos² Re z`**. -/
theorem norm_tan_le_um {z : ℂ} (h : Real.sin z.re ^ 2 ≤ Real.cos z.re ^ 2) : ‖tan z‖ ≤ 1 := by
  have hc2 : 0 < Real.cos z.re ^ 2 := by
    have := Real.sin_sq_add_cos_sq z.re
    nlinarith
  have hc : cos z ≠ 0 := by
    intro h0
    have := normSq_cos z
    rw [h0, map_zero] at this
    nlinarith [sq_nonneg (Real.sinh z.im)]
  apply norm_tan_le_of_sq zero_le_one hc
  rw [normSq_sin, normSq_cos, one_pow, one_mul]
  linarith

theorem sin_sq_esq (n : ℕ) :
    Real.sin (π * (2 * n + 3 / 2) / 2) ^ 2 ≤ Real.cos (π * (2 * n + 3 / 2) / 2) ^ 2 := by
  have e : 2 * (π * (2 * n + 3 / 2) / 2) = π / 2 + π + n * (2 * π) := by ring
  have hc : Real.cos (2 * (π * (2 * n + 3 / 2) / 2)) = 0 := by
    rw [e, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  rw [Real.cos_two_mul] at hc
  have := Real.sin_sq_add_cos_sq (π * (2 * n + 3 / 2) / 2)
  linarith

/-! ## 2. A digama à direita -/

theorem nao_neg_nat {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m h
  rw [h, neg_re, natCast_re] at hz
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  linarith

theorem digamma_cont : ContinuousOn digamma {z : ℂ | 0 < z.re} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (nao_neg_nat hz)).differentiableWithinAt
  have han : AnalyticOnNhd ℂ Gamma {z : ℂ | 0 < z.re} := hd.analyticOnNhd hU
  intro z hz
  have e : digamma = fun w => deriv Gamma w / Gamma w :=
    funext fun w => by rw [digamma_def, logDeriv_apply]
  rw [e]
  exact ((han z hz).deriv.continuousAt.div (han z hz).continuousAt
    (Complex.Gamma_ne_zero (nao_neg_nat hz))).continuousWithinAt

theorem digamma_meio : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
    ‖digamma ((1 / 2 : ℂ) + y * I)‖ ≤ B + Real.log (2 + |y|) := by
  have hcont : ContinuousOn (fun y : ℝ => digamma ((1 / 2 : ℂ) + y * I)) (Icc (-3) 3) := by
    refine digamma_cont.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro y _
    show (0 : ℝ) < ((1 / 2 : ℂ) + (y : ℂ) * I).re
    norm_num
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max B 11, le_max_of_le_right (by norm_num), fun y => ?_⟩
  have hl : 0 ≤ Real.log (2 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
  have hre : ((1 / 2 : ℂ) + (y : ℂ) * I).re = 1 / 2 := by simp
  have him : ((1 / 2 : ℂ) + (y : ℂ) * I).im = y := by simp
  by_cases hy : |y| ≤ 3
  · have := hB y ⟨(abs_le.mp hy).1, (abs_le.mp hy).2⟩
    linarith [le_max_left B 11]
  · have h3 : 3 ≤ |((1 / 2 : ℂ) + (y : ℂ) * I).im| := by rw [him]; linarith
    have := ATK.ZeroClasses.SomaZeros.norm_digamma_le (by rw [hre]; norm_num) (by rw [hre]; norm_num) h3
    rw [him] at this
    linarith [le_max_right B 11]

theorem digamma_rec {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖digamma (z + n)‖ ≤ ‖digamma z‖ + ∑ k ∈ Finset.range n, ‖(z + k)⁻¹‖ := by
  rw [Complex.digamma_apply_add_nat (nao_neg_nat hz) n]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))

/-- **`‖ψ(s)‖ ≤ log(2 + |Im s|) + 11 + Re s/3`** para `Re s ≥ 1`, `|Im s| ≥ 3`. -/
theorem digamma_hor {s : ℂ} (h1 : 1 ≤ s.re) (h3 : 3 ≤ |s.im|) :
    ‖digamma s‖ ≤ Real.log (2 + |s.im|) + 11 + s.re / 3 := by
  have hc1 : 1 ≤ ⌈s.re⌉₊ := Nat.ceil_pos.mpr (by linarith)
  set m : ℕ := ⌈s.re⌉₊ - 1 with hm
  have hmr : (m : ℝ) = ⌈s.re⌉₊ - 1 := by rw [hm, Nat.cast_sub hc1, Nat.cast_one]
  have hlt : (⌈s.re⌉₊ : ℝ) < s.re + 1 := Nat.ceil_lt_add_one (by linarith)
  have hle : s.re ≤ ⌈s.re⌉₊ := Nat.le_ceil _
  set z := s - m with hz
  have hzre : z.re = s.re - m := by simp [hz]
  have hzim : z.im = s.im := by simp [hz]
  have hz0 : 0 < z.re := by rw [hzre, hmr]; linarith
  have hz1 : z.re ≤ 1 := by rw [hzre, hmr]; linarith
  have hzs : z + m = s := by rw [hz]; ring
  have hrec := digamma_rec hz0 m
  rw [hzs] at hrec
  have hd := ATK.ZeroClasses.SomaZeros.norm_digamma_le hz0 hz1 (by rw [hzim]; exact h3)
  rw [hzim] at hd
  have hsum : ∑ k ∈ Finset.range m, ‖(z + k)⁻¹‖ ≤ m * (1 / 3) := by
    have hk : ∀ k ∈ Finset.range m, ‖(z + k)⁻¹‖ ≤ 1 / 3 := by
      intro k _
      rw [norm_inv]
      have hn : 3 ≤ ‖z + k‖ := by
        have := abs_im_le_norm (z + k)
        have e : (z + k).im = s.im := by simp [hzim]
        rw [e] at this
        linarith
      calc ‖z + k‖⁻¹ ≤ (3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn
        _ = 1 / 3 := by norm_num
    calc ∑ k ∈ Finset.range m, ‖(z + k)⁻¹‖ ≤ ∑ k ∈ Finset.range m, (1 / 3 : ℝ) := Finset.sum_le_sum hk
      _ = m * (1 / 3) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm3 : (m : ℝ) * (1 / 3) ≤ s.re / 3 := by rw [hmr]; linarith
  linarith

/-- **`‖ψ(n + ½ + iy)‖ ≤ B + log(2 + |y|) + 2n`**. -/
theorem digamma_esq : ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (y : ℝ),
    ‖digamma ((1 / 2 : ℂ) + y * I + n)‖ ≤ B + Real.log (2 + |y|) + 2 * n := by
  obtain ⟨B, hB0, hB⟩ := digamma_meio
  refine ⟨B, hB0, fun n y => ?_⟩
  have hz0 : 0 < ((1 / 2 : ℂ) + (y : ℂ) * I).re := by norm_num
  have hrec := digamma_rec hz0 n
  have hsum : ∑ k ∈ Finset.range n, ‖((1 / 2 : ℂ) + y * I + k)⁻¹‖ ≤ n * 2 := by
    have hk : ∀ k ∈ Finset.range n, ‖((1 / 2 : ℂ) + y * I + k)⁻¹‖ ≤ 2 := by
      intro k _
      rw [norm_inv]
      have hn : 1 / 2 ≤ ‖(1 / 2 : ℂ) + y * I + k‖ := by
        have := abs_re_le_norm ((1 / 2 : ℂ) + y * I + k)
        have e : ((1 / 2 : ℂ) + y * I + k).re = 1 / 2 + k := by simp
        have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
        rw [e, abs_of_nonneg (by positivity)] at this
        linarith
      calc ‖(1 / 2 : ℂ) + y * I + k‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn
        _ = 2 := by norm_num
    calc ∑ k ∈ Finset.range n, ‖((1 / 2 : ℂ) + y * I + k)⁻¹‖ ≤ ∑ k ∈ Finset.range n, (2 : ℝ) :=
          Finset.sum_le_sum hk
      _ = n * 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have := hB y
  linarith

/-! ## 3. `ζ′/ζ` à esquerda pela equação funcional -/

theorem log_dois_pi_lt : Real.log (2 * π) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have he := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]
  have h2 : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 :=
    mul_lt_mul'' he he (by norm_num) (by norm_num)
  have hpi := Real.pi_lt_d2
  linarith

/-- **`‖ζ′/ζ(w)‖ ≤ ‖ζ′/ζ(1 − w)‖ + 2 + ‖ψ(1 − w)‖ + 2‖tan(π(1 − w)/2)‖`** em `Re w ≤ 0`, `w ∉ ℤ`. -/
theorem logDeriv_esq_le {w : ℂ} (hw : w.re ≤ 0) (hZ : ∀ n : ℤ, w ≠ n) :
    ‖logDeriv riemannZeta w‖ ≤ ‖logDeriv riemannZeta (1 - w)‖ + 2 + ‖digamma (1 - w)‖ +
      2 * ‖tan (π * (1 - w) / 2)‖ := by
  have hZ' : ∀ n : ℤ, 1 - w ≠ n := by
    intro n h
    apply hZ (1 - n)
    rw [← sub_sub_cancel 1 w, h]
    push_cast
    ring
  have hz : riemannZeta (1 - w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [sub_re, one_re]; linarith)
  have e := logDeriv_riemannZeta_one_sub hZ' hz
  rw [sub_sub_cancel] at e
  have e2 : logDeriv riemannZeta w = -logDeriv riemannZeta (1 - w) + Complex.log (2 * π) -
      digamma (1 - w) + π / 2 * tan (π * (1 - w) / 2) := by linear_combination e
  rw [e2]
  have hlog : ‖Complex.log (2 * π)‖ ≤ 2 := by
    have e3 : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [e3, ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by linarith [Real.pi_gt_three]))]
    exact log_dois_pi_lt.le
  have hpi2 : ‖(π : ℂ) / 2‖ ≤ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_two]
    linarith [Real.pi_lt_d2]
  have t1 := norm_add_le (-logDeriv riemannZeta (1 - w) + Complex.log (2 * π) - digamma (1 - w))
    (π / 2 * tan (π * (1 - w) / 2))
  have t2 := norm_sub_le (-logDeriv riemannZeta (1 - w) + Complex.log (2 * π)) (digamma (1 - w))
  have t3 := norm_add_le (-logDeriv riemannZeta (1 - w)) (Complex.log (2 * π))
  rw [norm_neg] at t3
  rw [norm_mul] at t1
  have t4 : ‖(π : ℂ) / 2‖ * ‖tan (π * (1 - w) / 2)‖ ≤ 2 * ‖tan (π * (1 - w) / 2)‖ :=
    mul_le_mul_of_nonneg_right hpi2 (norm_nonneg _)
  linarith

/-- **As horizontais**: em alturas boas, `‖ζ′/ζ(σ ± iT)‖ ≤ C₁ log²(2 + T) + c₀ + log(2 + T) + 20 − σ` para `σ ≤ 2`. -/
theorem logDeriv_hor {C₁ c₀ T : ℝ} (hC₁ : 0 ≤ C₁) (hT : 6 ≤ T)
    (hc₀ : ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv riemannZeta s‖ ≤ c₀)
    (hgood : ∀ σ : ℝ, 0 < σ → σ ≤ 2 → ∀ τ : ℝ, (τ = T ∨ τ = -T) →
      riemannZeta ((σ : ℂ) + τ * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + τ * I)‖ ≤ C₁ * Real.log (2 + T) ^ 2)
    {σ τ : ℝ} (hσ : σ ≤ 2) (hτ : τ = T ∨ τ = -T) :
    ‖logDeriv riemannZeta ((σ : ℂ) + τ * I)‖ ≤
      C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 20 - σ := by
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  have hl0 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hq : 0 ≤ C₁ * Real.log (2 + T) ^ 2 := by positivity
  have hτabs : |τ| = T := by
    rcases hτ with h | h <;> rw [h]
    · exact abs_of_pos (by linarith)
    · rw [abs_neg]; exact abs_of_pos (by linarith)
  by_cases hσ0 : 0 < σ
  · have := (hgood σ hσ0 hσ τ hτ).2
    linarith
  · push Not at hσ0
    set w : ℂ := (σ : ℂ) + τ * I with hw
    have hwre : w.re = σ := by simp [hw]
    have hwim : w.im = τ := by simp [hw]
    have hZ : ∀ n : ℤ, w ≠ n := by
      intro n h
      have := congrArg Complex.im h
      rw [hwim, intCast_im] at this
      rw [this] at hτabs
      simp at hτabs
      linarith
    have hfe := logDeriv_esq_le (by rw [hwre]; exact hσ0) hZ
    -- `ζ′/ζ(1 − w)`
    have h1w : 1 - w = ((1 - σ : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I := by rw [hw]; push_cast; ring
    have hτ' : -τ = T ∨ -τ = -T := by
      rcases hτ with h | h
      · right; rw [h]
      · left; rw [h, neg_neg]
    have hA : ‖logDeriv riemannZeta (1 - w)‖ ≤ C₁ * Real.log (2 + T) ^ 2 + c₀ := by
      by_cases h2 : 1 - σ ≤ 2
      · rw [h1w]
        have := (hgood (1 - σ) (by linarith) h2 (-τ) hτ').2
        linarith
      · have := hc₀ (1 - w) (by rw [h1w]; simp; linarith)
        linarith
    -- `ψ(1 − w)`
    have hB : ‖digamma (1 - w)‖ ≤ Real.log (2 + T) + 11 + (1 - σ) / 3 := by
      have hre : (1 - w).re = 1 - σ := by rw [h1w]; simp
      have him : (1 - w).im = -τ := by rw [h1w]; simp
      have := digamma_hor (s := 1 - w) (by rw [hre]; linarith) (by rw [him, abs_neg, hτabs]; linarith)
      rw [hre, him, abs_neg, hτabs] at this
      exact this
    -- `tan(π(1 − w)/2)`
    have hC : ‖tan (π * (1 - w) / 2)‖ ≤ 2 := by
      apply norm_tan_le_dois
      have him : (π * (1 - w) / 2 : ℂ).im = π * (-τ) / 2 := by rw [h1w]; simp
      rw [him, abs_div, abs_mul, abs_neg, hτabs, abs_of_pos Real.pi_pos, abs_two]
      have := Real.pi_gt_three
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    linarith

/-- **A reta esquerda** `Re w = −(2K + ½)`, `K ≥ 1`: `‖ζ′/ζ(w)‖ ≤ c₀ + B + log(2 + |y|) + 4K + 8`. -/
theorem logDeriv_esq_reta {c₀ B : ℝ} (hc₀ : ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv riemannZeta s‖ ≤ c₀)
    (hB : ∀ (n : ℕ) (y : ℝ), ‖digamma ((1 / 2 : ℂ) + y * I + n)‖ ≤ B + Real.log (2 + |y|) + 2 * n)
    {K : ℕ} (hK : 1 ≤ K) (y : ℝ) :
    ‖logDeriv riemannZeta (((-(2 * K + 1 / 2) : ℝ) : ℂ) + y * I)‖ ≤
      c₀ + B + Real.log (2 + |y|) + 4 * K + 8 := by
  set w : ℂ := ((-(2 * K + 1 / 2) : ℝ) : ℂ) + y * I with hw
  have hwre : w.re = -(2 * K + 1 / 2) := by simp [hw]
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hZ : ∀ n : ℤ, w ≠ n := by
    intro n h
    have := congrArg Complex.re h
    rw [hwre, intCast_re] at this
    have h2 : ((2 * n : ℤ) : ℝ) = ((-(4 * K) - 1 : ℤ) : ℝ) := by push_cast; linarith
    have h3 : 2 * n = -(4 * (K : ℤ)) - 1 := by exact_mod_cast h2
    omega
  have hfe := logDeriv_esq_le (by rw [hwre]; linarith) hZ
  have h1w : 1 - w = (1 / 2 : ℂ) + ((-y : ℝ) : ℂ) * I + ((2 * K + 1 : ℕ) : ℂ) := by
    rw [hw]; push_cast; ring
  have hA : ‖logDeriv riemannZeta (1 - w)‖ ≤ c₀ :=
    hc₀ (1 - w) (by rw [h1w]; simp; linarith)
  have hBw : ‖digamma (1 - w)‖ ≤ B + Real.log (2 + |y|) + 4 * K + 2 := by
    rw [h1w]
    have := hB (2 * K + 1) (-y)
    rw [abs_neg] at this
    push_cast at this ⊢
    linarith
  have hC : ‖tan (π * (1 - w) / 2)‖ ≤ 1 := by
    apply norm_tan_le_um
    have hre : (π * (1 - w) / 2 : ℂ).re = π * (2 * K + 3 / 2) / 2 := by
      rw [h1w]; simp; ring
    rw [hre]
    exact sin_sq_esq K
  linarith

/-! ## 4. As integrais -/

/-- **`∫_{−U}^2 x^σ(A − σ) dσ ≤ x²((A − 2)/log x + 1/log² x)`**. -/
theorem integral_exp_lin {x A U : ℝ} (hx : 1 < x) (hU : 0 ≤ U) (hA : 2 ≤ A) :
    ∫ σ in (-U)..2, x ^ σ * (A - σ) ≤ x ^ (2 : ℝ) * ((A - 2) / Real.log x + 1 / Real.log x ^ 2) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hderiv : ∀ σ ∈ uIcc (-U) 2, HasDerivAt
      (fun σ : ℝ => x ^ σ * ((A - σ) / Real.log x + 1 / Real.log x ^ 2)) (x ^ σ * (A - σ)) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => x ^ σ) (x ^ σ * Real.log x) σ :=
      (Real.hasStrictDerivAt_const_rpow hx0 σ).hasDerivAt
    have h2 : HasDerivAt (fun σ : ℝ => (A - σ) / Real.log x + 1 / Real.log x ^ 2) (-1 / Real.log x) σ :=
      (((hasDerivAt_id σ).const_sub A).div_const (Real.log x)).add_const (1 / Real.log x ^ 2)
    convert h1.mul h2 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun σ : ℝ => x ^ σ * (A - σ)) volume (-U) 2 := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.rpow continuous_id fun _ => Or.inl hx0.ne').mul
      (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hΦ : 0 ≤ x ^ (-U) * ((A - -U) / Real.log x + 1 / Real.log x ^ 2) := by
    apply mul_nonneg (Real.rpow_nonneg hx0.le _)
    have : 0 ≤ (A - -U) / Real.log x := div_nonneg (by linarith) hL.le
    have : 0 ≤ 1 / Real.log x ^ 2 := by positivity
    linarith
  linarith

/-- **As horizontais**: `‖∫_{−U}^2 F(σ + iτ) dσ‖ ≤ x²((A − 2)/log x + 1/log² x)/T` se `‖ζ′/ζ‖ ≤ A − σ`. -/
theorem hor_le {x T A U τ : ℝ} (hx : 1 < x) (hT : 0 < T) (hU : 0 ≤ U) (hA : 2 ≤ A) (hτ : |τ| = T)
    (hb : ∀ σ : ℝ, -U ≤ σ → σ ≤ 2 → ‖logDeriv riemannZeta ((σ : ℂ) + τ * I)‖ ≤ A - σ) :
    ‖∫ σ in (-U)..2, Fx x ((σ : ℂ) + τ * I)‖ ≤
      x ^ (2 : ℝ) * ((A - 2) / Real.log x + 1 / Real.log x ^ 2) / T := by
  have hx0 : 0 < x := by linarith
  have hbound : ∀ σ ∈ Ioc (-U) 2, ‖Fx x ((σ : ℂ) + τ * I)‖ ≤ x ^ σ * (A - σ) / T := by
    intro σ hσ
    rw [norm_Fx hx0]
    have hre : ((σ : ℂ) + τ * I).re = σ := by simp
    rw [hre]
    have h4 : T ≤ ‖(σ : ℂ) + τ * I‖ := by
      rw [← hτ]
      have := abs_im_le_norm ((σ : ℂ) + τ * I)
      simpa using this
    have h2 := hb σ hσ.1.le hσ.2
    have hxs : 0 ≤ x ^ σ := Real.rpow_nonneg hx0.le σ
    exact div_le_div₀ (mul_nonneg hxs ((norm_nonneg _).trans h2)) (mul_le_mul_of_nonneg_left h2 hxs) hT h4
  have hgi : IntervalIntegrable (fun σ : ℝ => x ^ σ * (A - σ) / T) volume (-U) 2 := by
    apply Continuous.intervalIntegrable
    exact ((continuous_const.rpow continuous_id fun _ => Or.inl hx0.ne').mul
      (continuous_const.sub continuous_id)).div_const T
  have h := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -U ≤ 2) (ae_of_all _ hbound) hgi
  rw [intervalIntegral.integral_div] at h
  exact h.trans (div_le_div_of_nonneg_right (integral_exp_lin hx hU hA) hT.le)

/-- **A reta esquerda**: `‖∫_{−T}^T F(−U + iy) dy‖ ≤ x^{−U} M/U · 2T`. -/
theorem esq_le {x T U M : ℝ} (hx : 1 < x) (hT : 0 ≤ T) (hU : 0 < U) (hM : 0 ≤ M)
    (hb : ∀ y : ℝ, |y| ≤ T → ‖logDeriv riemannZeta (((-U : ℝ) : ℂ) + y * I)‖ ≤ M) :
    ‖∫ y in (-T)..T, Fx x (((-U : ℝ) : ℂ) + y * I)‖ ≤ x ^ (-U) * M / U * (2 * T) := by
  have hx0 : 0 < x := by linarith
  have hbound : ∀ y ∈ Ι (-T) T, ‖Fx x (((-U : ℝ) : ℂ) + y * I)‖ ≤ x ^ (-U) * M / U := by
    intro y hy
    rw [uIoc_of_le (by linarith)] at hy
    rw [norm_Fx hx0]
    have hre : (((-U : ℝ) : ℂ) + y * I).re = -U := by simp
    rw [hre]
    have h4 : U ≤ ‖((-U : ℝ) : ℂ) + y * I‖ := by
      have := abs_re_le_norm (((-U : ℝ) : ℂ) + y * I)
      rw [hre, abs_neg, abs_of_pos hU] at this
      exact this
    have h2 := hb y (abs_le.mpr ⟨hy.1.le, hy.2⟩)
    have hxs : 0 ≤ x ^ (-U) := Real.rpow_nonneg hx0.le _
    exact div_le_div₀ (mul_nonneg hxs hM) (mul_le_mul_of_nonneg_left h2 hxs) hU h4
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith)] at h
  exact h

/-! ## 5. Os termos de erro tendem a zero -/

/-- **`Σ_{n<K} x^{−2(n+1)}/(2(n+1)) → −½ log(1 − x^{−2})`**: os zeros triviais. -/
theorem triv_soma {x : ℝ} (hx : 1 < x) :
    Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)))
      atTop (𝓝 ((1 / 2 * -Real.log (1 - (x ^ 2)⁻¹) : ℝ) : ℂ)) := by
  have hx0 : 0 < x := by linarith
  have hy : |(x ^ 2)⁻¹| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have hs := (Real.hasSum_pow_div_log_of_abs_lt_one hy).mul_left (1 / 2)
  have hs' := Complex.hasSum_ofReal.mpr hs
  refine hs'.tendsto_sum_nat.congr fun K => Finset.sum_congr rfl fun n _ => ?_
  have h1 : x ^ (-2 * ((n : ℝ) + 1)) = ((x ^ 2)⁻¹) ^ (n + 1) := by
    rw [show -2 * ((n : ℝ) + 1) = -(((2 * (n + 1) : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg hx0.le,
      Real.rpow_natCast, pow_mul, inv_pow]
  rw [show (-2 * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hx0.le, h1]
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  push_cast
  field_simp

theorem lim_log (n : ℕ) :
    Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 9) ^ n / ((k : ℝ) + 6)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-3) n one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop 9 tendsto_natCast_atTop_atTop)
  refine h.congr fun k => ?_
  show Real.log ((k : ℝ) + 9) ^ n / (1 * ((k : ℝ) + 9) + -3) = Real.log ((k : ℝ) + 9) ^ n / ((k : ℝ) + 6)
  congr 1
  ring

theorem lim_geo (j : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 7) ^ j * r ^ (k + 7)) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one j (by rw [abs_of_nonneg hr0]; exact hr)).comp
    (tendsto_add_atTop_nat 7)
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

/-- O erro da altura `k`: Perron + as horizontais + a reta esquerda. -/
noncomputable def eps (x C₁ c₀ B : ℝ) (k : ℕ) : ℝ :=
  32 * x ^ (2 : ℝ) * (4 * x + 2) / (π * ((k : ℝ) + 6)) +
    (2 * (x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18) /
      Real.log x + 1 / Real.log x ^ 2) / ((k : ℝ) + 6)) +
      2 * ((k : ℝ) + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) * ((x ^ 2)⁻¹) ^ (k + 7)) / (2 * π)

theorem eps_tendsto {x C₁ c₀ B : ℝ} (hx : 1 < x) : Tendsto (eps x C₁ c₀ B) atTop (𝓝 0) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hL0 : Real.log x ≠ 0 := hL.ne'
  have h1 : Tendsto (fun k : ℕ => 32 * x ^ (2 : ℝ) * (4 * x + 2) / (π * ((k : ℝ) + 6))) atTop (𝓝 0) := by
    have := (lim_log 0).const_mul (32 * x ^ (2 : ℝ) * (4 * x + 2) / π)
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    simp only [pow_zero]
    rw [div_mul_div_comm, mul_one]
  have h2 : Tendsto (fun k : ℕ => x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ +
      Real.log ((k : ℝ) + 9) + 18) / Real.log x + 1 / Real.log x ^ 2) / ((k : ℝ) + 6)) atTop (𝓝 0) := by
    have := (((lim_log 2).const_mul (x ^ (2 : ℝ) * C₁ / Real.log x)).add
      ((lim_log 1).const_mul (x ^ (2 : ℝ) / Real.log x))).add
      ((lim_log 0).const_mul (x ^ (2 : ℝ) * ((c₀ + 18) / Real.log x + 1 / Real.log x ^ 2)))
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
    have := ((lim_geo 1 hr0 hr1).const_mul (2 * (c₀ + B + 10))).add ((lim_geo 2 hr0 hr1).const_mul 10)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    ring
  have := h1.add (((h2.const_mul 2).add h3).div_const (2 * π))
  simp only [mul_zero, add_zero, zero_div] at this
  exact this

/-! ## 6. A fórmula explícita -/

/-- **A fórmula explícita com erro, altura a altura**: para `x = N + ½` e cada `k`, há uma altura boa
`T ∈ [k + 6, k + 7]` com `‖Σ_{|γ|≤T} m_ρ x^ρ/ρ − (x + Σ_{n<k+7} x^{−2(n+1)}/(2(n+1)) − log 2π − ψ(N))‖ ≤ ε_k`. -/
theorem explicita_k (N : ℕ) (hN : 1 ≤ N) : ∃ C₁ c₀ B : ℝ, ∀ k : ℕ, ∃ T : ℝ, (k : ℝ) + 6 ≤ T ∧ T ≤ k + 7 ∧
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ riemannZeta u = 0 ∧ 0 < u.re ∧ |u.im| ≤ T) ∧
      ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px (xN N) u -
        ((xN N : ℂ) + ∑ n ∈ Finset.range (k + 7), (xN N : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) -
          (Real.log (2 * π) : ℂ) - (Chebyshev.psi N : ℂ))‖ ≤ eps (xN N) C₁ c₀ B k := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := ATK.ZeroClasses.Explicita.altura_boa
  obtain ⟨c₀, hc₀⟩ := ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
  obtain ⟨B, hB0, hB⟩ := digamma_esq
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  refine ⟨C₁, c₀, B, fun k => ?_⟩
  set x := xN N with hxdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 1 < x := by rw [hxdef]; unfold xN; linarith
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
    have hP := perron_psi N (η := 1 / 2) (c := 2) (T := T) (by norm_num) (by norm_num) (by norm_num) hT0
    rw [← hxdef, ← hVc] at hP
    have hPerron : ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤
        32 * x ^ (2 : ℝ) * (4 * x + 2) / (π * ((k : ℝ) + 6)) := by
      have e16 : (8 : ℝ) / (2 - 1 / 2 - 1) = 16 := by norm_num
      rw [e16] at hP
      have h1 : ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤ 32 * x ^ (2 : ℝ) * (4 * x + 2) / (π * T) := by
        have e : 32 * x ^ (2 : ℝ) * (4 * x + 2) / (π * T) = 2 * (x ^ (2 : ℝ) * (4 * x + 2) / (π * T) * 16) := by
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
    have hfin : ‖R - (x + Q - ℓ - (Chebyshev.psi N : ℂ))‖ ≤
        ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ + ‖(2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ)‖ := by
      have e : R - (x + Q - ℓ - (Chebyshev.psi N : ℂ)) =
          ((Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc) + ((2 * π : ℂ)⁻¹ * Vc - (x - R + Q - ℓ)) := by ring
      rw [e]
      exact norm_add_le _ _
    have hsum : (‖Bh‖ + ‖Tp‖ + ‖Vl‖) / (2 * π) ≤
        (2 * (x ^ (2 : ℝ) * ((C₁ * Real.log ((k : ℝ) + 9) ^ 2 + c₀ + Real.log ((k : ℝ) + 9) + 18) /
          Real.log x + 1 / Real.log x ^ 2) / ((k : ℝ) + 6)) +
          2 * ((k : ℝ) + 7) * (c₀ + B + 10 + 5 * ((k : ℝ) + 7)) * ((x ^ 2)⁻¹) ^ (k + 7)) / (2 * π) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    unfold eps
    linarith

/-- **A fórmula explícita de Riemann–von Mangoldt** (sem hipóteses): para `x = N + ½`, `N ≥ 1`, ao longo de
alturas boas `T_k ∈ [k + 6, k + 7]`,
`Σ_{|γ| ≤ T_k} m_ρ x^ρ/ρ → x − ψ(N) − log 2π − ½ log(1 − x^{−2})`. -/
theorem formula_explicita (N : ℕ) (hN : 1 ≤ N) : ∃ T : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 6 ≤ T k ∧ T k ≤ k + 7) ∧
    ∃ S : ℕ → Finset ℂ, (∀ k u, u ∈ S k ↔ riemannZeta u = 0 ∧ 0 < u.re ∧ |u.im| ≤ T k) ∧
      Tendsto (fun k => ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px (xN N) u) atTop
        (𝓝 ((xN N : ℂ) - Chebyshev.psi N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (xN N ^ 2)⁻¹))) := by
  obtain ⟨C₁, c₀, B, h⟩ := explicita_k N hN
  choose T hT1 hT2 S hS hb using h
  refine ⟨T, fun k => ⟨hT1 k, hT2 k⟩, S, hS, ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 1 < xN N := by unfold xN; linarith
  have hQ := (triv_soma hx).comp (tendsto_add_atTop_nat 7)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hQ ⊢
  have hlim := (eps_tendsto (C₁ := C₁) (c₀ := c₀) (B := B) hx).add hQ
  rw [zero_add] at hlim
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
  simp only [Function.comp_apply]
  set R : ℂ := ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px (xN N) u
  set Q : ℂ := ∑ n ∈ Finset.range (k + 7), (xN N : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1))
  have e : R - ((xN N : ℂ) - Chebyshev.psi N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (xN N ^ 2)⁻¹)) =
      (R - ((xN N : ℂ) + Q - (Real.log (2 * π) : ℂ) - (Chebyshev.psi N : ℂ))) +
        (Q - ((1 / 2 * -Real.log (1 - (xN N ^ 2)⁻¹) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hb k) le_rfl)

end ATK.ZeroClasses.ExplicitaLimite

#print axioms ATK.ZeroClasses.ExplicitaLimite.normSq_sin
#print axioms ATK.ZeroClasses.ExplicitaLimite.normSq_cos
#print axioms ATK.ZeroClasses.ExplicitaLimite.norm_tan_le_of_sq
#print axioms ATK.ZeroClasses.ExplicitaLimite.norm_tan_le_dois
#print axioms ATK.ZeroClasses.ExplicitaLimite.norm_tan_le_um
#print axioms ATK.ZeroClasses.ExplicitaLimite.sin_sq_esq
#print axioms ATK.ZeroClasses.ExplicitaLimite.nao_neg_nat
#print axioms ATK.ZeroClasses.ExplicitaLimite.digamma_cont
#print axioms ATK.ZeroClasses.ExplicitaLimite.digamma_meio
#print axioms ATK.ZeroClasses.ExplicitaLimite.digamma_rec
#print axioms ATK.ZeroClasses.ExplicitaLimite.digamma_hor
#print axioms ATK.ZeroClasses.ExplicitaLimite.digamma_esq
#print axioms ATK.ZeroClasses.ExplicitaLimite.log_dois_pi_lt
#print axioms ATK.ZeroClasses.ExplicitaLimite.logDeriv_esq_le
#print axioms ATK.ZeroClasses.ExplicitaLimite.logDeriv_hor
#print axioms ATK.ZeroClasses.ExplicitaLimite.logDeriv_esq_reta
#print axioms ATK.ZeroClasses.ExplicitaLimite.integral_exp_lin
#print axioms ATK.ZeroClasses.ExplicitaLimite.hor_le
#print axioms ATK.ZeroClasses.ExplicitaLimite.esq_le
#print axioms ATK.ZeroClasses.ExplicitaLimite.triv_soma
#print axioms ATK.ZeroClasses.ExplicitaLimite.lim_log
#print axioms ATK.ZeroClasses.ExplicitaLimite.lim_geo
#print axioms ATK.ZeroClasses.ExplicitaLimite.eps_tendsto
#print axioms ATK.ZeroClasses.ExplicitaLimite.explicita_k
#print axioms ATK.ZeroClasses.ExplicitaLimite.formula_explicita
