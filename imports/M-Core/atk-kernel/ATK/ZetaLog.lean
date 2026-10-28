import ATK.ZetaParcial
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# ATK — Região sem zeros logarítmica (tipo de la Vallée Poussin, potência 9 do log)

Com a fórmula de somas parciais (`ATK.ZetaParcial`), `N = ⌈2|t|⌉` e `L = log N`, o kernel prova
perto de `Re s = 1`:

* `norm_zeta_le_log`: `|ζ(u + iτ)| ≤ e(L + 7)` para `1 − 1/L ≤ u ≤ 2`, `1/2 ≤ |τ| ≤ N`;
* `norm_zeta_sub_le_log`: `|ζ(σ + iτ) − ζ(β + iτ)| ≤ (σ − β)·e(L² + 7L + 13)` (cinco parcelas
  `parte_a` … `parte_c2`);
* **`regiao_log`**: para `|t| ≥ 4`, todo zero `β + it` tem `β < 1 − c(t)`,
  `c(t) = 1/(256 e⁵ (ℓ² + 7ℓ + 13)⁴ (ℓ + 7))`, `ℓ = log(3|t|)`;
* **`faixa_log`**: todo zero não trivial com `|t| ≥ 4` satisfaz `c(t) < Re s < 1 − c(t)`;
* **`faixa_log_simples`**: e, em forma simples, `1/(10⁹ ℓ⁹) < Re s < 1 − 1/(10⁹ ℓ⁹)`.

Para `|t|` grande a largura `≍ 1/(log|t|)⁹` é muito melhor que `|t|⁻⁵` (`ATK.ZetaRegiao`). A região
clássica de de la Vallée Poussin tem largura `c/log|t|` (potência 1) e exige a derivada logarítmica
`ζ'/ζ` e uma contagem local de zeros; o meio (`Re s = 1/2`) é RH.
-/

open Complex Set MeasureTheory Filter Topology

namespace ATK.ZetaLog

open ATK.ZetaStrip ATK.ZetaSimetria ATK.ZetaRetangulo ATK.ZetaRegiao ATK.ZetaParcial

/-! ## Desigualdades elementares -/

theorem log_oito : 2 < Real.log 8 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h2]
  nlinarith [Real.exp_pos 1]

theorem rpow_inv_log_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (hL : 0 < Real.log N) :
    (n : ℝ) ^ (1 / Real.log N) ≤ Real.exp 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  rw [mul_one_div, div_le_one hL]
  exact Real.log_le_log hn0 (by exact_mod_cast hnN)

theorem rpow_le_e {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (hL : 0 < Real.log N) {v : ℝ}
    (hv : v ≤ 1 / Real.log N) : (n : ℝ) ^ v ≤ Real.exp 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hv).trans (rpow_inv_log_le hn hnN hL)

/-- `n^{−u} ≤ e/n` para `u ≥ 1 − 1/L`. -/
theorem rpow_neg_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (hL : 0 < Real.log N) {u : ℝ}
    (hu : 1 - 1 / Real.log N ≤ u) : (n : ℝ) ^ (-u) ≤ Real.exp 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ (-u) = (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (1 - u) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  rw [h1, Real.rpow_neg_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (rpow_le_e hn hnN hL (by linarith)) (by positivity)

theorem harmonic_real (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

theorem soma_rpow_le {N : ℕ} (hL : 0 < Real.log N) {u : ℝ} (hu : 1 - 1 / Real.log N ≤ u) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-u) ≤ Real.exp 1 * (1 + Real.log N) := by
  calc ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-u)
      ≤ ∑ n ∈ Finset.Icc 1 N, Real.exp 1 * (1 / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        rw [mul_one_div]; exact rpow_neg_le hn.1 hn.2 hL hu
    _ = Real.exp 1 * ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp 1 * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (harmonic_real N) (Real.exp_pos 1).le

theorem soma_rpow_log_le {N : ℕ} (hL : 0 < Real.log N) {u : ℝ} (hu : 1 - 1 / Real.log N ≤ u) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-u) * Real.log n ≤
      Real.log N * (Real.exp 1 * (1 + Real.log N)) := by
  calc ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-u) * Real.log n
      ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-u) * Real.log N := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
        exact mul_le_mul_of_nonneg_left (Real.log_le_log hn0 (by exact_mod_cast hn.2))
          (Real.rpow_nonneg hn0.le _)
    _ = Real.log N * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-u) := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ Real.log N * (Real.exp 1 * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left (soma_rpow_le hL hu) hL.le

/-- `x^{−β} − x^{−σ} ≤ (σ − β) x^{−β} log x` para `x ≥ 1`, `β ≤ σ`. -/
theorem rpow_sub_le {x : ℝ} (hx : 1 ≤ x) (β σ : ℝ) :
    x ^ (-β) - x ^ (-σ) ≤ (σ - β) * (x ^ (-β) * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have e1 : x ^ (-σ) = x ^ (-β) * Real.exp (-((σ - β) * Real.log x)) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0, ← Real.exp_add]
    congr 1; ring
  have e2 := Real.add_one_le_exp (-((σ - β) * Real.log x))
  have hp : 0 ≤ x ^ (-β) := Real.rpow_nonneg hx0.le _
  rw [e1]
  nlinarith [mul_le_mul_of_nonneg_left e2 hp]

/-! ## Potências complexas -/

theorem cpow_split {x : ℝ} (hx : 0 < x) (a τ : ℝ) :
    (x : ℂ) ^ (-((a : ℂ) + τ * I)) = ((x ^ (-a) : ℝ) : ℂ) * (x : ℂ) ^ (((-τ : ℝ) : ℂ) * I) := by
  rw [show -((a : ℂ) + τ * I) = ((-a : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cpow_add _ _ (by exact_mod_cast hx.ne'), ofReal_cpow hx.le]

theorem norm_fase {x : ℝ} (hx : 0 < x) (τ : ℝ) : ‖(x : ℂ) ^ (((-τ : ℝ) : ℂ) * I)‖ = 1 := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]; simp

theorem norm_cpow_sub {x : ℝ} (hx : 1 ≤ x) {β σ : ℝ} (h : β ≤ σ) (τ : ℝ) :
    ‖(x : ℂ) ^ (-((σ : ℂ) + τ * I)) - (x : ℂ) ^ (-((β : ℂ) + τ * I))‖ = x ^ (-β) - x ^ (-σ) := by
  have hx0 : 0 < x := by linarith
  rw [cpow_split hx0, cpow_split hx0, ← sub_mul, norm_mul, norm_fase hx0, mul_one, ← ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (by linarith [Real.rpow_le_rpow_of_exponent_le hx (show -σ ≤ -β by linarith)])]

theorem norm_cpow_nat {n : ℕ} (hn : 1 ≤ n) (a τ : ℝ) :
    ‖(n : ℂ) ^ (-((a : ℂ) + τ * I))‖ = (n : ℝ) ^ (-a) := by
  rw [norm_natCast_cpow_of_pos (by omega)]; simp

/-! ## A cauda `HN` -/

theorem integrableOn_rpow_N {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi (N : ℝ)) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) (by exact_mod_cast hN)

theorem integral_rpow_N {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Ioi (N : ℝ), t ^ (-σ - 1) = (N : ℝ) ^ (-σ) / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) (by exact_mod_cast hN),
    show -σ - 1 + 1 = -σ by ring]
  field_simp

theorem norm_HN_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖HN N s‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold HN
  rw [← integral_rpow_N hN hs]
  refine norm_integral_le_of_norm_le (integrableOn_rpow_N hN hs) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one (le_trans hN1 (le_of_lt hu))
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg _), show (-s - 1).re = -s.re - 1 by simp]
  calc u ^ (-s.re - 1) * Int.fract u ≤ u ^ (-s.re - 1) * 1 :=
        mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le (Real.rpow_nonneg hu0.le _)
    _ = u ^ (-s.re - 1) := mul_one _

theorem norm_HN_sub_le {N : ℕ} (hN : 1 ≤ N) {β σ τ : ℝ} (hβ : 0 < β) (hβσ : β ≤ σ) :
    ‖HN N (σ + τ * I) - HN N (β + τ * I)‖ ≤ (N : ℝ) ^ (-β) / β - (N : ℝ) ^ (-σ) / σ := by
  have hσ : 0 < σ := lt_of_lt_of_le hβ hβσ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold HN
  rw [← integral_sub (integrableOn_tail (by simp; linarith) hN1)
    (integrableOn_tail (by simp; linarith) hN1)]
  have hb : IntegrableOn (fun u : ℝ => u ^ (-β - 1) - u ^ (-σ - 1)) (Ioi (N : ℝ)) :=
    (integrableOn_rpow_N hN hβ).sub (integrableOn_rpow_N hN hσ)
  refine (norm_integral_le_of_norm_le hb ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu1 : (1 : ℝ) ≤ u := le_trans hN1 (le_of_lt hu)
    have hu0 : (0 : ℝ) < u := by linarith
    have hc : ∀ a : ℝ, (u : ℂ) ^ (-((a : ℂ) + τ * I) - 1) =
        ((u ^ (-a - 1) : ℝ) : ℂ) * (u : ℂ) ^ (((-τ : ℝ) : ℂ) * I) := by
      intro a
      rw [show -((a : ℂ) + τ * I) - 1 = ((-a - 1 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.cpow_add _ _ (by exact_mod_cast hu0.ne'), ofReal_cpow hu0.le]
    rw [hc σ, hc β]
    have hF : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
    have hmono : u ^ (-σ - 1) ≤ u ^ (-β - 1) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    have e : ((u ^ (-σ - 1) : ℝ) : ℂ) * (u : ℂ) ^ (((-τ : ℝ) : ℂ) * I) * ((Int.fract u : ℝ) : ℂ) -
        ((u ^ (-β - 1) : ℝ) : ℂ) * (u : ℂ) ^ (((-τ : ℝ) : ℂ) * I) * ((Int.fract u : ℝ) : ℂ) =
        ((u ^ (-σ - 1) - u ^ (-β - 1) : ℝ) : ℂ) * ((u : ℂ) ^ (((-τ : ℝ) : ℂ) * I) *
          ((Int.fract u : ℝ) : ℂ)) := by push_cast; ring
    rw [e, norm_mul, norm_mul, norm_fase hu0, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (by linarith), one_mul]
    calc (u ^ (-β - 1) - u ^ (-σ - 1)) * ‖((Int.fract u : ℝ) : ℂ)‖
        ≤ (u ^ (-β - 1) - u ^ (-σ - 1)) * 1 := mul_le_mul_of_nonneg_left hF (by linarith)
      _ = u ^ (-β - 1) - u ^ (-σ - 1) := mul_one _
  · rw [integral_sub (integrableOn_rpow_N hN hβ) (integrableOn_rpow_N hN hσ),
      integral_rpow_N hN hβ, integral_rpow_N hN hσ]


/-! ## Cotas de ζ perto de `Re s = 1` -/

theorem inv_log_lt {N : ℕ} (hL : 2 < Real.log N) : 1 / Real.log N < 1 / 2 := by
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith

/-- **`|ζ(s)| ≤ e(L + 7)`** perto de `Re s = 1`. -/
theorem norm_zeta_le_log {N : ℕ} (hN : 2 ≤ N) (hL : 2 < Real.log N) {s : ℂ}
    (hu1 : 1 - 1 / Real.log N ≤ s.re) (hu2 : s.re ≤ 2) (ht1 : 1 / 2 ≤ |s.im|)
    (ht2 : |s.im| ≤ N) : ‖riemannZeta s‖ ≤ Real.exp 1 * (Real.log N + 7) := by
  have hL0 : 0 < Real.log N := by linarith
  have hinvL := inv_log_lt hL
  have hspos : 0 < s.re := by linarith
  have hs2 : 1 / 2 < s.re := by linarith
  have him0 : s.im ≠ 0 := by intro h; rw [h, abs_zero] at ht1; linarith
  have hs1 : s ≠ 1 := fun h => him0 (by rw [h, one_im])
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hE := Real.exp_pos 1
  rw [zeta_parcial hspos hs1 N hN1]
  have h1 : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ Real.exp 1 * (1 + Real.log N) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s.re) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_Icc] at hn
          rw [norm_natCast_cpow_of_pos (by omega)]; simp
      _ ≤ _ := soma_rpow_le hL0 hu1
  have h2 : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 2 * Real.exp 1 := by
    rw [norm_div, norm_natCast_cpow_of_pos (by omega), show (1 - s).re = 1 - s.re by simp]
    have hp : (N : ℝ) ^ (1 - s.re) ≤ Real.exp 1 := rpow_le_e hN1 le_rfl hL0 (by linarith)
    have hd : 1 / 2 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [sub_im, one_im, sub_zero] at this; linarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ N by positivity) (1 - s.re)]
  have h3 : ‖s * HN N s‖ ≤ 4 * Real.exp 1 := by
    rw [norm_mul]
    have hH := norm_HN_le hN1 hspos
    have hp : (N : ℝ) ^ (-s.re) ≤ Real.exp 1 / N := rpow_neg_le hN1 le_rfl hL0 hu1
    have hns : ‖s‖ ≤ 2 * N := by
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hspos] at this; linarith
    have hEN : 0 < Real.exp 1 / N := by positivity
    have hinv : (N : ℝ) ^ (-s.re) / s.re ≤ 2 * (Real.exp 1 / N) := by
      rw [div_le_iff₀ hspos]; nlinarith
    calc ‖s‖ * ‖HN N s‖ ≤ (2 * N) * (2 * (Real.exp 1 / N)) :=
          mul_le_mul hns (hH.trans hinv) (norm_nonneg _) (by positivity)
      _ = 4 * Real.exp 1 := by field_simp; ring
  calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1) - s * HN N s‖
      ≤ ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ + ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ + ‖s * HN N s‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Real.exp 1 * (1 + Real.log N) + 2 * Real.exp 1 + 4 * Real.exp 1 := by linarith
    _ = Real.exp 1 * (Real.log N + 7) := by ring

/-! ### As cinco parcelas da diferença -/

theorem parte_a {N : ℕ} (hL0 : 0 < Real.log N) {β σ : ℝ} (hβ : 1 - 1 / Real.log N ≤ β)
    (hβσ : β ≤ σ) (τ : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + τ * I)) - (n : ℂ) ^ (-((β : ℂ) + τ * I)))‖ ≤
      (σ - β) * (Real.log N * (Real.exp 1 * (1 + Real.log N))) := by
  have hσβ : 0 ≤ σ - β := by linarith
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-((σ : ℂ) + τ * I)) - (n : ℂ) ^ (-((β : ℂ) + τ * I))‖
      = ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-β) - (n : ℝ) ^ (-σ)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
        have h := norm_cpow_sub hn1 hβσ τ
        have hc : ((n : ℝ) : ℂ) = (n : ℂ) := by norm_cast
        rw [hc] at h
        exact h
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (σ - β) * ((n : ℝ) ^ (-β) * Real.log n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        exact rpow_sub_le (by exact_mod_cast hn.1) β σ
    _ = (σ - β) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-β) * Real.log n := (Finset.mul_sum _ _ _).symm
    _ ≤ (σ - β) * (Real.log N * (Real.exp 1 * (1 + Real.log N))) :=
        mul_le_mul_of_nonneg_left (soma_rpow_log_le hL0 hβ) hσβ

theorem norm_N_sub {N : ℕ} (hN1 : 1 ≤ N) {β σ : ℝ} (hβσ : β ≤ σ) (τ : ℝ) :
    ‖(N : ℂ) ^ (1 - ((σ : ℂ) + τ * I)) - (N : ℂ) ^ (1 - ((β : ℂ) + τ * I))‖ =
      (N : ℝ) ^ (1 - β) - (N : ℝ) ^ (1 - σ) := by
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have e1 : ∀ a : ℝ, (1 : ℂ) - ((a : ℂ) + τ * I) = -(((a - 1 : ℝ) : ℂ) + τ * I) := by
    intro a; push_cast; ring
  have hnat : (N : ℂ) = ((N : ℝ) : ℂ) := by norm_cast
  rw [e1 σ, e1 β, hnat, norm_cpow_sub hNr1 (by linarith : β - 1 ≤ σ - 1) τ]
  rw [show -(β - 1) = 1 - β by ring, show -(σ - 1) = 1 - σ by ring]

theorem parte_b1 {N : ℕ} (hN1 : 1 ≤ N) (hL0 : 0 < Real.log N) {β σ τ : ℝ}
    (hβ : 1 - 1 / Real.log N ≤ β) (hβσ : β ≤ σ)
    (hd : 1 / 2 ≤ ‖((σ : ℂ) + τ * I) - 1‖) :
    ‖((N : ℂ) ^ (1 - ((σ : ℂ) + τ * I)) - (N : ℂ) ^ (1 - ((β : ℂ) + τ * I))) /
        (((σ : ℂ) + τ * I) - 1)‖ ≤ (σ - β) * (2 * Real.exp 1 * Real.log N) := by
  have hσβ : 0 ≤ σ - β := by linarith
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hE := Real.exp_pos 1
  rw [norm_div, norm_N_sub hN1 hβσ τ]
  have hsub := rpow_sub_le hNr1 (β - 1) (σ - 1)
  rw [show -(β - 1) = 1 - β by ring, show -(σ - 1) = 1 - σ by ring,
    show σ - 1 - (β - 1) = σ - β by ring] at hsub
  have hNpow : (N : ℝ) ^ (1 - β) ≤ Real.exp 1 := rpow_le_e hN1 le_rfl hL0 (by linarith)
  have h2 : (σ - β) * ((N : ℝ) ^ (1 - β) * Real.log N) ≤ (σ - β) * (Real.exp 1 * Real.log N) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNpow hL0.le) hσβ
  have hX : 0 ≤ (σ - β) * (Real.exp 1 * Real.log N) := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc (N : ℝ) ^ (1 - β) - (N : ℝ) ^ (1 - σ) ≤ (σ - β) * (Real.exp 1 * Real.log N) :=
        hsub.trans h2
    _ ≤ (σ - β) * (2 * Real.exp 1 * Real.log N) * ‖((σ : ℂ) + τ * I) - 1‖ := by
        have := mul_le_mul_of_nonneg_left hd (show 0 ≤ (σ - β) * (2 * Real.exp 1 * Real.log N) by
          positivity)
        linarith

theorem parte_b2 {N : ℕ} (hN1 : 1 ≤ N) (hL0 : 0 < Real.log N) {β σ τ : ℝ}
    (hβ : 1 - 1 / Real.log N ≤ β) (hβσ : β ≤ σ)
    (hd1 : 1 / 2 ≤ ‖((σ : ℂ) + τ * I) - 1‖) (hd0 : 1 / 2 ≤ ‖((β : ℂ) + τ * I) - 1‖) :
    ‖(N : ℂ) ^ (1 - ((β : ℂ) + τ * I)) *
        (1 / (((σ : ℂ) + τ * I) - 1) - 1 / (((β : ℂ) + τ * I) - 1))‖ ≤
      (σ - β) * (4 * Real.exp 1) := by
  have hσβ : 0 ≤ σ - β := by linarith
  have hE := Real.exp_pos 1
  set s1 : ℂ := (σ : ℂ) + τ * I with hs1def
  set s0 : ℂ := (β : ℂ) + τ * I with hs0def
  have hs1' : s1 - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hd1; linarith
  have hs0' : s0 - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hd0; linarith
  have hdiff : 1 / (s1 - 1) - 1 / (s0 - 1) = (s0 - s1) / ((s1 - 1) * (s0 - 1)) := by
    field_simp; ring
  have hds : s0 - s1 = ((β - σ : ℝ) : ℂ) := by simp [s0, s1]
  have hNpow : (N : ℝ) ^ (1 - β) ≤ Real.exp 1 := rpow_le_e hN1 le_rfl hL0 (by linarith)
  rw [hdiff, norm_mul, norm_div, norm_mul, hds, Complex.norm_real, Real.norm_eq_abs,
    abs_sub_comm, abs_of_nonneg hσβ, norm_natCast_cpow_of_pos (by omega),
    show (1 - s0).re = 1 - β by simp [s0]]
  have hprod : 1 / 4 ≤ ‖s1 - 1‖ * ‖s0 - 1‖ := by
    have := mul_le_mul hd1 hd0 (by norm_num) (norm_nonneg _); linarith
  have hfrac : (σ - β) / (‖s1 - 1‖ * ‖s0 - 1‖) ≤ 4 * (σ - β) := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * (σ - β) by linarith)
    linarith
  calc (N : ℝ) ^ (1 - β) * ((σ - β) / (‖s1 - 1‖ * ‖s0 - 1‖))
      ≤ Real.exp 1 * (4 * (σ - β)) := mul_le_mul hNpow hfrac (by positivity) hE.le
    _ = (σ - β) * (4 * Real.exp 1) := by ring

theorem parte_c1 {N : ℕ} (hN : 2 ≤ N) (hL0 : 0 < Real.log N) {β σ τ : ℝ}
    (hβ : 1 - 1 / Real.log N ≤ β) (hβσ : β ≤ σ) (hσ2 : 1 / 2 < σ) :
    ‖(((σ : ℂ) + τ * I) - ((β : ℂ) + τ * I)) * HN N ((σ : ℂ) + τ * I)‖ ≤
      (σ - β) * Real.exp 1 := by
  have hσβ : 0 ≤ σ - β := by linarith
  have hσ0 : 0 < σ := by linarith
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hE := Real.exp_pos 1
  have hds : ((σ : ℂ) + τ * I) - ((β : ℂ) + τ * I) = ((σ - β : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, hds, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσβ]
  have hH := norm_HN_le hN1 (s := (σ : ℂ) + τ * I) (by simp; linarith)
  rw [show ((σ : ℂ) + τ * I).re = σ by simp] at hH
  have hp : (N : ℝ) ^ (-σ) ≤ Real.exp 1 / N := rpow_neg_le hN1 le_rfl hL0 (by linarith)
  have hEN : Real.exp 1 / N ≤ Real.exp 1 / 2 := div_le_div_of_nonneg_left hE.le (by norm_num) hNr
  have hb : (N : ℝ) ^ (-σ) / σ ≤ Real.exp 1 := by
    rw [div_le_iff₀ hσ0]
    have : (N : ℝ) ^ (-σ) ≤ Real.exp 1 / 2 := hp.trans hEN
    nlinarith
  exact mul_le_mul_of_nonneg_left (hH.trans hb) hσβ

theorem parte_c2 {N : ℕ} (hN : 2 ≤ N) (hL0 : 0 < Real.log N) {β σ τ : ℝ}
    (hβ : 1 - 1 / Real.log N ≤ β) (hβσ : β ≤ σ) (hβ2 : 1 / 2 < β) (hβ1 : β ≤ 1) (hτ : |τ| ≤ N) :
    ‖((β : ℂ) + τ * I) * (HN N ((σ : ℂ) + τ * I) - HN N ((β : ℂ) + τ * I))‖ ≤
      (σ - β) * (4 * Real.exp 1 * Real.log N + 8 * Real.exp 1) := by
  have hσβ : 0 ≤ σ - β := by linarith
  have hβ0 : 0 < β := by linarith
  have hσ0 : 0 < σ := by linarith
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by linarith
  have hE := Real.exp_pos 1
  set L := Real.log N with hLdef
  set q := Real.exp 1 / N with hqdef
  have hq0 : 0 < q := by positivity
  rw [norm_mul]
  have hH := norm_HN_sub_le hN1 (τ := τ) hβ0 hβσ
  have hns : ‖(β : ℂ) + τ * I‖ ≤ 2 * N := by
    have hre : ((β : ℂ) + τ * I).re = β := by simp
    have him : ((β : ℂ) + τ * I).im = τ := by simp
    have := Complex.norm_le_abs_re_add_abs_im ((β : ℂ) + τ * I)
    rw [hre, him, abs_of_pos hβ0] at this
    linarith
  have hpβ : (N : ℝ) ^ (-β) ≤ q := rpow_neg_le hN1 le_rfl hL0 hβ
  have hpσ : (N : ℝ) ^ (-σ) ≤ q := rpow_neg_le hN1 le_rfl hL0 (by linarith)
  have hsub := rpow_sub_le hNr1 β σ
  have hpσ0 : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have hsplit : (N : ℝ) ^ (-β) / β - (N : ℝ) ^ (-σ) / σ =
      ((N : ℝ) ^ (-β) - (N : ℝ) ^ (-σ)) / β + (N : ℝ) ^ (-σ) * ((σ - β) / (β * σ)) := by
    field_simp; ring
  have hX : (N : ℝ) ^ (-β) - (N : ℝ) ^ (-σ) ≤ (σ - β) * (q * L) :=
    hsub.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpβ hL0.le) hσβ)
  have hX0 : 0 ≤ (σ - β) * (q * L) := by positivity
  have hA : ((N : ℝ) ^ (-β) - (N : ℝ) ^ (-σ)) / β ≤ 2 * ((σ - β) * (q * L)) := by
    rw [div_le_iff₀ hβ0]
    have : (σ - β) * (q * L) ≤ 2 * ((σ - β) * (q * L)) * β := by nlinarith
    linarith
  have hbs : 1 / 4 ≤ β * σ := by nlinarith
  have hq4 : (σ - β) / (β * σ) ≤ 4 * (σ - β) := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hbs (show 0 ≤ 4 * (σ - β) by linarith)
    linarith
  have hB : (N : ℝ) ^ (-σ) * ((σ - β) / (β * σ)) ≤ q * (4 * (σ - β)) :=
    mul_le_mul hpσ hq4 (div_nonneg hσβ (by linarith)) hq0.le
  have hT : ‖HN N ((σ : ℂ) + τ * I) - HN N ((β : ℂ) + τ * I)‖ ≤
      2 * ((σ - β) * (q * L)) + q * (4 * (σ - β)) := by linarith
  calc ‖(β : ℂ) + τ * I‖ * ‖HN N ((σ : ℂ) + τ * I) - HN N ((β : ℂ) + τ * I)‖
      ≤ (2 * N) * (2 * ((σ - β) * (q * L)) + q * (4 * (σ - β))) :=
        mul_le_mul hns hT (norm_nonneg _) (by positivity)
    _ = (σ - β) * (4 * Real.exp 1 * L + 8 * Real.exp 1) := by rw [hqdef]; field_simp; ring

/-- **`|ζ(σ + iτ) − ζ(β + iτ)| ≤ (σ − β)·e(L² + 7L + 13)`** perto de `Re s = 1`. -/
theorem norm_zeta_sub_le_log {N : ℕ} (hN : 2 ≤ N) (hL : 2 < Real.log N) {β σ τ : ℝ}
    (hβ : 1 - 1 / Real.log N ≤ β) (hβσ : β ≤ σ) (hβ1 : β ≤ 1) (ht1 : 1 / 2 ≤ |τ|)
    (ht2 : |τ| ≤ N) :
    ‖riemannZeta (σ + τ * I) - riemannZeta (β + τ * I)‖ ≤
      (σ - β) * (Real.exp 1 * (Real.log N ^ 2 + 7 * Real.log N + 13)) := by
  have hL0 : 0 < Real.log N := by linarith
  have hinvL := inv_log_lt hL
  have hβ2 : 1 / 2 < β := by linarith
  have hN1 : 1 ≤ N := by omega
  have hτ0 : τ ≠ 0 := by intro h; rw [h, abs_zero] at ht1; linarith
  have hd : ∀ a : ℝ, 1 / 2 ≤ ‖((a : ℂ) + τ * I) - 1‖ := by
    intro a
    have := Complex.abs_im_le_norm (((a : ℂ) + τ * I) - 1)
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add, one_im, sub_zero] at this
    linarith
  have hne : ∀ a : ℝ, ((a : ℂ) + τ * I) ≠ 1 := by
    intro a h
    have := congrArg Complex.im h
    simp at this
    exact hτ0 this
  rw [zeta_parcial (s := (σ : ℂ) + τ * I) (by simp; linarith) (hne σ) N hN1,
    zeta_parcial (s := (β : ℂ) + τ * I) (by simp; linarith) (hne β) N hN1]
  set s1 : ℂ := (σ : ℂ) + τ * I
  set s0 : ℂ := (β : ℂ) + τ * I
  have key : (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s1) + (N : ℂ) ^ (1 - s1) / (s1 - 1) -
        s1 * HN N s1) -
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s0) + (N : ℂ) ^ (1 - s0) / (s0 - 1) - s0 * HN N s0) =
      ∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-s1) - (n : ℂ) ^ (-s0)) +
        (((N : ℂ) ^ (1 - s1) - (N : ℂ) ^ (1 - s0)) / (s1 - 1) +
          (N : ℂ) ^ (1 - s0) * (1 / (s1 - 1) - 1 / (s0 - 1))) -
        ((s1 - s0) * HN N s1 + s0 * (HN N s1 - HN N s0)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [key]
  have ha := parte_a hL0 hβ hβσ τ
  have hb1 := parte_b1 hN1 hL0 hβ hβσ (hd σ)
  have hb2 := parte_b2 hN1 hL0 hβ hβσ (hd σ) (hd β)
  have hc1 := parte_c1 hN hL0 (τ := τ) hβ hβσ (by linarith)
  have hc2 := parte_c2 hN hL0 hβ hβσ hβ2 hβ1 ht2
  calc _ ≤ ‖∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-s1) - (n : ℂ) ^ (-s0))‖ +
        (‖((N : ℂ) ^ (1 - s1) - (N : ℂ) ^ (1 - s0)) / (s1 - 1)‖ +
          ‖(N : ℂ) ^ (1 - s0) * (1 / (s1 - 1) - 1 / (s0 - 1))‖) +
        (‖(s1 - s0) * HN N s1‖ + ‖s0 * (HN N s1 - HN N s0)‖) :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add le_rfl (norm_add_le _ _))) (norm_add_le _ _))
    _ ≤ (σ - β) * (Real.log N * (Real.exp 1 * (1 + Real.log N))) +
          ((σ - β) * (2 * Real.exp 1 * Real.log N) + (σ - β) * (4 * Real.exp 1)) +
          ((σ - β) * Real.exp 1 + (σ - β) * (4 * Real.exp 1 * Real.log N + 8 * Real.exp 1)) := by
        gcongr
    _ = (σ - β) * (Real.exp 1 * (Real.log N ^ 2 + 7 * Real.log N + 13)) := by ring

/-! ## A região logarítmica -/

/-- `K(L) = e(L² + 7L + 13)`: constante da cota de diferenças. -/
noncomputable def Kc (L : ℝ) : ℝ := Real.exp 1 * (L ^ 2 + 7 * L + 13)

/-- `B(L) = e(L + 7)`: constante da cota de `|ζ|`. -/
noncomputable def Bc (L : ℝ) : ℝ := Real.exp 1 * (L + 7)

/-- `N(t) = ⌈2|t|⌉`: onde cortar a soma parcial na altura `t`. -/
noncomputable def Nt (t : ℝ) : ℕ := ⌈2 * |t|⌉₊

/-- A largura com `L = log ⌈2|t|⌉`. -/
noncomputable def cN (t : ℝ) : ℝ :=
  1 / (256 * Kc (Real.log (Nt t)) ^ 4 * Bc (Real.log (Nt t)))

/-- **A largura logarítmica** `c(t) = 1/(256·K(ℓ)⁴·B(ℓ))`, `ℓ = log(3|t|)`, isto é
`c(t) = 1/(256 e⁵ (ℓ² + 7ℓ + 13)⁴ (ℓ + 7))`. -/
noncomputable def cl (t : ℝ) : ℝ :=
  1 / (256 * Kc (Real.log (3 * |t|)) ^ 4 * Bc (Real.log (3 * |t|)))

theorem Nt_props {t : ℝ} (ht : 4 ≤ |t|) :
    8 ≤ Nt t ∧ 2 * |t| ≤ (Nt t : ℝ) ∧ (Nt t : ℝ) ≤ 3 * |t| ∧ 2 < Real.log (Nt t) := by
  have h1 : 2 * |t| ≤ (Nt t : ℝ) := by unfold Nt; exact Nat.le_ceil _
  have h2 : (Nt t : ℝ) < 2 * |t| + 1 := by
    unfold Nt; exact Nat.ceil_lt_add_one (by positivity)
  have h8 : (8 : ℝ) ≤ Nt t := by linarith
  have h8' : 8 ≤ Nt t := by exact_mod_cast h8
  exact ⟨h8', h1, by linarith, log_oito.trans_le (Real.log_le_log (by norm_num) h8)⟩

theorem one_lt_e : 1 < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

theorem Kc_ge {L : ℝ} (hL : 0 ≤ L) : 1 ≤ Kc L ∧ L ≤ Kc L := by
  have hE := one_lt_e
  have hp : 0 ≤ L ^ 2 + 7 * L + 13 := by positivity
  have h : L ^ 2 + 7 * L + 13 ≤ Kc L := by
    unfold Kc; nlinarith
  constructor <;> nlinarith

theorem Bc_ge {L : ℝ} (hL : 0 ≤ L) : 1 ≤ Bc L := by
  have hE := one_lt_e
  unfold Bc; nlinarith

theorem Kc_mono {L ℓ : ℝ} (hL : 0 ≤ L) (h : L ≤ ℓ) : Kc L ≤ Kc ℓ := by
  unfold Kc
  exact mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos 1).le

theorem Bc_mono {L ℓ : ℝ} (h : L ≤ ℓ) : Bc L ≤ Bc ℓ := by
  unfold Bc
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le

/-- **Região sem zeros logarítmica** (com `L = log ⌈2|t|⌉`): para `|t| ≥ 4`, todo zero `β + it`
tem `β < 1 − 1/(256·K(L)⁴·B(L))`. -/
theorem regiao_logN {β t : ℝ} (ht : 4 ≤ |t|) (hz : riemannZeta (β + t * I) = 0) :
    β < 1 - cN t := by
  obtain ⟨h8, h2t, -, hL⟩ := Nt_props ht
  have hN : 2 ≤ Nt t := by omega
  set N := Nt t with hNdef
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  obtain ⟨hK1, hKL⟩ := Kc_ge hL0.le
  have hB1 := Bc_ge hL0.le
  set K := Kc L with hKdef
  set B := Bc L with hBdef
  set x := cN t with hxdef
  have hxeq : x = 1 / (256 * K ^ 4 * B) := rfl
  have hK4 : K ≤ K ^ 4 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
  have hK4' : 1 ≤ K ^ 4 := one_le_pow₀ hK1
  have hD : 256 ≤ 256 * K ^ 4 * B := by nlinarith
  have hDL : L ≤ 256 * K ^ 4 * B := by nlinarith
  have hx0 : 0 < x := by rw [hxeq]; positivity
  have hx1 : x ≤ 1 / 256 := by
    rw [hxeq]; exact one_div_le_one_div_of_le (by norm_num) hD
  have hxL : x ≤ 1 / L := by
    rw [hxeq]; exact one_div_le_one_div_of_le hL0 hDL
  have htN : |t| ≤ N := by linarith [abs_nonneg t]
  have ht1 : 1 / 2 ≤ |t| := by linarith
  by_contra hcon
  have hβx : 1 - x ≤ β := not_lt.mp hcon
  have hβ1 : β < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using not_lt.mp h) hz
  have hβL : 1 - 1 / L ≤ β := by linarith
  have h341 := tres_quatro_um hx0 t
  have b1 : ‖riemannZeta (1 + x)‖ ≤ 2 / x := by
    have h := norm_zeta_real_le (σ := 1 + x) (by linarith)
    push_cast at h
    refine h.trans ?_
    rw [show 1 + x - 1 = x by ring, div_le_div_iff_of_pos_right hx0]; linarith
  have b2 : ‖riemannZeta (1 + x + I * t)‖ ≤ (1 + x - β) * K := by
    have h := norm_zeta_sub_le_log hN hL (σ := 1 + x) hβL (by linarith) hβ1.le ht1 htN
    rw [hz, sub_zero] at h
    have e : ((1 + x : ℝ) : ℂ) + t * I = 1 + x + I * t := by push_cast; ring
    rw [e] at h
    exact h
  have b3 : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ B := by
    set s : ℂ := 1 + x + 2 * I * t with hsdef
    have hre : s.re = 1 + x := by simp [s]
    have him : s.im = 2 * t := by simp [s]
    have hab : |s.im| = 2 * |t| := by rw [him, abs_mul, abs_two]
    have h1L : 0 < 1 / L := by positivity
    exact norm_zeta_le_log hN hL (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [hab]; linarith) (by rw [hab]; exact h2t)
  have hδ : 0 ≤ 1 + x - β := by linarith
  have hδx : 1 + x - β ≤ 2 * x := by linarith
  have hK0 : 0 ≤ K := by linarith
  have key : ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * t)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ (2 / x) ^ 3 * (2 * x * K) ^ 4 * B := by
    have c2 : ‖riemannZeta (1 + x + I * t)‖ ≤ 2 * x * K :=
      b2.trans (mul_le_mul_of_nonneg_right hδx hK0)
    gcongr
  have hval : (2 / x) ^ 3 * (2 * x * K) ^ 4 * B = 1 / 2 := by
    have : (2 / x) ^ 3 * (2 * x * K) ^ 4 * B = 128 * x * (K ^ 4 * B) := by
      field_simp; ring
    rw [this, hxeq]; field_simp; norm_num
  linarith

theorem cN_ge_cl {t : ℝ} (ht : 4 ≤ |t|) : cl t ≤ cN t := by
  obtain ⟨h8, -, h3, hL⟩ := Nt_props ht
  have hL0 : 0 ≤ Real.log (Nt t) := by linarith
  have hle : Real.log (Nt t) ≤ Real.log (3 * |t|) :=
    Real.log_le_log (by positivity) h3
  have hK := Kc_mono hL0 hle
  have hB := Bc_mono hle
  have hK1 := (Kc_ge hL0).1
  have hB1 := Bc_ge hL0
  unfold cl cN
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

/-- **Região sem zeros logarítmica**: para `|t| ≥ 4`, todo zero `β + it` tem `β < 1 − c(t)`,
`c(t) = 1/(256 e⁵ (ℓ² + 7ℓ + 13)⁴ (ℓ + 7))`, `ℓ = log(3|t|)`. -/
theorem regiao_log {β t : ℝ} (ht : 4 ≤ |t|) (hz : riemannZeta (β + t * I) = 0) :
    β < 1 - cl t := by
  have h1 := regiao_logN ht hz
  have h2 := cN_ge_cl ht
  linarith

theorem cl_neg (t : ℝ) : cl (-t) = cl t := by unfold cl; rw [abs_neg]

/-- **A faixa se estreita logaritmicamente**: todo zero não trivial com `|Im s| ≥ 4` satisfaz
`c(Im s) < Re s < 1 − c(Im s)`. -/
theorem faixa_log : ∀ s ∈ Z, 4 ≤ |s.im| → cl s.im < s.re ∧ s.re < 1 - cl s.im := by
  intro s hs ht
  have hsplit : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  have hzs : riemannZeta ((s.re : ℂ) + (s.im : ℂ) * I) = 0 := by rw [← hsplit]; exact hs.1
  constructor
  · have h2 := tensao_mem_Z hs
    have him2 : (tensao s).im = -s.im := by unfold tensao; simp
    have hre2 : (tensao s).re = 1 - s.re := re_tensao s
    have hsplit2 : tensao s = ((tensao s).re : ℂ) + ((tensao s).im : ℂ) * I :=
      (Complex.re_add_im _).symm
    have hz2 : riemannZeta (((tensao s).re : ℂ) + ((tensao s).im : ℂ) * I) = 0 := by
      rw [← hsplit2]; exact h2.1
    have ht2 : 4 ≤ |(tensao s).im| := by rw [him2, abs_neg]; exact ht
    have := regiao_log ht2 hz2
    rw [hre2, him2, cl_neg] at this
    linarith
  · exact regiao_log ht hzs

/-- `e⁵ < 149`. -/
theorem e_cinco : Real.exp 1 ^ 5 < 149 := by
  have h := Real.exp_one_lt_d9
  have h0 := (Real.exp_pos 1).le
  calc Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := by gcongr
    _ < 149 := by norm_num

/-- **Forma simples**: `c(t) ≥ 1/(10⁹·ℓ⁹)` para `|t| ≥ 4`. -/
theorem cl_ge {t : ℝ} (ht : 4 ≤ |t|) :
    1 / (10 ^ 9 * Real.log (3 * |t|) ^ 9) ≤ cl t := by
  set ℓ := Real.log (3 * |t|) with hℓdef
  have hℓ : 2 ≤ ℓ := by
    have : (8 : ℝ) ≤ 3 * |t| := by linarith
    exact (log_oito.trans_le (Real.log_le_log (by norm_num) this)).le
  have hE := one_lt_e
  have hE0 := Real.exp_pos 1
  have h5 := e_cinco
  have hK : Kc ℓ ≤ 7.75 * Real.exp 1 * ℓ ^ 2 := by
    unfold Kc
    have : ℓ ^ 2 + 7 * ℓ + 13 ≤ 7.75 * ℓ ^ 2 := by nlinarith
    nlinarith
  have hB : Bc ℓ ≤ 4.5 * Real.exp 1 * ℓ := by
    unfold Bc
    have : ℓ + 7 ≤ 4.5 * ℓ := by linarith
    nlinarith
  have hK1 := (Kc_ge (by linarith : (0 : ℝ) ≤ ℓ)).1
  have hB1 := Bc_ge (by linarith : (0 : ℝ) ≤ ℓ)
  have hD : 256 * Kc ℓ ^ 4 * Bc ℓ ≤ 10 ^ 9 * ℓ ^ 9 := by
    calc 256 * Kc ℓ ^ 4 * Bc ℓ ≤ 256 * (7.75 * Real.exp 1 * ℓ ^ 2) ^ 4 * (4.5 * Real.exp 1 * ℓ) := by
          gcongr
      _ = 8311689 / 2 * Real.exp 1 ^ 5 * ℓ ^ 9 := by ring
      _ ≤ 8311689 / 2 * 149 * ℓ ^ 9 := by gcongr
      _ ≤ 10 ^ 9 * ℓ ^ 9 := by gcongr; norm_num
  unfold cl
  rw [← hℓdef]
  exact one_div_le_one_div_of_le (by positivity) hD

/-- **Faixa logarítmica, forma simples**: todo zero não trivial com `|Im s| ≥ 4` satisfaz
`1/(10⁹ ℓ⁹) < Re s < 1 − 1/(10⁹ ℓ⁹)`, `ℓ = log(3|Im s|)`. -/
theorem faixa_log_simples : ∀ s ∈ Z, 4 ≤ |s.im| →
    1 / (10 ^ 9 * Real.log (3 * |s.im|) ^ 9) < s.re ∧
      s.re < 1 - 1 / (10 ^ 9 * Real.log (3 * |s.im|) ^ 9) := by
  intro s hs ht
  have h := faixa_log s hs ht
  have hc := cl_ge ht
  constructor <;> linarith [h.1, h.2]

end ATK.ZetaLog

#print axioms ATK.ZetaLog.log_oito
#print axioms ATK.ZetaLog.rpow_inv_log_le
#print axioms ATK.ZetaLog.rpow_le_e
#print axioms ATK.ZetaLog.rpow_neg_le
#print axioms ATK.ZetaLog.harmonic_real
#print axioms ATK.ZetaLog.soma_rpow_le
#print axioms ATK.ZetaLog.soma_rpow_log_le
#print axioms ATK.ZetaLog.rpow_sub_le
#print axioms ATK.ZetaLog.cpow_split
#print axioms ATK.ZetaLog.norm_fase
#print axioms ATK.ZetaLog.norm_cpow_sub
#print axioms ATK.ZetaLog.norm_cpow_nat
#print axioms ATK.ZetaLog.integrableOn_rpow_N
#print axioms ATK.ZetaLog.integral_rpow_N
#print axioms ATK.ZetaLog.norm_HN_le
#print axioms ATK.ZetaLog.norm_HN_sub_le
#print axioms ATK.ZetaLog.inv_log_lt
#print axioms ATK.ZetaLog.norm_zeta_le_log
#print axioms ATK.ZetaLog.parte_a
#print axioms ATK.ZetaLog.norm_N_sub
#print axioms ATK.ZetaLog.parte_b1
#print axioms ATK.ZetaLog.parte_b2
#print axioms ATK.ZetaLog.parte_c1
#print axioms ATK.ZetaLog.parte_c2
#print axioms ATK.ZetaLog.norm_zeta_sub_le_log
#print axioms ATK.ZetaLog.Nt_props
#print axioms ATK.ZetaLog.one_lt_e
#print axioms ATK.ZetaLog.Kc_ge
#print axioms ATK.ZetaLog.Bc_ge
#print axioms ATK.ZetaLog.Kc_mono
#print axioms ATK.ZetaLog.Bc_mono
#print axioms ATK.ZetaLog.regiao_logN
#print axioms ATK.ZetaLog.cN_ge_cl
#print axioms ATK.ZetaLog.regiao_log
#print axioms ATK.ZetaLog.cl_neg
#print axioms ATK.ZetaLog.faixa_log
#print axioms ATK.ZetaLog.e_cinco
#print axioms ATK.ZetaLog.cl_ge
#print axioms ATK.ZetaLog.faixa_log_simples
