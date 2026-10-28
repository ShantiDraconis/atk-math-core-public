import ATK.ZeroClasses.LittlewoodRH
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Stirling complexo: um logaritmo holomorfo de `Γ` e `log Γ(z) = (z − ½) log z − z + ½ log 2π + O(1/|Im z|)`
(rodada 39)

A Mathlib tem Stirling para `n!` (`Stirling.tendsto_stirlingSeq_sqrt_pi`) e a sequência de Gauss
`GammaSeq z n → Γ(z)`, mas nenhum logaritmo de `Γ` complexa nem a sua assintótica. Aqui:

* `ell z = (z − ½) log z − z + ½ log 2π − Σ_k e_k(z)`, com o termo de Euler–Maclaurin explícito
  `e_k(z) = 1 − (z + k + ½)(log(z + k + 1) − log(z + k))` (`ek`); a soma telescópica `soma_log` é exata, sem
  integrais;
* `|e_k(z)| ≤ 2/|z + k|²` (`norm_ek_le`, pela série de Taylor de `log(1 + x)` da Mathlib), logo a série converge em
  `Re z > 0` e `Σ_k |e_k(z)| ≤ 8/|Im z|` para `|Im z| ≥ 2` (`tsum_norm_ek_le`);
* `log GammaSeq(z, n) → ell z` (`tendsto_lgs`, com Stirling para `n!`), logo **`exp (ell z) = Γ(z)`** (`exp_ell`);
* `ell` é **holomorfa** em `Re z > 0` (`ell_diff`), com **`ell′ = ψ`** (`hasDerivAt_ell`), real no eixo real
  (`ell_real`);
* **Stirling** (`stirling`): `‖ell z − ((z − ½) log z − z + ½ log 2π)‖ ≤ 8/|Im z|` para `Re z > 0`, `|Im z| ≥ 2`;
* a fase usada em Riemann–von Mangoldt (`im_ell_quarto`): `|Im ell(¼ + iτ) − (τ log τ − τ − π/8)| ≤ 9/τ`.

Classificação (rodada 39): **ferramenta** — o termo principal `(T/2π) log(T/2π) − T/2π` de Riemann–von Mangoldt.
RH continua OPEN_MATH.
-/

open Complex Set Filter Topology
open scoped Real Nat

namespace ATK.ZeroClasses.StirlingComplexo

/-! ## 1. O termo de Euler–Maclaurin -/

/-- O termo de Euler–Maclaurin de `log` no intervalo `[k, k + 1]`. -/
noncomputable def ek (z : ℂ) (k : ℕ) : ℂ := 1 - (z + k + 1 / 2) * (log (z + k + 1) - log (z + k))

theorem log_succ_sub {w : ℂ} (hw : 0 < w.re) : log (w + 1) - log w = log (1 + w⁻¹) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hu : 0 < (1 + w⁻¹).re := by
    rw [add_re, one_re, inv_re]
    have : 0 ≤ w.re / normSq w := div_nonneg hw.le (normSq_nonneg w)
    linarith
  have hu0 : 1 + w⁻¹ ≠ 0 := by
    intro h
    rw [h, zero_re] at hu
    linarith
  have e : w + 1 = w * (1 + w⁻¹) := by field_simp
  have harg := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have harg2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  rw [e, log_mul hw0 hu0 ⟨by linarith [(abs_lt.mp harg).1, (abs_lt.mp harg2).1],
    by linarith [(abs_lt.mp harg).2, (abs_lt.mp harg2).2]⟩]
  ring

/-- **A cota do termo**: `|1 − (w + ½)(log(w + 1) − log w)| ≤ 2/|w|²` para `Re w > 0`, `|w| ≥ 2`. -/
theorem norm_ek_le {w : ℂ} (hw : 0 < w.re) (h2 : 2 ≤ ‖w‖) :
    ‖1 - (w + 1 / 2) * (log (w + 1) - log w)‖ ≤ 2 / ‖w‖ ^ 2 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  rw [log_succ_sub hw]
  set x := w⁻¹ with hx
  have hwpos : 0 < ‖w‖ := by linarith
  have hxn : ‖x‖ = ‖w‖⁻¹ := norm_inv w
  have hxpos : 0 < ‖x‖ := by rw [hxn]; positivity
  have hx2 : ‖x‖ ≤ 1 / 2 := by
    rw [hxn, inv_le_comm₀ hwpos (by norm_num)]
    linarith
  have hx1 : ‖x‖ < 1 := by linarith
  have hwx : w * x = 1 := mul_inv_cancel₀ hw0
  set R := log (1 + x) - logTaylor 3 x with hR
  have hT : logTaylor 3 x = x - x ^ 2 / 2 := by
    simp [logTaylor, Finset.sum_range_succ]
    ring
  have hRb : ‖R‖ ≤ ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹ / 3 := by
    have := Complex.norm_log_sub_logTaylor_le 2 hx1
    norm_num at this
    exact this
  have hlog : log (1 + x) = x - x ^ 2 / 2 + R := by rw [hR, hT]; ring
  have e : 1 - (w + 1 / 2) * log (1 + x) = x ^ 2 / 4 - (w + 1 / 2) * R := by
    rw [hlog]
    linear_combination (x / 2 - 1) * hwx
  rw [e]
  have hR' : ‖R‖ ≤ 2 / 3 * ‖x‖ ^ 3 := by
    have hinv : (1 - ‖x‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖R‖ ≤ ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹ / 3 := hRb
      _ ≤ ‖x‖ ^ 3 * 2 / 3 := by gcongr
      _ = 2 / 3 * ‖x‖ ^ 3 := by ring
  have hwn : ‖w‖ = ‖x‖⁻¹ := by rw [hxn, inv_inv]
  have hwh : ‖w + 1 / 2‖ ≤ ‖x‖⁻¹ + 1 / 2 := by
    calc ‖w + 1 / 2‖ ≤ ‖w‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ = ‖x‖⁻¹ + 1 / 2 := by rw [hwn]; norm_num
  have hx4 : ‖x ^ 2 / 4‖ = ‖x‖ ^ 2 / 4 := by rw [norm_div, norm_pow]; norm_num
  have hprod : ‖(w + 1 / 2) * R‖ ≤ (‖x‖⁻¹ + 1 / 2) * (2 / 3 * ‖x‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hwh hR' (norm_nonneg _) (by positivity)
  have hcomp : (‖x‖⁻¹ + 1 / 2) * (2 / 3 * ‖x‖ ^ 3) = 2 / 3 * ‖x‖ ^ 2 + 1 / 3 * ‖x‖ ^ 3 := by
    field_simp
  calc ‖x ^ 2 / 4 - (w + 1 / 2) * R‖ ≤ ‖x ^ 2 / 4‖ + ‖(w + 1 / 2) * R‖ := norm_sub_le _ _
    _ ≤ ‖x‖ ^ 2 / 4 + (2 / 3 * ‖x‖ ^ 2 + 1 / 3 * ‖x‖ ^ 3) := by rw [hx4, ← hcomp]; linarith
    _ ≤ 2 * ‖x‖ ^ 2 := by nlinarith [pow_pos hxpos 2]
    _ = 2 / ‖w‖ ^ 2 := by rw [hxn]; field_simp

theorem re_add_nat {z : ℂ} (k : ℕ) : (z + k).re = z.re + k := by simp

theorem norm_ek_le' {z : ℂ} (hz : 0 < z.re) (k : ℕ) (h2 : 2 ≤ ‖z + k‖) :
    ‖ek z k‖ ≤ 2 / ‖z + k‖ ^ 2 := by
  have hw : 0 < (z + k).re := by rw [re_add_nat]; positivity
  exact norm_ek_le hw h2

/-- Para `k ≥ 2`: `|e_k(z)| ≤ 2/k²` uniformemente em `Re z > 0`. -/
theorem ek_le_k {z : ℂ} (hz : 0 < z.re) (k : ℕ) (hk : 2 ≤ k) : ‖ek z k‖ ≤ 2 / (k : ℝ) ^ 2 := by
  have hk' : (k : ℝ) ≤ ‖z + k‖ := by
    have := Complex.re_le_norm (z + k)
    rw [re_add_nat] at this
    linarith
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  calc ‖ek z k‖ ≤ 2 / ‖z + k‖ ^ 2 := norm_ek_le' hz k (le_trans hk2 hk')
    _ ≤ 2 / (k : ℝ) ^ 2 := by gcongr

theorem summable_aux : Summable (fun k : ℕ => 2 / ((k : ℝ) + 2) ^ 2) := by
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) ^ 2)) := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hs2 := ((summable_nat_add_iff 2).mpr hs).mul_left 2
  refine hs2.congr fun k => ?_
  push_cast
  ring

theorem summable_norm_ek {z : ℂ} (hz : 0 < z.re) : Summable (fun k => ‖ek z k‖) := by
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) summable_aux
  have := ek_le_k hz (k + 2) (by omega)
  push_cast at this
  exact this

theorem summable_ek {z : ℂ} (hz : 0 < z.re) : Summable (ek z) := (summable_norm_ek hz).of_norm

/-- `Σ_k |e_k(z)| ≤ 8/|Im z|` para `|Im z| ≥ 2`. -/
theorem tsum_norm_ek_le {z : ℂ} (hz : 0 < z.re) (hv : 2 ≤ |z.im|) : ∑' k, ‖ek z k‖ ≤ 8 / |z.im| := by
  set v := |z.im| with hvdef
  have hterm : ∀ k : ℕ, ‖ek z k‖ ≤ 4 * (1 / ((k : ℝ) + v - 1) - 1 / ((k : ℝ) + v)) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsq : ‖z + k‖ ^ 2 = (z.re + k) ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, re_add_nat]
      simp only [add_im, natCast_im, add_zero]
      ring
    have hv2 : z.im ^ 2 = v ^ 2 := (sq_abs _).symm
    have hn2 : ((k : ℝ) + v) ^ 2 ≤ 2 * ‖z + k‖ ^ 2 := by
      rw [hsq, hv2]
      nlinarith [sq_nonneg ((k : ℝ) - v), mul_pos hz hz, mul_nonneg hz.le hk0]
    have hge2 : 2 ≤ ‖z + k‖ := by
      have := Complex.abs_im_le_norm (z + k)
      simp only [add_im, natCast_im, add_zero] at this
      linarith
    have hpos : 0 < (k : ℝ) + v - 1 := by linarith
    have ha : 0 < (k : ℝ) + v := by linarith
    have hnz : 0 < ‖z + k‖ ^ 2 := by positivity
    calc ‖ek z k‖ ≤ 2 / ‖z + k‖ ^ 2 := norm_ek_le' hz k hge2
      _ ≤ 4 / ((k : ℝ) + v) ^ 2 := by
          rw [div_le_div_iff₀ hnz (by positivity)]
          nlinarith
      _ ≤ 4 * (1 / ((k : ℝ) + v - 1) - 1 / ((k : ℝ) + v)) := by
          have e : 1 / ((k : ℝ) + v - 1) - 1 / ((k : ℝ) + v) =
              1 / (((k : ℝ) + v - 1) * ((k : ℝ) + v)) := by
            field_simp
            ring
          rw [e, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + v - 1) - 1 / ((k : ℝ) + v)) =
      1 / (v - 1) - 1 / ((n : ℝ) + v - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  refine Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) fun n => ?_
  have hn0 : 0 < (n : ℝ) + v - 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  calc ∑ k ∈ Finset.range n, ‖ek z k‖
      ≤ ∑ k ∈ Finset.range n, 4 * (1 / ((k : ℝ) + v - 1) - 1 / ((k : ℝ) + v)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 4 * (1 / (v - 1) - 1 / ((n : ℝ) + v - 1)) := by rw [← Finset.mul_sum, htel]
    _ ≤ 4 * (1 / (v - 1)) := by
        have : 0 ≤ 1 / ((n : ℝ) + v - 1) := by positivity
        linarith
    _ ≤ 8 / v := by
        rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith

/-! ## 2. A soma telescópica exata -/

/-- **Euler–Maclaurin exato** para `log`: `Σ_{k ≤ n} log(z + k) = [F]₀ⁿ + (log z + log(z + n))/2 + Σ_{k<n} e_k`,
`F(t) = (z + t) log(z + t) − (z + t)`. -/
theorem soma_log (z : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), log (z + k) =
      ((z + n) * log (z + n) - (z + n)) - (z * log z - z) + (log z + log (z + n)) / 2 +
        ∑ k ∈ Finset.range n, ek z k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (ek z)]
    simp only [ek]
    push_cast
    simp only [← add_assoc]
    ring

/-! ## 3. O logaritmo da sequência de Gauss -/

/-- `log GammaSeq(z, n) = z log n + log n! − Σ_{k ≤ n} log(z + k)`. -/
noncomputable def lgs (n : ℕ) (z : ℂ) : ℂ :=
  z * (Real.log n : ℂ) + (Real.log (n ! : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), log (z + k)

theorem add_nat_ne_zero {z : ℂ} (hz : 0 < z.re) (k : ℕ) : z + k ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_add_nat, zero_re] at this
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem exp_lgs {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) : cexp (lgs n z) = GammaSeq z n := by
  unfold lgs GammaSeq
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_sum]
  have h1 : cexp (z * (Real.log n : ℂ)) = (n : ℂ) ^ z := by
    rw [cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), mul_comm, Complex.ofReal_log (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
  have h2 : cexp (Real.log (n ! : ℝ) : ℂ) = (n ! : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
    push_cast
    rfl
  rw [h1, h2, Finset.prod_congr rfl fun k _ => Complex.exp_log (add_nat_ne_zero hz k)]

/-- `log n! = (log s_n − ½ log π) + ½ log 2π + (n + ½) log n − n`, com `s_n` a sequência de Stirling. -/
theorem log_fatorial (n : ℕ) (hn : n ≠ 0) :
    Real.log (n ! : ℝ) = (Real.log (Stirling.stirlingSeq n) - Real.log π / 2) + Real.log (2 * π) / 2 +
      (n + 1 / 2) * Real.log n - n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) hn'.ne', Real.log_div hn'.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
  linarith

theorem lgs_eq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    lgs n z = (z - 1 / 2) * log z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) +
      ((Real.log (Stirling.stirlingSeq n) - Real.log π / 2 : ℝ) : ℂ) -
      (z + n + 1 / 2) * log (1 + z / n) - ∑ k ∈ Finset.range n, ek z k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hu : 1 + z / n ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [add_re, one_re, zero_re, div_natCast_re] at this
    have : 0 < z.re / n := div_pos hz hn'
    linarith
  have hzn : log (z + n) = (Real.log n : ℂ) + log (1 + z / n) := by
    have e : z + n = ((n : ℝ) : ℂ) * (1 + z / n) := by
      push_cast
      field_simp
      ring
    rw [e, log_ofReal_mul hn' hu]
  unfold lgs
  rw [soma_log, hzn, log_fatorial n hn]
  push_cast
  ring

/-! ## 4. O logaritmo de Γ -/

/-- A soma dos termos de Euler–Maclaurin. -/
noncomputable def EE (z : ℂ) : ℂ := ∑' k, ek z k

/-- **O logaritmo holomorfo de `Γ`** em `Re z > 0`. -/
noncomputable def ell (z : ℂ) : ℂ := (z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) - EE z

theorem tendsto_lgs {z : ℂ} (hz : 0 < z.re) : Tendsto (fun n => lgs n z) atTop (𝓝 (ell z)) := by
  have h1 : Tendsto (fun n : ℕ => ((Real.log (Stirling.stirlingSeq n) - Real.log π / 2 : ℝ) : ℂ)) atTop
      (𝓝 0) := by
    have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)
    have e : Real.log √π = Real.log π / 2 := by
      rw [Real.log_sqrt Real.pi_pos.le]
    rw [e] at hs
    have hs2 := hs.sub_const (Real.log π / 2)
    rw [sub_self] at hs2
    have := (Complex.continuous_ofReal.tendsto 0).comp hs2
    rw [Complex.ofReal_zero] at this
    exact this
  have h2 : Tendsto (fun n : ℕ => (z + n + 1 / 2) * log (1 + z / n)) atTop (𝓝 z) := by
    have hg : Tendsto (fun n : ℕ => (n : ℂ) * (z / n)) atTop (𝓝 z) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp [Nat.cast_ne_zero.mpr hn]
    have ha := tendsto_nat_mul_log_one_add_of_tendsto hg
    have hzn : Tendsto (fun n : ℕ => z / (n : ℂ)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul z
      simpa [div_eq_mul_inv] using this
    have hb : Tendsto (fun n : ℕ => log (1 + z / n)) atTop (𝓝 0) := by
      have hc : ContinuousAt log 1 := continuousAt_clog (by simp)
      have h1 := hzn.const_add 1
      rw [add_zero] at h1
      have := hc.tendsto.comp h1
      rw [log_one] at this
      exact this
    have := ha.add (hb.const_mul (z + 1 / 2))
    rw [mul_zero, add_zero] at this
    refine this.congr fun n => ?_
    ring
  have h3 : Tendsto (fun n => ∑ k ∈ Finset.range n, ek z k) atTop (𝓝 (EE z)) :=
    (summable_ek hz).hasSum.tendsto_sum_nat
  have hlim := (((tendsto_const_nhds (x := (z - 1 / 2) * log z + ((Real.log (2 * π) / 2 : ℝ) : ℂ))).add
    h1).sub h2).sub h3
  have e : (z - 1 / 2) * log z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) + 0 - z - EE z = ell z := by
    unfold ell
    ring
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (lgs_eq hz hn).symm

/-- **`exp (ell z) = Γ(z)`** em `Re z > 0`. -/
theorem exp_ell {z : ℂ} (hz : 0 < z.re) : cexp (ell z) = Gamma z := by
  have h1 : Tendsto (fun n => cexp (lgs n z)) atTop (𝓝 (cexp (ell z))) :=
    (Complex.continuous_exp.tendsto _).comp (tendsto_lgs hz)
  have h2 : Tendsto (fun n => cexp (lgs n z)) atTop (𝓝 (Gamma z)) := by
    refine (Complex.GammaSeq_tendsto_Gamma z).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (exp_lgs hz hn).symm
  exact tendsto_nhds_unique h1 h2

theorem mem_slit {z : ℂ} (hz : 0 < z.re) (k : ℕ) : z + k ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (by rw [re_add_nat]; positivity))

theorem ek_diff (k : ℕ) : DifferentiableOn ℂ (fun z => ek z k) {z : ℂ | 0 < z.re} := by
  intro z hz
  have hz' : 0 < z.re := hz
  have h0 : z + k ∈ slitPlane := mem_slit hz' k
  have h1 : z + k + 1 ∈ slitPlane := by
    have := mem_slit hz' (k + 1)
    push_cast at this
    rwa [← add_assoc] at this
  apply DifferentiableAt.differentiableWithinAt
  unfold ek
  exact (differentiableAt_const 1).sub (((differentiableAt_id.add_const _).add_const _).mul
    ((((differentiableAt_id.add_const _).add_const 1).clog h1).sub
      ((differentiableAt_id.add_const _).clog h0)))

/-- **`ell` é holomorfa** em `Re z > 0`. -/
theorem ell_diff : DifferentiableOn ℂ ell {z : ℂ | 0 < z.re} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have htail : DifferentiableOn ℂ (fun w => ∑' k : ℕ, ek w (k + 2)) {z : ℂ | 0 < z.re} :=
    differentiableOn_tsum_of_summable_norm summable_aux (fun k => ek_diff (k + 2)) hU
      (fun k w hw => by
        have := ek_le_k hw (k + 2) (by omega)
        push_cast at this
        exact this)
  have hEE : ∀ w ∈ {z : ℂ | 0 < z.re}, EE w = ek w 0 + ek w 1 + ∑' k : ℕ, ek w (k + 2) := by
    intro w hw
    rw [EE, ← (summable_ek hw).sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ]
  intro z hz
  have hz' : 0 < z.re := hz
  have hlog : DifferentiableAt ℂ log z := differentiableAt_log (mem_slitPlane_iff.mpr (Or.inl hz'))
  have hE : DifferentiableWithinAt ℂ EE {z : ℂ | 0 < z.re} z :=
    (((ek_diff 0 z hz).add (ek_diff 1 z hz)).add (htail z hz)).congr hEE (hEE z hz)
  exact ((((differentiableAt_id.sub_const _).mul hlog).sub differentiableAt_id).add_const
    _).differentiableWithinAt.sub hE

/-- **`ell′ = ψ`**: a derivada de `ell` é a digama da Mathlib. -/
theorem hasDerivAt_ell {z : ℂ} (hz : 0 < z.re) : HasDerivAt ell (digamma z) z := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableAt ℂ ell z := ell_diff.differentiableAt (hU.mem_nhds hz)
  have hev : Gamma =ᶠ[𝓝 z] fun w => cexp (ell w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (exp_ell hw).symm
  have hG : HasDerivAt Gamma (cexp (ell z) * deriv ell z) z :=
    (hd.hasDerivAt.cexp).congr_of_eventuallyEq hev
  have hΓ : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz
  have e : digamma z = deriv ell z := by
    rw [digamma_def, logDeriv_apply, hG.deriv, exp_ell hz]
    field_simp
  rw [e]
  exact hd.hasDerivAt

/-- `ell` é real no eixo real positivo. -/
theorem ell_real {x : ℝ} (hx : 0 < x) : (ell x).im = 0 := by
  have hr : ∀ r : ℝ, 0 ≤ r → (log (r : ℂ)).im = 0 := by
    intro r hr
    rw [← Complex.ofReal_log hr, ofReal_im]
  have hk : ∀ k : ℕ, (ek x k).im = 0 := by
    intro k
    have e0 : (x : ℂ) + k = ((x + k : ℝ) : ℂ) := by push_cast; ring
    have e1 : (x : ℂ) + k + 1 = ((x + k + 1 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (x : ℂ) + k + 1 / 2 = ((x + k + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    unfold ek
    rw [e1, e2, e0, ← Complex.ofReal_log (by linarith), ← Complex.ofReal_log (by linarith)]
    simp
  have hsum := summable_ek (z := (x : ℂ)) (by simpa using hx)
  have hEE : (EE x).im = 0 := by
    rw [EE, Complex.im_tsum hsum]
    simp [hk]
  unfold ell
  simp only [sub_im, mul_im, add_im, ofReal_im, hEE, hr x hx.le]
  simp

/-! ## 5. Stirling -/

/-- **Stirling complexo**: `‖log Γ(z) − ((z − ½) log z − z + ½ log 2π)‖ ≤ 8/|Im z|` para `Re z > 0`, `|Im z| ≥ 2`,
com `log Γ = ell` (`exp_ell`). -/
theorem stirling {z : ℂ} (hz : 0 < z.re) (hv : 2 ≤ |z.im|) :
    ‖ell z - ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ))‖ ≤ 8 / |z.im| := by
  have e : ell z - ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)) = -EE z := by
    unfold ell
    ring
  rw [e, norm_neg]
  calc ‖EE z‖ ≤ ∑' k, ‖ek z k‖ := norm_tsum_le_tsum_norm (summable_norm_ek hz)
    _ ≤ 8 / |z.im| := tsum_norm_ek_le hz hv

/-- **A fase de `Γ` em `¼ + iτ`**: `|Im log Γ(¼ + iτ) − (τ log τ − τ − π/8)| ≤ 9/τ` para `τ ≥ 2`. -/
theorem im_ell_quarto {τ : ℝ} (hτ : 2 ≤ τ) :
    |(ell (1 / 4 + τ * I)).im - (τ * Real.log τ - τ - π / 8)| ≤ 9 / τ := by
  set z : ℂ := 1 / 4 + τ * I with hzdef
  have hτ0 : 0 < τ := by linarith
  have hzre : z.re = 1 / 4 := by simp [hzdef]
  have hzim : z.im = τ := by simp [hzdef]
  have hs := stirling (z := z) (by rw [hzre]; norm_num) (by rw [hzim, abs_of_pos hτ0]; exact hτ)
  rw [hzim, abs_of_pos hτ0] at hs
  have hmain : ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)).im =
      τ * Real.log ‖z‖ - arg z / 4 - τ := by
    simp only [add_im, sub_im, mul_im, log_re, log_im, ofReal_im, hzim]
    simp
    rw [hzre]
    ring
  have hzn2 : ‖z‖ ^ 2 = τ ^ 2 + 1 / 16 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
    ring
  have hzτ : τ ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rwa [hzim, abs_of_pos hτ0] at this
  have hzτ2 : ‖z‖ ≤ τ + 1 / (32 * τ) := by
    have h1 : (τ + 1 / (32 * τ)) ^ 2 ≥ ‖z‖ ^ 2 := by
      rw [hzn2]
      have : (τ + 1 / (32 * τ)) ^ 2 = τ ^ 2 + 1 / 16 + (1 / (32 * τ)) ^ 2 := by
        field_simp
        ring
      rw [this]
      nlinarith [sq_nonneg (1 / (32 * τ))]
    nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - (τ + 1 / (32 * τ))), show 0 < τ + 1 / (32 * τ) by positivity]
  have hlog1 : Real.log τ ≤ Real.log ‖z‖ := Real.log_le_log hτ0 hzτ
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hτ0 hzτ
  have hlog2 : Real.log ‖z‖ - Real.log τ ≤ 1 / (32 * τ ^ 2) := by
    rw [← Real.log_div hzpos.ne' hτ0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hzpos hτ0)
    have h2 : ‖z‖ / τ - 1 ≤ 1 / (32 * τ ^ 2) := by
      have h3 : ‖z‖ - τ ≤ 1 / (32 * τ) := by linarith [hzτ2]
      have e : ‖z‖ / τ - 1 = (‖z‖ - τ) / τ := by rw [sub_div, div_self hτ0.ne']
      rw [e]
      calc (‖z‖ - τ) / τ ≤ (1 / (32 * τ)) / τ := div_le_div_of_nonneg_right h3 hτ0.le
        _ = 1 / (32 * τ ^ 2) := by rw [div_div, show 32 * τ * τ = 32 * τ ^ 2 by ring]
    linarith
  have harg1 : arg z ≤ π / 2 := arg_le_pi_div_two_iff.mpr (Or.inl (by rw [hzre]; norm_num))
  have harg2 : π / 2 - 1 / (4 * τ) ≤ arg z := by
    have habs := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hzre]; norm_num : 0 < z.re))
    have htan : Real.tan (arg z) = 4 * τ := by
      rw [tan_arg, hzre, hzim]
      ring
    have hat : Real.arctan (4 * τ) = arg z := by
      rw [← htan, Real.arctan_tan (abs_lt.mp habs).1 (abs_lt.mp habs).2]
    have hinv := Real.arctan_inv_of_pos (show 0 < 4 * τ by positivity)
    have hle := Real.arctan_le_self (show 0 ≤ (4 * τ)⁻¹ by positivity)
    rw [← hat]
    rw [one_div]
    linarith
  have hdiff : |(ell z).im - ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)).im| ≤ 8 / τ := by
    rw [← sub_im]
    exact (Complex.abs_im_le_norm _).trans hs
  rw [hmain] at hdiff
  have h32 : τ * (1 / (32 * τ ^ 2)) = 1 / (32 * τ) := by field_simp
  have hA : 0 ≤ τ * (Real.log ‖z‖ - Real.log τ) := mul_nonneg hτ0.le (by linarith)
  have hB : τ * (Real.log ‖z‖ - Real.log τ) ≤ 1 / (32 * τ) := by
    rw [← h32]
    exact mul_le_mul_of_nonneg_left hlog2 hτ0.le
  have h1 : 1 / (32 * τ) + 1 / (4 * τ) / 4 ≤ 1 / τ := by
    rw [show 1 / (32 * τ) + 1 / (4 * τ) / 4 = (3 / 32) / τ by field_simp; ring]
    exact div_le_div_of_nonneg_right (by norm_num) hτ0.le
  rw [abs_le] at hdiff ⊢
  have h9 : 8 / τ + 1 / τ = 9 / τ := by ring
  constructor <;> nlinarith [hdiff.1, hdiff.2]

end ATK.ZeroClasses.StirlingComplexo

#print axioms ATK.ZeroClasses.StirlingComplexo.log_succ_sub
#print axioms ATK.ZeroClasses.StirlingComplexo.norm_ek_le
#print axioms ATK.ZeroClasses.StirlingComplexo.re_add_nat
#print axioms ATK.ZeroClasses.StirlingComplexo.norm_ek_le'
#print axioms ATK.ZeroClasses.StirlingComplexo.ek_le_k
#print axioms ATK.ZeroClasses.StirlingComplexo.summable_aux
#print axioms ATK.ZeroClasses.StirlingComplexo.summable_norm_ek
#print axioms ATK.ZeroClasses.StirlingComplexo.summable_ek
#print axioms ATK.ZeroClasses.StirlingComplexo.tsum_norm_ek_le
#print axioms ATK.ZeroClasses.StirlingComplexo.soma_log
#print axioms ATK.ZeroClasses.StirlingComplexo.add_nat_ne_zero
#print axioms ATK.ZeroClasses.StirlingComplexo.exp_lgs
#print axioms ATK.ZeroClasses.StirlingComplexo.log_fatorial
#print axioms ATK.ZeroClasses.StirlingComplexo.lgs_eq
#print axioms ATK.ZeroClasses.StirlingComplexo.tendsto_lgs
#print axioms ATK.ZeroClasses.StirlingComplexo.exp_ell
#print axioms ATK.ZeroClasses.StirlingComplexo.mem_slit
#print axioms ATK.ZeroClasses.StirlingComplexo.ek_diff
#print axioms ATK.ZeroClasses.StirlingComplexo.ell_diff
#print axioms ATK.ZeroClasses.StirlingComplexo.hasDerivAt_ell
#print axioms ATK.ZeroClasses.StirlingComplexo.ell_real
#print axioms ATK.ZeroClasses.StirlingComplexo.stirling
#print axioms ATK.ZeroClasses.StirlingComplexo.im_ell_quarto
