import ATK.ZeroClasses.LittlewoodMedia
import ATK.ZeroClasses.LittlewoodTeta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Littlewood para `π(x) − Li(x)` sob RH (rodada 95)

**Sob RH, `π(x) − Li(x) = Ω±(√x log log log x/log x)`** (`pi_littlewood_RH`), com `Li(x) = ∫₂ˣ dt/log t`, e
portanto `π(x) − Li(x)` troca de sinal infinitas vezes (`pi_troca_sinal_RH`).

* §1 `Li` é o de `PiLi` (rodada 60). `Li_eq`: `Li(x) = x/log x − 2/log 2 + ∫₂ˣ dt/log² t`; **`pi_sub_Li`**: com a fórmula
  de Abel da Mathlib (`Chebyshev.primeCounting_eq_theta_div_log_add_integral`; as provas são as de `PiLi` e `PiLiRH`),
  `π(x) − Li(x) = (θ(x) − x)/log x + 2/log 2 + ∫₂ˣ (θ(t) − t) dt/(t log² t)`.
* §2 `integral_exp_subst`, `E_subst`: a troca `t = e^w` sem hipóteses sobre o integrando
  (`integral_Icc_deriv_smul_of_deriv_nonneg`).
* §3 `Fpsi_right_cont` (`F` contínua à direita), `integral_gpeso_le` (`∫₁ʸ e^{w/2}/w² ≤ 7e⁴ + 4e^{y/2}/y²`) e
  **`integral_Fg_le`**: por partes com `I(w) = ∫₁ʷ F = O(log w)` (rodada 94),
  `|∫₁ʸ F(w)e^{w/2}/w² dw| ≤ K(1 + log y)(1 + e^{y/2}/y²)`.
* §4 `resto_pi_le`: `|2/log 2 + E(x)| ≤ K(1 + log log x)(1 + √x/log² x)` (com `ψ − θ ≤ C√x` da Mathlib), que é
  `o(√x log log log x/log x)`; com `theta_littlewood` (rodada 93) sai `pi_littlewood_RH`.

Classificação: **consequência** (de RH; Littlewood 1914). A versão incondicional precisa do caso `¬RH`
(`π(x) − Li(x) = Ω±(x^θ)` para `θ < Θ`, via Landau para `log ζ`), BUILD_PENDING. RH continua OPEN_MATH.
-/

open Set Filter Topology MeasureTheory
open scoped Real Interval

namespace ATK.ZeroClasses.LittlewoodPi

open ATK.ZeroClasses.LittlewoodBase (Fpsi)

/-! ## 1. `Li` e a fórmula `π − Li = (θ − x)/log x + 2/log 2 + ∫ (θ(t) − t)/(t log² t)` -/

open ATK.ZeroClasses.PiLi (Li Li_partes log_pos_of_ge)

theorem log_pos_of_two_le {t : ℝ} (ht : 2 ≤ t) : 0 < Real.log t := log_pos_of_ge ht

theorem continuousOn_inv_log_pow (n : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    ContinuousOn (fun t => 1 / Real.log t ^ n) (Set.uIcc 2 x) := by
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  have h0 : t ≠ 0 := by linarith [ht.1]
  have hl : Real.log t ^ n ≠ 0 := pow_ne_zero _ (log_pos_of_two_le ht.1).ne'
  exact (continuousAt_const.div ((Real.continuousAt_log h0).pow n) hl).continuousWithinAt

/-- **Integração por partes de `Li`**: `Li(x) = x/log x − 2/log 2 + ∫₂ˣ dt/log² t` (é `PiLi.Li_partes`). -/
theorem Li_eq {x : ℝ} (hx : 2 ≤ x) :
    Li x = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 :=
  Li_partes hx

/-- **`π(x) − Li(x) = (θ(x) − x)/log x + 2/log 2 + ∫₂ˣ (θ(t) − t)/(t log² t) dt`** para `x ≥ 2` (é
`PiLiRH.pi_sub_Li`, com os termos noutra ordem). -/
theorem pi_sub_Li {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x = (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2 +
      ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  rw [ATK.ZeroClasses.PiLiRH.pi_sub_Li hx]
  ring

/-! ## 2. A troca `t = e^w` -/

/-- `∫_{e^a}^{e^b} g(t) dt = ∫ₐᵇ e^w g(e^w) dw` para `a ≤ b`, sem hipóteses sobre `g`. -/
theorem integral_exp_subst (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Real.exp a..Real.exp b, g t = ∫ w in a..b, Real.exp w * g (Real.exp w) := by
  have h := integral_Icc_deriv_smul_of_deriv_nonneg (f := Real.exp) (f' := Real.exp) (g := g)
    Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le) hab
  simp only [smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hab), intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, h]

/-- **`E(x) = ∫₂ˣ (θ(t) − t)/(t log² t) dt = ∫_{log 2}^{log x} (θ(e^w) − e^w)/w² dw`**. -/
theorem E_subst {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) =
      ∫ w in Real.log 2..Real.log x, (Chebyshev.theta (Real.exp w) - Real.exp w) / w ^ 2 := by
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have hx' : Real.exp (Real.log x) = x := Real.exp_log (by linarith)
  have h := integral_exp_subst (fun t => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
    (Real.log_le_log (by norm_num) hx)
  rw [h2, hx'] at h
  rw [h]
  refine intervalIntegral.integral_congr fun w _ => ?_
  simp only [Real.log_exp]
  have he := (Real.exp_pos w).ne'
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw]
  · field_simp

/-! ## 3. `∫₁ʸ F(w) e^{w/2}/w² dw` por partes, sob RH -/

/-- `F` é contínua à direita (`ψ` é constante à direita de cada ponto). -/
theorem Fpsi_right_cont (w : ℝ) : ContinuousWithinAt Fpsi (Ioi w) w := by
  have hψ : ContinuousWithinAt (fun w' => Chebyshev.psi (Real.exp w')) (Ioi w) w := by
    refine (continuousWithinAt_const (b := Chebyshev.psi (Real.exp w))).congr_of_eventuallyEq ?_ rfl
    have hlt : Real.exp w < ⌊Real.exp w⌋₊ + 1 := Nat.lt_floor_add_one _
    have hev : ∀ᶠ w' in 𝓝 w, Real.exp w' < ⌊Real.exp w⌋₊ + 1 :=
      Real.continuous_exp.continuousAt.eventually_lt continuousAt_const hlt
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with w' hw' hlt'
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_psi_coe_floor (Real.exp w)]
    congr 2
    rw [Nat.floor_eq_iff (Real.exp_pos _).le]
    have : Real.exp w ≤ Real.exp w' := Real.exp_le_exp.mpr (le_of_lt hw')
    exact ⟨(Nat.floor_le (Real.exp_pos _).le).trans this, hlt'⟩
  unfold Fpsi
  exact (hψ.sub Real.continuous_exp.continuousWithinAt).mul
    (Real.continuous_exp.comp (continuous_id.div_const 2).neg).continuousWithinAt

/-- O peso `g(w) = e^{w/2}/w²`. -/
noncomputable def gpeso (w : ℝ) : ℝ := Real.exp (w / 2) / w ^ 2

theorem hasDerivAt_gpeso {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt gpeso (Real.exp (w / 2) / (2 * w ^ 2) - 2 * Real.exp (w / 2) / w ^ 3) w := by
  have h1 : HasDerivAt (fun w => Real.exp (w / 2)) (Real.exp (w / 2) * (1 / 2)) w := by
    have := ((hasDerivAt_id' w).div_const 2).exp
    simpa using this
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
  have h := h1.div h2 (pow_ne_zero 2 hw)
  unfold gpeso
  convert h using 1
  field_simp

theorem abs_deriv_gpeso_le {w : ℝ} (hw : 1 ≤ w) :
    |Real.exp (w / 2) / (2 * w ^ 2) - 2 * Real.exp (w / 2) / w ^ 3| ≤ 5 / 2 * gpeso w := by
  unfold gpeso
  have hw0 : 0 < w := by linarith
  have he := Real.exp_pos (w / 2)
  have h3 : 2 * Real.exp (w / 2) / w ^ 3 ≤ 2 * Real.exp (w / 2) / w ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [pow_pos hw0 2]
  have h4 : 0 ≤ 2 * Real.exp (w / 2) / w ^ 3 := by positivity
  have h5 : 0 ≤ Real.exp (w / 2) / (2 * w ^ 2) := by positivity
  have e1 : Real.exp (w / 2) / (2 * w ^ 2) = 1 / 2 * (Real.exp (w / 2) / w ^ 2) := by
    field_simp
  have e2 : 2 * Real.exp (w / 2) / w ^ 2 = 2 * (Real.exp (w / 2) / w ^ 2) := by ring
  rw [abs_le]
  constructor <;> linarith

/-- **`∫₁ʸ e^{w/2}/w² dw ≤ 7e⁴ + 4e^{y/2}/y²`** para `y ≥ 1`. -/
theorem integral_gpeso_le {y : ℝ} (hy : 1 ≤ y) :
    ∫ w in (1 : ℝ)..y, gpeso w ≤ 7 * Real.exp 4 + 4 * gpeso y := by
  have hcont : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable gpeso volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable fun w hw => ?_
    rw [Set.uIcc_of_le hab] at hw
    have : w ≠ 0 := by linarith [hw.1]
    exact (hasDerivAt_gpeso this).continuousAt.continuousWithinAt
  have hg0 : ∀ w, 0 < w → 0 ≤ gpeso w := fun w hw => by unfold gpeso; positivity
  -- a parte `[1, min y 8]`
  have hbaixo : ∀ b : ℝ, 1 ≤ b → b ≤ 8 → ∫ w in (1 : ℝ)..b, gpeso w ≤ 7 * Real.exp 4 := by
    intro b hb1 hb8
    have hpt : ∀ w ∈ Ι (1 : ℝ) b, ‖gpeso w‖ ≤ Real.exp 4 := by
      intro w hw
      rw [Set.uIoc_of_le hb1] at hw
      have hw1 : 1 ≤ w := le_of_lt hw.1
      unfold gpeso
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc Real.exp (w / 2) / w ^ 2 ≤ Real.exp (w / 2) / 1 :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le one_pos (by nlinarith)
        _ ≤ Real.exp 4 := by rw [div_one]; exact Real.exp_le_exp.mpr (by linarith [hw.2])
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - 1)] at h
    have := le_abs_self (∫ w in (1 : ℝ)..b, gpeso w)
    nlinarith [Real.exp_pos 4]
  rcases le_or_gt y 8 with h8 | h8
  · have := hbaixo y hy h8
    have : 0 ≤ 4 * gpeso y := by have := hg0 y (by linarith); linarith
    linarith
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hcont 1 8 one_pos (by norm_num))
      (hcont 8 y (by norm_num) h8.le)]
    have h1 := hbaixo 8 (by norm_num) le_rfl
    -- `G(w) = 4e^{w/2}/w²`, `G′ ≥ g` em `w ≥ 8`
    have hG : ∀ w ∈ Set.uIcc (8 : ℝ) y, HasDerivAt (fun w => 4 * gpeso w)
        (4 * (Real.exp (w / 2) / (2 * w ^ 2) - 2 * Real.exp (w / 2) / w ^ 3)) w := by
      intro w hw
      rw [Set.uIcc_of_le h8.le] at hw
      exact (hasDerivAt_gpeso (by linarith [hw.1])).const_mul 4
    have hG'cont : ContinuousOn (fun w => 4 * (Real.exp (w / 2) / (2 * w ^ 2) - 2 * Real.exp (w / 2) / w ^ 3))
        (Set.uIcc 8 y) := by
      intro w hw
      rw [Set.uIcc_of_le h8.le] at hw
      have : w ≠ 0 := by linarith [hw.1]
      have : (2 * w ^ 2) ≠ 0 := by positivity
      have : w ^ 3 ≠ 0 := by positivity
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hG'cont.intervalIntegrable
    have hmono : ∫ w in (8 : ℝ)..y, gpeso w ≤
        ∫ w in (8 : ℝ)..y, 4 * (Real.exp (w / 2) / (2 * w ^ 2) - 2 * Real.exp (w / 2) / w ^ 3) := by
      refine intervalIntegral.integral_mono_on h8.le (hcont 8 y (by norm_num) h8.le)
        hG'cont.intervalIntegrable fun w hw => ?_
      unfold gpeso
      have hw8 : 8 ≤ w := hw.1
      have hw0 : 0 < w := by linarith
      have he := Real.exp_pos (w / 2)
      have : Real.exp (w / 2) / w ^ 2 * 8 ≤ Real.exp (w / 2) / w ^ 2 * w := by
        apply mul_le_mul_of_nonneg_left hw8 (by positivity)
      have e1 : 4 * (Real.exp (w / 2) / (2 * w ^ 2) - 2 * Real.exp (w / 2) / w ^ 3) =
          2 * (Real.exp (w / 2) / w ^ 2) - 8 * (Real.exp (w / 2) / w ^ 2) / w := by
        field_simp
        ring
      rw [e1]
      have : 8 * (Real.exp (w / 2) / w ^ 2) / w ≤ Real.exp (w / 2) / w ^ 2 := by
        rw [div_le_iff₀ hw0]; linarith
      linarith
    have hG8 : 0 ≤ 4 * gpeso 8 := by have := hg0 8 (by norm_num); linarith
    linarith

theorem continuousOn_gpeso {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ContinuousOn gpeso (Set.uIcc a b) := by
  intro w hw
  rw [Set.uIcc_of_le hab] at hw
  exact (hasDerivAt_gpeso (by linarith [hw.1])).continuousAt.continuousWithinAt

/-- **Sob RH, `|∫₁ʸ F(w) e^{w/2}/w² dw| ≤ K(1 + log y)(1 + e^{y/2}/y²)`** (por partes, com
`I(w) = ∫₁ʷ F = O(log w)`, rodada 94). -/
theorem integral_Fg_le (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
    |∫ w in (1 : ℝ)..y, Fpsi w * gpeso w| ≤ K * (1 + Real.log y) * (1 + gpeso y) := by
  obtain ⟨C, hC0, hC⟩ := ATK.ZeroClasses.LittlewoodMedia.integral_F_log hRH
  obtain ⟨B, hB0, hB⟩ := ATK.ZeroClasses.LittlewoodBase.Fpsi_le_RH hRH
  have hI : ∀ a b : ℝ, IntervalIntegrable Fpsi volume a b :=
    ATK.ZeroClasses.LittlewoodMedia.intervalIntegrable_F hB
  refine ⟨C * (11 + 18 * Real.exp 4), by positivity, fun y hy => ?_⟩
  set I : ℝ → ℝ := fun w => ∫ u in (1 : ℝ)..w, Fpsi u with hIdef
  have hIc : Continuous I := intervalIntegral.continuous_primitive hI 1
  set g' : ℝ → ℝ := fun w => Real.exp (w / 2) / (2 * w ^ 2) - 2 * Real.exp (w / 2) / w ^ 3 with hg'
  have hg'c : ContinuousOn g' (Set.uIcc 1 y) := by
    intro w hw
    rw [Set.uIcc_of_le hy] at hw
    have : w ≠ 0 := by linarith [hw.1]
    have : (2 * w ^ 2) ≠ 0 := by positivity
    have : w ^ 3 ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hgc := continuousOn_gpeso one_pos hy
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right (u := I) (v := gpeso)
    (u' := Fpsi) (v' := g') hIc.continuousOn hgc
    (fun w _ => (intervalIntegral.integral_hasDerivWithinAt_right (hI 1 w) (s := Ici w) (t := Ioi w)
      ATK.ZeroClasses.LittlewoodBase.measurable_Fpsi.stronglyMeasurable.stronglyMeasurableAtFilter
      (Fpsi_right_cont w)).mono Ioi_subset_Ici_self)
    (fun w hw => by
      have : w ≠ 0 := by
        rw [min_eq_left hy] at hw
        linarith [hw.1]
      exact (hasDerivAt_gpeso this).hasDerivWithinAt)
    (hI 1 y) hg'c.intervalIntegrable
  have hI1 : I 1 = 0 := intervalIntegral.integral_same
  have hFg : IntervalIntegrable (fun w => Fpsi w * gpeso w) volume 1 y := (hI 1 y).mul_continuousOn hgc
  have hIg : IntervalIntegrable (fun w => I w * g' w) volume 1 y :=
    (hIc.continuousOn.mul hg'c).intervalIntegrable
  rw [intervalIntegral.integral_add hFg hIg, hI1, zero_mul, sub_zero] at hIBP
  have hLy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hIy : |I y| ≤ C * (1 + Real.log y) := hC 1 y le_rfl hy
  have hgy : 0 ≤ gpeso y := by unfold gpeso; positivity
  have hJ := integral_gpeso_le hy
  have hint2 : |∫ w in (1 : ℝ)..y, I w * g' w| ≤ 5 / 2 * C * (1 + Real.log y) * (7 * Real.exp 4 + 4 * gpeso y) := by
    have hpt : ∀ᵐ w ∂volume, w ∈ Ioc (1 : ℝ) y → ‖I w * g' w‖ ≤ 5 / 2 * C * (1 + Real.log y) * gpeso w := by
      refine Eventually.of_forall fun w hw => ?_
      have hw1 : 1 ≤ w := le_of_lt hw.1
      have h1 : |I w| ≤ C * (1 + Real.log y) := by
        refine (hC 1 w le_rfl hw1).trans ?_
        have := Real.log_le_log (by linarith) hw.2
        nlinarith
      have h2 := abs_deriv_gpeso_le hw1
      rw [Real.norm_eq_abs, abs_mul]
      have hgw : 0 ≤ gpeso w := by unfold gpeso; positivity
      calc |I w| * |g' w| ≤ C * (1 + Real.log y) * (5 / 2 * gpeso w) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 5 / 2 * C * (1 + Real.log y) * gpeso w := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le hy hpt
      ((continuousOn_gpeso one_pos hy).intervalIntegrable.const_mul (5 / 2 * C * (1 + Real.log y)))
    rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left hJ (by positivity)
  have hFgeq : ∫ w in (1 : ℝ)..y, Fpsi w * gpeso w = I y * gpeso y - ∫ w in (1 : ℝ)..y, I w * g' w := by
    linarith
  rw [hFgeq]
  have hE4 := Real.exp_pos 4
  calc |I y * gpeso y - ∫ w in (1 : ℝ)..y, I w * g' w|
      ≤ |I y * gpeso y| + |∫ w in (1 : ℝ)..y, I w * g' w| := abs_sub _ _
    _ ≤ C * (1 + Real.log y) * gpeso y + 5 / 2 * C * (1 + Real.log y) * (7 * Real.exp 4 + 4 * gpeso y) := by
        rw [abs_mul, abs_of_nonneg hgy]
        exact add_le_add (mul_le_mul_of_nonneg_right hIy hgy) hint2
    _ ≤ C * (11 + 18 * Real.exp 4) * (1 + Real.log y) * (1 + gpeso y) := by
        have hCL : 0 ≤ C * (1 + Real.log y) := by positivity
        nlinarith [mul_nonneg hCL hgy, mul_nonneg hCL hE4.le, mul_nonneg (mul_nonneg hCL hgy) hE4.le]

/-! ## 4. O resto `E(x)` sob RH e Littlewood para `π − Li` -/

theorem intervalIntegrable_comp_exp {f : ℝ → ℝ} (hf : Monotone f) (a b : ℝ) :
    IntervalIntegrable (fun w => f (Real.exp w)) volume a b :=
  (hf.comp Real.exp_monotone).intervalIntegrable

theorem continuousOn_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun w : ℝ => 1 / w ^ 2) (Set.uIcc a b) := by
  intro w hw
  rw [Set.uIcc_of_le hab] at hw
  have : w ^ 2 ≠ 0 := by have : 0 < w := by linarith [hw.1]
                         positivity
  exact (continuousAt_const.div (continuousAt_id.pow 2) this).continuousWithinAt

theorem Fpsi_mul_gpeso (w : ℝ) :
    Fpsi w * gpeso w = (Chebyshev.psi (Real.exp w) - Real.exp w) / w ^ 2 := by
  unfold Fpsi gpeso
  have he : Real.exp (-(w / 2)) * Real.exp (w / 2) = 1 := by rw [← Real.exp_add]; simp
  calc (Chebyshev.psi (Real.exp w) - Real.exp w) * Real.exp (-(w / 2)) * (Real.exp (w / 2) / w ^ 2)
      = (Chebyshev.psi (Real.exp w) - Real.exp w) / w ^ 2 * (Real.exp (-(w / 2)) * Real.exp (w / 2)) := by ring
    _ = (Chebyshev.psi (Real.exp w) - Real.exp w) / w ^ 2 := by rw [he, mul_one]

/-- **Sob RH, `|2/log 2 + E(x)| ≤ K(1 + log log x)(1 + √x/log² x)`** para `x ≥ e`. -/
theorem resto_pi_le (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, Real.exp 1 ≤ x →
    |2 / Real.log 2 + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      K * (1 + Real.log (Real.log x)) * (1 + gpeso (Real.log x)) := by
  obtain ⟨K, hK0, hK⟩ := integral_Fg_le hRH
  obtain ⟨C₁, hC₁⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C := max C₁ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  set h : ℝ → ℝ := fun w => (Chebyshev.theta (Real.exp w) - Real.exp w) / w ^ 2 with hh
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hhI : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable h volume a b := by
    intro a b ha hab
    have e : h = fun w => (Chebyshev.theta (Real.exp w) - Real.exp w) * (1 / w ^ 2) := by
      funext w; simp only [hh]; ring
    rw [e]
    exact ((intervalIntegrable_comp_exp Chebyshev.theta_mono a b).sub
      (Real.continuous_exp.intervalIntegrable a b)).mul_continuousOn (continuousOn_inv_sq ha hab)
  set K₃ := |2 / Real.log 2 + ∫ w in Real.log 2..1, h w| with hK₃
  refine ⟨K₃ + K + 4 * C * (2 * Real.exp 4 + 1), by positivity, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := by have := Real.add_one_le_exp 1; linarith
  have hy1 : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  set y := Real.log x with hy
  rw [E_subst hx2, ← intervalIntegral.integral_add_adjacent_intervals (hhI _ _ hl2 hl21) (hhI 1 y one_pos hy1)]
  -- em `[1, y]`: `h = F·g − (ψ − θ)(e^w)/w²`
  have hsplit : ∫ w in (1 : ℝ)..y, h w = (∫ w in (1 : ℝ)..y, Fpsi w * gpeso w) -
      ∫ w in (1 : ℝ)..y, (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2 := by
    have hFg : IntervalIntegrable (fun w => Fpsi w * gpeso w) volume 1 y := by
      have e : (fun w => Fpsi w * gpeso w) = fun w => (Chebyshev.psi (Real.exp w) - Real.exp w) * (1 / w ^ 2) := by
        funext w
        rw [Fpsi_mul_gpeso]
        ring
      rw [e]
      exact ((intervalIntegrable_comp_exp Chebyshev.psi_mono 1 y).sub
        (Real.continuous_exp.intervalIntegrable 1 y)).mul_continuousOn (continuousOn_inv_sq one_pos hy1)
    have hpt : IntervalIntegrable (fun w => (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2)
        volume 1 y := by
      have e : (fun w => (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2) =
          fun w => (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) * (1 / w ^ 2) := by
        funext w; ring
      rw [e]
      exact ((intervalIntegrable_comp_exp Chebyshev.psi_mono 1 y).sub
        (intervalIntegrable_comp_exp Chebyshev.theta_mono 1 y)).mul_continuousOn (continuousOn_inv_sq one_pos hy1)
    rw [← intervalIntegral.integral_sub hFg hpt]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le hy1] at hw
    rw [Fpsi_mul_gpeso]
    simp only [hh]
    ring
  -- `0 ≤ (ψ − θ)(e^w) ≤ C e^{w/2}`
  have hpsith : |∫ w in (1 : ℝ)..y, (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2| ≤
      C * (7 * Real.exp 4 + 4 * gpeso y) := by
    have hb : ∀ᵐ w ∂volume, w ∈ Ioc (1 : ℝ) y →
        ‖(Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2‖ ≤ C * gpeso w := by
      refine Eventually.of_forall fun w hw => ?_
      have hw0 : 0 < w := by linarith [hw.1]
      have h0 := Chebyshev.theta_le_psi (Real.exp w)
      have h1 := hC₁ (Real.exp w)
      rw [← Real.exp_half] at h1
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by linarith), abs_of_pos (by positivity)]
      unfold gpeso
      rw [mul_div_assoc']
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hn := intervalIntegral.norm_integral_le_of_norm_le hy1 hb
      ((continuousOn_gpeso one_pos hy1).intervalIntegrable.const_mul C)
    rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left (integral_gpeso_le hy1) hC0)
  have hFg := hK y hy1
  rw [hsplit]
  have hLy : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hg : 0 ≤ gpeso y := by unfold gpeso; have : 0 < y := by linarith
                              positivity
  have hE4 := Real.exp_pos 4
  calc |2 / Real.log 2 + ((∫ w in Real.log 2..1, h w) + ((∫ w in (1 : ℝ)..y, Fpsi w * gpeso w) -
        ∫ w in (1 : ℝ)..y, (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2))|
      ≤ K₃ + |∫ w in (1 : ℝ)..y, Fpsi w * gpeso w| +
          |∫ w in (1 : ℝ)..y, (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2| := by
        rw [hK₃]
        have := abs_add_le (2 / Real.log 2 + ∫ w in Real.log 2..1, h w)
          ((∫ w in (1 : ℝ)..y, Fpsi w * gpeso w) -
            ∫ w in (1 : ℝ)..y, (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2)
        have h2 := abs_sub (∫ w in (1 : ℝ)..y, Fpsi w * gpeso w)
            (∫ w in (1 : ℝ)..y, (Chebyshev.psi (Real.exp w) - Chebyshev.theta (Real.exp w)) / w ^ 2)
        rw [← add_assoc]
        linarith
    _ ≤ K₃ + K * (1 + Real.log y) * (1 + gpeso y) + C * (7 * Real.exp 4 + 4 * gpeso y) := by linarith
    _ ≤ (K₃ + K + 4 * C * (2 * Real.exp 4 + 1)) * (1 + Real.log y) * (1 + gpeso y) := by
        have hK3 : 0 ≤ K₃ := abs_nonneg _
        have h1 : K₃ ≤ K₃ * (1 + Real.log y) * (1 + gpeso y) := by
          have : 1 ≤ (1 + Real.log y) * (1 + gpeso y) := by nlinarith
          nlinarith
        have h2 : C * (7 * Real.exp 4 + 4 * gpeso y) ≤
            4 * C * (2 * Real.exp 4 + 1) * (1 + Real.log y) * (1 + gpeso y) := by
          have : 7 * Real.exp 4 + 4 * gpeso y ≤ 4 * (2 * Real.exp 4 + 1) * (1 + gpeso y) := by nlinarith
          have h3 : 4 * (2 * Real.exp 4 + 1) * (1 + gpeso y) ≤
              4 * (2 * Real.exp 4 + 1) * (1 + Real.log y) * (1 + gpeso y) := by
            have : 0 ≤ 4 * (2 * Real.exp 4 + 1) * (1 + gpeso y) := by positivity
            nlinarith
          calc C * (7 * Real.exp 4 + 4 * gpeso y) ≤ C * (4 * (2 * Real.exp 4 + 1) * (1 + Real.log y) * (1 + gpeso y)) :=
                mul_le_mul_of_nonneg_left (this.trans h3) hC0
            _ = 4 * C * (2 * Real.exp 4 + 1) * (1 + Real.log y) * (1 + gpeso y) := by ring
        nlinarith

theorem ev_y {K c : ℝ} (hc : 0 < c) : ∀ᶠ y in atTop,
    K * (1 + Real.log y) ≤ c / 4 * y ∧ y ^ 2 ≤ Real.exp (y / 2) ∧ 1 ≤ Real.log (Real.log y) ∧ 1 ≤ y := by
  have hε : 0 < c / (8 * (|K| + 1)) := by positivity
  have hlo := (Real.isLittleO_log_id_atTop).bound hε
  filter_upwards [hlo, eventually_ge_atTop (8 * |K| / c), eventually_ge_atTop (48 : ℝ),
    eventually_ge_atTop (Real.exp (Real.exp 1))] with y h1 h2 h3 h4
  have hy0 : 0 < y := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hly, id, abs_of_pos hy0] at h1
  refine ⟨?_, ?_, ?_, by linarith⟩
  · have hK1 : |K| ≤ c / 8 * y := by
      rw [div_le_iff₀ hc] at h2; linarith
    have hK2 : |K| * Real.log y ≤ c / 8 * y := by
      calc |K| * Real.log y ≤ |K| * (c / (8 * (|K| + 1)) * y) := mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
        _ = c / 8 * y * (|K| / (|K| + 1)) := by field_simp
        _ ≤ c / 8 * y * 1 := by
            gcongr
            rw [div_le_one (by positivity)]; linarith
        _ = c / 8 * y := by ring
    have : K * (1 + Real.log y) ≤ |K| * (1 + Real.log y) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    linarith
  · have h := Real.pow_div_factorial_le_exp (y / 2) (by positivity) 3
    norm_num [Nat.factorial] at h
    nlinarith
  · have h5 : Real.exp 1 ≤ Real.log y := by
      rw [Real.le_log_iff_exp_le hy0]; exact h4
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]
    exact h5

/-- **Littlewood para `π(x) − Li(x)` sob RH**: `π(x) − Li(x) = Ω±(√x log log log x/log x)`. -/
theorem pi_littlewood_RH (hRH : RiemannHypothesis) : ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x ≤
      -(c * √x * Real.log (Real.log (Real.log x)) / Real.log x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * √x * Real.log (Real.log (Real.log x)) / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) := by
  obtain ⟨c, hc, h1, h2⟩ := ATK.ZeroClasses.LittlewoodTeta.theta_littlewood
  obtain ⟨K, hK0, hK⟩ := resto_pi_le hRH
  have hev := Real.tendsto_log_atTop.eventually (ev_y (K := K) hc)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop (Real.exp 1)))
  -- o resto é pequeno a partir de `X₀`
  have hR : ∀ x, X₀ ≤ x →
      |2 / Real.log 2 + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        c / 2 * (√x * Real.log (Real.log (Real.log x)) / Real.log x) ∧ 2 ≤ x ∧ 0 < Real.log x := by
    intro x hx
    obtain ⟨⟨hA, hB, hC, hD⟩, hE⟩ := hX₀ x hx
    have hx2 : 2 ≤ x := by have := Real.add_one_le_exp 1; linarith
    have hx0 : 0 < x := by linarith
    set y := Real.log x with hy
    have hy0 : 0 < y := by linarith
    have hsq : √x = Real.exp (y / 2) := by rw [Real.exp_half, hy, Real.exp_log hx0]
    refine ⟨(hK x hE).trans ?_, hx2, hy0⟩
    rw [hsq]
    have hg : gpeso y = Real.exp (y / 2) / y ^ 2 := rfl
    rw [hg]
    have he := Real.exp_pos (y / 2)
    have hL : 0 ≤ Real.log y := Real.log_nonneg hD
    have hlhs : K * (1 + Real.log y) * (1 + Real.exp (y / 2) / y ^ 2) ≤
        c / 4 * y + c / 4 * (Real.exp (y / 2) / y) := by
      have e : K * (1 + Real.log y) * (1 + Real.exp (y / 2) / y ^ 2) =
          K * (1 + Real.log y) + K * (1 + Real.log y) * (Real.exp (y / 2) / y ^ 2) := by ring
      rw [e]
      have h3 : K * (1 + Real.log y) * (Real.exp (y / 2) / y ^ 2) ≤ c / 4 * y * (Real.exp (y / 2) / y ^ 2) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      have e2 : c / 4 * y * (Real.exp (y / 2) / y ^ 2) = c / 4 * (Real.exp (y / 2) / y) := by
        field_simp
      linarith
    have hyy : c / 4 * y ≤ c / 4 * (Real.exp (y / 2) / y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ hy0]; nlinarith
    have hfin : c / 2 * (Real.exp (y / 2) / y) ≤
        c / 2 * (Real.exp (y / 2) * Real.log (Real.log y) / y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right _ hy0.le
      nlinarith
    linarith
  refine ⟨c / 2, by positivity, fun X => ?_, fun X => ?_⟩
  · obtain ⟨x, hx, hθ⟩ := h1 (max X X₀)
    obtain ⟨hRx, hx2, hlx⟩ := hR x (le_trans (le_max_right _ _) hx)
    refine ⟨x, le_trans (le_max_left _ _) hx, ?_⟩
    rw [pi_sub_Li hx2]
    have hdiv : (Chebyshev.theta x - x) / Real.log x ≤ -(c * √x * Real.log (Real.log (Real.log x))) / Real.log x :=
      div_le_div_of_nonneg_right hθ hlx.le
    have hR' := (abs_le.mp hRx).2
    have e : -(c * √x * Real.log (Real.log (Real.log x))) / Real.log x =
        -(2 * (c / 2 * (√x * Real.log (Real.log (Real.log x)) / Real.log x))) := by ring
    have e2 : -(c / 2 * √x * Real.log (Real.log (Real.log x)) / Real.log x) =
        -(c / 2 * (√x * Real.log (Real.log (Real.log x)) / Real.log x)) := by ring
    rw [e] at hdiv
    rw [e2]
    linarith
  · obtain ⟨x, hx, hθ⟩ := h2 (max X X₀)
    obtain ⟨hRx, hx2, hlx⟩ := hR x (le_trans (le_max_right _ _) hx)
    refine ⟨x, le_trans (le_max_left _ _) hx, ?_⟩
    rw [pi_sub_Li hx2]
    have hdiv : c * √x * Real.log (Real.log (Real.log x)) / Real.log x ≤ (Chebyshev.theta x - x) / Real.log x :=
      div_le_div_of_nonneg_right hθ hlx.le
    have hR' := (abs_le.mp hRx).1
    have e : c * √x * Real.log (Real.log (Real.log x)) / Real.log x =
        2 * (c / 2 * (√x * Real.log (Real.log (Real.log x)) / Real.log x)) := by ring
    have e2 : c / 2 * √x * Real.log (Real.log (Real.log x)) / Real.log x =
        c / 2 * (√x * Real.log (Real.log (Real.log x)) / Real.log x) := by ring
    rw [e] at hdiv
    rw [e2]
    linarith

/-- **Sob RH, `π(x) − Li(x)` troca de sinal infinitas vezes.** -/
theorem pi_troca_sinal_RH (hRH : RiemannHypothesis) (X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x < 0) ∧
    (∃ x : ℝ, X ≤ x ∧ 0 < (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) := by
  obtain ⟨c, hc, h1, h2⟩ := pi_littlewood_RH hRH
  have hpos : ∀ x : ℝ, Real.exp (Real.exp (Real.exp 1)) ≤ x →
      0 < c * √x * Real.log (Real.log (Real.log x)) / Real.log x := by
    intro x hx
    have hl := ATK.ZeroClasses.LittlewoodTeta.lll_ge hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hx1 : 1 < x := lt_of_lt_of_le (by
      have := Real.add_one_le_exp (Real.exp (Real.exp 1))
      have := Real.exp_pos (Real.exp 1)
      linarith) hx
    have := Real.sqrt_pos.mpr hx0
    have := Real.log_pos hx1
    positivity
  constructor
  · obtain ⟨x, hx, hπ⟩ := h1 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩
  · obtain ⟨x, hx, hπ⟩ := h2 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩

end ATK.ZeroClasses.LittlewoodPi

#print axioms ATK.ZeroClasses.LittlewoodPi.log_pos_of_two_le
#print axioms ATK.ZeroClasses.LittlewoodPi.continuousOn_inv_log_pow
#print axioms ATK.ZeroClasses.LittlewoodPi.Li_eq
#print axioms ATK.ZeroClasses.LittlewoodPi.pi_sub_Li
#print axioms ATK.ZeroClasses.LittlewoodPi.integral_exp_subst
#print axioms ATK.ZeroClasses.LittlewoodPi.E_subst
#print axioms ATK.ZeroClasses.LittlewoodPi.Fpsi_right_cont
#print axioms ATK.ZeroClasses.LittlewoodPi.hasDerivAt_gpeso
#print axioms ATK.ZeroClasses.LittlewoodPi.abs_deriv_gpeso_le
#print axioms ATK.ZeroClasses.LittlewoodPi.integral_gpeso_le
#print axioms ATK.ZeroClasses.LittlewoodPi.continuousOn_gpeso
#print axioms ATK.ZeroClasses.LittlewoodPi.integral_Fg_le
#print axioms ATK.ZeroClasses.LittlewoodPi.intervalIntegrable_comp_exp
#print axioms ATK.ZeroClasses.LittlewoodPi.continuousOn_inv_sq
#print axioms ATK.ZeroClasses.LittlewoodPi.Fpsi_mul_gpeso
#print axioms ATK.ZeroClasses.LittlewoodPi.resto_pi_le
#print axioms ATK.ZeroClasses.LittlewoodPi.ev_y
#print axioms ATK.ZeroClasses.LittlewoodPi.pi_littlewood_RH
#print axioms ATK.ZeroClasses.LittlewoodPi.pi_troca_sinal_RH
