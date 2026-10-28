import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ATK — Formas `0/0` e `∞/∞` com valor determinado (catálogos C53 e D15)

Exemplos certificados de formas indeterminadas cujo limite **é** determinado — o contraponto de
`ATK.IFormas` (onde o conjunto de valores possíveis é todo `ℝ`):

* `sin_div_x`: `sin x / x → 1`;
* `one_sub_cos_div_sq`: `(1 − cos x)/x² → 1/2`;
* `sin_sub_div_cube`: `(sin x − x)/x³ → −1/6`;
* `tan_sub_sin_div_cube`: `(tan x − sin x)/x³ → 1/2`;
* `x_mul_sqrt_sub`: `x(√(x² + 1) − x) → 1/2` em `+∞` (forma `∞ · 0`);
* `hipotenusa_infinito`: `√(x² + 1/4)/x → 1` em `+∞`; `hipotenusa_zero`: `→ +∞` em `0⁺`
  (refuta G35 do acervo, que afirmava limite 1 em `0`);
* `modulo_critico`: `|1/2 + it| / t → 1` em `t → +∞`.

As cotas usadas são as de Taylor da Mathlib (`Real.cos_bound`, `Real.sin_bound`). Matemática
clássica; nova só a formalização.
-/

open Filter Topology Real

namespace ATK.LimitesUm

/-- Vizinhança perfurada: `|x| ≤ 1` e `x ≠ 0`. -/
theorem perto_de_zero : ∀ᶠ x in 𝓝[≠] (0 : ℝ), |x| ≤ 1 ∧ x ≠ 0 := by
  have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), |x| ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with x hx
    simpa [Real.dist_eq] using hx
  exact (h1.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin

/-- `c · x² → 0` em `𝓝[≠] 0`. -/
theorem quadrado_tende_zero (c : ℝ) : Tendsto (fun x : ℝ => c * x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => c * x ^ 2) (𝓝 0) (𝓝 (c * 0 ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).tendsto 0
  simpa using h.mono_left nhdsWithin_le_nhds

/-- **`sin x / x → 1`.** -/
theorem sin_div_x : Tendsto (fun x : ℝ => sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  have h := (hasDerivAt_sin 0).tendsto_slope_zero
  rw [cos_zero] at h
  refine h.congr fun t => ?_
  simp [div_eq_inv_mul]

/-- **`(1 − cos x)/x² → 1/2`.** -/
theorem one_sub_cos_div_sq : Tendsto (fun x : ℝ => (1 - cos x) / x ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ (quadrado_tende_zero (5 / 96))
  filter_upwards [perto_de_zero] with x ⟨hx1, hx0⟩
  have hc := cos_bound hx1
  have hx2 : 0 < x ^ 2 := by positivity
  have e : (1 - cos x) / x ^ 2 - 1 / 2 = -(cos x - (1 - x ^ 2 / 2)) / x ^ 2 := by
    field_simp
    ring
  have h4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, e, abs_div, abs_neg, abs_of_pos hx2, div_le_iff₀ hx2]
  rw [h4] at hc
  nlinarith [hc]

/-- **`(sin x − x)/x³ → −1/6`.** -/
theorem sin_sub_div_cube : Tendsto (fun x : ℝ => (sin x - x) / x ^ 3) (𝓝[≠] 0) (𝓝 (-1 / 6)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ (quadrado_tende_zero (1 / 100))
  filter_upwards [perto_de_zero] with x ⟨hx1, hx0⟩
  have hs := sin_bound hx1
  have hx3 : 0 < |x| ^ 3 := by positivity
  have e : (sin x - x) / x ^ 3 - -1 / 6 = (sin x - (x - x ^ 3 / 6)) / x ^ 3 := by
    field_simp
    ring
  rw [Real.norm_eq_abs, e, abs_div, abs_pow, div_le_iff₀ hx3]
  have h5 : |x| ^ 5 / 100 = 1 / 100 * x ^ 2 * |x| ^ 3 := by
    rw [← sq_abs x]
    ring
  linarith [hs, h5]

/-- `cos x → 1` em `𝓝[≠] 0`. -/
theorem cos_tende_um : Tendsto cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hc : Continuous cos := by fun_prop
  have h := hc.tendsto (0 : ℝ)
  rw [cos_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **`(tan x − sin x)/x³ → 1/2`.** -/
theorem tan_sub_sin_div_cube :
    Tendsto (fun x : ℝ => (tan x - sin x) / x ^ 3) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have hinv : Tendsto (fun x : ℝ => (cos x)⁻¹) (𝓝[≠] 0) (𝓝 1) := by
    simpa using cos_tende_um.inv₀ one_ne_zero
  have hprod := (sin_div_x.mul one_sub_cos_div_sq).mul hinv
  rw [show (1 : ℝ) * (1 / 2) * 1 = 1 / 2 by norm_num] at hprod
  refine hprod.congr' ?_
  have hpos : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 0 < cos x := cos_tende_um.eventually (lt_mem_nhds one_pos)
  filter_upwards [hpos, self_mem_nhdsWithin] with x hc hx
  have hc' : cos x ≠ 0 := hc.ne'
  have hx' : x ≠ 0 := hx
  rw [tan_eq_sin_div_cos]
  field_simp

/-- **`x(√(x² + 1) − x) → 1/2`** quando `x → +∞` (forma `∞ · 0`). -/
theorem x_mul_sqrt_sub : Tendsto (fun x : ℝ => x * (√(x ^ 2 + 1) - x)) atTop (𝓝 (1 / 2)) := by
  have h2 : Tendsto (fun y : ℝ => √(1 + y ^ 2) + 1) (𝓝 0) (𝓝 2) := by
    have hc : Continuous (fun y : ℝ => √(1 + y ^ 2) + 1) := by fun_prop
    have h := hc.tendsto 0
    norm_num at h
    exact h
  have h3 := (h2.comp tendsto_inv_atTop_zero).inv₀ two_ne_zero
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs2 : √(x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ √(x ^ 2 + 1) := Real.sqrt_nonneg _
  have hroot : √(1 + x⁻¹ ^ 2) = √(x ^ 2 + 1) / x := by
    rw [show 1 + x⁻¹ ^ 2 = (√(x ^ 2 + 1) / x) ^ 2 by rw [div_pow, hs2]; field_simp]
    exact Real.sqrt_sq (div_nonneg hs0 hx.le)
  simp only [Function.comp_apply]
  rw [hroot]
  have hden : √(x ^ 2 + 1) + x ≠ 0 := by linarith
  have hx' : x ≠ 0 := hx.ne'
  field_simp
  linear_combination (-1 : ℝ) * hs2

/-- **Hipotenusa no infinito**: `√(x² + 1/4)/x → 1`. -/
theorem hipotenusa_infinito : Tendsto (fun x : ℝ => √(x ^ 2 + 1 / 4) / x) atTop (𝓝 1) := by
  have h2 : Tendsto (fun y : ℝ => √(1 + y ^ 2 / 4)) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun y : ℝ => √(1 + y ^ 2 / 4)) := by fun_prop
    have h := hc.tendsto 0
    norm_num at h
    exact h
  refine (h2.comp tendsto_inv_atTop_zero).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs2 : √(x ^ 2 + 1 / 4) ^ 2 = x ^ 2 + 1 / 4 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ √(x ^ 2 + 1 / 4) := Real.sqrt_nonneg _
  simp only [Function.comp_apply]
  rw [show 1 + x⁻¹ ^ 2 / 4 = (√(x ^ 2 + 1 / 4) / x) ^ 2 by rw [div_pow, hs2]; field_simp]
  exact Real.sqrt_sq (div_nonneg hs0 hx.le)

/-- **Hipotenusa em `0⁺`**: `√(x² + 1/4)/x → +∞` (refuta "limite 1 em 0", G35). -/
theorem hipotenusa_zero : Tendsto (fun x : ℝ => √(x ^ 2 + 1 / 4) / x) (𝓝[>] 0) atTop := by
  have hb : Tendsto (fun x : ℝ => 1 / 2 * x⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hb
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  have hle : 1 / 2 ≤ √(x ^ 2 + 1 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg x]
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hle hx'.le

/-- **Módulo na reta crítica**: `|1/2 + it| / t → 1` quando `t → +∞`. -/
theorem modulo_critico :
    Tendsto (fun t : ℝ => ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ / t) atTop (𝓝 1) := by
  refine hipotenusa_infinito.congr' (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [Complex.norm_add_mul_I]
  congr 2
  ring

end ATK.LimitesUm

#print axioms ATK.LimitesUm.perto_de_zero
#print axioms ATK.LimitesUm.quadrado_tende_zero
#print axioms ATK.LimitesUm.sin_div_x
#print axioms ATK.LimitesUm.one_sub_cos_div_sq
#print axioms ATK.LimitesUm.sin_sub_div_cube
#print axioms ATK.LimitesUm.cos_tende_um
#print axioms ATK.LimitesUm.tan_sub_sin_div_cube
#print axioms ATK.LimitesUm.x_mul_sqrt_sub
#print axioms ATK.LimitesUm.hipotenusa_infinito
#print axioms ATK.LimitesUm.hipotenusa_zero
#print axioms ATK.LimitesUm.modulo_critico
