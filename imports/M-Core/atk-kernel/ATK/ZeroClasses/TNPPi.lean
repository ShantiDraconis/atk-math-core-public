import ATK.ZeroClasses.BDBurnolL1
import ATK.ZeroClasses.PiLi

/-!
# O teorema dos números primos com erro para `θ` e `π` (rodada 81)

A rodada 54 deu `|ψ(x) − x| ≤ K x e^{−b√log x}` (`PNT.psi_tnp`). Aqui ficam montadas as duas formas que faltavam:

  **`|θ(x) − x| ≤ K x e^{−b√log x}`**   (`theta_tnp`),
  **`|π(x) − Li(x)| ≤ K′ x e^{−b′√log x}`**   (`pi_tnp`, com `b′ = b/2`).

* `sqrt_log_le_V`: `√x log x ≤ x e^{−b√log x}` para `x` grande. Com `u = √log x`, isso é `u² e^{u²/2} ≤ e^{u² − bu}`,
  que segue de `u² ≤ 2e^u`. Daí `θ` a partir de `ψ − θ ≤ 2√x log x` (Mathlib).
* `pi_tnp`: a fórmula de Abel da Mathlib e `Li_partes` (rodada 57) dão
  `π − Li = (θ − x)/log x + ∫_2^x (θ(t) − t)/(t log²t) dt + 2/log 2`. A integral se parte em `[2, √x]`
  (`≤ C√x`) e `[√x, x]`, onde `e^{−b√log t} ≤ e^{−(b/2)√log x}` (`exp_meio_le`).

Classificação (rodada 81): **consequência** (o TNP com erro de de la Vallée Poussin para `π`, BUILD_PENDING desde a
rodada 57). Não é RH: RH equivale a `π(x) = Li(x) + O(x^{1/2+ε})` (`PiLi.rh_iff_pi`). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

namespace ATK.ZeroClasses.TNPPi

open ATK.ZeroClasses.PiLi (Li Li_partes log_pos_of_ge)

/-! ## 1. `√x log x` é desprezível -/

/-- **`√x log x ≤ x e^{−b√log x}`** para `x ≥ exp((2b + 4)²)`. -/
theorem sqrt_log_le_V {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, √x * Real.log x ≤ x * Real.exp (-(b * Real.sqrt (Real.log x))) := by
  filter_upwards [eventually_ge_atTop (Real.exp ((2 * b + 4) ^ 2))] with x hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by positivity)) hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  set u : ℝ := Real.sqrt (Real.log x) with hu
  have hu2 : u ^ 2 = Real.log x := Real.sq_sqrt hl0
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hlx : (2 * b + 4) ^ 2 ≤ Real.log x := by
    rw [← Real.log_exp ((2 * b + 4) ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hub : 2 * b + 4 ≤ u := by
    rw [hu]
    exact Real.le_sqrt_of_sq_le hlx
  have hsx : √x = Real.exp (u ^ 2 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, hu2]
    ring_nf
  have hxe : x = Real.exp (u ^ 2) := by rw [hu2, Real.exp_log hx0]
  have hq := Real.quadratic_le_exp_of_nonneg hu0
  have hu2e : u ^ 2 ≤ Real.exp (Real.log 2 + u) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
    nlinarith [Real.exp_pos u]
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  calc √x * Real.log x = Real.exp (u ^ 2 / 2) * u ^ 2 := by rw [hsx, hu2]
    _ ≤ Real.exp (u ^ 2 / 2) * Real.exp (Real.log 2 + u) :=
        mul_le_mul_of_nonneg_left hu2e (Real.exp_pos _).le
    _ = Real.exp (u ^ 2 / 2 + (Real.log 2 + u)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (u ^ 2 - b * u) := by
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = x * Real.exp (-(b * u)) := by
        rw [hxe, ← Real.exp_add]
        ring_nf

/-! ## 2. `θ` -/

/-- **O TNP com erro para `θ`**: `|θ(x) − x| ≤ K x e^{−b√log x}` para `x` grande. -/
theorem theta_tnp : ∃ b > 0, ∃ K : ℝ, ∀ᶠ x in atTop,
    |Chebyshev.theta x - x| ≤ K * x * Real.exp (-(b * Real.sqrt (Real.log x))) := by
  obtain ⟨b, hb, K, hK⟩ := ATK.ZeroClasses.PNT.psi_tnp
  refine ⟨b, hb, K + 2, ?_⟩
  filter_upwards [hK, sqrt_log_le_V hb, eventually_ge_atTop 1] with x h1 h2 hx1
  have h3 := Chebyshev.theta_le_psi x
  have h4 := Chebyshev.psi_sub_theta_le hx1
  have e : (K + 2) * x * Real.exp (-(b * Real.sqrt (Real.log x))) =
      K * x * Real.exp (-(b * Real.sqrt (Real.log x))) + 2 * (x * Real.exp (-(b * Real.sqrt (Real.log x)))) := by
    ring
  rw [e]
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith [h1.1, h1.2]

/-! ## 3. `π` -/

/-- `e^{−b√log t} ≤ e^{−(b/2)√log x}` para `t ≥ √x`, `x ≥ 1`. -/
theorem exp_meio_le {b x t : ℝ} (hb : 0 < b) (hx : 1 ≤ x) (ht : √x ≤ t) :
    Real.exp (-(b * Real.sqrt (Real.log t))) ≤ Real.exp (-(b / 2 * Real.sqrt (Real.log x))) := by
  apply Real.exp_le_exp.mpr
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hlt : Real.log x / 2 ≤ Real.log t := by
    have e : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
    rw [← e]
    exact Real.log_le_log hs ht
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log x / 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hl0]
    linarith
  have h1 : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log t) := h2.trans (Real.sqrt_le_sqrt hlt)
  nlinarith

/-- A cota pontual do integrando de Abel: `|θ(t) − t|/(t log²t) ≤ (KE + D)/log²2`. -/
theorem f_le {K M b t E D : ℝ} (hK : 0 ≤ K) (ht : 2 ≤ t) (hE : Real.exp (-(b * Real.sqrt (Real.log t))) ≤ E)
    (hD : M ≤ t * D)
    (hθ : |Chebyshev.theta t - t| ≤ K * t * Real.exp (-(b * Real.sqrt (Real.log t))) + M) :
    ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤ (K * E + D) / Real.log 2 ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (pow_pos (by linarith) 2)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  have hsq : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hl2.le hlt 2
  have h1 : |Chebyshev.theta t - t| ≤ t * (K * E + D) := by
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hK ht0.le)
    nlinarith
  have hKED : 0 ≤ K * E + D :=
    (mul_nonneg_iff_of_pos_left ht0).mp ((abs_nonneg _).trans h1)
  calc |Chebyshev.theta t - t| * Real.log 2 ^ 2 ≤ t * (K * E + D) * Real.log 2 ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ ≤ (K * E + D) * (t * Real.log t ^ 2) := by
        have := mul_le_mul_of_nonneg_left hsq (mul_nonneg ht0.le hKED)
        nlinarith

/-- O integrando de Abel `(θ(t) − t)/(t log²t)`. -/
noncomputable def fA (t : ℝ) : ℝ := (Chebyshev.theta t - t) / (t * Real.log t ^ 2)

/-- **Abel**: `π(x) − Li(x) = (θ(x) − x)/log x + ∫_2^x fA + 2/log 2`, com `fA` integrável. -/
theorem abel_dif {x : ℝ} (hx2 : 2 ≤ x) :
    IntervalIntegrable fA volume 2 x ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x = (Chebyshev.theta x - x) / Real.log x +
        (∫ t in (2 : ℝ)..x, fA t) + 2 / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hlx0 : 0 < Real.log x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  have hLi := Li_partes hx2
  have hint1 : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx2]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hfeq : ∀ t ∈ Ι (2 : ℝ) x, Chebyshev.theta t / (t * Real.log t ^ 2) - 1 / Real.log t ^ 2 = fA t := by
    intro t ht
    rw [uIoc_of_le hx2] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (log_pos_of_ge ht.1.le).ne'
    unfold fA
    field_simp
  refine ⟨(hint1.sub hint2).congr (fun t ht => hfeq t ht), ?_⟩
  rw [hπ, hLi]
  have e : ∫ t in (2 : ℝ)..x, fA t =
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
        ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_sub hint1 hint2]
    exact intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => (hfeq t ht).symm)
  rw [e]
  field_simp
  ring

/-- **A integral de Abel**: com `|θ(t) − t| ≤ K t e^{−b√log t} + M` em `t ≥ 2` e `x ≥ 16`,
`|∫_2^x fA| ≤ (K + M)√x/log²2 + (K x e^{−(b/2)√log x} + M√x)/log²2`. -/
theorem integral_fA_le {K M b x : ℝ} (hK0 : 0 ≤ K) (hM0 : 0 ≤ M) (hb : 0 < b) (hx16 : 16 ≤ x)
    (hglob : ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| ≤ K * t * Real.exp (-(b * Real.sqrt (Real.log t))) + M)
    (hfi : IntervalIntegrable fA volume 2 x) :
    |∫ t in (2 : ℝ)..x, fA t| ≤ (K + M) / Real.log 2 ^ 2 * √x +
      (K * (x * Real.exp (-(b / 2 * Real.sqrt (Real.log x)))) + M * √x) / Real.log 2 ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx4 : 4 ≤ √x := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hsx0 : 0 < √x := by linarith
  have hsxx : √x ≤ x := by
    have := Real.mul_self_sqrt hx0.le
    nlinarith
  set e' : ℝ := Real.exp (-(b / 2 * Real.sqrt (Real.log x))) with he'
  have hsplit : ∫ t in (2 : ℝ)..x, fA t = (∫ t in (2 : ℝ)..√x, fA t) + ∫ t in √x..x, fA t := by
    have h1 : IntervalIntegrable fA volume 2 √x :=
      hfi.mono_set (uIcc_subset_uIcc (left_mem_uIcc) (by rw [uIcc_of_le hx2]; exact ⟨by linarith, hsxx⟩))
    have h2 : IntervalIntegrable fA volume √x x :=
      hfi.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le hx2]; exact ⟨by linarith, hsxx⟩) right_mem_uIcc)
    exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hI1 : ‖∫ t in (2 : ℝ)..√x, fA t‖ ≤ (K + M) / Real.log 2 ^ 2 * √x := by
    have hle : ∀ t ∈ Ι (2 : ℝ) √x, ‖fA t‖ ≤ (K * 1 + M) / Real.log 2 ^ 2 := by
      intro t ht
      rw [uIoc_of_le (by linarith)] at ht
      have ht2 : 2 ≤ t := ht.1.le
      have hE : Real.exp (-(b * Real.sqrt (Real.log t))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
        nlinarith
      exact f_le hK0 ht2 hE (by nlinarith) (hglob t ht2)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rw [mul_one, abs_of_nonneg (by linarith)] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hI2 : ‖∫ t in √x..x, fA t‖ ≤ (K * (x * e') + M * √x) / Real.log 2 ^ 2 := by
    have hle : ∀ t ∈ Ι √x x, ‖fA t‖ ≤ (K * e' + M / √x) / Real.log 2 ^ 2 := by
      intro t ht
      rw [uIoc_of_le hsxx] at ht
      have ht2 : 2 ≤ t := by linarith [ht.1]
      have hE := exp_meio_le hb hx1 ht.1.le
      have hD : M ≤ t * (M / √x) := by
        have h1 : 1 ≤ t / √x := by rw [le_div_iff₀ hsx0]; linarith [ht.1]
        calc M = M * 1 := (mul_one M).symm
          _ ≤ M * (t / √x) := mul_le_mul_of_nonneg_left h1 hM0
          _ = t * (M / √x) := by ring
      exact f_le hK0 ht2 hE hD (hglob t ht2)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rw [abs_of_nonneg (by linarith)] at h
    refine h.trans ?_
    have hxs : x / √x = √x := by
      rw [div_eq_iff hsx0.ne']
      exact (Real.mul_self_sqrt hx0.le).symm
    have hpos : 0 ≤ (K * e' + M / √x) / Real.log 2 ^ 2 := by positivity
    calc (K * e' + M / √x) / Real.log 2 ^ 2 * (x - √x) ≤ (K * e' + M / √x) / Real.log 2 ^ 2 * x :=
          mul_le_mul_of_nonneg_left (by linarith) hpos
      _ = (K * (x * e') + M * (x / √x)) / Real.log 2 ^ 2 := by ring
      _ = (K * (x * e') + M * √x) / Real.log 2 ^ 2 := by rw [hxs]
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact add_le_add hI1 hI2

/-- **O TNP com erro para `π`**: `|π(x) − Li(x)| ≤ K x e^{−b√log x}` para `x` grande. -/
theorem pi_tnp : ∃ b > 0, ∃ K : ℝ, ∀ᶠ x in atTop,
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * x * Real.exp (-(b * Real.sqrt (Real.log x))) := by
  obtain ⟨b, hb, K₀, hK₀⟩ := theta_tnp
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hK₀
  set X : ℝ := max X₀ 2 with hX
  have hX2 : (2 : ℝ) ≤ X := le_max_right _ _
  set K : ℝ := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hKK : K₀ ≤ K := le_max_left _ _
  set M : ℝ := Chebyshev.theta X + X with hM
  have hM0 : 0 ≤ M := by have := Chebyshev.theta_nonneg X; linarith
  have hglob : ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| ≤ K * t * Real.exp (-(b * Real.sqrt (Real.log t))) + M := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    have he : 0 ≤ t * Real.exp (-(b * Real.sqrt (Real.log t))) := by positivity
    rcases le_or_gt X₀ t with h | h
    · have h1 := hX₀ t h
      have h2 : K₀ * t * Real.exp (-(b * Real.sqrt (Real.log t))) ≤
          K * t * Real.exp (-(b * Real.sqrt (Real.log t))) := by
        have := mul_le_mul_of_nonneg_right hKK he
        linarith [this]
      linarith
    · have htX : t ≤ X := by linarith [le_max_left X₀ 2]
      have hθ := Chebyshev.theta_mono htX
      have hθ0 := Chebyshev.theta_nonneg t
      have hKe : 0 ≤ K * t * Real.exp (-(b * Real.sqrt (Real.log t))) := by positivity
      rw [abs_le]
      constructor <;> linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb'0 : 0 < b / 2 := by positivity
  refine ⟨b / 2, hb'0, K / Real.log 2 + (K + M) / Real.log 2 ^ 2 + K / Real.log 2 ^ 2 + M / Real.log 2 ^ 2 +
    2 / Real.log 2, ?_⟩
  filter_upwards [hK₀, sqrt_log_le_V hb'0, eventually_ge_atTop (max X 16)] with x hθx hsq hx
  have hx16 : (16 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set e' : ℝ := Real.exp (-(b / 2 * Real.sqrt (Real.log x))) with he'
  set V : ℝ := x * e' with hV
  have hlx1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hsx : √x ≤ V := (le_mul_of_one_le_right (Real.sqrt_nonneg x) hlx1).trans hsq
  have hsx1 : 1 ≤ √x := by
    have h := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ x)
    rwa [Real.sqrt_one] at h
  have hV1 : 1 ≤ V := by linarith
  have hee : Real.exp (-(b * Real.sqrt (Real.log x))) ≤ e' := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    nlinarith
  have hlx0 : 0 < Real.log x := by linarith
  obtain ⟨hfi, hdiff⟩ := abel_dif hx2
  have hb1 : |(Chebyshev.theta x - x) / Real.log x| ≤ K / Real.log 2 * V := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    have hxe : 0 ≤ x * Real.exp (-(b * Real.sqrt (Real.log x))) := by positivity
    have h1 : |Chebyshev.theta x - x| ≤ K * V := by
      calc |Chebyshev.theta x - x| ≤ K₀ * x * Real.exp (-(b * Real.sqrt (Real.log x))) := hθx
        _ ≤ K * x * Real.exp (-(b * Real.sqrt (Real.log x))) := by
            have := mul_le_mul_of_nonneg_right hKK hxe
            linarith
        _ ≤ K * V := by
            rw [hV, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hee hx0.le) hK0
    have hKV : 0 ≤ K * V := by positivity
    have : 1 ≤ Real.log x / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith [Real.log_two_lt_d9]
    calc |Chebyshev.theta x - x| ≤ K * V := h1
      _ ≤ K * V * (Real.log x / Real.log 2) := le_mul_of_one_le_right hKV this
      _ = K / Real.log 2 * V * Real.log x := by ring
  have hb2 := integral_fA_le hK0 hM0 hb hx16 hglob hfi
  rw [← he', ← hV] at hb2
  have hb3 : |2 / Real.log 2| ≤ 2 / Real.log 2 * V := by
    rw [abs_of_pos (by positivity)]
    exact le_mul_of_one_le_right (by positivity) hV1
  rw [hdiff]
  have a1 := abs_add_le ((Chebyshev.theta x - x) / Real.log x + (∫ t in (2 : ℝ)..x, fA t)) (2 / Real.log 2)
  have a2 := abs_add_le ((Chebyshev.theta x - x) / Real.log x) (∫ t in (2 : ℝ)..x, fA t)
  have hc1 : 0 ≤ (K + M) / Real.log 2 ^ 2 := by positivity
  have hc2 : 0 ≤ M / Real.log 2 ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hsx hc1
  have h2 := mul_le_mul_of_nonneg_left hsx hc2
  have e2 : (K * V + M * √x) / Real.log 2 ^ 2 = K / Real.log 2 ^ 2 * V + M / Real.log 2 ^ 2 * √x := by ring
  rw [e2] at hb2
  have e3 : (K / Real.log 2 + (K + M) / Real.log 2 ^ 2 + K / Real.log 2 ^ 2 + M / Real.log 2 ^ 2 +
      2 / Real.log 2) * x * e' = K / Real.log 2 * V + (K + M) / Real.log 2 ^ 2 * V + K / Real.log 2 ^ 2 * V +
        M / Real.log 2 ^ 2 * V + 2 / Real.log 2 * V := by rw [hV]; ring
  rw [e3]
  linarith

/-- **`π(x) = Li(x) + O(x/log^A x)` para todo `A`**. -/
theorem pi_log_pow (A : ℕ) : ∃ K : ℝ, ∀ᶠ x in atTop,
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * x / Real.log x ^ A := by
  obtain ⟨b, hb, K, hK⟩ := pi_tnp
  have h1 : Tendsto (fun u : ℝ => u ^ (2 * A) * Real.exp (-(b * u))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * A)).comp
      (tendsto_id.const_mul_atTop hb)).const_mul ((b ^ (2 * A))⁻¹)
    rw [mul_zero] at h
    refine h.congr fun u => ?_
    have hb0 : b ^ (2 * A) ≠ 0 := pow_ne_zero _ hb.ne'
    simp only [Function.comp_apply, id]
    rw [mul_pow]
    field_simp
  have h2 := h1.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  refine ⟨max K 0, ?_⟩
  filter_upwards [hK, h2.eventually (ge_mem_nhds one_pos), eventually_ge_atTop 3] with x hx hx1 hx3
  simp only [Function.comp_apply] at hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hpow : Real.sqrt (Real.log x) ^ (2 * A) = Real.log x ^ A := by
    rw [pow_mul, Real.sq_sqrt hlx.le]
  rw [hpow] at hx1
  have hlA : 0 < Real.log x ^ A := pow_pos hlx A
  have he : Real.exp (-(b * Real.sqrt (Real.log x))) ≤ 1 / Real.log x ^ A := by
    rw [le_div_iff₀ hlA]
    linarith [mul_comm (Real.log x ^ A) (Real.exp (-(b * Real.sqrt (Real.log x))))]
  have hK' : K * x * Real.exp (-(b * Real.sqrt (Real.log x))) ≤
      max K 0 * x * Real.exp (-(b * Real.sqrt (Real.log x))) := by
    have : 0 ≤ x * Real.exp (-(b * Real.sqrt (Real.log x))) := by positivity
    nlinarith [le_max_left K 0]
  calc |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ max K 0 * x * Real.exp (-(b * Real.sqrt (Real.log x))) :=
        hx.trans hK'
    _ ≤ max K 0 * x * (1 / Real.log x ^ A) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (le_max_right K 0) hx0.le)
    _ = max K 0 * x / Real.log x ^ A := by ring

end ATK.ZeroClasses.TNPPi

#print axioms ATK.ZeroClasses.TNPPi.sqrt_log_le_V
#print axioms ATK.ZeroClasses.TNPPi.theta_tnp
#print axioms ATK.ZeroClasses.TNPPi.exp_meio_le
#print axioms ATK.ZeroClasses.TNPPi.f_le
#print axioms ATK.ZeroClasses.TNPPi.abel_dif
#print axioms ATK.ZeroClasses.TNPPi.integral_fA_le
#print axioms ATK.ZeroClasses.TNPPi.pi_tnp
#print axioms ATK.ZeroClasses.TNPPi.pi_log_pow
