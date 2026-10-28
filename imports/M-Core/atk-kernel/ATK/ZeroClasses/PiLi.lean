import ATK.ZeroClasses.QuasiRH

/-!
# `π(x) = Li(x) + O(x^{θ+ε})` ⟺ `ζ ≠ 0` em `Re s > θ`; `RH ⟺ π(x) = Li(x) + O(x^{1/2+ε})` (rodada 60)

Com `Li(x) = ∫_2^x dt/log t` (`Li`):

* **`semZeros_iff_pi`** (`½ ≤ θ < 1`): `ζ ≠ 0` em `Re s > θ` ⟺ `∀ ε > 0, |π(x) − Li(x)| ≤ C_ε x^{θ+ε}` para `x ≥ 2`;
* **`rh_iff_pi`**: **`RH ⟺ π(x) = Li(x) + O(x^{1/2+ε})`** (von Koch 1901);
* `semZeros_iff_theta`: o mesmo para `θ(x) = Σ_{p ≤ x} log p`.

A ponte entre `ψ`, `θ` e `π` é somação por partes, toda na Mathlib ou aqui:

* `ψ − θ ≤ 2√x log x` (Mathlib) ⟹ as cotas de `ψ` e de `θ` com expoente `b > ½` são equivalentes (`theta_of_psi`,
  `psi_of_theta`);
* `π(x) = θ(x)/log x + ∫_2^x θ(t)/(t log²t) dt` (Mathlib) e `Li(x) = x/log x − 2/log 2 + ∫_2^x dt/log²t`
  (`Li_partes`) dão `π − Li = (θ − x)/log x + ∫(θ − t)/(t log²t) + 2/log 2` (`pi_of_theta`);
* `θ(x) = π(x) log x − ∫_2^x π(t)/t dt` (Mathlib) e `Li(x) log x = x − 2 + ∫_2^x Li(t)/t dt` (`Li_log_partes`) dão
  `θ − x + 2 = (π − Li) log x − ∫ (π − Li)/t` (`theta_of_pi`).

Classificação (rodada 60): **reformulação** (a forma mais conhecida do critério de von Koch). RH continua OPEN_MATH.
-/

open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

namespace ATK.ZeroClasses.PiLi

open ATK.ZeroClasses.QuasiRH (SemZeros semZeros_iff_psi semZeros_meio_iff)

/-! ## 1. `Li` -/

/-- O logaritmo integral `Li(x) = ∫_2^x dt/log t`. -/
noncomputable def Li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

theorem log_pos_of_ge {t : ℝ} (ht : 2 ≤ t) : 0 < Real.log t := Real.log_pos (by linarith)

theorem continuousOn_inv_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Ioi 1) := by
  intro t ht
  have ht1 : (1 : ℝ) < t := ht
  have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  exact (continuousAt_const.div (Real.continuousAt_log (by linarith)) hl).continuousWithinAt

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b :=
  (continuousOn_inv_log.mono fun t ht => by
    rcases Set.mem_uIcc.mp ht with h | h
    · show (1 : ℝ) < t; linarith [h.1]
    · show (1 : ℝ) < t; linarith [h.1]).intervalIntegrable

theorem hasDerivAt_Li {x : ℝ} (hx : 1 < x) : HasDerivAt Li (1 / Real.log x) x := by
  unfold Li
  refine integral_hasDerivAt_right (intervalIntegrable_inv_log (by norm_num) hx) ?_ ?_
  · exact continuousOn_inv_log.stronglyMeasurableAtFilter isOpen_Ioi x hx
  · exact continuousOn_inv_log.continuousAt (isOpen_Ioi.mem_nhds hx)

theorem continuousOn_Li : ContinuousOn Li (Ioi 1) := fun _ hx =>
  (hasDerivAt_Li hx).continuousAt.continuousWithinAt

/-- `Li(x) = x/log x − 2/log 2 + ∫_2^x dt/log²t` (por partes). -/
theorem Li_partes {x : ℝ} (hx : 2 ≤ x) :
    Li x = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hu : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt (fun t => 1 / Real.log t) (-(1 / (t * Real.log t ^ 2))) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (log_pos_of_ge ht.1).ne'
    have h := (Real.hasDerivAt_log ht0.ne').inv hl
    convert h.const_mul 1 using 1
    · funext u; simp [one_div]
    · field_simp
  have hv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt (fun t : ℝ => t) 1 t := fun t _ => hasDerivAt_id' t
  have hu' : IntervalIntegrable (fun t : ℝ => -(1 / (t * Real.log t ^ 2))) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (log_pos_of_ge ht.1).ne'
    exact (((continuousAt_id.mul ((Real.continuousAt_log ht0.ne').pow 2)).inv₀
      (mul_ne_zero ht0.ne' (pow_ne_zero 2 hl))).neg.congr (by
        filter_upwards with u; simp [one_div])).continuousWithinAt
  have hv' : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 2 x := intervalIntegrable_const
  have h := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : ∫ t in (2 : ℝ)..x, 1 / Real.log t * 1 = Li x := by unfold Li; simp
  have e2 : ∫ t in (2 : ℝ)..x, -(1 / (t * Real.log t ^ 2)) * t = -∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (log_pos_of_ge ht.1).ne'
    field_simp
  rw [e1, e2] at h
  rw [h]
  ring

/-- `Li(x) log x = x − 2 + ∫_2^x Li(t)/t dt` (por partes). -/
theorem Li_log_partes {x : ℝ} (hx : 2 ≤ x) :
    Li x * Real.log x = x - 2 + ∫ t in (2 : ℝ)..x, Li t / t := by
  have hu : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt Li (1 / Real.log t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact hasDerivAt_Li (by linarith [ht.1])
  have hv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt Real.log (1 / t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    simpa [one_div] using Real.hasDerivAt_log ht0.ne'
  have hu' : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x :=
    intervalIntegrable_inv_log (by norm_num) (by linarith)
  have hv' : IntervalIntegrable (fun t : ℝ => 1 / t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    exact (continuousAt_const.div continuousAt_id ht0.ne').continuousWithinAt
  have h := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hLi2 : Li 2 = 0 := by unfold Li; simp
  have e1 : ∫ t in (2 : ℝ)..x, Li t * (1 / t) = ∫ t in (2 : ℝ)..x, Li t / t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have e2 : ∫ t in (2 : ℝ)..x, 1 / Real.log t * Real.log t = x - 2 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun t ht => by
      rw [uIcc_of_le hx] at ht
      have hl : Real.log t ≠ 0 := (log_pos_of_ge ht.1).ne'
      simp only; field_simp]
    simp
  rw [e1, e2, hLi2, zero_mul, sub_zero] at h
  linarith

/-! ## 2. As cotas de erro -/

/-- `|ψ(x) − x| ≤ C x^b` para `x ≥ 2`. -/
def ErroPsi (b : ℝ) : Prop := ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ b

/-- `|θ(x) − x| ≤ C x^b` para `x ≥ 2`. -/
def ErroTheta (b : ℝ) : Prop := ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C * x ^ b

/-- `|π(x) − Li(x)| ≤ C x^b` para `x ≥ 2`. -/
def ErroPi (b : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ C * x ^ b

theorem one_le_rpow_of_ge {x b : ℝ} (hx : 2 ≤ x) (hb : 0 ≤ b) : 1 ≤ x ^ b :=
  Real.one_le_rpow (by linarith) hb

theorem rpow_mono_exp {x a b : ℝ} (hx : 2 ≤ x) (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) hab

/-- `√x log x ≤ x^{½+δ}/δ`. -/
theorem sqrt_log_le {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) : √x * Real.log x ≤ x ^ (1 / 2 + δ) / δ := by
  have hl := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) hδ
  have hs : √x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hx0 : (0 : ℝ) < x := by linarith
  calc √x * Real.log x ≤ x ^ (1 / 2 : ℝ) * (x ^ δ / δ) := by
        rw [hs]; exact mul_le_mul_of_nonneg_left hl (by positivity)
    _ = x ^ (1 / 2 + δ) / δ := by rw [Real.rpow_add hx0]; ring

theorem theta_of_psi {b : ℝ} (hb : 1 / 2 < b) (h : ErroPsi b) : ErroTheta b := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C + 2 / (b - 1 / 2), fun x hx => ?_⟩
  have h1 := Chebyshev.theta_le_psi x
  have h2 := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ x)
  have h3 := sqrt_log_le (by linarith : (1 : ℝ) ≤ x) (by linarith : 0 < b - 1 / 2)
  rw [show 1 / 2 + (b - 1 / 2) = b by ring] at h3
  have h4 := hC x hx
  have hxb : 0 ≤ x ^ b := Real.rpow_nonneg (by linarith) _
  have h5 : Chebyshev.psi x - Chebyshev.theta x ≤ 2 / (b - 1 / 2) * x ^ b := by
    calc Chebyshev.psi x - Chebyshev.theta x ≤ 2 * √x * Real.log x := h2
      _ = 2 * (√x * Real.log x) := by ring
      _ ≤ 2 * (x ^ b / (b - 1 / 2)) := by linarith
      _ = 2 / (b - 1 / 2) * x ^ b := by ring
  rw [abs_le] at h4 ⊢
  constructor <;> linarith [h4.1, h4.2, h1, h5]

theorem psi_of_theta {b : ℝ} (hb : 1 / 2 < b) (h : ErroTheta b) : ErroPsi b := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C + 2 / (b - 1 / 2), fun x hx => ?_⟩
  have h1 := Chebyshev.theta_le_psi x
  have h2 := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ x)
  have h3 := sqrt_log_le (by linarith : (1 : ℝ) ≤ x) (by linarith : 0 < b - 1 / 2)
  rw [show 1 / 2 + (b - 1 / 2) = b by ring] at h3
  have h4 := hC x hx
  have hxb : 0 ≤ x ^ b := Real.rpow_nonneg (by linarith) _
  have h5 : Chebyshev.psi x - Chebyshev.theta x ≤ 2 / (b - 1 / 2) * x ^ b := by
    calc Chebyshev.psi x - Chebyshev.theta x ≤ 2 * √x * Real.log x := h2
      _ = 2 * (√x * Real.log x) := by ring
      _ ≤ 2 * (x ^ b / (b - 1 / 2)) := by linarith
      _ = 2 / (b - 1 / 2) * x ^ b := by ring
  rw [abs_le] at h4 ⊢
  constructor <;> linarith [h4.1, h4.2, h1, h5]

/-- `∫_2^x t^{b−1} dt ≤ x^b/b`. -/
theorem integral_rpow_le {x b : ℝ} (_hx : 2 ≤ x) (hb : 0 < b) :
    ∫ t in (2 : ℝ)..x, t ^ (b - 1) ≤ x ^ b / b := by
  rw [integral_rpow (Or.inl (by linarith))]
  rw [show b - 1 + 1 = b by ring]
  have h2 : 0 ≤ (2 : ℝ) ^ b := by positivity
  rw [div_le_div_iff_of_pos_right hb]
  linarith

theorem pi_of_theta {b : ℝ} (hb : 0 < b) (h : ErroTheta b) : ErroPi b := by
  obtain ⟨K, hK⟩ := h
  have hK0 : 0 ≤ K := by
    have := hK 2 le_rfl
    have h2 : (0 : ℝ) < 2 ^ b := by positivity
    by_contra hneg
    push Not at hneg
    have : K * 2 ^ b < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [abs_nonneg (Chebyshev.theta 2 - 2)]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K / Real.log 2 + 2 / Real.log 2 + K / (b * Real.log 2 ^ 2), fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 < Real.log x := by linarith
  have hxb1 : 1 ≤ x ^ b := one_le_rpow_of_ge hx hb.le
  -- a fórmula
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hLi := Li_partes hx
  have hint1 : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hdiff : (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x = (Chebyshev.theta x - x) / Real.log x +
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) + 2 / Real.log 2 := by
    rw [hπ, hLi]
    have e : ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) =
        (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
          ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
      rw [← intervalIntegral.integral_sub hint1 hint2]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hx] at ht
      have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      have hl : Real.log t ≠ 0 := (log_pos_of_ge ht.1).ne'
      field_simp
    rw [e]
    field_simp
    ring
  -- as cotas
  have hb1 : |(Chebyshev.theta x - x) / Real.log x| ≤ K / Real.log 2 * x ^ b := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    calc |Chebyshev.theta x - x| ≤ K * x ^ b := hK x hx
      _ ≤ K / Real.log 2 * x ^ b * Real.log x := by
          rw [show K / Real.log 2 * x ^ b * Real.log x = K * x ^ b * (Real.log x / Real.log 2) by ring]
          have : 1 ≤ Real.log x / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
          nlinarith [mul_nonneg hK0 (by positivity : (0 : ℝ) ≤ x ^ b)]
  have hb2 : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      K / (b * Real.log 2 ^ 2) * x ^ b := by
    have hle : ∀ t ∈ Ioc (2 : ℝ) x, ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤
        K / Real.log 2 ^ 2 * t ^ (b - 1) := by
      intro t ht
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := by linarith
      have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have hlt0 : 0 < Real.log t := by linarith
      have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (pow_pos hlt0 2)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
      have htb : t ^ (b - 1) * t = t ^ b := by
        rw [← Real.rpow_add_one ht0.ne']; ring_nf
      have hsq : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hl2.le hlt 2
      calc |Chebyshev.theta t - t| ≤ K * t ^ b := hK t ht2
        _ = K / Real.log 2 ^ 2 * t ^ (b - 1) * (t * Real.log 2 ^ 2) := by
            rw [← htb]; field_simp
        _ ≤ K / Real.log 2 ^ 2 * t ^ (b - 1) * (t * Real.log t ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hsq ht0.le
    have hn := intervalIntegral.norm_integral_le_of_norm_le hx (Eventually.of_forall hle)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < b - 1)).const_mul _)
    rw [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    rw [intervalIntegral.integral_const_mul]
    calc K / Real.log 2 ^ 2 * ∫ t in (2 : ℝ)..x, t ^ (b - 1) ≤ K / Real.log 2 ^ 2 * (x ^ b / b) :=
          mul_le_mul_of_nonneg_left (integral_rpow_le hx hb) (by positivity)
      _ = K / (b * Real.log 2 ^ 2) * x ^ b := by field_simp
  have hb3 : |2 / Real.log 2| ≤ 2 / Real.log 2 * x ^ b := by
    rw [abs_of_pos (by positivity)]
    exact le_mul_of_one_le_right (by positivity) hxb1
  rw [hdiff]
  calc |(Chebyshev.theta x - x) / Real.log x +
        (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) + 2 / Real.log 2|
      ≤ |(Chebyshev.theta x - x) / Real.log x| +
        |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| + |2 / Real.log 2| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _ ≤ K / Real.log 2 * x ^ b + K / (b * Real.log 2 ^ 2) * x ^ b + 2 / Real.log 2 * x ^ b := by
        linarith
    _ = (K / Real.log 2 + 2 / Real.log 2 + K / (b * Real.log 2 ^ 2)) * x ^ b := by ring

theorem monotone_pi_floor : Monotone fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  intro a b hab
  show (Nat.primeCounting ⌊a⌋₊ : ℝ) ≤ Nat.primeCounting ⌊b⌋₊
  exact_mod_cast Nat.monotone_primeCounting (Nat.floor_le_floor hab)

theorem theta_of_pi {b : ℝ} (hb : 0 < b) (h : ErroPi b) {b' : ℝ} (hbb : b < b') : ErroTheta b' := by
  obtain ⟨K, hK⟩ := h
  have hK0 : 0 ≤ K := by
    have := hK 2 le_rfl
    have h2 : (0 : ℝ) < 2 ^ b := by positivity
    by_contra hneg
    push Not at hneg
    have : K * 2 ^ b < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [abs_nonneg ((Nat.primeCounting ⌊(2 : ℝ)⌋₊ : ℝ) - Li 2)]
  set δ := b' - b with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨K / δ + K / b + 2, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hxb1 : 1 ≤ x ^ b' := one_le_rpow_of_ge hx (by linarith)
  have hθ := Chebyshev.theta_eq_primeCounting_mul_log_sub_integral hx
  have hL := Li_log_partes hx
  have hint1 : IntervalIntegrable (fun t => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) volume 2 x := by
    have hm : IntervalIntegrable (fun t => (Nat.primeCounting ⌊t⌋₊ : ℝ)) volume 2 x :=
      monotone_pi_floor.intervalIntegrable
    have hc : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 2 x) := fun t ht => by
      rw [uIcc_of_le hx] at ht
      exact (continuousAt_inv₀ (by linarith [ht.1] : t ≠ 0)).continuousWithinAt
    simpa [div_eq_mul_inv] using hm.mul_continuousOn hc
  have hint2 : IntervalIntegrable (fun t => Li t / t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    have ht1 : (1 : ℝ) < t := by linarith [ht.1]
    exact ((hasDerivAt_Li ht1).continuousAt.div continuousAt_id
      (by linarith : (0 : ℝ) < t).ne').continuousWithinAt
  have hdiff : Chebyshev.theta x - x = ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) * Real.log x -
      (∫ t in (2 : ℝ)..x, ((Nat.primeCounting ⌊t⌋₊ : ℝ) - Li t) / t) - 2 := by
    have e : ∫ t in (2 : ℝ)..x, ((Nat.primeCounting ⌊t⌋₊ : ℝ) - Li t) / t =
        (∫ t in (2 : ℝ)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) - ∫ t in (2 : ℝ)..x, Li t / t := by
      rw [← intervalIntegral.integral_sub hint1 hint2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [e, hθ]
    linarith
  have hb1 : |((Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) * Real.log x| ≤ K / δ * x ^ b' := by
    rw [abs_mul, abs_of_pos (Real.log_pos (by linarith))]
    have hl := Real.log_le_rpow_div hx0.le hδ0
    calc |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| * Real.log x ≤ K * x ^ b * (x ^ δ / δ) :=
          mul_le_mul (hK x hx) hl (Real.log_nonneg (by linarith)) (by positivity)
      _ = K / δ * x ^ b' := by
          rw [show K * x ^ b * (x ^ δ / δ) = K / δ * (x ^ b * x ^ δ) by ring, ← Real.rpow_add hx0, hδ]
          ring_nf
  have hb2 : |∫ t in (2 : ℝ)..x, ((Nat.primeCounting ⌊t⌋₊ : ℝ) - Li t) / t| ≤ K / b * x ^ b' := by
    have hle : ∀ t ∈ Ioc (2 : ℝ) x, ‖((Nat.primeCounting ⌊t⌋₊ : ℝ) - Li t) / t‖ ≤ K * t ^ (b - 1) := by
      intro t ht
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
      have htb : t ^ (b - 1) * t = t ^ b := by
        rw [← Real.rpow_add_one ht0.ne']; ring_nf
      calc |(Nat.primeCounting ⌊t⌋₊ : ℝ) - Li t| ≤ K * t ^ b := hK t ht2
        _ = K * t ^ (b - 1) * t := by rw [mul_assoc, htb]
    have hn := intervalIntegral.norm_integral_le_of_norm_le hx (Eventually.of_forall hle)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < b - 1)).const_mul _)
    rw [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    rw [intervalIntegral.integral_const_mul]
    calc K * ∫ t in (2 : ℝ)..x, t ^ (b - 1) ≤ K * (x ^ b / b) :=
          mul_le_mul_of_nonneg_left (integral_rpow_le hx hb) hK0
      _ = K / b * x ^ b := by ring
      _ ≤ K / b * x ^ b' := mul_le_mul_of_nonneg_left (rpow_mono_exp hx (by linarith)) (by positivity)
  rw [hdiff]
  calc |((Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) * Real.log x -
        (∫ t in (2 : ℝ)..x, ((Nat.primeCounting ⌊t⌋₊ : ℝ) - Li t) / t) - 2|
      ≤ |((Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) * Real.log x| +
        |∫ t in (2 : ℝ)..x, ((Nat.primeCounting ⌊t⌋₊ : ℝ) - Li t) / t| + |(2 : ℝ)| :=
        (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans_eq (by ring)
    _ ≤ K / δ * x ^ b' + K / b * x ^ b' + 2 * x ^ b' := by
        rw [abs_two]; nlinarith
    _ = (K / δ + K / b + 2) * x ^ b' := by ring

/-! ## 3. Entre a forma inteira e a real -/

theorem erroPsi_of_int {b : ℝ} (hb : 0 ≤ b)
    (h : ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ b) : ErroPsi b := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
    exact le_trans (abs_nonneg _) this
  refine ⟨C * 2 ^ b + 1, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set N := ⌊x⌋₊ with hN
  have hN1 : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hN2 : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hψ : Chebyshev.psi x = Chebyshev.psi N := Chebyshev.psi_eq_psi_coe_floor x
  have hpow : ((N : ℝ) + 1) ^ b ≤ 2 ^ b * x ^ b := by
    rw [← Real.mul_rpow (by norm_num) hx0]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hb
  have hxb : 1 ≤ x ^ b := one_le_rpow_of_ge hx hb
  have h1 := hC N
  rw [hψ]
  calc |Chebyshev.psi N - x| ≤ |Chebyshev.psi N - N| + |(N : ℝ) - x| := by
        rw [show Chebyshev.psi N - x = (Chebyshev.psi N - N) + ((N : ℝ) - x) by ring]
        exact abs_add_le _ _
    _ ≤ C * ((N : ℝ) + 1) ^ b + 1 := by
        have : |(N : ℝ) - x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        linarith
    _ ≤ C * (2 ^ b * x ^ b) + 1 * x ^ b := add_le_add (mul_le_mul_of_nonneg_left hpow hC0) (by linarith)
    _ = (C * 2 ^ b + 1) * x ^ b := by ring

theorem int_of_erroPsi {b : ℝ} (hb : 0 ≤ b) (h : ErroPsi b) :
    ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ b := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0 + 2, fun N => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  have hpow1 : 1 ≤ ((N : ℝ) + 1) ^ b := Real.one_le_rpow hN1 hb
  rcases lt_or_ge N 2 with hN | hN
  · have hψ : Chebyshev.psi N = 0 := Chebyshev.psi_eq_zero_of_lt_two (by exact_mod_cast hN)
    have hN' : (N : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hN
    rw [hψ, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg N)]
    nlinarith [le_max_right C 0]
  · have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 := hC N hN2
    have hpow : (N : ℝ) ^ b ≤ ((N : ℝ) + 1) ^ b := Real.rpow_le_rpow (by linarith) (by linarith) hb
    have hpos : 0 ≤ (N : ℝ) ^ b := by positivity
    calc |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ b := h1
      _ ≤ max C 0 * (N : ℝ) ^ b := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ b := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
      _ ≤ (max C 0 + 2) * ((N : ℝ) + 1) ^ b := by nlinarith

theorem erroPi_mono {a b : ℝ} (hab : a ≤ b) (h : ErroPi a) : ErroPi b := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun x hx => (hC x hx).trans ?_⟩
  calc C * x ^ a ≤ max C 0 * x ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * x ^ b := mul_le_mul_of_nonneg_left (rpow_mono_exp hx hab) (le_max_right _ _)

theorem int_mono {a b : ℝ} (hab : a ≤ b)
    (h : ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ a) :
    ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ b := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun N => (hC N).trans ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  calc C * ((N : ℝ) + 1) ^ a ≤ max C 0 * ((N : ℝ) + 1) ^ a :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ((N : ℝ) + 1) ^ b :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hab) (le_max_right _ _)

/-! ## 4. As equivalências -/

/-- **Quasi-RH ⟺ erro de `θ`**. -/
theorem semZeros_iff_theta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ ε : ℝ, 0 < ε → ErroTheta (θ + ε) := by
  rw [semZeros_iff_psi hθ hθ1]
  constructor
  · intro h ε hε
    exact theta_of_psi (by linarith) (erroPsi_of_int (by linarith) (h ε hε))
  · intro h ε hε
    exact int_of_erroPsi (by linarith) (psi_of_theta (by linarith) (h ε hε))

/-- **Quasi-RH ⟺ erro de `π`**: para `½ ≤ θ < 1`, `ζ ≠ 0` em `Re s > θ` ⟺ `π(x) = Li(x) + O(x^{θ+ε})` para todo
`ε > 0`. -/
theorem semZeros_iff_pi {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ ε : ℝ, 0 < ε → ErroPi (θ + ε) := by
  rw [semZeros_iff_theta hθ hθ1]
  constructor
  · intro h ε hε
    exact pi_of_theta (by linarith) (h ε hε)
  · intro h ε hε
    exact theta_of_pi (b := θ + ε / 2) (by linarith) (h (ε / 2) (by linarith)) (by linarith)

/-- **O critério de von Koch para `π`**: `RH ⟺ π(x) = Li(x) + O(x^{1/2+ε})` para todo `ε > 0`. -/
theorem rh_iff_pi : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ErroPi (1 / 2 + ε) :=
  semZeros_meio_iff.symm.trans (semZeros_iff_pi (by norm_num) (by norm_num))

/-- `RH ⟺ θ(x) = x + O(x^{1/2+ε})`. -/
theorem rh_iff_theta : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ErroTheta (1 / 2 + ε) :=
  semZeros_meio_iff.symm.trans (semZeros_iff_theta (by norm_num) (by norm_num))

end ATK.ZeroClasses.PiLi

#print axioms ATK.ZeroClasses.PiLi.log_pos_of_ge
#print axioms ATK.ZeroClasses.PiLi.continuousOn_inv_log
#print axioms ATK.ZeroClasses.PiLi.intervalIntegrable_inv_log
#print axioms ATK.ZeroClasses.PiLi.hasDerivAt_Li
#print axioms ATK.ZeroClasses.PiLi.continuousOn_Li
#print axioms ATK.ZeroClasses.PiLi.Li_partes
#print axioms ATK.ZeroClasses.PiLi.Li_log_partes
#print axioms ATK.ZeroClasses.PiLi.one_le_rpow_of_ge
#print axioms ATK.ZeroClasses.PiLi.rpow_mono_exp
#print axioms ATK.ZeroClasses.PiLi.sqrt_log_le
#print axioms ATK.ZeroClasses.PiLi.theta_of_psi
#print axioms ATK.ZeroClasses.PiLi.psi_of_theta
#print axioms ATK.ZeroClasses.PiLi.integral_rpow_le
#print axioms ATK.ZeroClasses.PiLi.pi_of_theta
#print axioms ATK.ZeroClasses.PiLi.monotone_pi_floor
#print axioms ATK.ZeroClasses.PiLi.theta_of_pi
#print axioms ATK.ZeroClasses.PiLi.erroPsi_of_int
#print axioms ATK.ZeroClasses.PiLi.int_of_erroPsi
#print axioms ATK.ZeroClasses.PiLi.erroPi_mono
#print axioms ATK.ZeroClasses.PiLi.int_mono
#print axioms ATK.ZeroClasses.PiLi.semZeros_iff_theta
#print axioms ATK.ZeroClasses.PiLi.semZeros_iff_pi
#print axioms ATK.ZeroClasses.PiLi.rh_iff_pi
#print axioms ATK.ZeroClasses.PiLi.rh_iff_theta
