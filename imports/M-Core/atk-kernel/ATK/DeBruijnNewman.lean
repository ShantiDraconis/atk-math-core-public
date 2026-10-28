import ATK.XiCrescimento

/-!
# ATK — A família de de Bruijn–Newman `H_t` e a constante `Λ`

`H_t(z) = ∫₀^∞ e^{tu²}Φ(u)cos(zu)du` (`H`), para todo `t ∈ ℝ`.

* **Construção** (sem hipóteses): `H_t` é inteira para todo `t` (`H_differentiable`; dominação
  `|e^{tu²}Φ(u)|e^{yu} ≤ 160·e^{K}e^{−u}`, `peso_cota`), par (`H_neg`), real em `ℝ` (`H_ofReal`), e
  `H₀(z) = ξ(1/2 + iz)/2` (`H_zero`, de `ATK.XiCresc.gXi_eq_HPhi`).
* **Equação do calor reversa** (`calor`): `∂H_t/∂t = −∂²H_t/∂z²` — derivação sob a integral em `t` e duas vezes
  em `z`.
* **HR ⟺ `0 ∈ S`** (`rh_iff_zero_mem`), onde `S = {t | todo zero de H_t é real}` e `Λ = inf S` (`Lambda`).
* **Pontes condicionais** (`rh_iff_Lambda_le_zero`, `rh_iff_Lambda_eq_zero`): com `S ≠ ∅` (de Bruijn 1950:
  `1/2 ∈ S`), `S` limitado inferiormente (Newman 1976), `S` fechado (Hurwitz) e `S` fechado para cima (de Bruijn
  1950), **HR ⟺ Λ ≤ 0**; com `Λ ≥ 0` (Rodgers–Tao 2020), **HR ⟺ Λ = 0**. Esses quatro fatos são teoremas
  conhecidos **não formalizados aqui** (`BUILD_PENDING`), e entram como hipóteses explícitas. `Lambda_vazio`,
  `Lambda_nao_limitado` mostram por que `S ≠ ∅` e a limitação são necessárias com o `sInf` do Mathlib.

Cotas superiores numéricas (`Λ ≤ 0,22`, Polymath15 2019; `Λ ≤ 0,2`, Platt–Trudgian 2021) não estão aqui. Nada
disto prova HR.
-/

open Complex Filter Topology Metric Set MeasureTheory

namespace ATK.DBN

open ATK.XiCresc ATK.XiTP ATK.BaseRiemannXi
open ATK.XiPhi (Phi)

/-- O peso `e^{tu²}Φ(u)`. -/
noncomputable def peso (t u : ℝ) : ℝ := Real.exp (t * u ^ 2) * Phi u

/-- **`H_t(z) = ∫₀^∞ e^{tu²}Φ(u)cos(zu)du`.** -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), (peso t u : ℂ) * Complex.cos (z * u)

/-! ## 1. Dominação -/

/-- `u/2 − (3/2)e^{2u} + tu² + yu ≤ K − u`, `K = |t| + y + (|t| + y)²` (`y, u ≥ 0`). -/
theorem expoente_dbn {t y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) :
    u / 2 - 3 / 2 * Real.exp (2 * u) + t * u ^ 2 + y * u ≤ (|t| + y + (|t| + y) ^ 2) - u := by
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have h4 : (2 * u) ^ 4 / 24 ≤ Real.exp (2 * u) := by
    have := Real.pow_div_factorial_le_exp (2 * u) (by linarith) 4
    simpa [Nat.factorial] using this
  have h4' : 2 / 3 * u ^ 4 ≤ Real.exp (2 * u) := by
    have e : (2 * u) ^ 4 / 24 = 2 / 3 * u ^ 4 := by ring
    linarith
  have ht : t * u ^ 2 ≤ |t| * u ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self t) (sq_nonneg u)
  have hT : 0 ≤ |t| := abs_nonneg t
  have key : -(u ^ 4 / 2) + |t| * u ^ 2 + y * u ≤ |t| + y + (|t| + y) ^ 2 := by
    rcases le_total u 1 with h | h
    · have hu2 : u ^ 2 ≤ 1 := by nlinarith
      have h5 : y * u ≤ y := by nlinarith
      have h6 : |t| * u ^ 2 ≤ |t| := by nlinarith
      nlinarith [pow_nonneg hu 4, sq_nonneg (|t| + y)]
    · have hyu : y * u ≤ y * u ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hy
      nlinarith [sq_nonneg (u ^ 2 - (|t| + y)), sq_nonneg (|t| + y)]
  nlinarith

/-- **`|e^{tu²}Φ(u)|·e^{yu} ≤ 160·e^{|t| + y + (|t| + y)²}·e^{−u}`** (`y, u ≥ 0`). -/
theorem peso_cota {t y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) :
    |peso t u| * Real.exp (y * u) ≤ 160 * Real.exp (|t| + y + (|t| + y) ^ 2) * Real.exp (-u) := by
  unfold peso
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (t * u ^ 2) * |Phi u| * Real.exp (y * u)
      ≤ Real.exp (t * u ^ 2) * (160 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u))) *
          Real.exp (y * u) := by
        gcongr
        exact Phi_cota hu
    _ = 160 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u) + t * u ^ 2 + y * u) := by
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ 160 * Real.exp ((|t| + y + (|t| + y) ^ 2) - u) := by
        gcongr
        exact expoente_dbn hy hu
    _ = 160 * Real.exp (|t| + y + (|t| + y) ^ 2) * Real.exp (-u) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring

theorem continuousOn_peso (t : ℝ) : ContinuousOn (peso t) (Ici 0) :=
  ((by fun_prop : Continuous fun u : ℝ => Real.exp (t * u ^ 2)).continuousOn).mul continuousOn_Phi

theorem aesm_G (t : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (peso t u : ℂ) * Complex.cos (z * u))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine (Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_peso t).mono Ioi_subset_Ici_self)).mul ?_
  exact (by fun_prop : Continuous fun u : ℝ => Complex.cos (z * u)).continuousOn

theorem integrable_G (t : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => (peso t u : ℂ) * Complex.cos (z * u)) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' (ATK.XiPhi.integrableOn_exp_neg_mul
    (160 * Real.exp (|t| + ‖z‖ + (|t| + ‖z‖) ^ 2))) (aesm_G t z) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc : ‖Complex.cos (z * u)‖ ≤ Real.exp (‖z‖ * u) := by
    refine (norm_cos_le _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
  calc |peso t u| * ‖Complex.cos (z * u)‖ ≤ |peso t u| * Real.exp (‖z‖ * u) :=
        mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ ≤ _ := peso_cota (norm_nonneg z) hu0

/-! ## 2. `H_t` é inteira -/

theorem hasDerivAt_H (t : ℝ) (z₀ : ℂ) : HasDerivAt (H t)
    (∫ u in Ioi (0 : ℝ), (peso t u : ℂ) * (-Complex.sin (z₀ * u) * u)) z₀ := by
  set Y := ‖z₀‖ + 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z u => (peso t u : ℂ) * Complex.cos (z * u))
    (F' := fun z u => (peso t u : ℂ) * (-Complex.sin (z * u) * u))
    (bound := fun u => 160 * Real.exp (|t| + Y + (|t| + Y) ^ 2) * Real.exp (-u))
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall fun z => aesm_G t z) (integrable_G t z₀)
    ?_ ?_ (ATK.XiPhi.integrableOn_exp_neg_mul _) ?_
  · exact key.2
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_peso t).mono Ioi_subset_Ici_self)).mul ?_
    exact (by fun_prop : Continuous fun u : ℝ => -Complex.sin (z₀ * u) * u).continuousOn
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu z hz => ?_
    have hu0 : 0 ≤ u := le_of_lt hu
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := mem_ball_iff_norm.mp hz
      have h2 := norm_le_insert' z z₀
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hu0]
    have hs : ‖Complex.sin (z * u)‖ ≤ Real.exp ((‖z₀‖ + 1) * u) := by
      refine (norm_sin_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      exact mul_le_mul_of_nonneg_right hzn hu0
    have hu1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hprod : ‖Complex.sin (z * u)‖ * u ≤ Real.exp (Y * u) := by
      calc ‖Complex.sin (z * u)‖ * u ≤ Real.exp ((‖z₀‖ + 1) * u) * Real.exp u :=
            mul_le_mul hs hu1 hu0 (Real.exp_pos _).le
        _ = Real.exp (Y * u) := by rw [← Real.exp_add, hY]; ring_nf
    calc |peso t u| * (‖Complex.sin (z * u)‖ * u) ≤ |peso t u| * Real.exp (Y * u) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ ≤ _ := peso_cota hY0 hu0
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => z * u) (u : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (u : ℂ)
    have h2 := (Complex.hasDerivAt_cos (z * u)).comp z h1
    have h3 := h2.const_mul (peso t u : ℂ)
    simpa [mul_comm, mul_assoc, mul_left_comm] using h3

/-- **`H_t` é inteira para todo `t ∈ ℝ`.** -/
theorem H_differentiable (t : ℝ) : Differentiable ℂ (H t) := fun z => (hasDerivAt_H t z).differentiableAt

/-- **`H₀(z) = ξ(1/2 + iz)/2`.** -/
theorem H_zero (z : ℂ) : H 0 z = gXi z / 2 := by
  rw [gXi_eq_HPhi, HPhi, H]
  simp only [peso, zero_mul, Real.exp_zero, one_mul]
  ring

/-- `H_t` é par. -/
theorem H_neg (t : ℝ) (z : ℂ) : H t (-z) = H t z := by
  unfold H
  congr 1
  funext u
  rw [neg_mul, Complex.cos_neg]

/-- `H_t` é real no eixo real. -/
theorem H_ofReal (t x : ℝ) :
    H t x = ((∫ u in Ioi (0 : ℝ), peso t u * Real.cos (x * u) : ℝ) : ℂ) := by
  rw [H, ← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  rfl

/-! ## 3. Equação do calor reversa -/

/-- Segunda derivada em `z`. -/
theorem hasDerivAt_H1 (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (peso t u : ℂ) * (-Complex.sin (z * u) * u))
      (∫ u in Ioi (0 : ℝ), (peso t u : ℂ) * (-Complex.cos (z₀ * u) * (u : ℂ) ^ 2)) z₀ := by
  set Y := ‖z₀‖ + 3 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hdom : ∀ {z : ℂ} {u : ℝ}, 0 ≤ u → ‖z‖ ≤ ‖z₀‖ + 1 → ∀ {f : ℂ → ℂ},
      (∀ w, ‖f w‖ ≤ Real.exp ‖w‖) → ∀ k : ℕ, k ≤ 2 →
      ‖(peso t u : ℂ) * (-f (z * u) * (u : ℂ) ^ k)‖ ≤
        160 * Real.exp (|t| + Y + (|t| + Y) ^ 2) * Real.exp (-u) := by
    intro z u hu0 hzn f hf k hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hu0]
    have hs : ‖f (z * u)‖ ≤ Real.exp ((‖z₀‖ + 1) * u) := by
      refine (hf _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      exact mul_le_mul_of_nonneg_right hzn hu0
    have hu2 : u ^ k ≤ Real.exp (2 * u) := by
      rcases le_total u 1 with h | h
      · calc u ^ k ≤ 1 := pow_le_one₀ hu0 h
          _ ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
      · calc u ^ k ≤ u ^ 2 := pow_le_pow_right₀ h hk
          _ ≤ Real.exp (2 * u) := by
            have := Real.pow_div_factorial_le_exp (2 * u) (by linarith) 2
            simp [Nat.factorial] at this
            nlinarith
    have hprod : ‖f (z * u)‖ * u ^ k ≤ Real.exp (Y * u) := by
      calc ‖f (z * u)‖ * u ^ k ≤ Real.exp ((‖z₀‖ + 1) * u) * Real.exp (2 * u) :=
            mul_le_mul hs hu2 (pow_nonneg hu0 k) (Real.exp_pos _).le
        _ = Real.exp (Y * u) := by rw [← Real.exp_add, hY]; ring_nf
    calc |peso t u| * (‖f (z * u)‖ * u ^ k) ≤ |peso t u| * Real.exp (Y * u) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ ≤ _ := peso_cota hY0 hu0
  have hball : ∀ z ∈ ball z₀ 1, ‖z‖ ≤ ‖z₀‖ + 1 := fun z hz => by
    have := mem_ball_iff_norm.mp hz
    have h2 := norm_le_insert' z z₀
    linarith
  have aesm1 : ∀ z : ℂ, AEStronglyMeasurable
      (fun u : ℝ => (peso t u : ℂ) * (-Complex.sin (z * u) * u)) (volume.restrict (Ioi 0)) := by
    intro z
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_peso t).mono Ioi_subset_Ici_self)).mul ?_
    exact (by fun_prop : Continuous fun u : ℝ => -Complex.sin (z * u) * u).continuousOn
  have hint : Integrable (fun u : ℝ => (peso t u : ℂ) * (-Complex.sin (z₀ * u) * u))
      (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' (ATK.XiPhi.integrableOn_exp_neg_mul
      (160 * Real.exp (|t| + Y + (|t| + Y) ^ 2))) (aesm1 z₀) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have := hdom (z := z₀) (le_of_lt hu) (by linarith) (f := Complex.sin) norm_sin_le 1 (by norm_num)
    simpa using this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z u => (peso t u : ℂ) * (-Complex.sin (z * u) * u))
    (F' := fun z u => (peso t u : ℂ) * (-Complex.cos (z * u) * (u : ℂ) ^ 2))
    (bound := fun u => 160 * Real.exp (|t| + Y + (|t| + Y) ^ 2) * Real.exp (-u))
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall aesm1) hint
    ?_ ?_ (ATK.XiPhi.integrableOn_exp_neg_mul _) ?_
  · exact key.2
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_peso t).mono Ioi_subset_Ici_self)).mul ?_
    exact (by fun_prop : Continuous fun u : ℝ => -Complex.cos (z₀ * u) * (u : ℂ) ^ 2).continuousOn
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu z hz => ?_
    exact hdom (le_of_lt hu) (hball z hz) norm_cos_le 2 le_rfl
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => z * u) (u : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (u : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => Complex.sin (z * u)) (Complex.cos (z * u) * u) z := h1.csin
    have h3 : HasDerivAt (fun z : ℂ => (peso t u : ℂ) * (-Complex.sin (z * u) * u))
        ((peso t u : ℂ) * (-(Complex.cos (z * u) * u) * u)) z :=
      (h2.neg.mul_const (u : ℂ)).const_mul (peso t u : ℂ)
    convert h3 using 1
    ring

/-- Derivada em `t`. -/
theorem hasDerivAt_H_t (t₀ : ℝ) (z : ℂ) : HasDerivAt (fun s => H s z)
    (∫ u in Ioi (0 : ℝ), ((u ^ 2 * peso t₀ u : ℝ) : ℂ) * Complex.cos (z * u)) t₀ := by
  set T := |t₀| + 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have aesm2 : AEStronglyMeasurable (fun u : ℝ => ((u ^ 2 * peso t₀ u : ℝ) : ℂ) * Complex.cos (z * u))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Complex.continuous_ofReal.comp_continuousOn
      (((by fun_prop : Continuous fun u : ℝ => u ^ 2).continuousOn).mul
        ((continuousOn_peso t₀).mono Ioi_subset_Ici_self))).mul ?_
    exact (by fun_prop : Continuous fun u : ℝ => Complex.cos (z * u)).continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s u => (peso s u : ℂ) * Complex.cos (z * u))
    (F' := fun s u => ((u ^ 2 * peso s u : ℝ) : ℂ) * Complex.cos (z * u))
    (bound := fun u => 160 * Real.exp (|T| + ‖z‖ + (|T| + ‖z‖) ^ 2) * Real.exp (-u))
    (Metric.ball_mem_nhds t₀ one_pos) (Eventually.of_forall fun s => aesm_G s z) (integrable_G t₀ z)
    aesm2 ?_ (ATK.XiPhi.integrableOn_exp_neg_mul _) ?_
  · exact key.2
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu s hs => ?_
    have hu0 : 0 ≤ u := le_of_lt hu
    have hsn : |s| ≤ |t₀| + 1 := by
      have := mem_ball_iff_norm.mp hs
      rw [Real.norm_eq_abs] at this
      have h2 := abs_sub_abs_le_abs_sub s t₀
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg u)]
    have hc : ‖Complex.cos (z * u)‖ ≤ Real.exp (‖z‖ * u) := by
      refine (norm_cos_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    have hpe : u ^ 2 * |peso s u| ≤ |peso T u| := by
      unfold peso
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have h1 : u ^ 2 ≤ Real.exp (u ^ 2) := by linarith [Real.add_one_le_exp (u ^ 2)]
      have h2 : Real.exp (s * u ^ 2) ≤ Real.exp ((|t₀| + 1) * u ^ 2) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self s).trans hsn) (sq_nonneg u))
      have h3 : Real.exp (u ^ 2) * Real.exp ((|t₀| + 1) * u ^ 2) = Real.exp (T * u ^ 2) := by
        rw [← Real.exp_add, hT]; ring_nf
      have hP := abs_nonneg (Phi u)
      calc u ^ 2 * (Real.exp (s * u ^ 2) * |Phi u|)
          ≤ Real.exp (u ^ 2) * (Real.exp ((|t₀| + 1) * u ^ 2) * |Phi u|) := by
            gcongr
        _ = Real.exp (T * u ^ 2) * |Phi u| := by rw [← h3]; ring
    calc u ^ 2 * |peso s u| * ‖Complex.cos (z * u)‖ ≤ |peso T u| * Real.exp (‖z‖ * u) :=
          mul_le_mul hpe hc (norm_nonneg _) (abs_nonneg _)
      _ ≤ _ := peso_cota (norm_nonneg z) hu0
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * u ^ 2)) (Real.exp (s * u ^ 2) * u ^ 2) s := by
      have := ((hasDerivAt_id s).mul_const (u ^ 2)).exp
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => peso s u) (u ^ 2 * peso s u) s := by
      have := h1.mul_const (Phi u)
      unfold peso
      convert this using 1
      ring
    have h3 := (h2.ofReal_comp).mul_const (Complex.cos (z * u))
    simpa using h3

/-- **Equação do calor reversa**: `∂H_t/∂t = −∂²H_t/∂z²`. -/
theorem calor (t : ℝ) (z : ℂ) : HasDerivAt (fun s => H s z) (-deriv (deriv (H t)) z) t := by
  have h1 : deriv (H t) = fun z => ∫ u in Ioi (0 : ℝ), (peso t u : ℂ) * (-Complex.sin (z * u) * u) :=
    funext fun z => (hasDerivAt_H t z).deriv
  rw [h1, (hasDerivAt_H1 t z).deriv, ← integral_neg]
  convert hasDerivAt_H_t t z using 2
  funext u
  push_cast
  ring

/-! ## 4. `Λ` e HR -/

/-- `H₀(z) = 0 ⟺ ξ(1/2 + iz) = 0`. -/
theorem H_zero_eq_zero_iff (z : ℂ) : H 0 z = 0 ↔ gXi z = 0 := by
  rw [H_zero, div_eq_zero_iff]
  simp

/-- **HR ⟺ todo zero de `H₀` é real.** -/
theorem rh_iff_H0 : RiemannHypothesis ↔ ∀ z : ℂ, H 0 z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_Xi]
  simp only [H_zero_eq_zero_iff]
  exact Iff.rfl

/-- `S = {t | todo zero de H_t é real}`. -/
def S : Set ℝ := {t | ∀ z : ℂ, H t z = 0 → z.im = 0}

/-- **A constante de de Bruijn–Newman** `Λ = inf S`. -/
noncomputable def Lambda : ℝ := sInf S

/-- **HR ⟺ `0 ∈ S`.** -/
theorem rh_iff_zero_mem : RiemannHypothesis ↔ (0 : ℝ) ∈ S := rh_iff_H0

/-- Com o `sInf` do Mathlib, `S = ∅` daria `Λ = 0`: a hipótese `S ≠ ∅` (de Bruijn) é necessária. -/
theorem Lambda_vazio (h : S = ∅) : Lambda = 0 := by
  rw [Lambda, h, Real.sInf_empty]

/-- Idem para `S` não limitado inferiormente (Newman). -/
theorem Lambda_nao_limitado (h : ¬ BddBelow S) : Lambda = 0 := by
  rw [Lambda, Real.sInf_of_not_bddBelow h]

/-- **HR ⇒ `Λ ≤ 0`** (com `S` limitado inferiormente). -/
theorem Lambda_le_zero_of_rh (hb : BddBelow S) (h : RiemannHypothesis) : Lambda ≤ 0 :=
  csInf_le hb (rh_iff_zero_mem.mp h)

/-- **`Λ ≤ 0` ⇒ HR**, dados os teoremas de de Bruijn (`S ≠ ∅`, `S` fechado para cima), Newman (`S` limitado
inferiormente) e Hurwitz (`S` fechado) — hipóteses explícitas, `BUILD_PENDING`. -/
theorem rh_of_Lambda_le_zero (hne : S.Nonempty) (hb : BddBelow S) (hcl : IsClosed S)
    (hup : ∀ s ∈ S, ∀ t, s ≤ t → t ∈ S) (hΛ : Lambda ≤ 0) : RiemannHypothesis :=
  rh_iff_zero_mem.mpr (hup _ (hcl.csInf_mem hne hb) 0 hΛ)

/-- **HR ⟺ `Λ ≤ 0`** (condicional aos quatro teoremas conhecidos acima). -/
theorem rh_iff_Lambda_le_zero (hne : S.Nonempty) (hb : BddBelow S) (hcl : IsClosed S)
    (hup : ∀ s ∈ S, ∀ t, s ≤ t → t ∈ S) : RiemannHypothesis ↔ Lambda ≤ 0 :=
  ⟨Lambda_le_zero_of_rh hb, rh_of_Lambda_le_zero hne hb hcl hup⟩

/-- **HR ⟺ `Λ = 0`**, somando `Λ ≥ 0` (Rodgers–Tao). -/
theorem rh_iff_Lambda_eq_zero (hne : S.Nonempty) (hb : BddBelow S) (hcl : IsClosed S)
    (hup : ∀ s ∈ S, ∀ t, s ≤ t → t ∈ S) (hRT : 0 ≤ Lambda) : RiemannHypothesis ↔ Lambda = 0 := by
  rw [rh_iff_Lambda_le_zero hne hb hcl hup]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Sob o fechamento para cima (de Bruijn), HR dá zeros reais para todo `t ≥ 0`. -/
theorem rh_todo_t (hup : ∀ s ∈ S, ∀ t, s ≤ t → t ∈ S) (h : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) :
    ∀ z : ℂ, H t z = 0 → z.im = 0 :=
  hup 0 (rh_iff_zero_mem.mp h) t ht

end ATK.DBN

#print axioms ATK.DBN.expoente_dbn
#print axioms ATK.DBN.peso_cota
#print axioms ATK.DBN.continuousOn_peso
#print axioms ATK.DBN.aesm_G
#print axioms ATK.DBN.integrable_G
#print axioms ATK.DBN.hasDerivAt_H
#print axioms ATK.DBN.H_differentiable
#print axioms ATK.DBN.H_zero
#print axioms ATK.DBN.H_neg
#print axioms ATK.DBN.H_ofReal
#print axioms ATK.DBN.hasDerivAt_H1
#print axioms ATK.DBN.hasDerivAt_H_t
#print axioms ATK.DBN.calor
#print axioms ATK.DBN.H_zero_eq_zero_iff
#print axioms ATK.DBN.rh_iff_H0
#print axioms ATK.DBN.rh_iff_zero_mem
#print axioms ATK.DBN.Lambda_vazio
#print axioms ATK.DBN.Lambda_nao_limitado
#print axioms ATK.DBN.Lambda_le_zero_of_rh
#print axioms ATK.DBN.rh_of_Lambda_le_zero
#print axioms ATK.DBN.rh_iff_Lambda_le_zero
#print axioms ATK.DBN.rh_iff_Lambda_eq_zero
#print axioms ATK.DBN.rh_todo_t
