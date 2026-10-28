import ATK.ZeroClasses.HardyFourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# ATK — Hardy (parte 3): inversão de Fourier, continuação à faixa e a identidade dos momentos

Rodada 49 do projeto Hardy (R4). Sobre a representação `Ξ(t)/(t² + 1/4) = ∫₀^∞ Hr(u) cos(tu) du` e o
decaimento `|Ξ(t)| ≤ 24CΓ(1 + |t|)⁴e^{−π|t|/4}` (rodada 48):

* funções pares na reta (`integrable_of_even`, `integral_of_even`, `integral_exp_of_even`);
* **`integral_Fx_cos`** — a inversão de Fourier (`Continuous.fourierInv_fourier_eq` da Mathlib):
  `∫₀^∞ Fx(t) cos(xt) dt = (π/2) Hr(x)` para `x` real;
* `Gc n z = ∫₀^∞ Fx(t) t^{2n} cos(zt) dt`, holomorfa na faixa `|Im z| < π/4` (derivação sob a integral,
  `hasDerivAt_Gc`, `hasDerivAt_Sc`), e **`Gc_zero_eq`**: `Gc 0 = (π/2)(2cosh(z/2) − Θ(z))` na faixa
  (princípio da identidade);
* **`Gc_eq`**: `Gc n z = (−1)^n (π/2)(2·4^{−n} cosh(z/2) − Θ^{(2n)}(z))` na faixa;
* **`momento`**: `∫₀^∞ Fx(t) t^{2n} cosh(αt) dt = (−1)^n (π/2)(2·4^{−n} cos(α/2) − Re Θ^{(2n)}(iα))`, `|α| < π/4`;
* **`momento_tendsto`**: com a cúspide (rodada 47), quando `α → π/4⁻` o momento tende a `(−1)^n π 4^{−n} cos(π/8)`.

Nada aqui toca a Hipótese de Riemann; é a identidade de Hardy (1914), Titchmarsh §10.2.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real FourierTransform

namespace ATK.ZeroClasses.Hardy

open ATK.BaseRiemannXi (Xi continuous_Xi)
open ATK.GammaVertical (CΓ CΓ_pos)

/-! ## 1. Funções pares na reta -/

section Par

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem integrableOn_Iic_of_even {f : ℝ → E} (heven : ∀ x, f (-x) = f x)
    (hf : IntegrableOn f (Ioi 0)) : IntegrableOn f (Iic 0) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  have m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simp_rw [Function.comp_def, heven, neg_preimage, neg_Iic, neg_zero]
  exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf

omit [NormedSpace ℝ E] in
theorem integrable_of_even {f : ℝ → E} (heven : ∀ x, f (-x) = f x) (hf : IntegrableOn f (Ioi 0)) :
    Integrable f := by
  have h := (integrableOn_Iic_of_even heven hf).union hf
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem integral_of_even {f : ℝ → E} (heven : ∀ x, f (-x) = f x) (hf : IntegrableOn f (Ioi 0)) :
    ∫ x, f x = (2 : ℝ) • ∫ x in Ioi 0, f x := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrableOn_Iic_of_even heven hf) hf, two_smul]
  congr 1
  have h := integral_comp_neg_Ioi 0 f
  rw [neg_zero] at h
  rw [← h]
  simp_rw [heven]

end Par

theorem integrable_exp_mul {g : ℝ → ℝ} (hgi : Integrable g) (hgc : Continuous g) (b : ℝ) :
    Integrable (fun v : ℝ => cexp (((b * v : ℝ) : ℂ) * I) * (g v : ℂ)) := by
  refine hgi.norm.mono' (by fun_prop : Continuous _).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]

theorem exp_add_exp_neg (y : ℝ) (c : ℂ) :
    cexp ((y : ℂ) * I) * c + cexp (-(y : ℂ) * I) * c = ((2 * Real.cos y : ℝ) : ℂ) * c := by
  push_cast
  rw [Complex.two_cos]
  ring

/-- `∫ e^{iav} g(v) dv = 2∫₀^∞ g(v) cos(av) dv` para `g` real, contínua, par e integrável em `(0, ∞)`. -/
theorem integral_exp_of_even {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) (hg : IntegrableOn g (Ioi 0))
    (hgc : Continuous g) (a : ℝ) :
    ∫ v, cexp (((a * v : ℝ) : ℂ) * I) * (g v : ℂ) =
      ((2 * ∫ v in Ioi 0, g v * Real.cos (a * v) : ℝ) : ℂ) := by
  have hgi := integrable_of_even heven hg
  have h1 := integrable_exp_mul hgi hgc a
  have h2 := integrable_exp_mul hgi hgc (-a)
  have hneg : ∫ v, cexp ((((-a) * v : ℝ) : ℂ) * I) * (g v : ℂ) =
      ∫ v, cexp (((a * v : ℝ) : ℂ) * I) * (g v : ℂ) := by
    rw [← integral_neg_eq_self]
    congr 1
    funext v
    rw [heven]
    congr 4
    ring
  have hsum : (∫ v, cexp (((a * v : ℝ) : ℂ) * I) * (g v : ℂ)) +
      ∫ v, cexp ((((-a) * v : ℝ) : ℂ) * I) * (g v : ℂ) =
      ∫ v, ((2 * (g v * Real.cos (a * v)) : ℝ) : ℂ) := by
    refine (integral_add h1 h2).symm.trans ?_
    congr 1
    funext v
    rw [show (-a) * v = -(a * v) by ring, ofReal_neg, exp_add_exp_neg]
    push_cast
    ring
  have hc : IntegrableOn (fun v => g v * Real.cos (a * v)) (Ioi 0) := by
    refine hg.norm.mono' ((hgc.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have he := integral_of_even (f := fun v => g v * Real.cos (a * v))
    (fun v => by simp only [heven, mul_neg, Real.cos_neg]) hc
  rw [hneg, integral_complex_ofReal, integral_const_mul, he, smul_eq_mul] at hsum
  have hsum' : (2 : ℂ) * (∫ v, cexp (((a * v : ℝ) : ℂ) * I) * (g v : ℂ)) =
      2 * ((2 * ∫ v in Ioi 0, g v * Real.cos (a * v) : ℝ) : ℂ) := by
    rw [two_mul, hsum]; push_cast; ring
  exact mul_left_cancel₀ two_ne_zero hsum'

/-! ## 2. A inversão de Fourier -/

theorem continuous_Fx : Continuous Fx := by
  unfold Fx
  exact continuous_Xi.div (by fun_prop) fun t => by positivity

theorem integrableOn_pow_exp (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-δ * t)) (Ioi 0) := by
  have hk : (-1 : ℝ) < k := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := k) (b := δ) hk one_pos hδ
  simpa only [Real.rpow_natCast, Real.rpow_one] using h

theorem integrableOn_poly_exp (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ 4 * t ^ m * Real.exp (-δ * t)) (Ioi 0) := by
  have h := (integrableOn_pow_exp m hδ).add (((integrableOn_pow_exp (m + 1) hδ).const_mul 4).add
    (((integrableOn_pow_exp (m + 2) hδ).const_mul 6).add (((integrableOn_pow_exp (m + 3) hδ).const_mul 4).add
      (integrableOn_pow_exp (m + 4) hδ))))
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

/-- `|Fx(t)| t^m e^{βt}` é integrável em `(0, ∞)` para `β < π/4`. -/
theorem integrableOn_dom (m : ℕ) {β : ℝ} (hβ : β < π / 4) :
    IntegrableOn (fun t : ℝ => |Fx t| * t ^ m * Real.exp (β * t)) (Ioi 0) := by
  have hδ : 0 < π / 4 - β := by linarith
  refine ((integrableOn_poly_exp m hδ).const_mul (96 * CΓ)).mono' ?_ ?_
  · exact (((continuous_abs.comp continuous_Fx).mul (continuous_pow m)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht
    have h := abs_Fx_le t
    rw [abs_of_pos ht0] at h
    have hC := CΓ_pos
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e : Real.exp (-(π / 4) * t) * Real.exp (β * t) = Real.exp (-(π / 4 - β) * t) := by
      rw [← Real.exp_add]; ring_nf
    calc |Fx t| * t ^ m * Real.exp (β * t)
        ≤ 96 * CΓ * (1 + t) ^ 4 * Real.exp (-(π / 4) * t) * t ^ m * Real.exp (β * t) := by gcongr
      _ = 96 * CΓ * ((1 + t) ^ 4 * t ^ m * Real.exp (-(π / 4 - β) * t)) := by rw [← e]; ring

theorem integrableOn_Fx : IntegrableOn Fx (Ioi 0) := by
  refine (integrableOn_dom 0 (show (0 : ℝ) < π / 4 by positivity)).mono' continuous_Fx.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => ?_))
  simp

theorem integrable_Hr : Integrable Hr := by
  refine integrable_of_even Hr_neg ((integrableOn_exp_Ioi.const_mul 5).mono'
    continuous_Hr.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => ?_)))
  rw [Real.norm_eq_abs]
  exact abs_Hr_le_of_nonneg (le_of_lt hu)

/-- `𝓕 Hr (w) = 2 Fx(2πw)`. -/
theorem fourier_Hr (w : ℝ) : 𝓕 (fun u : ℝ => (Hr u : ℂ)) w = ((2 * Fx (2 * π * w) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  have e : ∀ v : ℝ, (((-2 * π * v * w : ℝ)) : ℂ) = (((-(2 * π * w)) * v : ℝ) : ℂ) := fun v => by
    congr 1; ring
  simp_rw [e]
  rw [integral_exp_of_even Hr_neg integrable_Hr.integrableOn continuous_Hr, Fx_eq]
  congr 3
  funext u
  rw [neg_mul, Real.cos_neg]

/-- **Inversão de Fourier**: `∫₀^∞ Fx(t) cos(xt) dt = (π/2) Hr(x)`. -/
theorem integral_Fx_cos (x : ℝ) : ∫ t in Ioi 0, Fx t * Real.cos (x * t) = π / 2 * Hr x := by
  have hc : Continuous (fun u : ℝ => (Hr u : ℂ)) := continuous_ofReal.comp continuous_Hr
  have hi : Integrable (fun u : ℝ => (Hr u : ℂ)) := integrable_Hr.ofReal
  have hF : 𝓕 (fun u : ℝ => (Hr u : ℂ)) = fun w => ((2 * Fx (2 * π * w) : ℝ) : ℂ) := funext fourier_Hr
  have hFx : Integrable Fx := integrable_of_even Fx_neg integrableOn_Fx
  have hFi : Integrable (fun w : ℝ => ((2 * Fx (2 * π * w) : ℝ) : ℂ)) :=
    ((hFx.comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)).const_mul 2).ofReal
  have hinv := hc.fourierInv_fourier_eq hi (hF ▸ hFi)
  have hx := congrFun hinv x
  rw [hF, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hx
  simp_rw [smul_eq_mul] at hx
  have e : ∀ v : ℝ, (((-2 * π * v * -x : ℝ)) : ℂ) = (((2 * π * x) * v : ℝ) : ℂ) := fun v => by
    congr 1; ring
  simp_rw [e] at hx
  have hgc : Continuous fun v : ℝ => 2 * Fx (2 * π * v) := by
    have := continuous_Fx; fun_prop
  have hgi : IntegrableOn (fun v : ℝ => 2 * Fx (2 * π * v)) (Ioi 0) :=
    ((hFx.comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)).const_mul 2).integrableOn
  rw [integral_exp_of_even (g := fun v => 2 * Fx (2 * π * v)) (fun v => by rw [mul_neg, Fx_neg]) hgi hgc]
    at hx
  have hx' := ofReal_injective hx
  have hcv := integral_comp_mul_left_Ioi (fun t => 2 * Fx t * Real.cos (x * t)) 0
    (by positivity : (0 : ℝ) < 2 * π)
  rw [mul_zero] at hcv
  have e2 : ∫ v in Ioi (0 : ℝ), 2 * Fx (2 * π * v) * Real.cos (2 * π * x * v) =
      ∫ v in Ioi (0 : ℝ), 2 * Fx (2 * π * v) * Real.cos (x * (2 * π * v)) := by
    congr 1; funext v; congr 2; ring
  rw [e2, hcv, smul_eq_mul] at hx'
  have e3 : ∫ t in Ioi (0 : ℝ), 2 * Fx t * Real.cos (x * t) = 2 * ∫ t in Ioi (0 : ℝ), Fx t * Real.cos (x * t) := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [e3] at hx'
  have hπ := Real.pi_pos
  field_simp at hx'
  linarith

/-! ## 3. A continuação à faixa `|Im z| < π/4` -/

/-- A faixa `|Im z| < π/4`. -/
def faixa : Set ℂ := {z | |z.im| < π / 4}

theorem isOpen_faixa : IsOpen faixa := isOpen_lt (continuous_abs.comp continuous_im) continuous_const

theorem convex_faixa : Convex ℝ faixa := by
  have e : faixa = Complex.imLm ⁻¹' (Ioo (-(π / 4)) (π / 4)) := by
    ext z; simp [faixa, abs_lt]
  rw [e]
  exact (convex_Ioo _ _).linear_preimage _

theorem norm_cos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h : 2 * ‖Complex.cos w‖ = ‖cexp (w * I) + cexp (-w * I)‖ := by
    rw [← Complex.two_cos, norm_mul, Complex.norm_two]
  have h1 : ‖cexp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact neg_le_abs _
  have h2 : ‖cexp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact le_abs_self _
  have := norm_add_le (cexp (w * I)) (cexp (-w * I))
  linarith

theorem norm_sin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h : ‖(2 : ℂ) * Complex.sin w‖ = ‖cexp (-w * I) - cexp (w * I)‖ := by
    rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
  rw [norm_mul, Complex.norm_two] at h
  have h1 : ‖cexp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact neg_le_abs _
  have h2 : ‖cexp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact le_abs_self _
  have := norm_sub_le (cexp (-w * I)) (cexp (w * I))
  linarith

/-- Derivação sob a integral para `∫₀^∞ Fx(t) t^m c(zt) dt`. -/
theorem hasDerivAt_trig {c c' : ℂ → ℂ} (hc : ∀ w, HasDerivAt c (c' w) w)
    (hcc : Continuous c) (hcc' : Continuous c')
    (hb : ∀ w, ‖c w‖ ≤ Real.exp |w.im|) (hb' : ∀ w, ‖c' w‖ ≤ Real.exp |w.im|)
    (m : ℕ) {z₀ : ℂ} (hz : z₀ ∈ faixa) :
    HasDerivAt (fun z => ∫ t in Ioi (0 : ℝ), ((Fx t * t ^ m : ℝ) : ℂ) * c (z * t))
      (∫ t in Ioi (0 : ℝ), ((Fx t * t ^ (m + 1) : ℝ) : ℂ) * c' (z₀ * t)) z₀ := by
  have hz' : |z₀.im| < π / 4 := hz
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (π / 4 - |z₀.im|) / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = |z₀.im| + ε := ⟨_, rfl⟩
  have hβ4 : β < π / 4 := by rw [hβ, hε]; linarith
  have hball : ∀ z ∈ ball z₀ ε, |z.im| ≤ β := by
    intro z hzb
    rw [mem_ball, dist_eq] at hzb
    have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by rw [← sub_im]; exact abs_im_le_norm _
    have h2 : |z.im| ≤ |z₀.im| + |z.im - z₀.im| := by
      calc |z.im| = |z₀.im + (z.im - z₀.im)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [hβ]; linarith
  have hnorm : ∀ (k : ℕ) (f : ℂ → ℂ), (∀ w, ‖f w‖ ≤ Real.exp |w.im|) → ∀ z : ℂ, ∀ t : ℝ, 0 < t →
      ‖((Fx t * t ^ k : ℝ) : ℂ) * f (z * t)‖ ≤ |Fx t| * t ^ k * Real.exp (|z.im| * t) := by
    intro k f hf z t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht.le k)]
    have h := hf (z * t)
    have e : |(z * (t : ℂ)).im| = |z.im| * t := by
      rw [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, abs_mul, abs_of_pos ht]
    rw [e] at h
    gcongr
  have hmeas : ∀ (k : ℕ) (f : ℂ → ℂ), Continuous f → ∀ z : ℂ,
      AEStronglyMeasurable (fun t : ℝ => ((Fx t * t ^ k : ℝ) : ℂ) * f (z * t)) (volume.restrict (Ioi 0)) := by
    intro k f hf z
    exact ((continuous_ofReal.comp (continuous_Fx.mul (continuous_pow k))).mul
      (hf.comp (continuous_const.mul continuous_ofReal))).aestronglyMeasurable
  have hint : ∀ (k : ℕ) (f : ℂ → ℂ), Continuous f → (∀ w, ‖f w‖ ≤ Real.exp |w.im|) → ∀ z : ℂ,
      |z.im| < π / 4 →
      Integrable (fun t : ℝ => ((Fx t * t ^ k : ℝ) : ℂ) * f (z * t)) (volume.restrict (Ioi 0)) := by
    intro k f hf hfb z hzi
    refine (integrableOn_dom k hzi).mono' (hmeas k f hf z) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hnorm k f hfb z t ht)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => ((Fx t * t ^ m : ℝ) : ℂ) * c (z * t))
    (F' := fun z t => ((Fx t * t ^ (m + 1) : ℝ) : ℂ) * c' (z * t)) (ball_mem_nhds z₀ hε0)
    (Eventually.of_forall fun z => hmeas m c hcc z) (hint m c hcc hb z₀ hz') (hmeas (m + 1) c' hcc' z₀)
    (bound := fun t => |Fx t| * t ^ (m + 1) * Real.exp (β * t)) ?_ (integrableOn_dom (m + 1) hβ4) ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hzb => ?_)
    have ht0 : (0 : ℝ) < t := ht
    refine (hnorm (m + 1) c' hb' z t ht0).trans ?_
    have := hball z hzb
    gcongr
  · refine Eventually.of_forall fun t z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => z * (t : ℂ)) (t : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (t : ℂ)
    have h2 := (hc (z * t)).comp z h1
    have h3 := h2.const_mul ((Fx t * t ^ m : ℝ) : ℂ)
    convert h3 using 1
    · rfl
    · push_cast
      ring

/-- `Gc n z = ∫₀^∞ Fx(t) t^{2n} cos(zt) dt`. -/
noncomputable def Gc (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), ((Fx t * t ^ (2 * n) : ℝ) : ℂ) * Complex.cos (z * t)

/-- `Sc n z = ∫₀^∞ Fx(t) t^{2n+1} sin(zt) dt`. -/
noncomputable def Sc (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), ((Fx t * t ^ (2 * n + 1) : ℝ) : ℂ) * Complex.sin (z * t)

theorem hasDerivAt_Gc (n : ℕ) {z : ℂ} (hz : z ∈ faixa) : HasDerivAt (Gc n) (-Sc n z) z := by
  have h := hasDerivAt_trig (c := Complex.cos) (c' := fun w => -Complex.sin w) Complex.hasDerivAt_cos
    Complex.continuous_cos Complex.continuous_sin.neg norm_cos_le_exp
    (fun w => by rw [norm_neg]; exact norm_sin_le_exp w) (2 * n) hz
  unfold Gc Sc
  convert h using 1
  rw [← integral_neg]
  congr 1
  funext t
  ring

theorem hasDerivAt_Sc (n : ℕ) {z : ℂ} (hz : z ∈ faixa) : HasDerivAt (Sc n) (Gc (n + 1) z) z := by
  have h := hasDerivAt_trig (c := Complex.sin) (c' := Complex.cos) Complex.hasDerivAt_sin
    Complex.continuous_sin Complex.continuous_cos norm_sin_le_exp norm_cos_le_exp (2 * n + 1) hz
  have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
  unfold Sc Gc
  rw [e]
  exact h

/-- `H(z) = 2 cosh(z/2) − Θ(z)`. -/
noncomputable def Hc (z : ℂ) : ℂ := 2 * Complex.cosh (z / 2) - Th z

theorem analyticOnNhd_Th : AnalyticOnNhd ℂ Th faixa :=
  DifferentiableOn.analyticOnNhd (f := Th) (fun _ hw => (Th_diff hw).differentiableWithinAt) isOpen_faixa

/-- **Continuação**: `Gc 0 = (π/2) H` na faixa (princípio da identidade). -/
theorem Gc_zero_eq {z : ℂ} (hz : z ∈ faixa) : Gc 0 z = π / 2 * Hc z := by
  have hG : AnalyticOnNhd ℂ (Gc 0) faixa :=
    DifferentiableOn.analyticOnNhd (f := Gc 0)
      (fun _ hw => (hasDerivAt_Gc 0 hw).differentiableAt.differentiableWithinAt) isOpen_faixa
  have hH : AnalyticOnNhd ℂ (fun w => π / 2 * Hc w) faixa := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_faixa
    unfold Hc
    have h1 : DifferentiableAt ℂ (fun w : ℂ => Complex.cosh (w / 2)) w :=
      Complex.differentiable_cosh.differentiableAt.comp w ((differentiableAt_id).div_const 2)
    exact ((differentiableAt_const _).mul ((h1.const_mul 2).sub (Th_diff hw))).differentiableWithinAt
  have hreal : ∀ x : ℝ, Gc 0 x = π / 2 * Hc x := by
    intro x
    unfold Gc Hc
    rw [← Hr_eq]
    have e : ∀ t : ℝ, ((Fx t * t ^ (2 * 0) : ℝ) : ℂ) * Complex.cos (↑x * ↑t) =
        ((Fx t * Real.cos (x * t) : ℝ) : ℂ) := by
      intro t; push_cast; simp
    simp_rw [e]
    rw [integral_complex_ofReal, integral_Fx_cos]
    push_cast
    ring
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), Gc 0 w = π / 2 * Hc w := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_ofReal.tendsto' 0 0 ofReal_zero).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun x hx => by simpa using hx
    exact ht.frequently (Frequently.of_forall hreal)
  have h0 : (0 : ℂ) ∈ faixa := by
    show |(0 : ℂ).im| < π / 4
    simp [Real.pi_pos]
  exact hG.eqOn_of_preconnected_of_frequently_eq hH convex_faixa.isPreconnected h0 hfreq hz

theorem hasDerivAt_iteratedDeriv_Th (k : ℕ) {z : ℂ} (hz : z ∈ faixa) :
    HasDerivAt (iteratedDeriv k Th) (iteratedDeriv (k + 1) Th z) z := by
  have h := (analyticOnNhd_Th.iterated_deriv k z hz).differentiableAt
  rw [← iteratedDeriv_eq_iterate] at h
  rw [iteratedDeriv_succ]
  exact h.hasDerivAt

/-- **Identidade dos momentos (complexa)**: `Gc n z = (−1)^n (π/2)(2·4^{−n} cosh(z/2) − Θ^{(2n)}(z))`. -/
theorem Gc_eq (n : ℕ) : ∀ z ∈ faixa,
    Gc n z = (-1) ^ n * (π / 2) * (2 * (1 / 4) ^ n * Complex.cosh (z / 2) - iteratedDeriv (2 * n) Th z) := by
  induction n with
  | zero =>
    intro z hz
    rw [Gc_zero_eq hz]
    unfold Hc
    simp
  | succ n ih =>
    have hS : ∀ z ∈ faixa, Sc n z = (-1) ^ (n + 1) * (π / 2) *
        (2 * (1 / 4) ^ n * (Complex.sinh (z / 2) * (1 / 2)) - iteratedDeriv (2 * n + 1) Th z) := by
      intro z hz
      have hc : HasDerivAt (fun w : ℂ => Complex.cosh (w / 2)) (Complex.sinh (z / 2) * (1 / 2)) z := by
        have := ((hasDerivAt_id z).div_const 2).ccosh
        simpa using this
      have hR : HasDerivAt (fun w => (-1) ^ n * (π / 2) *
          (2 * (1 / 4) ^ n * Complex.cosh (w / 2) - iteratedDeriv (2 * n) Th w))
          ((-1) ^ n * (π / 2) * (2 * (1 / 4) ^ n * (Complex.sinh (z / 2) * (1 / 2)) -
            iteratedDeriv (2 * n + 1) Th z)) z :=
        ((hc.const_mul _).sub (hasDerivAt_iteratedDeriv_Th (2 * n) hz)).const_mul _
      have hev : Gc n =ᶠ[𝓝 z] fun w => (-1) ^ n * (π / 2) *
          (2 * (1 / 4) ^ n * Complex.cosh (w / 2) - iteratedDeriv (2 * n) Th w) :=
        Filter.eventually_of_mem (isOpen_faixa.mem_nhds hz) ih
      have := (hasDerivAt_Gc n hz).unique (hR.congr_of_eventuallyEq hev)
      linear_combination (-1 : ℂ) * this
    intro z hz
    have hs : HasDerivAt (fun w : ℂ => Complex.sinh (w / 2)) (Complex.cosh (z / 2) * (1 / 2)) z := by
      have := ((hasDerivAt_id z).div_const 2).csinh
      simpa using this
    have hQ : HasDerivAt (fun w => (-1) ^ (n + 1) * (π / 2) *
        (2 * (1 / 4) ^ n * (Complex.sinh (w / 2) * (1 / 2)) - iteratedDeriv (2 * n + 1) Th w))
        ((-1) ^ (n + 1) * (π / 2) * (2 * (1 / 4) ^ n * (Complex.cosh (z / 2) * (1 / 2) * (1 / 2)) -
          iteratedDeriv (2 * n + 1 + 1) Th z)) z :=
      ((((hs.mul_const (1 / 2)).const_mul _).sub (hasDerivAt_iteratedDeriv_Th (2 * n + 1) hz))).const_mul _
    have hev : Sc n =ᶠ[𝓝 z] fun w => (-1) ^ (n + 1) * (π / 2) *
        (2 * (1 / 4) ^ n * (Complex.sinh (w / 2) * (1 / 2)) - iteratedDeriv (2 * n + 1) Th w) :=
      Filter.eventually_of_mem (isOpen_faixa.mem_nhds hz) hS
    have := (hasDerivAt_Sc n hz).unique (hQ.congr_of_eventuallyEq hev)
    rw [this, show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    ring

/-! ## 4. Os momentos de Hardy -/

/-- **Momentos de Hardy**: para `|α| < π/4`,
`∫₀^∞ Fx(t) t^{2n} cosh(αt) dt = (−1)^n (π/2)(2·4^{−n} cos(α/2) − Re Θ^{(2n)}(iα))`. -/
theorem momento (n : ℕ) {α : ℝ} (hα : |α| < π / 4) :
    ∫ t in Ioi (0 : ℝ), Fx t * t ^ (2 * n) * Real.cosh (α * t) =
      (-1) ^ n * (π / 2) * (2 * (1 / 4) ^ n * Real.cos (α / 2) - (iteratedDeriv (2 * n) Th (I * α)).re) := by
  have hz : I * (α : ℂ) ∈ faixa := by
    show |(I * (α : ℂ)).im| < π / 4
    simpa using hα
  have h := Gc_eq n (I * α) hz
  unfold Gc at h
  have e : ∀ t : ℝ, ((Fx t * t ^ (2 * n) : ℝ) : ℂ) * Complex.cos (I * ↑α * ↑t) =
      ((Fx t * t ^ (2 * n) * Real.cosh (α * t) : ℝ) : ℂ) := by
    intro t
    rw [show I * (α : ℂ) * (t : ℂ) = ((α * t : ℝ) : ℂ) * I by push_cast; ring, Complex.cos_mul_I,
      ← ofReal_cosh]
    push_cast
    ring
  simp_rw [e] at h
  rw [integral_complex_ofReal] at h
  have e2 : I * (α : ℂ) / 2 = ((α / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e2, Complex.cosh_mul_I, ← ofReal_cos] at h
  have e5 : (-1 : ℂ) ^ n * (↑π / 2) * (2 * (1 / 4) ^ n * ↑(Real.cos (α / 2)) - iteratedDeriv (2 * n) Th (I * ↑α)) =
      (((-1) ^ n * (π / 2) : ℝ) : ℂ) * (((2 * (1 / 4) ^ n * Real.cos (α / 2) : ℝ) : ℂ) -
        iteratedDeriv (2 * n) Th (I * ↑α)) := by
    push_cast; ring
  rw [e5] at h
  have h2 := congrArg Complex.re h
  rw [ofReal_re, re_ofReal_mul, sub_re, ofReal_re] at h2
  rw [h2]

/-- **A cúspide nos momentos**: quando `α = π/4 − 2r → π/4⁻`,
`∫₀^∞ Fx(t) t^{2n} cosh(αt) dt → (−1)^n π 4^{−n} cos(π/8)`. -/
theorem momento_tendsto (n : ℕ) :
    Tendsto (fun r : ℝ => ∫ t in Ioi (0 : ℝ), Fx t * t ^ (2 * n) * Real.cosh ((π / 4 - 2 * r) * t))
      (𝓝[>] 0) (𝓝 ((-1) ^ n * π * (1 / 4) ^ n * Real.cos (π / 8))) := by
  have hπ := Real.pi_pos
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, ∫ t in Ioi (0 : ℝ), Fx t * t ^ (2 * n) * Real.cosh ((π / 4 - 2 * r) * t) =
      (-1) ^ n * (π / 2) * (2 * (1 / 4) ^ n * Real.cos ((π / 4 - 2 * r) / 2) -
        (iteratedDeriv (2 * n) Th (I * ((π / 4 - 2 * r : ℝ) : ℂ))).re) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 8 by positivity)] with r hr
    obtain ⟨hr0, hr1⟩ := hr
    have hα : |π / 4 - 2 * r| < π / 4 := by
      rw [abs_lt]; constructor <;> linarith
    exact momento n hα
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hT := (continuous_re.tendsto 0).comp (iteratedDeriv_Th_tendsto (2 * n))
  have hc : Tendsto (fun r : ℝ => Real.cos ((π / 4 - 2 * r) / 2)) (𝓝[>] 0) (𝓝 (Real.cos (π / 8))) := by
    have : Continuous fun r : ℝ => Real.cos ((π / 4 - 2 * r) / 2) := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert h using 2
    ring_nf
  have hlim := ((hc.const_mul (2 * (1 / 4) ^ n)).sub hT).const_mul ((-1) ^ n * (π / 2))
  convert hlim using 2
  · simp
  · simp only [zero_re, sub_zero]
    ring

end ATK.ZeroClasses.Hardy

#print axioms ATK.ZeroClasses.Hardy.integrableOn_Iic_of_even
#print axioms ATK.ZeroClasses.Hardy.integrable_of_even
#print axioms ATK.ZeroClasses.Hardy.integral_of_even
#print axioms ATK.ZeroClasses.Hardy.integrable_exp_mul
#print axioms ATK.ZeroClasses.Hardy.exp_add_exp_neg
#print axioms ATK.ZeroClasses.Hardy.integral_exp_of_even
#print axioms ATK.ZeroClasses.Hardy.continuous_Fx
#print axioms ATK.ZeroClasses.Hardy.integrableOn_pow_exp
#print axioms ATK.ZeroClasses.Hardy.integrableOn_poly_exp
#print axioms ATK.ZeroClasses.Hardy.integrableOn_dom
#print axioms ATK.ZeroClasses.Hardy.integrableOn_Fx
#print axioms ATK.ZeroClasses.Hardy.integrable_Hr
#print axioms ATK.ZeroClasses.Hardy.fourier_Hr
#print axioms ATK.ZeroClasses.Hardy.integral_Fx_cos
#print axioms ATK.ZeroClasses.Hardy.isOpen_faixa
#print axioms ATK.ZeroClasses.Hardy.convex_faixa
#print axioms ATK.ZeroClasses.Hardy.norm_cos_le_exp
#print axioms ATK.ZeroClasses.Hardy.norm_sin_le_exp
#print axioms ATK.ZeroClasses.Hardy.hasDerivAt_trig
#print axioms ATK.ZeroClasses.Hardy.hasDerivAt_Gc
#print axioms ATK.ZeroClasses.Hardy.hasDerivAt_Sc
#print axioms ATK.ZeroClasses.Hardy.analyticOnNhd_Th
#print axioms ATK.ZeroClasses.Hardy.Gc_zero_eq
#print axioms ATK.ZeroClasses.Hardy.hasDerivAt_iteratedDeriv_Th
#print axioms ATK.ZeroClasses.Hardy.Gc_eq
#print axioms ATK.ZeroClasses.Hardy.momento
#print axioms ATK.ZeroClasses.Hardy.momento_tendsto
