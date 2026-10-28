import ATK.NSMild
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# ATK — Navier–Stokes, marco NS8f: unicidade na classe `SolucaoLocal` (pressão arbitrária)

Ponte B3, marco NS8 (sexta e última parte). **`unicidade`**: duas soluções `U₁, U₂` da classe
`SolucaoLocal` com o mesmo dado `u₀` (e pressões `P₁, P₂` **quaisquer**) coincidem em
`ℝ³ × [0, τ]` (`τ < T₁, T₂`) desde que a segunda seja limitada em `ℝ³ × [0, τ]`.

Ingredientes (todos provados aqui ou nos marcos NS8a–e):

* `nP_estimate`: o termo não linear da fórmula de Duhamel testada é
  `≤ (K₁ s^{−3/4} + K₂ s^{−1/2}) ‖W(σ)‖₂ ‖h‖₂` (integração por partes no espaço todo e
  `div W = 0`; cotas do teste do calor `|Re F0 (e^{−c|η|²s} h)| ≤ (π/(2cs))^{3/4} ‖h‖₂` e
  `‖∂_j Re F0 (e^{−c|η|²s} h)‖₂² ≤ (2π)²/(cs) ‖h‖₂²`);
* **`norming`**: para `W` suave, de divergência nula, `W, ∇W ∈ L²`, se `|∫ W · Re F0 h| ≤ A ‖h‖₂`
  para todo teste `h`, então `‖W‖₂ ≤ A` (corte em anel, projeção de Leray — a parte gradiente
  não enxerga `W` —, transformada de Fourier de `κ_R W` e `R → ∞`);
* Gronwall com peso `e^{−λt}` e o núcleo singular `s^{−a} e^{−λs} ≤ λ^{−1/8} s^{−a−1/8}`.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta** (falta a montagem NS9);
**CLOSED_MATH continua false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open scoped ContDiff Interval
open ATK.LigacaoNS (E3 dX e div lap conv grad gradSq fatia NSEq SolucaoLocal EnergiaAte)
open ATK.NSFourierBase ATK.NSPicard ATK.NSFisico ATK.NSCampos ATK.NSFraca ATK.NSTeste
  ATK.NSFracaF ATK.NSDual ATK.NSMild
open ATK.NSEnergia (amgm sq_le_of_forall integrable_Q)
open ATK.NSEquacao (cxL cxL_apply reV_cx v0S cota_v0 herm_v0 fourierInv_v0 sub_leray)
open scoped SchwartzMap

namespace ATK.NSUnico

/-! ### Cauchy–Schwarz -/

theorem cs {f g : E3 → ℝ} (hfm : AEStronglyMeasurable f) (hgm : AEStronglyMeasurable g)
    (hf : Integrable fun x => f x ^ 2) (hg : Integrable fun x => g x ^ 2) :
    ∫ x, |f x * g x| ≤ sqrt (∫ x, f x ^ 2) * sqrt (∫ x, g x ^ 2) := by
  set A := ∫ x, f x ^ 2
  set B := ∫ x, g x ^ 2
  have hA : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hi : Integrable fun x => |f x * g x| := by
    refine ((hf.add hg).div_const 2).mono' (hfm.mul hgm).norm (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_mul]
    show |f x| * |g x| ≤ (f x ^ 2 + g x ^ 2) / 2
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  set X := ∫ x, |f x * g x|
  have hX : 0 ≤ X := integral_nonneg fun x => abs_nonneg _
  have key : ∀ μ > 0, X ≤ (μ * A + B / μ) / 2 := by
    intro μ hμ
    have hb : Integrable fun x => (μ * f x ^ 2 + g x ^ 2 / μ) / 2 :=
      ((hf.const_mul μ).add (hg.div_const μ)).div_const 2
    calc X ≤ ∫ x, (μ * f x ^ 2 + g x ^ 2 / μ) / 2 := by
          refine integral_mono hi hb fun x => ?_
          rw [abs_mul]
          have := amgm |f x| |g x| hμ
          rw [sq_abs, sq_abs] at this
          exact this
      _ = (μ * A + B / μ) / 2 := by
          have j1 : Integrable fun x => μ * f x ^ 2 := hf.const_mul μ
          have j2 : Integrable fun x => g x ^ 2 / μ := hg.div_const μ
          rw [integral_div, integral_add j1 j2, integral_const_mul, integral_div]
  have hsq : X ^ 2 ≤ A * B := by
    have hε : ∀ ε > 0, X ^ 2 ≤ (A + ε) * B := by
      intro ε hε
      refine sq_le_of_forall hX (by linarith) hB fun μ hμ => (key μ hμ).trans ?_
      gcongr
      linarith
    by_contra hlt
    push Not at hlt
    set ε := (X ^ 2 - A * B) / (2 * (B + 1))
    have hεp : 0 < ε := by positivity
    have := hε ε hεp
    have hεB : ε * B < X ^ 2 - A * B := by
      have : ε * B ≤ (X ^ 2 - A * B) / 2 := by
        simp only [ε]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    nlinarith
  rw [← Real.sqrt_mul hA]
  exact Real.le_sqrt_of_sq_le hsq

/-! ### Gaussianas e cotas do teste do calor -/

theorem gauss {b : ℝ} (hb : 0 < b) :
    (Integrable fun η : E3 => exp (-b * ‖η‖ ^ 2)) ∧
      ∫ η : E3, exp (-b * ‖η‖ ^ 2) = (π / b) ^ (3 / 2 : ℝ) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E3) hb
  rw [finrank_E3] at h
  have h' : ∫ η : E3, exp (-b * ‖η‖ ^ 2) = (π / b) ^ (3 / 2 : ℝ) := by
    rw [h]
    norm_num
  refine ⟨Integrable.of_integral_ne_zero ?_, h'⟩
  rw [h']
  exact (rpow_pos_of_pos (by positivity) _).ne'

theorem norm_mj_le_norm (j : Fin 3) (ξ : E3) : ‖mj j ξ‖ ≤ 2 * π * ‖ξ‖ := by
  have e : mj j ξ = ((2 * π * ξ j : ℝ) : ℂ) * Complex.I := by
    unfold mj
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  gcongr
  exact NSFracaF.abs_coord_le ξ j

theorem norm_Hk0 (c : ℝ) (h : E3 → C3) (s : ℝ) (η : E3) :
    ‖Hk c h 0 s η‖ = exp (-(c * ‖η‖ ^ 2 * s)) * ‖h η‖ := by
  rw [Hk, norm_smul, pow_zero, one_mul, Real.norm_of_nonneg (exp_pos _).le]

/-- `|Re F0 (e^{−c|η|²s} h)| ≤ (π/(2cs))^{3/4} ‖h‖₂`. -/
theorem sup_R0_Hk {c s : ℝ} (hc : 0 < c) (hs : 0 < s) {h : E3 → C3} (hh : Pesos h)
    (h2 : Integrable fun η => ‖h η‖ ^ 2) (x : E3) :
    ‖R0 (Hk c h 0 s) x‖ ≤ (π / (2 * c * s)) ^ (3 / 4 : ℝ) * sqrt (∫ η, ‖h η‖ ^ 2) := by
  obtain ⟨hgi, hgv⟩ := gauss (b := 2 * c * s) (by positivity)
  have hf : Integrable fun η : E3 => exp (-(c * ‖η‖ ^ 2 * s)) ^ 2 := by
    refine hgi.congr (Eventually.of_forall fun η => ?_)
    simp only
    rw [← exp_nat_mul]
    ring_nf
  have hfm : AEStronglyMeasurable fun η : E3 => exp (-(c * ‖η‖ ^ 2 * s)) :=
    (by fun_prop : Continuous fun η : E3 => exp (-(c * ‖η‖ ^ 2 * s))).aestronglyMeasurable
  have hcs := cs hfm (hh.1.norm : Continuous fun η => ‖h η‖).aestronglyMeasurable hf h2
  have e1 : ∫ η : E3, exp (-(c * ‖η‖ ^ 2 * s)) ^ 2 = (π / (2 * c * s)) ^ (3 / 2 : ℝ) := by
    rw [← hgv]
    congr 1
    funext η
    rw [← exp_nat_mul]
    ring_nf
  rw [e1] at hcs
  have e2 : sqrt ((π / (2 * c * s)) ^ (3 / 2 : ℝ)) = (π / (2 * c * s)) ^ (3 / 4 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_mul (by positivity)]
    norm_num
  rw [e2] at hcs
  calc ‖R0 (Hk c h 0 s) x‖ ≤ ∫ η, ‖Hk c h 0 s η‖ :=
        (norm_R0_le _ x).trans (norm_F0_le _ x)
    _ = ∫ η, |exp (-(c * ‖η‖ ^ 2 * s)) * ‖h η‖| := by
        congr 1
        funext η
        rw [norm_Hk0, abs_of_nonneg (by positivity)]
    _ ≤ _ := hcs

/-- `‖∂_j Re F0 (e^{−c|η|²s} h)‖₂² ≤ (2π)²/(cs) ‖h‖₂²`. -/
theorem L2_dX_R0_Hk {c s : ℝ} (hc : 0 < c) (hs : 0 < s) {h : E3 → C3} (hh : Pesos h)
    (h2 : Integrable fun η => ‖h η‖ ^ 2) (j : Fin 3) :
    ∫ x, ‖dX j (R0 (Hk c h 0 s)) x‖ ^ 2 ≤ (2 * π) ^ 2 / (c * s) * ∫ η, ‖h η‖ ^ 2 := by
  have hpH : Pesos (Hk c h 0 s) := by
    refine ⟨continuous_Hk hh.1 0 s, fun m => ?_⟩
    obtain ⟨C, hC⟩ := hh.2 m
    refine ⟨C, fun ζ => ?_⟩
    rw [norm_Hk0]
    have h1 : exp (-(c * ‖ζ‖ ^ 2 * s)) ≤ 1 := by
      rw [exp_le_one_iff]; have : 0 ≤ c * ‖ζ‖ ^ 2 * s := by positivity
      linarith
    calc exp (-(c * ‖ζ‖ ^ 2 * s)) * ‖h ζ‖ * (1 + ‖ζ‖) ^ m ≤ 1 * ‖h ζ‖ * (1 + ‖ζ‖) ^ m := by
          gcongr
      _ = ‖h ζ‖ * (1 + ‖ζ‖) ^ m := by ring
      _ ≤ C := hC ζ
  have e : ∀ x, dX j (R0 (Hk c h 0 s)) x = R0 (fun η => mj j η • Hk c h 0 s η) x :=
    fun x => dX_R0 hpH j x
  simp_rw [e]
  have hG := pesos_mj hpH j
  refine (integral_R0_sq_le hG).trans ?_
  rw [← integral_const_mul]
  have hGi : Integrable fun η => ‖mj j η • Hk c h 0 s η‖ ^ 2 := by
    obtain ⟨C, hC⟩ := hG.2 2
    have := integrable_Q (k := 0) (by norm_num) hG.1 hC
    simpa using this
  refine integral_mono hGi (h2.const_mul _) fun η => ?_
  have h1 := norm_mj_le_norm j η
  have h3 := norm_mul_heat_le hc hs η
  have h4 : ‖mj j η • Hk c h 0 s η‖ ≤ 2 * π / sqrt (c * s) * ‖h η‖ := by
    rw [norm_smul, norm_Hk0]
    calc ‖mj j η‖ * (exp (-(c * ‖η‖ ^ 2 * s)) * ‖h η‖)
        ≤ 2 * π * ‖η‖ * (exp (-(c * ‖η‖ ^ 2 * s)) * ‖h η‖) := by gcongr
      _ = 2 * π * (‖η‖ * exp (-(c * ‖η‖ ^ 2 * s))) * ‖h η‖ := by ring
      _ ≤ 2 * π * (1 / sqrt (c * s)) * ‖h η‖ := by gcongr
      _ = 2 * π / sqrt (c * s) * ‖h η‖ := by ring
  have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
  have h6 : (2 * π / sqrt (c * s) * ‖h η‖) ^ 2 = (2 * π) ^ 2 / (c * s) * ‖h η‖ ^ 2 := by
    rw [mul_pow, div_pow, sq_sqrt (by positivity)]
  linarith

/-! ### Integração por partes no espaço todo (forma geral) -/

theorem int_mul_L2 {a b : E3 → ℝ} (ha : Continuous a) (hb : Continuous b)
    (ha2 : Integrable fun x => a x ^ 2) (hb2 : Integrable fun x => b x ^ 2) :
    Integrable fun x => a x * b x := by
  refine ((ha2.add hb2).div_const 2).mono' (ha.mul hb).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  show |a x| * |b x| ≤ (a x ^ 2 + b x ^ 2) / 2
  nlinarith [sq_nonneg (|a x| - |b x|), sq_abs (a x), sq_abs (b x)]

theorem ibp_whole {F G : E3 → E3} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (j : Fin 3)
    (h1 : Integrable fun x => ‖F x‖ * ‖dX j G x‖) (h2 : Integrable fun x => ‖dX j F x‖ * ‖G x‖)
    (h3 : Integrable fun x => ‖F x‖ * ‖G x‖) :
    ∫ x, inner ℝ (F x) (dX j G x) = -∫ x, inner ℝ (dX j F x) (G x) := by
  have hFi : ∀ i, ContDiff ℝ 1 fun x => F x i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  have hGi : ∀ i, ContDiff ℝ 1 fun x => G x i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hG
  have hdF : Continuous (dX j F) := continuous_dX_gen hF j
  have hdG : Continuous (dX j G) := continuous_dX_gen hG j
  have bnd : ∀ (a b : E3) (i : Fin 3), ‖a i * b i‖ ≤ ‖a‖ * ‖b‖ := fun a b i => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (NSFracaF.abs_coord_le a i) (NSFracaF.abs_coord_le b i) (abs_nonneg _)
      (norm_nonneg _)
  have e1 : (fun x => inner ℝ (F x) (dX j G x)) =
      fun x => ∑ i, F x i * dX j (fun y => G y i) x := by
    funext x
    rw [inner_E3]
    congr 1
    funext i
    rw [dX_coord (hG.differentiable one_ne_zero x)]
  have e2 : (fun x => inner ℝ (dX j F x) (G x)) =
      fun x => ∑ i, dX j (fun y => F y i) x * G x i := by
    funext x
    rw [inner_E3]
    congr 1
    funext i
    rw [dX_coord (hF.differentiable one_ne_zero x)]
  have i1 : ∀ i, Integrable fun x => F x i * dX j (fun y => G y i) x := by
    intro i
    refine h1.mono' ((hFi i).continuous.mul (continuous_dX (hGi i) j)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [← dX_coord (hG.differentiable one_ne_zero x)]
    exact bnd _ _ i
  have i2 : ∀ i, Integrable fun x => dX j (fun y => F y i) x * G x i := by
    intro i
    refine h2.mono' ((continuous_dX (hFi i) j).mul (hGi i).continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [← dX_coord (hF.differentiable one_ne_zero x)]
    exact bnd _ _ i
  have i3 : ∀ i, Integrable fun x => F x i * G x i := fun i =>
    h3.mono' ((hFi i).continuous.mul (hGi i).continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => bnd _ _ i)
  rw [e1, e2, integral_finsetSum _ fun i _ => i1 i, integral_finsetSum _ fun i _ => i2 i,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (i2 i) (i1 i) (i3 i)
    (fun x _ => (hFi i).differentiable one_ne_zero x) (fun x _ => (hGi i).differentiable one_ne_zero x)

theorem cs_norm {a b : E3 → E3} (ha : Continuous a) (hb : Continuous b)
    (ha2 : Integrable fun x => ‖a x‖ ^ 2) (hb2 : Integrable fun x => ‖b x‖ ^ 2) :
    ∫ x, ‖a x‖ * ‖b x‖ ≤ sqrt (∫ x, ‖a x‖ ^ 2) * sqrt (∫ x, ‖b x‖ ^ 2) := by
  have := cs ha.norm.aestronglyMeasurable hb.norm.aestronglyMeasurable ha2 hb2
  refine le_trans (le_of_eq ?_) this
  congr 1
  funext x
  rw [abs_of_nonneg (by positivity)]

theorem pesos_Hk0 {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) {h : E3 → C3} (hh : Pesos h) :
    Pesos (Hk c h 0 s) := by
  refine ⟨continuous_Hk hh.1 0 s, fun m => ?_⟩
  obtain ⟨C, hC⟩ := hh.2 m
  refine ⟨C, fun ζ => ?_⟩
  rw [norm_Hk0]
  have h1 : exp (-(c * ‖ζ‖ ^ 2 * s)) ≤ 1 := by
    rw [exp_le_one_iff]; have : 0 ≤ c * ‖ζ‖ ^ 2 * s := by positivity
    linarith
  calc exp (-(c * ‖ζ‖ ^ 2 * s)) * ‖h ζ‖ * (1 + ‖ζ‖) ^ m ≤ 1 * ‖h ζ‖ * (1 + ‖ζ‖) ^ m := by
        gcongr
    _ = ‖h ζ‖ * (1 + ‖ζ‖) ^ m := by ring
    _ ≤ C := hC ζ

/-! ### A estimativa do termo não linear -/

/-- **Estimativa estática** do termo não linear: com `w = u₁ − u₂`, `div u_i = 0`, `|u₂| ≤ B`,
`|φ| ≤ Φ` e `‖∂_jφ‖₂² ≤ D`,
`|Σ_j ∫ (u₁ⱼu₁ − u₂ⱼu₂)·∂_jφ| ≤ 3Φ‖w‖₂ √C₁ + 3B‖w‖₂√D`. -/
theorem nP_static {u₁ u₂ : E3 → E3} (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (hdiv₁ : ∀ x, div u₁ x = 0) (hdiv₂ : ∀ x, div u₂ x = 0)
    (hU1 : Integrable fun x => ‖u₁ x‖ ^ 2) (hU2 : Integrable fun x => ‖u₂ x‖ ^ 2)
    (hdU1 : ∀ j, Integrable fun x => ‖dX j u₁ x‖ ^ 2)
    (hdU2 : ∀ j, Integrable fun x => ‖dX j u₂ x‖ ^ 2) {C₁ : ℝ}
    (hdU1L : ∀ j, ∫ x, ‖dX j u₁ x‖ ^ 2 ≤ C₁) {B : ℝ} (hB : ∀ x, ‖u₂ x‖ ≤ B)
    {g : E3 → C3} (hg : Pesos g) {Φ : ℝ} (hΦ : ∀ x, ‖R0 g x‖ ≤ Φ) {Dφ : ℝ}
    (hD : ∀ j, ∫ x, ‖dX j (R0 g) x‖ ^ 2 ≤ Dφ) :
    |∑ j, (pr (fun x => u₁ x j • u₁ x) (mjg j g) - pr (fun x => u₂ x j • u₂ x) (mjg j g))| ≤
      Φ * (3 * sqrt C₁) * sqrt (∫ x, ‖u₁ x - u₂ x‖ ^ 2) +
        3 * B * sqrt (∫ x, ‖u₁ x - u₂ x‖ ^ 2) * sqrt Dφ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans (hΦ 0)
  set w : E3 → E3 := fun x => u₁ x - u₂ x with hwdef
  have hwx : ∀ x, w x = u₁ x - u₂ x := fun x => rfl
  have hWeq : (∫ x, ‖u₁ x - u₂ x‖ ^ 2) = ∫ x, ‖w x‖ ^ 2 := rfl
  rw [hWeq]
  set φ := R0 g with hφdef
  have hφ : ContDiff ℝ ∞ φ := contDiff_R0 hg
  have hw1 : ContDiff ℝ ∞ w := hu₁.sub hu₂
  have hcu₁ := hu₁.continuous
  have hcu₂ := hu₂.continuous
  have hcw := hw1.continuous
  have hcφ := hφ.continuous
  have hcdφ : ∀ j, Continuous (dX j φ) := fun j => continuous_dX_gen (hφ.of_le (by simp)) j
  have hcdu₁ : ∀ j, Continuous (dX j u₁) := fun j => continuous_dX_gen (hu₁.of_le (by simp)) j
  have hcdw : ∀ j, Continuous (dX j w) := fun j => continuous_dX_gen (hw1.of_le (by simp)) j
  have hdφ : ∀ j x, dX j φ x = R0 (mjg j g) x := fun j x => dX_R0 hg j x
  have hdφB : ∀ j, ∃ D, ∀ x, ‖dX j φ x‖ ≤ D := fun j =>
    ⟨∫ η, ‖mjg j g η‖, fun x => by
      rw [hdφ]; exact (norm_R0_le _ x).trans (norm_F0_le _ x)⟩
  have hdφ2 : ∀ j, Integrable fun x => ‖dX j φ x‖ ^ 2 := fun j => by
    simp_rw [hdφ]; exact (L2B_R0 (pesos_mj hg j)).2.2
  have hdW : ∀ j x, dX j w x = dX j u₁ x - dX j u₂ x := by
    intro j x
    show fderiv ℝ (fun x => u₁ x - u₂ x) x (e j) = fderiv ℝ u₁ x (e j) - fderiv ℝ u₂ x (e j)
    rw [fderiv_fun_sub (hu₁.differentiable (by simp) x) (hu₂.differentiable (by simp) x)]
    rfl
  have hdivw : ∀ x, ∑ j, dX j w x j = 0 := by
    intro x
    have h1 := hdiv₁ x
    have h2 := hdiv₂ x
    unfold div at h1 h2
    simp_rw [hdW, PiLp.sub_apply]
    rw [Finset.sum_sub_distrib, h1, h2, sub_zero]
  have hW2 : Integrable fun x => ‖w x‖ ^ 2 := by
    refine ((hU1.const_mul 2).add (hU2.const_mul 2)).mono'
      (hcw.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hwx]
    have h1 := norm_sub_le (u₁ x) (u₂ x)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    show _ ≤ 2 * ‖u₁ x‖ ^ 2 + 2 * ‖u₂ x‖ ^ 2
    nlinarith [sq_nonneg (‖u₁ x‖ - ‖u₂ x‖)]
  have hdW2 : ∀ j, Integrable fun x => ‖dX j w x‖ ^ 2 := by
    intro j
    refine (((hdU1 j).const_mul 2).add ((hdU2 j).const_mul 2)).mono'
      ((hcdw j).norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hdW]
    have h1 := norm_sub_le (dX j u₁ x) (dX j u₂ x)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    show _ ≤ 2 * ‖dX j u₁ x‖ ^ 2 + 2 * ‖dX j u₂ x‖ ^ 2
    nlinarith [sq_nonneg (‖dX j u₁ x‖ - ‖dX j u₂ x‖)]
  have hpj : ∀ (j : Fin 3), Continuous fun x : E3 => (x : E3) j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  -- integrabilidades dos pareamentos
  have iN : ∀ (u : E3 → E3), Continuous u → (Integrable fun x => ‖u x‖ ^ 2) → ∀ j,
      Integrable fun x => inner ℝ (u x j • u x) (R0 (mjg j g) x) := by
    intro u hu hu2 j
    have hc : Continuous fun x => u x j • u x := ((hpj j).comp hu).smul hu
    refine integrable_pr_L1 (F := fun x => u x j • u x) hc.aestronglyMeasurable ?_ (pesos_mj hg j)
    refine hu2.mono' hc.norm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_norm, norm_smul, Real.norm_eq_abs, sq]
    exact mul_le_mul_of_nonneg_right (NSFracaF.abs_coord_le _ j) (norm_nonneg _)
  have ia : ∀ j, Integrable fun x => w x j * inner ℝ (u₁ x) (dX j φ x) := by
    intro j
    obtain ⟨D, hD⟩ := hdφB j
    refine ((int_mul_L2 hcw.norm hcu₁.norm hW2 hU1).mul_const D).mono'
      ((((hpj j).comp hcw).mul (hcu₁.inner (hcdφ j))).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |w x j| * |inner ℝ (u₁ x) (dX j φ x)| ≤ ‖w x‖ * (‖u₁ x‖ * ‖dX j φ x‖) :=
          mul_le_mul (NSFracaF.abs_coord_le _ j) (abs_real_inner_le_norm _ _) (abs_nonneg _)
            (norm_nonneg _)
      _ ≤ ‖w x‖ * (‖u₁ x‖ * D) := by gcongr; exact hD x
      _ = ‖w x‖ * ‖u₁ x‖ * D := by ring
  have ib : ∀ j, Integrable fun x => u₂ x j * inner ℝ (w x) (dX j φ x) := by
    intro j
    refine ((int_mul_L2 hcw.norm (hcdφ j).norm hW2 (hdφ2 j)).const_mul B).mono'
      ((((hpj j).comp hcu₂).mul (hcw.inner (hcdφ j))).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul ((NSFracaF.abs_coord_le _ j).trans (hB x)) (abs_real_inner_le_norm _ _)
      (abs_nonneg _) hB0
  have hsplit : ∀ j, pr (fun x => u₁ x j • u₁ x) (mjg j g) - pr (fun x => u₂ x j • u₂ x) (mjg j g) =
      (∫ x, w x j * inner ℝ (u₁ x) (dX j φ x)) + ∫ x, u₂ x j * inner ℝ (w x) (dX j φ x) := by
    intro j
    unfold pr
    rw [← integral_sub (iN u₁ hcu₁ hU1 j) (iN u₂ hcu₂ hU2 j), ← integral_add (ia j) (ib j)]
    congr 1
    funext x
    rw [real_inner_smul_left, real_inner_smul_left, ← hdφ, hwx, PiLp.sub_apply, inner_sub_left]
    ring
  -- termo A: integração por partes e divergência nula
  have hF : ∀ j, ContDiff ℝ ∞ (fun x => w x j • u₁ x) := fun j =>
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hw1).smul hu₁
  have hdF : ∀ j x, dX j (fun x => w x j • u₁ x) x = dX j w x j • u₁ x + w x j • dX j u₁ x := by
    intro j x
    have hwj : DifferentiableAt ℝ (fun y => w y j) x :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hw1).differentiable (by simp) x
    rw [dX_smul_scalar (a := fun y => w y j) hwj (hu₁.differentiable (by simp) x) j,
      dX_coord (hw1.differentiable (by simp) x)]
  have iDF : ∀ j, Integrable fun x => ‖dX j (fun x => w x j • u₁ x) x‖ * ‖φ x‖ := by
    intro j
    refine (((int_mul_L2 (hcdw j).norm hcu₁.norm (hdW2 j) hU1).add
      (int_mul_L2 hcw.norm (hcdu₁ j).norm hW2 (hdU1 j))).mul_const Φ).mono'
      ((continuous_dX_gen ((hF j).of_le (by simp)) j).norm.mul hcφ.norm).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), hdF]
    have h1 : ‖dX j w x j • u₁ x + w x j • dX j u₁ x‖ ≤
        ‖dX j w x‖ * ‖u₁ x‖ + ‖w x‖ * ‖dX j u₁ x‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs] <;>
        gcongr <;> exact NSFracaF.abs_coord_le _ j
    calc ‖dX j w x j • u₁ x + w x j • dX j u₁ x‖ * ‖φ x‖ ≤
        (‖dX j w x‖ * ‖u₁ x‖ + ‖w x‖ * ‖dX j u₁ x‖) * Φ := by
          gcongr
          exact hΦ x
      _ = _ := rfl
  have iq : ∀ j, Integrable fun x => w x j * inner ℝ (dX j u₁ x) (φ x) := by
    intro j
    refine ((int_mul_L2 hcw.norm (hcdu₁ j).norm hW2 (hdU1 j)).mul_const Φ).mono'
      ((((hpj j).comp hcw).mul ((hcdu₁ j).inner hcφ)).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |w x j| * |inner ℝ (dX j u₁ x) (φ x)| ≤ ‖w x‖ * (‖dX j u₁ x‖ * ‖φ x‖) :=
          mul_le_mul (NSFracaF.abs_coord_le _ j) (abs_real_inner_le_norm _ _) (abs_nonneg _)
            (norm_nonneg _)
      _ ≤ ‖w x‖ * (‖dX j u₁ x‖ * Φ) := by gcongr; exact hΦ x
      _ = ‖w x‖ * ‖dX j u₁ x‖ * Φ := by ring
  have hA : ∀ j, ∫ x, w x j * inner ℝ (u₁ x) (dX j φ x) =
      -∫ x, inner ℝ (dX j (fun x => w x j • u₁ x) x) (φ x) := by
    intro j
    obtain ⟨D, hD⟩ := hdφB j
    have e : (fun x => w x j * inner ℝ (u₁ x) (dX j φ x)) =
        fun x => inner ℝ ((fun x => w x j • u₁ x) x) (dX j φ x) := by
      funext x
      rw [real_inner_smul_left]
    rw [e]
    have hcF : Continuous fun x => w x j • u₁ x := ((hpj j).comp hcw).smul hcu₁
    refine ibp_whole ((hF j).of_le (by simp)) (hφ.of_le (by simp)) j ?_ (iDF j) ?_
    · refine ((int_mul_L2 hcw.norm hcu₁.norm hW2 hU1).mul_const D).mono'
        ((hcF.norm.mul (hcdφ j).norm).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity), norm_smul, Real.norm_eq_abs]
      gcongr
      · exact NSFracaF.abs_coord_le _ j
      · exact hD x
    · refine ((int_mul_L2 hcw.norm hcu₁.norm hW2 hU1).mul_const Φ).mono'
        ((hcF.norm.mul hcφ.norm).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity), norm_smul, Real.norm_eq_abs]
      gcongr
      · exact NSFracaF.abs_coord_le _ j
      · exact hΦ x
  have hsumA : ∑ j, ∫ x, w x j * inner ℝ (u₁ x) (dX j φ x) =
      -∑ j, ∫ x, w x j * inner ℝ (dX j u₁ x) (φ x) := by
    simp_rw [hA]
    have iI : ∀ j, Integrable fun x => inner ℝ (dX j (fun x => w x j • u₁ x) x) (φ x) := by
      intro j
      refine (iDF j).mono' ((continuous_dX_gen ((hF j).of_le (by simp)) j).inner
        hcφ).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      exact abs_real_inner_le_norm _ _
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => iI j),
      ← integral_finsetSum _ (fun j _ => iq j)]
    congr 2
    funext x
    simp_rw [hdF, inner_add_left, real_inner_smul_left]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hdivw x, zero_mul, zero_add]
  have hAbnd : ∀ j, |∫ x, w x j * inner ℝ (dX j u₁ x) (φ x)| ≤
      Φ * sqrt C₁ * sqrt (∫ x, ‖w x‖ ^ 2) := by
    intro j
    refine (abs_integral_le_integral_abs).trans ?_
    have hi : Integrable fun x => ‖w x‖ * ‖dX j u₁ x‖ * Φ :=
      (int_mul_L2 hcw.norm (hcdu₁ j).norm hW2 (hdU1 j)).mul_const Φ
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hi
      (Eventually.of_forall fun x => ?_)).trans ?_
    · show |w x j * inner ℝ (dX j u₁ x) (φ x)| ≤ ‖w x‖ * ‖dX j u₁ x‖ * Φ
      rw [abs_mul]
      calc |w x j| * |inner ℝ (dX j u₁ x) (φ x)| ≤ ‖w x‖ * (‖dX j u₁ x‖ * ‖φ x‖) :=
            mul_le_mul (NSFracaF.abs_coord_le _ j) (abs_real_inner_le_norm _ _) (abs_nonneg _)
              (norm_nonneg _)
        _ ≤ ‖w x‖ * (‖dX j u₁ x‖ * Φ) := by gcongr; exact hΦ x
        _ = _ := by ring
    · rw [integral_mul_const]
      have h1 := cs_norm hcw (hcdu₁ j) hW2 (hdU1 j)
      have h2 : sqrt (∫ x, ‖dX j u₁ x‖ ^ 2) ≤ sqrt C₁ := sqrt_le_sqrt (hdU1L j)
      have h3 : (∫ x, ‖w x‖ * ‖dX j u₁ x‖) ≤ sqrt (∫ x, ‖w x‖ ^ 2) * sqrt C₁ :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (sqrt_nonneg _))
      calc (∫ x, ‖w x‖ * ‖dX j u₁ x‖) * Φ ≤ (sqrt (∫ x, ‖w x‖ ^ 2) * sqrt C₁) * Φ := by
            gcongr
        _ = _ := by ring
  have hBbnd : ∀ j, |∫ x, u₂ x j * inner ℝ (w x) (dX j φ x)| ≤
      B * sqrt (∫ x, ‖w x‖ ^ 2) * sqrt Dφ := by
    intro j
    refine (abs_integral_le_integral_abs).trans ?_
    have hi : Integrable fun x => B * (‖w x‖ * ‖dX j φ x‖) :=
      (int_mul_L2 hcw.norm (hcdφ j).norm hW2 (hdφ2 j)).const_mul B
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hi
      (Eventually.of_forall fun x => ?_)).trans ?_
    · show |u₂ x j * inner ℝ (w x) (dX j φ x)| ≤ B * (‖w x‖ * ‖dX j φ x‖)
      rw [abs_mul]
      exact mul_le_mul ((NSFracaF.abs_coord_le _ j).trans (hB x)) (abs_real_inner_le_norm _ _)
        (abs_nonneg _) hB0
    · rw [integral_const_mul, mul_assoc]
      have h1 := cs_norm hcw (hcdφ j) hW2 (hdφ2 j)
      have h2 : sqrt (∫ x, ‖dX j φ x‖ ^ 2) ≤ sqrt Dφ := sqrt_le_sqrt (hD j)
      gcongr
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (sqrt_nonneg _))
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, hsumA]
  simp only [Fin.sum_univ_three] at *
  have a0 := abs_le.mp (hAbnd 0)
  have a1 := abs_le.mp (hAbnd 1)
  have a2 := abs_le.mp (hAbnd 2)
  have b0 := abs_le.mp (hBbnd 0)
  have b1 := abs_le.mp (hBbnd 1)
  have b2 := abs_le.mp (hBbnd 2)
  rw [abs_le]
  constructor <;> nlinarith

section Est

variable {ν T₁ T₂ τ : ℝ} {u₀ : E3 → E3} {U₁ U₂ : E3 × ℝ → E3} {P₁ P₂ : E3 × ℝ → ℝ}

/-- **Estimativa do termo não linear** com o teste `e^{−c|η|²s} h` (a segunda solução limitada
por `B` em `[0, τ]`). -/
theorem nP_estimate (hS₁ : SolucaoLocal ν u₀ T₁ U₁ P₁) (hS₂ : SolucaoLocal ν u₀ T₂ U₂ P₂)
    (hτ0 : 0 ≤ τ) (hτ₁ : τ < T₁) (hτ₂ : τ < T₂) {B : ℝ}
    (hB : ∀ x, ∀ s ∈ Icc 0 τ, ‖U₂ (x, s)‖ ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ {c s : ℝ}, 0 < c → 0 < s → ∀ {h : E3 → C3}, Pesos h →
      (Integrable fun η => ‖h η‖ ^ 2) → ∀ σ,
      |nP τ U₁ U₂ (Hk c h 0 s) σ| ≤
        (K * (π / (2 * c * s)) ^ (3 / 4 : ℝ) + 3 * B * (2 * π / sqrt (c * s))) *
          sqrt (∫ x, ‖Wc τ U₁ U₂ σ x‖ ^ 2) * sqrt (∫ η, ‖h η‖ ^ 2) := by
  obtain ⟨C₁, hC₁⟩ := sol_bounds hS₁ hτ₁
  obtain ⟨C₂, hC₂⟩ := sol_bounds hS₂ hτ₂
  have hC₁0 : 0 ≤ C₁ := (integral_nonneg fun x => sq_nonneg ‖U₁ (x, 0)‖).trans
    (hC₁ 0 ⟨le_rfl, hτ0⟩).1.2
  refine ⟨3 * sqrt C₁, by positivity, fun {c s} hc hs {h} hh h2 σ => ?_⟩
  have hσ' : clamp τ σ ∈ Icc 0 τ := clamp_mem hτ0 σ
  have hσ₁ : clamp τ σ ∈ Ico 0 T₁ := ⟨hσ'.1, hσ'.2.trans_lt hτ₁⟩
  have hσ₂ : clamp τ σ ∈ Ico 0 T₂ := ⟨hσ'.1, hσ'.2.trans_lt hτ₂⟩
  have key := nP_static (u₁ := fatia U₁ (clamp τ σ)) (u₂ := fatia U₂ (clamp τ σ))
    (slice_contDiff hS₁.1 hσ₁) (slice_contDiff hS₂.1 hσ₂)
    (fun x => hS₁.2.2.2.2.1 x _ hσ₁) (fun x => hS₂.2.2.2.2.1 x _ hσ₂)
    (hC₁ _ hσ').1.1 (hC₂ _ hσ').1.1 (fun j => ((hC₁ _ hσ').2 j).1)
    (fun j => ((hC₂ _ hσ').2 j).1) (fun j => ((hC₁ _ hσ').2 j).2) (fun x => hB x _ hσ')
    (pesos_Hk0 hc.le hs.le hh) (fun x => sup_R0_Hk hc hs hh h2 x)
    (fun j => L2_dX_R0_Hk hc hs hh h2 j)
  have e1 : sqrt ((2 * π) ^ 2 / (c * s) * ∫ η, ‖h η‖ ^ 2) =
      2 * π / sqrt (c * s) * sqrt (∫ η, ‖h η‖ ^ 2) := by
    rw [sqrt_mul (by positivity), sqrt_div (by positivity), sqrt_sq (by positivity)]
  rw [e1] at key
  have e2 : (∫ x, ‖Wc τ U₁ U₂ σ x‖ ^ 2) =
      ∫ x, ‖fatia U₁ (clamp τ σ) x - fatia U₂ (clamp τ σ) x‖ ^ 2 := rfl
  rw [e2]
  calc |nP τ U₁ U₂ (Hk c h 0 s) σ| = |∑ j, (pr (fun x => fatia U₁ (clamp τ σ) x j •
        fatia U₁ (clamp τ σ) x) (mjg j (Hk c h 0 s)) - pr (fun x => fatia U₂ (clamp τ σ) x j •
        fatia U₂ (clamp τ σ) x) (mjg j (Hk c h 0 s)))| := rfl
    _ ≤ _ := key
    _ = _ := by ring

end Est

/-! ### Normação: a norma `L²` de um campo de divergência nula é controlada pelos testes -/

theorem ibp_scalar {f g : E3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (j : Fin 3)
    (i1 : Integrable fun x => f x * dX j g x) (i2 : Integrable fun x => dX j f x * g x)
    (i3 : Integrable fun x => f x * g x) :
    ∫ x, f x * dX j g x = -∫ x, dX j f x * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i2 i1 i3
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)

theorem R0_sub {g₁ g₂ : E3 → C3} (h₁ : Integrable g₁) (h₂ : Integrable g₂) (x : E3) :
    R0 (fun η => g₁ η - g₂ η) x = R0 g₁ x - R0 g₂ x := by
  unfold R0 F0
  have e : (fun ξ => ex ξ x • (g₁ ξ - g₂ ξ)) = fun ξ => ex ξ x • g₁ ξ - ex ξ x • g₂ ξ := by
    funext ξ
    rw [smul_sub]
  rw [e, integral_sub (integrable_ex_smul h₁ x) (integrable_ex_smul h₂ x), map_sub]

theorem pr_sub {W : E3 → E3} (hWm : AEStronglyMeasurable W)
    (hW2 : Integrable fun x => ‖W x‖ ^ 2) {g₁ g₂ : E3 → C3} (h₁ : Pesos g₁) (h₂ : Pesos g₂) :
    pr W (fun η => g₁ η - g₂ η) = pr W g₁ - pr W g₂ := by
  unfold pr
  simp_rw [R0_sub (integrable_pesos h₁) (integrable_pesos h₂), inner_sub_right]
  exact integral_sub (integrable_pr_L2 hWm hW2 h₁) (integrable_pr_L2 hWm hW2 h₂)

theorem integrable_sq_pesos {g : E3 → C3} (hg : Pesos g) : Integrable fun η => ‖g η‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hg.2 2
  have := integrable_Q (k := 0) (by norm_num) hg.1 hC
  simpa using this

theorem abs_pr_le {W : E3 → E3} (hW : Continuous W) (hW2 : Integrable fun x => ‖W x‖ ^ 2)
    {g : E3 → C3} (hg : Pesos g) :
    |pr W g| ≤ sqrt (∫ x, ‖W x‖ ^ 2) * sqrt (∫ η, ‖g η‖ ^ 2) := by
  unfold pr
  refine (abs_integral_le_integral_abs).trans ?_
  have hc := (contDiff_R0 hg).continuous
  have hi := int_mul_L2 hW.norm hc.norm hW2 (integrable_R0_sq hg)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hi
    (Eventually.of_forall fun x => abs_real_inner_le_norm _ _)).trans ?_
  refine (cs_norm hW hc hW2 (integrable_R0_sq hg)).trans ?_
  exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (integral_R0_sq_le hg)) (sqrt_nonneg _)

theorem continuous_ip_of {g : E3 → C3} (hg : Continuous g) : Continuous fun η => ip η (g η) := by
  unfold ip
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_ofReal.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous)).mul
    ((EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp hg)

/-- O vetor `e₀ ∈ ℂ³`. -/
noncomputable def e0c : C3 := EuclideanSpace.single 0 (1 : ℂ)

/-- **A parte gradiente não enxerga campos de divergência nula**: para `g` contínua, de suporte
compacto e nula perto de `0`, `∫ W · Re F0 (𝐏 g) = ∫ W · Re F0 g`. -/
theorem pr_leray {W : E3 → E3} (hW : ContDiff ℝ ∞ W) (hdiv : ∀ x, div W x = 0)
    (hW2 : Integrable fun x => ‖W x‖ ^ 2) (hdW2 : ∀ j, Integrable fun x => ‖dX j W x‖ ^ 2)
    {g : E3 → C3} (hg : Continuous g) (hgs : HasCompactSupport g)
    (h0 : ∃ a > 0, ∀ η : E3, ‖η‖ < a → g η = 0) :
    pr W (fun η => leray η (g η)) = pr W g := by
  obtain ⟨a, ha, hga⟩ := h0
  set q : E3 → ℂ := fun η => (((‖η‖ ^ 2 : ℝ) : ℂ))⁻¹ * ip η (g η) with hq
  have hq0 : ∀ η, g η = 0 → q η = 0 := fun η hη => by simp [hq, hη, ip_zero]
  have hqc : Continuous q := by
    rw [continuous_iff_continuousAt]
    intro η₀
    by_cases h : ‖η₀‖ < a
    · have hev : q =ᶠ[𝓝 η₀] fun _ => 0 := by
        have hopen : IsOpen {η : E3 | ‖η‖ < a} := isOpen_lt continuous_norm continuous_const
        filter_upwards [hopen.mem_nhds h] with η hη using hq0 η (hga η hη)
      exact continuousAt_const.congr hev.symm
    · have hne : η₀ ≠ 0 := by
        intro h'
        apply h
        rw [h', norm_zero]
        exact ha
      have hn : ((‖η₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        have : ‖η₀‖ ≠ 0 := norm_ne_zero_iff.mpr hne
        exact_mod_cast pow_ne_zero 2 this
      refine ContinuousAt.mul ?_ (continuous_ip_of hg).continuousAt
      exact ContinuousAt.inv₀ (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).continuousAt hn
  set k : E3 → C3 := fun η => q η • cx η with hk
  set K : E3 → C3 := fun η => ((2 * π * Complex.I)⁻¹ * q η) • e0c with hK
  have hkc : Continuous k := hqc.smul cxL.continuous
  have hKc : Continuous K := (continuous_const.mul hqc).smul continuous_const
  have hks : HasCompactSupport k := hgs.mono fun η hη => by
    intro hg0
    apply hη
    simp [hk, hq0 η hg0]
  have hKs : HasCompactSupport K := hgs.mono fun η hη => by
    intro hg0
    apply hη
    simp [hK, hq0 η hg0]
  have hkP : Pesos k := pesos_of_compact hkc hks
  have hKP : Pesos K := pesos_of_compact hKc hKs
  have hgP : Pesos g := pesos_of_compact hg hgs
  have hlg : (fun η => leray η (g η)) = fun η => g η - k η := by
    funext η
    have h := sub_leray η (g η)
    show leray η (g η) = g η - ((((‖η‖ ^ 2 : ℝ) : ℂ))⁻¹ * ip η (g η)) • cx η
    rw [← h, sub_sub_cancel]
  have hlP : Pesos fun η => leray η (g η) := by
    rw [hlg]
    exact pesos_of_compact (hg.sub hkc) (hgs.sub hks)
  rw [hlg, pr_sub hW.continuous.aestronglyMeasurable hW2 hgP hkP, sub_eq_self]
  -- `Re F0 k = ∇ψ`
  set ψ : E3 → ℝ := fun x => R0 K x 0 with hψ
  have hRK : ContDiff ℝ ∞ (R0 K) := contDiff_R0 hKP
  have hψc : ContDiff ℝ ∞ ψ := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.comp hRK
  have h2πI : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have hdψ : ∀ j x, dX j ψ x = R0 k x j := by
    intro j x
    have h1 : dX j ψ x = dX j (R0 K) x 0 :=
      (dX_coord (hRK.differentiable (by simp) x) j 0).symm
    rw [h1, dX_R0 hKP j x]
    show (F0 (fun ξ => mj j ξ • K ξ) x 0).re = (F0 k x j).re
    rw [F0_coord _ (integrable_pesos (pesos_mj hKP j)) x 0, F0_coord _ (integrable_pesos hkP) x j]
    congr 2
    funext ξ
    congr 1
    simp only [hK, hk, PiLp.smul_apply, smul_eq_mul, e0c, cx_apply, mj]
    rw [PiLp.single_apply]
    simp only [ite_true, mul_one]
    field_simp
  have hRk : Continuous (R0 k) := (contDiff_R0 hkP).continuous
  have hpj : ∀ (j : Fin 3), Continuous fun x : E3 => (x : E3) j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  have hWj : ∀ j, ContDiff ℝ ∞ fun x => W x j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hW
  have hψb : ∀ x, |ψ x| ≤ ‖R0 K x‖ := fun x => NSFracaF.abs_coord_le _ 0
  have hcRK := hRK.continuous
  have i1 : ∀ j, Integrable fun x => W x j * dX j ψ x := by
    intro j
    refine (int_mul_L2 hW.continuous.norm hRk.norm hW2 (integrable_R0_sq hkP)).mono'
      (((hpj j).comp hW.continuous).mul (continuous_dX_gen (hψc.of_le (by simp)) j)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [hdψ, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (NSFracaF.abs_coord_le _ j) (NSFracaF.abs_coord_le _ j) (abs_nonneg _)
      (norm_nonneg _)
  have i2 : ∀ j, Integrable fun x => dX j (fun y => W y j) x * ψ x := by
    intro j
    refine (int_mul_L2 (continuous_dX_gen (hW.of_le (by simp)) j).norm hcRK.norm (hdW2 j)
      (integrable_R0_sq hKP)).mono'
      ((continuous_dX_gen ((hWj j).of_le (by simp)) j).mul hψc.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [← dX_coord (hW.differentiable (by simp) x), norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (NSFracaF.abs_coord_le _ j) (hψb x) (abs_nonneg _) (norm_nonneg _)
  have i3 : ∀ j, Integrable fun x => W x j * ψ x := by
    intro j
    refine (int_mul_L2 hW.continuous.norm hcRK.norm hW2 (integrable_R0_sq hKP)).mono'
      (((hpj j).comp hW.continuous).mul hψc.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (NSFracaF.abs_coord_le _ j) (hψb x) (abs_nonneg _) (norm_nonneg _)
  have e1 : (fun x => inner ℝ (W x) (R0 k x)) = fun x => ∑ j, W x j * dX j ψ x := by
    funext x
    rw [inner_E3]
    congr 1
    funext j
    rw [hdψ]
  unfold pr
  rw [e1, integral_finsetSum _ fun j _ => i1 j]
  have e2 : ∀ j, ∫ x, W x j * dX j ψ x = -∫ x, dX j (fun y => W y j) x * ψ x := fun j =>
    ibp_scalar ((hWj j).of_le (by simp)) (hψc.of_le (by simp)) j (i1 j) (i2 j) (i3 j)
  simp_rw [e2]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ => i2 j, neg_eq_zero]
  have e3 : (fun x => ∑ j, dX j (fun y => W y j) x * ψ x) = fun _ => (0 : ℝ) := by
    funext x
    rw [← Finset.sum_mul]
    have : ∑ j, dX j (fun y => W y j) x = div W x := by
      unfold div
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dX_coord (hW.differentiable (by simp) x)]
    rw [this, hdiv x, zero_mul]
  rw [e3, integral_zero]

/-- A projeção de Leray de uma `g` contínua, de suporte compacto, nula perto de `0` e hermitiana
é um **teste**. -/
theorem teste_leray {g : E3 → C3} (hg : Continuous g) (hgs : HasCompactSupport g)
    (h0 : ∃ a > 0, ∀ η : E3, ‖η‖ < a → g η = 0) (hh : ∀ η, g (-η) = cj (g η)) :
    Teste fun η => leray η (g η) := by
  obtain ⟨a, ha, hga⟩ := h0
  obtain ⟨M, hM⟩ := hgs.exists_bound_of_continuous hg
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨?_, ?_, ⟨a, ha, fun η hη => by simp [hga η hη]⟩, fun η => ip_leray η _, fun η => ?_⟩
  · refine ATK.NSRegular.continuous_leray_of hg (Q := M / a) fun ξ => ?_
    by_cases h : ‖ξ‖ < a
    · rw [hga ξ h, norm_zero]
      positivity
    · have h' : a ≤ ‖ξ‖ := not_lt.mp h
      calc ‖g ξ‖ ≤ M := hM ξ
        _ = a * (M / a) := by field_simp
        _ ≤ ‖ξ‖ * (M / a) := by gcongr
  · exact hgs.mono fun η hη => by
      intro hg0
      apply hη
      simp [hg0]
  · rw [leray_neg, hh, leray_cj]

/-- Corte radial em anel: `0` para `|η| < 1/(n+1)` e para `|η| ≥ n+2`, `1` no meio. -/
noncomputable def corte (n : ℕ) (η : E3) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * ‖η‖ - 1)) * min 1 (max 0 ((n : ℝ) + 2 - ‖η‖))

theorem continuous_corte (n : ℕ) : Continuous (corte n) := by
  unfold corte
  exact (continuous_const.min (continuous_const.max
    ((continuous_const.mul continuous_norm).sub continuous_const))).mul
    (continuous_const.min (continuous_const.max (continuous_const.sub continuous_norm)))

theorem corte_nonneg (n : ℕ) (η : E3) : 0 ≤ corte n η := by
  unfold corte
  have h1 : 0 ≤ min 1 (max 0 (((n : ℝ) + 1) * ‖η‖ - 1)) :=
    le_min zero_le_one (le_max_left _ _)
  have h2 : 0 ≤ min 1 (max 0 ((n : ℝ) + 2 - ‖η‖)) := le_min zero_le_one (le_max_left _ _)
  positivity

theorem corte_le_one (n : ℕ) (η : E3) : corte n η ≤ 1 := by
  unfold corte
  have h1 : 0 ≤ min 1 (max 0 (((n : ℝ) + 1) * ‖η‖ - 1)) :=
    le_min zero_le_one (le_max_left _ _)
  have h1' : min 1 (max 0 (((n : ℝ) + 1) * ‖η‖ - 1)) ≤ 1 := min_le_left _ _
  have h2' : min 1 (max 0 ((n : ℝ) + 2 - ‖η‖)) ≤ 1 := min_le_left _ _
  have h2 : 0 ≤ min 1 (max 0 ((n : ℝ) + 2 - ‖η‖)) := le_min zero_le_one (le_max_left _ _)
  nlinarith

theorem corte_small (n : ℕ) {η : E3} (hη : ‖η‖ < ((n : ℝ) + 1)⁻¹) : corte n η = 0 := by
  unfold corte
  have h : ((n : ℝ) + 1) * ‖η‖ - 1 < 0 := by
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := mul_lt_mul_of_pos_left hη hp
    rw [mul_inv_cancel₀ hp.ne'] at this
    linarith
  rw [max_eq_left h.le, min_eq_right zero_le_one, zero_mul]

theorem corte_large (n : ℕ) {η : E3} (hη : (n : ℝ) + 2 ≤ ‖η‖) : corte n η = 0 := by
  unfold corte
  rw [max_eq_left (by linarith : (n : ℝ) + 2 - ‖η‖ ≤ 0), min_eq_right zero_le_one, mul_zero]

theorem corte_neg (n : ℕ) (η : E3) : corte n (-η) = corte n η := by
  simp only [corte, norm_neg]

theorem hasCompactSupport_corte (n : ℕ) : HasCompactSupport (corte n) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E3) ((n : ℝ) + 2)) fun η hη => by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hη
    exact corte_large n hη.le

theorem corte_eventually_one {η : E3} (hη : η ≠ 0) : ∀ᶠ n : ℕ in atTop, corte n η = 1 := by
  have hp : 0 < ‖η‖ := norm_pos_iff.mpr hη
  obtain ⟨N, hN⟩ := exists_nat_ge (max (2 / ‖η‖) ‖η‖)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : max (2 / ‖η‖) ‖η‖ ≤ n := hN.trans (by exact_mod_cast hn)
  have h1 : 2 / ‖η‖ ≤ n := (le_max_left _ _).trans hn'
  have h2 : ‖η‖ ≤ n := (le_max_right _ _).trans hn'
  have h3 : 2 ≤ (n : ℝ) * ‖η‖ := by
    rw [div_le_iff₀ hp] at h1
    exact h1
  unfold corte
  rw [max_eq_right (by nlinarith), min_eq_left (by nlinarith), max_eq_right (by linarith),
    min_eq_left (by linarith), one_mul]

theorem ae_ne_zero : ∀ᵐ η ∂(volume : Measure E3), η ≠ 0 := by
  rw [ae_iff]
  simp

/-- Da cota nos testes para toda `g` com pesos e hermitiana: corte em anel, projeção de Leray e
limite (`‖g − corte_n g‖₂ → 0`). -/
theorem pr_bound_pesos {W : E3 → E3} (hW : ContDiff ℝ ∞ W) (hdiv : ∀ x, div W x = 0)
    (hW2 : Integrable fun x => ‖W x‖ ^ 2) (hdW2 : ∀ j, Integrable fun x => ‖dX j W x‖ ^ 2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ h, Teste h → |pr W h| ≤ A * sqrt (∫ η, ‖h η‖ ^ 2))
    {g : E3 → C3} (hg : Pesos g) (hh : ∀ η, g (-η) = cj (g η)) :
    |pr W g| ≤ A * sqrt (∫ η, ‖g η‖ ^ 2) := by
  set gn : ℕ → E3 → C3 := fun n η => corte n η • g η with hgn
  have hgc : ∀ n, Continuous (gn n) := fun n => (continuous_corte n).smul hg.1
  have hgs : ∀ n, HasCompactSupport (gn n) := fun n => (hasCompactSupport_corte n).smul_right
  have hg0 : ∀ n, ∃ a > 0, ∀ η : E3, ‖η‖ < a → gn n η = 0 := fun n =>
    ⟨((n : ℝ) + 1)⁻¹, by positivity, fun η hη => by simp [hgn, corte_small n hη]⟩
  have hgh : ∀ n η, gn n (-η) = cj (gn n η) := by
    intro n η
    simp only [hgn]
    rw [corte_neg, hh, cj_real_smul]
  have hgP : ∀ n, Pesos (gn n) := fun n => pesos_of_compact (hgc n) (hgs n)
  have hg2 := integrable_sq_pesos hg
  have hdiff : ∀ n η, ‖g η - gn n η‖ ≤ ‖g η‖ := by
    intro n η
    simp only [hgn]
    have e : g η - corte n η • g η = (1 - corte n η) • g η := by
      rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_of_nonneg (by linarith [corte_le_one n η])]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [corte_nonneg n η])
  have hdP : ∀ n, Pesos fun η => g η - gn n η := fun n =>
    ⟨hg.1.sub (hgc n), fun m => by
      obtain ⟨C, hC⟩ := hg.2 m
      exact ⟨C, fun ζ => (mul_le_mul_of_nonneg_right (hdiff n ζ) (by positivity)).trans (hC ζ)⟩⟩
  -- a cota para cada `n`
  have hAn : ∀ n, |pr W (gn n)| ≤ A * sqrt (∫ η, ‖g η‖ ^ 2) := by
    intro n
    have hT := teste_leray (hgc n) (hgs n) (hg0 n) (hgh n)
    rw [← pr_leray hW hdiv hW2 hdW2 (hgc n) (hgs n) (hg0 n)]
    refine (hA _ hT).trans ?_
    refine mul_le_mul_of_nonneg_left (sqrt_le_sqrt ?_) hA0
    refine integral_mono (integrable_sq_pesos hT.pesos) hg2 fun η => ?_
    have h1 : ‖leray η (gn n η)‖ ≤ ‖g η‖ := by
      refine (norm_leray_le η _).trans ?_
      simp only [hgn]
      rw [norm_smul, Real.norm_of_nonneg (corte_nonneg n η)]
      exact mul_le_of_le_one_left (norm_nonneg _) (corte_le_one n η)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  -- `∫ ‖g − gₙ‖² → 0`
  have hlim : Tendsto (fun n => ∫ η, ‖g η - gn n η‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun η => ‖g η‖ ^ 2)
      (F := fun n η => ‖g η - gn n η‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun n => ((hg.1.sub (hgc n)).norm.pow 2).aestronglyMeasurable) hg2
      (fun n => Eventually.of_forall fun η => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdiff n η) 2) (by
        filter_upwards [ae_ne_zero] with η hη
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [corte_eventually_one hη] with n hn
        simp [hgn, hn])
    simpa using this
  have hlim' : Tendsto (fun n => A * sqrt (∫ η, ‖g η‖ ^ 2) +
      sqrt (∫ x, ‖W x‖ ^ 2) * sqrt (∫ η, ‖g η - gn n η‖ ^ 2)) atTop
      (𝓝 (A * sqrt (∫ η, ‖g η‖ ^ 2))) := by
    have h1 : Tendsto (fun n => sqrt (∫ η, ‖g η - gn n η‖ ^ 2)) atTop (𝓝 0) := by
      have := (continuous_sqrt.tendsto 0).comp hlim
      rwa [sqrt_zero] at this
    simpa using tendsto_const_nhds.add (h1.const_mul (sqrt (∫ x, ‖W x‖ ^ 2)))
  refine ge_of_tendsto' hlim' fun n => ?_
  have hd := pr_sub hW.continuous.aestronglyMeasurable hW2 hg (hgP n)
  have h1 := abs_pr_le hW.continuous hW2 (hdP n)
  have h2 := hAn n
  have e : pr W g = pr W (gn n) + pr W (fun η => g η - gn n η) := by rw [hd]; ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add h2 h1)

/-- **Normação**: se `|∫ W · Re F0 h| ≤ A ‖h‖₂` para todo teste `h`, então `‖W‖₂ ≤ A`
(`W` suave, de divergência nula, `W, ∇W ∈ L²`). Prova: `h = 𝓕(κ_R W)` e `R → ∞`. -/
theorem norming {W : E3 → E3} (hW : ContDiff ℝ ∞ W) (hdiv : ∀ x, div W x = 0)
    (hW2 : Integrable fun x => ‖W x‖ ^ 2) (hdW2 : ∀ j, Integrable fun x => ‖dX j W x‖ ^ 2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ h, Teste h → |pr W h| ≤ A * sqrt (∫ η, ‖h η‖ ^ 2)) :
    sqrt (∫ x, ‖W x‖ ^ 2) ≤ A := by
  have key : ∀ n : ℕ, ∫ x, kR (n + 1) x * ‖W x‖ ^ 2 ≤ A * sqrt (∫ x, ‖W x‖ ^ 2) := by
    intro n
    have hR : ((n : ℝ) + 1) ≠ 0 := by positivity
    set u : E3 → E3 := fun x => kR (n + 1) x • W x with hu
    have huc : ContDiff ℝ ∞ u := (contDiff_kR _).smul hW
    have hus : HasCompactSupport u := (hasCompactSupport_kR hR).smul_right
    set U : 𝓢(E3, E3) := hus.toSchwartzMap huc
    have hUx : ∀ x, U x = u x := fun x => rfl
    have hg : Pesos ⇑(v0S U) := ⟨(v0S U).continuous, fun m => cota_v0 U m⟩
    have hF0 : ∀ x, F0 (⇑(v0S U)) x = cx (u x) := by
      intro x
      rw [F0_eq_Fi _ x 0, Fi_eq_fourierInv, ← hUx]
      exact fourierInv_v0 U x
    have hR0 : ∀ x, R0 (⇑(v0S U)) x = u x := fun x => by
      rw [R0, hF0, reV_cx]
    have hpr : pr W (⇑(v0S U)) = ∫ x, kR (n + 1) x * ‖W x‖ ^ 2 := by
      unfold pr
      congr 1
      funext x
      rw [hR0, hu, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hgL : ∫ η, ‖v0S U η‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
      rw [← (plancherel_F0 hg).2]
      congr 1
      funext x
      rw [hF0, norm_cx]
    have hul : ∫ x, ‖u x‖ ^ 2 ≤ ∫ x, ‖W x‖ ^ 2 := by
      have hle : ∀ x, ‖u x‖ ^ 2 ≤ ‖W x‖ ^ 2 := by
        intro x
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [hu, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (kR_bound _ x)
      exact integral_mono (hW2.mono' (huc.continuous.norm.pow 2).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle x)) hW2 hle
    calc ∫ x, kR (n + 1) x * ‖W x‖ ^ 2 = pr W (⇑(v0S U)) := hpr.symm
      _ ≤ |pr W (⇑(v0S U))| := le_abs_self _
      _ ≤ A * sqrt (∫ η, ‖v0S U η‖ ^ 2) :=
          pr_bound_pesos hW hdiv hW2 hdW2 hA0 hA hg (herm_v0 U)
      _ ≤ A * sqrt (∫ x, ‖W x‖ ^ 2) := by
          rw [hgL]
          exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt hul) hA0
  have hlim : Tendsto (fun n : ℕ => ∫ x, kR (n + 1) x * ‖W x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖W x‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖W x‖ ^ 2)
      (fun n => ((contDiff_kR _).continuous.mul (hW.continuous.norm.pow 2)).aestronglyMeasurable)
      hW2 (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
      exact mul_le_of_le_one_left (sq_nonneg _) (kR_bound _ x)
    · simpa using (tendsto_kR x).mul_const (‖W x‖ ^ 2)
  have hI : ∫ x, ‖W x‖ ^ 2 ≤ A * sqrt (∫ x, ‖W x‖ ^ 2) := le_of_tendsto' hlim key
  have hI0 : 0 ≤ ∫ x, ‖W x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  by_contra hlt
  have hlt' : A < sqrt (∫ x, ‖W x‖ ^ 2) := not_le.mp hlt
  have hs : 0 < sqrt (∫ x, ‖W x‖ ^ 2) := lt_of_le_of_lt hA0 hlt'
  have h1 : sqrt (∫ x, ‖W x‖ ^ 2) * sqrt (∫ x, ‖W x‖ ^ 2) = ∫ x, ‖W x‖ ^ 2 :=
    mul_self_sqrt hI0
  nlinarith

/-! ### O núcleo singular -/

theorem exp_neg_le_rpow {x : ℝ} (hx : 0 < x) : exp (-x) ≤ x ^ (-(1 / 8 : ℝ)) := by
  have h1 : x ^ (1 / 8 : ℝ) ≤ exp x := by
    rcases le_total x 1 with h | h
    · exact (rpow_le_one hx.le h (by norm_num)).trans (one_le_exp hx.le)
    · calc x ^ (1 / 8 : ℝ) ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le h (by norm_num)
        _ = x := rpow_one x
        _ ≤ x + 1 := by linarith
        _ ≤ exp x := add_one_le_exp x
  rw [rpow_neg hx.le, exp_neg]
  exact inv_anti₀ (rpow_pos_of_pos hx _) h1

theorem kernel_bound {l s : ℝ} (hl : 0 < l) (hs : 0 < s) (a : ℝ) :
    s ^ (-a) * exp (-(l * s)) ≤ l ^ (-(1 / 8 : ℝ)) * s ^ (-(a + 1 / 8)) := by
  have h1 := exp_neg_le_rpow (mul_pos hl hs)
  rw [mul_rpow hl.le hs.le] at h1
  calc s ^ (-a) * exp (-(l * s)) ≤ s ^ (-a) * (l ^ (-(1 / 8 : ℝ)) * s ^ (-(1 / 8 : ℝ))) := by
        gcongr
    _ = l ^ (-(1 / 8 : ℝ)) * (s ^ (-a) * s ^ (-(1 / 8 : ℝ))) := by ring
    _ = l ^ (-(1 / 8 : ℝ)) * s ^ (-(a + 1 / 8)) := by
        rw [← rpow_add hs]
        congr 2
        ring

theorem intervalIntegrable_kernel {t a : ℝ} (ha : a < 1) :
    IntervalIntegrable (fun σ => (t - σ) ^ (-a)) volume 0 t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t) (b := 0)
    (r := -a) (by linarith)).comp_sub_left t
  rwa [sub_self, sub_zero] at h

theorem integral_kernel {t a : ℝ} (ha : a < 1) :
    ∫ σ in (0 : ℝ)..t, (t - σ) ^ (-a) = t ^ (1 - a) / (1 - a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (-a)) t, sub_self, sub_zero,
    integral_rpow (Or.inl (by linarith)), zero_rpow (by linarith), sub_zero]
  congr 1 <;> ring_nf

theorem coef_eq {K B c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    K * (π / (2 * c * s)) ^ (3 / 4 : ℝ) + 3 * B * (2 * π / sqrt (c * s)) =
      K * (π / (2 * c)) ^ (3 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) +
        3 * B * (2 * π / sqrt c) * s ^ (-(1 / 2 : ℝ)) := by
  have e1 : π / (2 * c * s) = π / (2 * c) * s⁻¹ := by field_simp
  have e2 : (π / (2 * c * s)) ^ (3 / 4 : ℝ) = (π / (2 * c)) ^ (3 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) := by
    rw [e1, mul_rpow (by positivity) (by positivity), inv_rpow hs.le, rpow_neg hs.le]
  have e3 : 2 * π / sqrt (c * s) = 2 * π / sqrt c * s ^ (-(1 / 2 : ℝ)) := by
    rw [sqrt_mul hc.le, rpow_neg hs.le, ← sqrt_eq_rpow]
    have : sqrt s ≠ 0 := (sqrt_pos.mpr hs).ne'
    have : sqrt c ≠ 0 := (sqrt_pos.mpr hc).ne'
    field_simp
  rw [e2, e3]
  ring

theorem div_sub_fields {u₁ u₂ : E3 → E3} (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (j : Fin 3) (x : E3) : dX j (fun y => u₁ y - u₂ y) x = dX j u₁ x - dX j u₂ x := by
  show fderiv ℝ (fun x => u₁ x - u₂ x) x (e j) = fderiv ℝ u₁ x (e j) - fderiv ℝ u₂ x (e j)
  rw [fderiv_fun_sub (hu₁.differentiable (by simp) x) (hu₂.differentiable (by simp) x)]
  rfl

section Gron

variable {ν T₁ T₂ τ : ℝ} {u₀ : E3 → E3} {U₁ U₂ : E3 × ℝ → E3} {P₁ P₂ : E3 × ℝ → ℝ}

/-- A diferença congelada é suave, de divergência nula, e `W, ∇W ∈ L²`. -/
theorem Wc_campo (hS₁ : SolucaoLocal ν u₀ T₁ U₁ P₁) (hS₂ : SolucaoLocal ν u₀ T₂ U₂ P₂)
    (hτ0 : 0 ≤ τ) (hτ₁ : τ < T₁) (hτ₂ : τ < T₂) (t : ℝ) :
    ContDiff ℝ ∞ (Wc τ U₁ U₂ t) ∧ (∀ x, div (Wc τ U₁ U₂ t) x = 0) ∧
      (Integrable fun x => ‖Wc τ U₁ U₂ t x‖ ^ 2) ∧
      ∀ j, Integrable fun x => ‖dX j (Wc τ U₁ U₂ t) x‖ ^ 2 := by
  have hσ' : clamp τ t ∈ Icc 0 τ := clamp_mem hτ0 t
  have hσ₁ : clamp τ t ∈ Ico 0 T₁ := ⟨hσ'.1, hσ'.2.trans_lt hτ₁⟩
  have hσ₂ : clamp τ t ∈ Ico 0 T₂ := ⟨hσ'.1, hσ'.2.trans_lt hτ₂⟩
  have hu₁ := slice_contDiff hS₁.1 hσ₁
  have hu₂ := slice_contDiff hS₂.1 hσ₂
  have hW : Wc τ U₁ U₂ t = fun y => fatia U₁ (clamp τ t) y - fatia U₂ (clamp τ t) y := rfl
  obtain ⟨C₁, hC₁⟩ := sol_bounds hS₁ hτ₁
  obtain ⟨C₂, hC₂⟩ := sol_bounds hS₂ hτ₂
  obtain ⟨CW, -, hCW⟩ := Wc_props hS₁ hS₂ hτ0 hτ₁ hτ₂
  refine ⟨by rw [hW]; exact hu₁.sub hu₂, fun x => ?_, (hCW t).2.1, fun j => ?_⟩
  · rw [hW]
    unfold div
    simp_rw [div_sub_fields hu₁ hu₂, PiLp.sub_apply]
    rw [Finset.sum_sub_distrib]
    have h1 := hS₁.2.2.2.2.1 x _ hσ₁
    have h2 := hS₂.2.2.2.2.1 x _ hσ₂
    unfold div at h1 h2
    rw [h1, h2, sub_zero]
  · have hd1 := ((hC₁ _ hσ').2 j).1
    have hd2 := ((hC₂ _ hσ').2 j).1
    have hcd : Continuous (dX j (Wc τ U₁ U₂ t)) := by
      rw [hW]; exact continuous_dX_gen ((hu₁.sub hu₂).of_le (by simp)) j
    refine ((hd1.const_mul 2).add (hd2.const_mul 2)).mono'
      (hcd.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hW, div_sub_fields hu₁ hu₂]
    have h1 := norm_sub_le (dX j (fatia U₁ (clamp τ t)) x) (dX j (fatia U₂ (clamp τ t)) x)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    show _ ≤ 2 * ‖dX j (fatia U₁ (clamp τ t)) x‖ ^ 2 + 2 * ‖dX j (fatia U₂ (clamp τ t)) x‖ ^ 2
    nlinarith [sq_nonneg (‖dX j (fatia U₁ (clamp τ t)) x‖ - ‖dX j (fatia U₂ (clamp τ t)) x‖)]

end Gron

section Teorema

variable {ν T₁ T₂ τ : ℝ} {u₀ : E3 → E3} {U₁ U₂ : E3 × ℝ → E3} {P₁ P₂ : E3 × ℝ → ℝ}

/-- **Unicidade (fraca-forte) na classe `SolucaoLocal`, com pressões arbitrárias**: duas soluções
com o mesmo dado coincidem em `[0, τ]` se a segunda é limitada em `ℝ³ × [0, τ]`.

Prova: fórmula de Duhamel testada (`duhamel_testado`), estimativa do termo não linear
(`nP_estimate`, núcleo `s^{−3/4}` e `s^{−1/2}`), normação (`norming`) e Gronwall com peso
exponencial `e^{−λt}` (`λ` grande). -/
theorem unicidade (hS₁ : SolucaoLocal ν u₀ T₁ U₁ P₁) (hS₂ : SolucaoLocal ν u₀ T₂ U₂ P₂)
    (hν : 0 < ν) (hτ0 : 0 ≤ τ) (hτ₁ : τ < T₁) (hτ₂ : τ < T₂) {B : ℝ}
    (hB : ∀ x, ∀ s ∈ Icc 0 τ, ‖U₂ (x, s)‖ ≤ B) :
    ∀ x, ∀ t ∈ Icc 0 τ, U₁ (x, t) = U₂ (x, t) := by
  obtain ⟨K, hK0, hK⟩ := nP_estimate hS₁ hS₂ hτ0 hτ₁ hτ₂ hB
  obtain ⟨CW, hCW0, hCW⟩ := Wc_props hS₁ hS₂ hτ0 hτ₁ hτ₂
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0 ⟨le_rfl, hτ0⟩)
  have hc : 0 < 4 * π ^ 2 * ν := by positivity
  set c := 4 * π ^ 2 * ν with hc_def
  set m : ℝ → ℝ := fun σ => sqrt (∫ x, ‖Wc τ U₁ U₂ σ x‖ ^ 2) with hm
  set K₁ := K * (π / (2 * c)) ^ (3 / 4 : ℝ) with hK₁
  set K₂ := 3 * B * (2 * π / sqrt c) with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  set L := K₁ * (8 * τ ^ (1 / 8 : ℝ)) + K₂ * (8 / 3 * τ ^ (3 / 8 : ℝ)) with hL
  have hL0 : 0 ≤ L := by positivity
  set lam : ℝ := (2 * L + 1) ^ (8 : ℕ) with hlam_def
  have hlam : 0 < lam := by positivity
  have hlam8 : lam ^ (-(1 / 8 : ℝ)) = (2 * L + 1)⁻¹ := by
    rw [rpow_neg hlam.le, hlam_def, ← rpow_natCast, ← rpow_mul (by positivity)]
    norm_num
  have hLlam : L * lam ^ (-(1 / 8 : ℝ)) ≤ 1 / 2 := by
    rw [hlam8, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  -- o supremo com peso
  set f : ℝ → ℝ := fun σ => exp (-(lam * σ)) * m σ with hf
  have hfb : ∀ σ ∈ Icc 0 τ, f σ ≤ sqrt CW := by
    intro σ hσ
    have h1 : exp (-(lam * σ)) ≤ 1 := by
      rw [exp_le_one_iff]
      have : 0 ≤ lam * σ := mul_nonneg hlam.le hσ.1
      linarith
    calc f σ ≤ 1 * m σ := mul_le_mul_of_nonneg_right h1 (sqrt_nonneg _)
      _ = m σ := one_mul _
      _ ≤ sqrt CW := sqrt_le_sqrt (hCW σ).2.2
  have hbdd : BddAbove (f '' Icc 0 τ) := ⟨sqrt CW, by
    rintro _ ⟨σ, hσ, rfl⟩
    exact hfb σ hσ⟩
  set M := sSup (f '' Icc 0 τ) with hM_def
  have hfM : ∀ σ ∈ Icc 0 τ, f σ ≤ M := fun σ hσ => le_csSup hbdd ⟨σ, hσ, rfl⟩
  have hM0 : 0 ≤ M := (by positivity : 0 ≤ f 0).trans (hfM 0 ⟨le_rfl, hτ0⟩)
  have hmM : ∀ σ ∈ Icc 0 τ, m σ ≤ exp (lam * σ) * M := by
    intro σ hσ
    have he : exp (lam * σ) * exp (-(lam * σ)) = 1 := by rw [← exp_add]; simp
    calc m σ = exp (lam * σ) * (exp (-(lam * σ)) * m σ) := by rw [← mul_assoc, he, one_mul]
      _ ≤ exp (lam * σ) * M := by gcongr; exact hfM σ hσ
  -- a estimativa principal em cada tempo
  have hmain : ∀ t ∈ Icc 0 τ, m t ≤ exp (lam * t) * (M / 2) := by
    intro t ht
    obtain ⟨hWs, hWd, hW2, hdW2⟩ := Wc_campo hS₁ hS₂ hτ0 hτ₁ hτ₂ t
    have hA0 : 0 ≤ exp (lam * t) * M * lam ^ (-(1 / 8 : ℝ)) * L := by positivity
    have hnorm := norming hWs hWd hW2 hdW2 hA0 (fun h hh => by
      have hP := hh.pesos
      have hH2 := integrable_sq_pesos hP
      have hdu := duhamel_testado hS₁ hS₂ hτ0 hτ₁ hτ₂ hν.le hh ht
      show |wP τ U₁ U₂ h t| ≤ _
      rw [hdu]
      set H := sqrt (∫ η, ‖h η‖ ^ 2) with hH
      have hH0 : 0 ≤ H := sqrt_nonneg _
      set G : ℝ → ℝ := fun σ => H * M * exp (lam * t) * lam ^ (-(1 / 8 : ℝ)) *
        (K₁ * (t - σ) ^ (-(7 / 8 : ℝ)) + K₂ * (t - σ) ^ (-(5 / 8 : ℝ))) with hG
      have hGi : IntervalIntegrable G volume 0 t :=
        (((intervalIntegrable_kernel (t := t) (a := 7 / 8) (by norm_num)).const_mul K₁).add
          ((intervalIntegrable_kernel (t := t) (a := 5 / 8) (by norm_num)).const_mul K₂)).const_mul
          (H * M * exp (lam * t) * lam ^ (-(1 / 8 : ℝ)))
      have hGint : ∫ σ in (0 : ℝ)..t, G σ ≤ exp (lam * t) * M * lam ^ (-(1 / 8 : ℝ)) * L * H := by
        have i1 := (intervalIntegrable_kernel (t := t) (a := 7 / 8) (by norm_num)).const_mul K₁
        have i2 := (intervalIntegrable_kernel (t := t) (a := 5 / 8) (by norm_num)).const_mul K₂
        rw [hG, intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          integral_kernel (by norm_num), integral_kernel (by norm_num)]
        have t1 : t ^ (1 - 7 / 8 : ℝ) / (1 - 7 / 8) ≤ 8 * τ ^ (1 / 8 : ℝ) := by
          rw [show (1 - 7 / 8 : ℝ) = 1 / 8 by norm_num, div_eq_mul_inv, mul_comm]
          norm_num
          exact rpow_le_rpow ht.1 ht.2 (by norm_num)
        have t2 : t ^ (1 - 5 / 8 : ℝ) / (1 - 5 / 8) ≤ 8 / 3 * τ ^ (3 / 8 : ℝ) := by
          rw [show (1 - 5 / 8 : ℝ) = 3 / 8 by norm_num, div_eq_mul_inv, mul_comm]
          norm_num
          exact rpow_le_rpow ht.1 ht.2 (by norm_num)
        have hpos : 0 ≤ H * M * exp (lam * t) * lam ^ (-(1 / 8 : ℝ)) := by positivity
        calc H * M * exp (lam * t) * lam ^ (-(1 / 8 : ℝ)) *
              (K₁ * (t ^ (1 - 7 / 8 : ℝ) / (1 - 7 / 8)) + K₂ * (t ^ (1 - 5 / 8 : ℝ) / (1 - 5 / 8)))
            ≤ H * M * exp (lam * t) * lam ^ (-(1 / 8 : ℝ)) *
              (K₁ * (8 * τ ^ (1 / 8 : ℝ)) + K₂ * (8 / 3 * τ ^ (3 / 8 : ℝ))) := by
              gcongr
          _ = exp (lam * t) * M * lam ^ (-(1 / 8 : ℝ)) * L * H := by rw [hL]; ring
      have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ t := by
        rw [ae_iff]
        simp
      have hbound : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioc 0 t →
          ‖nP τ U₁ U₂ (Hk c h 0 (t - σ)) σ‖ ≤ G σ := by
        filter_upwards [hne] with σ hσt hσ
        have hs : 0 < t - σ := sub_pos.mpr (lt_of_le_of_ne hσ.2 hσt)
        have hστ : σ ∈ Icc 0 τ := ⟨hσ.1.le, hσ.2.trans ht.2⟩
        have e1 := hK hc hs hP hH2 σ
        rw [coef_eq hc hs] at e1
        have k1 := kernel_bound hlam hs (3 / 4)
        have k2 := kernel_bound hlam hs (1 / 2)
        rw [show -(3 / 4 + 1 / 8 : ℝ) = -(7 / 8) by norm_num] at k1
        rw [show -(1 / 2 + 1 / 8 : ℝ) = -(5 / 8) by norm_num] at k2
        have hexp : exp (lam * σ) = exp (lam * t) * exp (-(lam * (t - σ))) := by
          rw [← exp_add]
          congr 1
          ring
        have hcoef : 0 ≤ K₁ * (t - σ) ^ (-(3 / 4 : ℝ)) + K₂ * (t - σ) ^ (-(1 / 2 : ℝ)) := by
          positivity
        rw [Real.norm_eq_abs]
        calc |nP τ U₁ U₂ (Hk c h 0 (t - σ)) σ|
            ≤ (K₁ * (t - σ) ^ (-(3 / 4 : ℝ)) + K₂ * (t - σ) ^ (-(1 / 2 : ℝ))) * m σ * H := e1
          _ ≤ (K₁ * (t - σ) ^ (-(3 / 4 : ℝ)) + K₂ * (t - σ) ^ (-(1 / 2 : ℝ))) *
                (exp (lam * σ) * M) * H := by
              gcongr
              exact hmM σ hστ
          _ = H * M * exp (lam * t) * (K₁ * ((t - σ) ^ (-(3 / 4 : ℝ)) * exp (-(lam * (t - σ)))) +
                K₂ * ((t - σ) ^ (-(1 / 2 : ℝ)) * exp (-(lam * (t - σ))))) := by
              rw [hexp]
              ring
          _ ≤ H * M * exp (lam * t) * (K₁ * (lam ^ (-(1 / 8 : ℝ)) * (t - σ) ^ (-(7 / 8 : ℝ))) +
                K₂ * (lam ^ (-(1 / 8 : ℝ)) * (t - σ) ^ (-(5 / 8 : ℝ)))) := by
              gcongr
          _ = G σ := by rw [hG]; ring
      calc |∫ σ in (0 : ℝ)..t, nP τ U₁ U₂ (Hk c h 0 (t - σ)) σ|
          = ‖∫ σ in (0 : ℝ)..t, nP τ U₁ U₂ (Hk c h 0 (t - σ)) σ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ σ in (0 : ℝ)..t, G σ := intervalIntegral.norm_integral_le_of_norm_le ht.1 hbound hGi
        _ ≤ _ := hGint)
    calc m t ≤ exp (lam * t) * M * lam ^ (-(1 / 8 : ℝ)) * L := hnorm
      _ = exp (lam * t) * M * (L * lam ^ (-(1 / 8 : ℝ))) := by ring
      _ ≤ exp (lam * t) * M * (1 / 2) := by gcongr
      _ = exp (lam * t) * (M / 2) := by ring
  have hMle : M ≤ M / 2 := by
    refine csSup_le ⟨f 0, 0, ⟨le_rfl, hτ0⟩, rfl⟩ ?_
    rintro _ ⟨σ, hσ, rfl⟩
    calc f σ = exp (-(lam * σ)) * m σ := rfl
      _ ≤ exp (-(lam * σ)) * (exp (lam * σ) * (M / 2)) := by gcongr; exact hmain σ hσ
      _ = M / 2 := by rw [← mul_assoc, ← exp_add]; simp
  have hM : M = 0 := by linarith
  intro x t ht
  have hmt : m t = 0 := by
    have h1 := hmain t ht
    rw [hM, zero_div, mul_zero] at h1
    exact le_antisymm h1 (sqrt_nonneg _)
  have h0 : 0 ≤ ∫ y, ‖Wc τ U₁ U₂ t y‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hint : ∫ y, ‖Wc τ U₁ U₂ t y‖ ^ 2 = 0 := (sqrt_eq_zero h0).mp hmt
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) (hCW t).2.1).mp hint
  have hc0 : (fun y => ‖Wc τ U₁ U₂ t y‖ ^ 2) = fun _ => (0 : ℝ) :=
    ((Continuous.ae_eq_iff_eq volume ((hCW t).1.norm.pow 2) continuous_const).mp hae)
  have hx := congrFun hc0 x
  simp only [Wc, clamp_of_mem ht] at hx
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Teorema

end ATK.NSUnico

#print axioms ATK.NSUnico.cs
#print axioms ATK.NSUnico.gauss
#print axioms ATK.NSUnico.norm_mj_le_norm
#print axioms ATK.NSUnico.norm_Hk0
#print axioms ATK.NSUnico.sup_R0_Hk
#print axioms ATK.NSUnico.L2_dX_R0_Hk
#print axioms ATK.NSUnico.int_mul_L2
#print axioms ATK.NSUnico.ibp_whole
#print axioms ATK.NSUnico.cs_norm
#print axioms ATK.NSUnico.pesos_Hk0
#print axioms ATK.NSUnico.nP_static
#print axioms ATK.NSUnico.nP_estimate
#print axioms ATK.NSUnico.ibp_scalar
#print axioms ATK.NSUnico.R0_sub
#print axioms ATK.NSUnico.pr_sub
#print axioms ATK.NSUnico.integrable_sq_pesos
#print axioms ATK.NSUnico.abs_pr_le
#print axioms ATK.NSUnico.continuous_ip_of
#print axioms ATK.NSUnico.e0c
#print axioms ATK.NSUnico.pr_leray
#print axioms ATK.NSUnico.teste_leray
#print axioms ATK.NSUnico.corte
#print axioms ATK.NSUnico.continuous_corte
#print axioms ATK.NSUnico.corte_nonneg
#print axioms ATK.NSUnico.corte_le_one
#print axioms ATK.NSUnico.corte_small
#print axioms ATK.NSUnico.corte_large
#print axioms ATK.NSUnico.corte_neg
#print axioms ATK.NSUnico.hasCompactSupport_corte
#print axioms ATK.NSUnico.corte_eventually_one
#print axioms ATK.NSUnico.ae_ne_zero
#print axioms ATK.NSUnico.pr_bound_pesos
#print axioms ATK.NSUnico.norming
#print axioms ATK.NSUnico.exp_neg_le_rpow
#print axioms ATK.NSUnico.kernel_bound
#print axioms ATK.NSUnico.intervalIntegrable_kernel
#print axioms ATK.NSUnico.integral_kernel
#print axioms ATK.NSUnico.coef_eq
#print axioms ATK.NSUnico.div_sub_fields
#print axioms ATK.NSUnico.Wc_campo
#print axioms ATK.NSUnico.unicidade
