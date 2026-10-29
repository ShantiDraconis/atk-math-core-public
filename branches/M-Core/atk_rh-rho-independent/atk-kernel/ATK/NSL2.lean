import ATK.NSPlancherel
import ATK.NSEstimativas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Fourier.Convolution

/-!
# ATK — Navier–Stokes: a transformada de Fourier em `L²(ℝ³, ℂ³)`

Camada 18 do ataque a B3 (unicidade fraca–forte, passo U-3). A Mathlib tem a transformada de
Fourier em `L²` como isometria (`Lp.fourierTransformₗᵢ`). Para comparar uma solução suave
qualquer com a solução da classe de Fourier é preciso ler, no lado de Fourier, campos que só são
`L²` (sem decaimento rápido). Aqui:

* `FL f`: um representante de `𝓕 f` para `f ∈ L²`; Plancherel `∫ ‖FL f‖² = ∫ ‖f‖²`;
* `integral_inner_FL`: `∫ ⟪FL f, H⟫ = ∫ ⟪f, 𝓕⁻ H⟫` para `H` de Schwartz;
* `ae_eq_of_integral_inner_eq`: dois campos localmente integráveis com os mesmos pareamentos
  contra os campos-teste `C^∞` de suporte compacto coincidem q.t.p.;
* **`FL_dX`**: `𝓕(∂ⱼ f) = 2πi ξⱼ 𝓕 f` q.t.p. para `f` diferenciável com `f, ∂ⱼ f ∈ L²`
  (integração por partes em `ℝ³` com hipóteses de integrabilidade, sem suporte compacto).

**CLOSED_MATH continua false.**
-/

open MeasureTheory FourierTransform SchwartzMap Filter Set ComplexConjugate
open scoped ContDiff InnerProductSpace Real Convolution

namespace ATK.NSL2

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSPlancherel

/-! ### A transformada em `L²` -/

open Classical in
/-- Representante da transformada de Fourier `L²` de `f : ℝ³ → ℂ³` (`0` se `f ∉ L²`). -/
noncomputable def FL (f : E3 → C3) : E3 → C3 :=
  if h : MemLp f 2 then ⇑(𝓕 (h.toLp f) : Lp C3 2 (volume : Measure E3)) else 0

theorem FL_eq {f : E3 → C3} (h : MemLp f 2) :
    FL f = ⇑(𝓕 (h.toLp f) : Lp C3 2 (volume : Measure E3)) := by
  rw [FL, dif_pos h]

theorem memLp_FL (f : E3 → C3) : MemLp (FL f) 2 := by
  by_cases h : MemLp f 2
  · rw [FL_eq h]; exact Lp.memLp _
  · rw [FL, dif_neg h]; exact MemLp.zero

theorem locallyIntegrable_FL (f : E3 → C3) : LocallyIntegrable (FL f) volume :=
  (memLp_FL f).locallyIntegrable (by norm_num)

/-- **Plancherel**: `∫ ‖FL f‖² = ∫ ‖f‖²`. -/
theorem integral_norm_sq_FL {f : E3 → C3} (h : MemLp f 2) :
    ∫ ξ, ‖FL f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [FL_eq h, ← norm_sq_eq_integral, Lp.norm_fourier_eq, norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx]

/-- Pareamento com campos de Schwartz: `∫ ⟪FL f, H⟫ = ∫ ⟪f, 𝓕⁻ H⟫`. -/
theorem integral_inner_FL {f : E3 → C3} (hf : MemLp f 2) (H : 𝓢(E3, C3)) :
    ∫ ξ, ⟪FL f ξ, H ξ⟫_ℂ = ∫ x, ⟪f x, (𝓕⁻ H : 𝓢(E3, C3)) x⟫_ℂ := by
  set u : Lp C3 2 (volume : Measure E3) := hf.toLp f
  set v : Lp C3 2 (volume : Measure E3) := (𝓕⁻ H : 𝓢(E3, C3)).toLp 2
  have hv : (𝓕 v : Lp C3 2 (volume : Measure E3)) = H.toLp 2 := by
    rw [SchwartzMap.toLp_fourier_eq, FourierTransform.fourier_fourierInv_eq]
  have h1 := Lp.inner_fourier_eq u v
  rw [hv, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h1
  have e1 : ∫ ξ, ⟪(𝓕 u : Lp C3 2 (volume : Measure E3)) ξ, H ξ⟫_ℂ =
      ∫ ξ, ⟪(𝓕 u : Lp C3 2 (volume : Measure E3)) ξ,
        (H.toLp 2 : Lp C3 2 (volume : Measure E3)) ξ⟫_ℂ := by
    apply integral_congr_ae
    filter_upwards [H.coeFn_toLp 2] with ξ hξ
    rw [hξ]
  have e2 : ∫ x, ⟪(u : E3 → C3) x, (v : E3 → C3) x⟫_ℂ =
      ∫ x, ⟪f x, (𝓕⁻ H : 𝓢(E3, C3)) x⟫_ℂ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, (𝓕⁻ H : 𝓢(E3, C3)).coeFn_toLp 2] with x h1 h2
    rw [h1, h2]
  rw [FL_eq hf, e1, h1, e2]

/-! ### O lema fundamental para pareamentos -/

/-- O campo-teste `φ e_k`. -/
noncomputable def tk (φ : E3 → ℝ) (k : Fin 3) (ξ : E3) : C3 :=
  ((φ ξ : ℝ) : ℂ) • EuclideanSpace.single k (1 : ℂ)

theorem inner_tk (v : C3) (φ : E3 → ℝ) (k : Fin 3) (ξ : E3) :
    ⟪v, tk φ k ξ⟫_ℂ = (φ ξ : ℂ) * conj (v k) := by
  rw [tk, inner_smul_right, EuclideanSpace.inner_single_right, one_mul]

theorem contDiff_tk {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : Fin 3) : ContDiff ℝ ∞ (tk φ k) :=
  (Complex.ofRealCLM.contDiff.comp hφ).smul contDiff_const

theorem hasCompactSupport_tk {φ : E3 → ℝ} (hφ : HasCompactSupport φ) (k : Fin 3) :
    HasCompactSupport (tk φ k) :=
  (hφ.comp_left Complex.ofReal_zero).smul_right

theorem integrable_inner_of_hasCompactSupport {g : E3 → C3} (hg : LocallyIntegrable g volume)
    {H : E3 → C3} (hH : Continuous H) (hHs : HasCompactSupport H) :
    Integrable fun ξ => ⟪g ξ, H ξ⟫_ℂ := by
  have h1 : Integrable fun ξ => ‖H ξ‖ • g ξ :=
    hg.integrable_smul_left_of_hasCompactSupport hH.norm hHs.norm
  refine h1.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (hg.aestronglyMeasurable.inner hH.aestronglyMeasurable)
  · rw [norm_smul, norm_norm, mul_comm]; exact norm_inner_le_norm _ _

/-- **Lema fundamental**: dois campos localmente integráveis com os mesmos pareamentos contra os
campos `C^∞` de suporte compacto coincidem q.t.p. -/
theorem ae_eq_of_integral_inner_eq {g₁ g₂ : E3 → C3} (h₁ : LocallyIntegrable g₁ volume)
    (h₂ : LocallyIntegrable g₂ volume)
    (h : ∀ H : E3 → C3, ContDiff ℝ ∞ H → HasCompactSupport H →
      ∫ ξ, ⟪g₁ ξ, H ξ⟫_ℂ = ∫ ξ, ⟪g₂ ξ, H ξ⟫_ℂ) :
    g₁ =ᵐ[volume] g₂ := by
  have hk : ∀ k : Fin 3, ∀ᵐ ξ ∂volume, conj (g₁ ξ k - g₂ ξ k) = 0 := by
    intro k
    have hloc : LocallyIntegrable (fun ξ => conj (g₁ ξ k - g₂ ξ k)) volume := by
      have hc : LocallyIntegrable (fun ξ => g₁ ξ k - g₂ ξ k) volume := by
        have e1 : LocallyIntegrable (fun ξ => g₁ ξ k) volume :=
          locallyIntegrableOn_univ.mp ((EuclideanSpace.proj (𝕜 := ℂ) k).locallyIntegrableOn_comp
            (h₁.locallyIntegrableOn univ))
        have e2 : LocallyIntegrable (fun ξ => g₂ ξ k) volume :=
          locallyIntegrableOn_univ.mp ((EuclideanSpace.proj (𝕜 := ℂ) k).locallyIntegrableOn_comp
            (h₂.locallyIntegrableOn univ))
        exact e1.sub e2
      exact locallyIntegrableOn_univ.mp (Complex.conjCLE.toContinuousLinearMap.locallyIntegrableOn_comp
        (hc.locallyIntegrableOn univ))
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun φ hφ hφs => ?_)
    have hH := h (tk φ k) (contDiff_tk hφ k) (hasCompactSupport_tk hφs k)
    have i1 := integrable_inner_of_hasCompactSupport h₁ (contDiff_tk hφ k).continuous
      (hasCompactSupport_tk hφs k)
    have i2 := integrable_inner_of_hasCompactSupport h₂ (contDiff_tk hφ k).continuous
      (hasCompactSupport_tk hφs k)
    have e : ∀ ξ, φ ξ • conj (g₁ ξ k - g₂ ξ k) =
        ⟪g₁ ξ, tk φ k ξ⟫_ℂ - ⟪g₂ ξ, tk φ k ξ⟫_ℂ := by
      intro ξ
      rw [inner_tk, inner_tk, map_sub, Complex.real_smul]
      ring
    simp_rw [e]
    rw [integral_sub i1 i2, hH, sub_self]
  have hall : ∀ᵐ ξ ∂volume, ∀ k : Fin 3, conj (g₁ ξ k - g₂ ξ k) = 0 := ae_all_iff.mpr hk
  filter_upwards [hall] with ξ hξ
  ext k
  have := hξ k
  rw [map_eq_zero, sub_eq_zero] at this
  exact this

/-! ### Integração por partes contra campos de Schwartz -/

/-- O produto interno de `ℂ³` como forma `ℝ`-bilinear contínua. -/
noncomputable def innR : C3 →L[ℝ] C3 →L[ℝ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w : C3 => ⟪v, w⟫_ℂ) (fun v v' w => inner_add_left v v' w)
      (fun c v w => by
        rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, Complex.real_smul])
      (fun v w w' => inner_add_right v w w')
      (fun c v w => by rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]))
    1 (fun v w => by rw [one_mul]; exact norm_inner_le_norm v w)

theorem innR_apply (v w : C3) : innR v w = ⟪v, w⟫_ℂ := rfl

/-- Integração por partes em `ℝ³` para o pareamento `⟪f, Ψ⟫` (hipóteses de integrabilidade). -/
theorem integral_inner_dX {f Ψ : E3 → C3} (j : Fin 3) (hf : Differentiable ℝ f)
    (hΨ : Differentiable ℝ Ψ)
    (h1 : Integrable fun x => ⟪dX j f x, Ψ x⟫_ℂ) (h2 : Integrable fun x => ⟪f x, dX j Ψ x⟫_ℂ)
    (h3 : Integrable fun x => ⟪f x, Ψ x⟫_ℂ) :
    ∫ x, ⟪f x, dX j Ψ x⟫_ℂ = -∫ x, ⟪dX j f x, Ψ x⟫_ℂ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innR) (v := e j) h1 h2 h3
    (fun x _ => hf x) (fun x _ => hΨ x)

theorem integrable_inner_of_memLp {f g : E3 → C3} (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable fun x => ⟪f x, g x⟫_ℂ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  refine h.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem hasTemperateGrowth_coord (j : Fin 3) :
    (fun ξ : E3 => inner ℝ ξ (e j)).HasTemperateGrowth :=
  ((innerSL ℝ).flip (e j)).hasTemperateGrowth

/-- `cj j ξ • S ξ` como campo de Schwartz. -/
noncomputable def mulCj (j : Fin 3) (S : 𝓢(E3, C3)) : 𝓢(E3, C3) :=
  (2 * π * Complex.I) • smulLeftCLM C3 (inner ℝ · (e j)) S

theorem mulCj_apply (j : Fin 3) (S : 𝓢(E3, C3)) (ξ : E3) : mulCj j S ξ = cj j ξ • S ξ := by
  have h0 : ((2 * π * Complex.I) • smulLeftCLM C3 (inner ℝ · (e j)) S : 𝓢(E3, C3)) ξ =
      (2 * π * Complex.I) • (smulLeftCLM C3 (inner ℝ · (e j)) S : 𝓢(E3, C3)) ξ := rfl
  rw [mulCj, h0, smulLeftCLM_apply_apply (hasTemperateGrowth_coord j), ← Complex.coe_smul,
    smul_smul, cj]
  congr 1
  rw [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  push_cast
  ring

/-- `∂ⱼ 𝓕⁻ S = 𝓕⁻ (2πi ξⱼ S)`. -/
theorem dX_fourierInv (S : 𝓢(E3, C3)) (j : Fin 3) (x : E3) :
    dX j (⇑(𝓕⁻ S : 𝓢(E3, C3))) x = (𝓕⁻ (mulCj j S) : 𝓢(E3, C3)) x := by
  rw [dX, ← SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_fourierInv_eq]
  rfl

theorem conj_cj (j : Fin 3) (ξ : E3) : conj (cj j ξ) = -cj j ξ := by
  rw [cj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem locallyIntegrable_smul {c : E3 → ℂ} (hc : Continuous c) {g : E3 → C3}
    (hg : LocallyIntegrable g volume) : LocallyIntegrable (fun ξ => c ξ • g ξ) volume :=
  (locallyIntegrable_iff).mpr fun _ hK =>
    (hg.integrableOn_isCompact hK).continuousOn_smul hc.continuousOn hK

/-- **Transformada da derivada em `L²`**: `𝓕(∂ⱼ f) = 2πi ξⱼ 𝓕 f` q.t.p. -/
theorem FL_dX {f : E3 → C3} (j : Fin 3) (hf : Differentiable ℝ f) (h2 : MemLp f 2)
    (hd : MemLp (dX j f) 2) :
    FL (dX j f) =ᵐ[volume] fun ξ => cj j ξ • FL f ξ := by
  refine ae_eq_of_integral_inner_eq (locallyIntegrable_FL _)
    (locallyIntegrable_smul (continuous_cj j) (locallyIntegrable_FL f)) (fun H hH hHs => ?_)
  set S : 𝓢(E3, C3) := hHs.toSchwartzMap hH
  have hS : ∀ ξ, S ξ = H ξ := fun ξ => rfl
  have hL : ∫ ξ, ⟪FL (dX j f) ξ, H ξ⟫_ℂ = ∫ x, ⟪dX j f x, (𝓕⁻ S : 𝓢(E3, C3)) x⟫_ℂ :=
    integral_inner_FL hd S
  have hibp := integral_inner_dX j hf (𝓕⁻ S : 𝓢(E3, C3)).differentiable
    (integrable_inner_of_memLp hd ((𝓕⁻ S : 𝓢(E3, C3)).memLp 2))
    (by
      simp_rw [dX_fourierInv]
      exact integrable_inner_of_memLp h2 ((𝓕⁻ (mulCj j S) : 𝓢(E3, C3)).memLp 2))
    (integrable_inner_of_memLp h2 ((𝓕⁻ S : 𝓢(E3, C3)).memLp 2))
  simp_rw [dX_fourierInv] at hibp
  have hR : ∫ x, ⟪f x, (𝓕⁻ (mulCj j S) : 𝓢(E3, C3)) x⟫_ℂ =
      ∫ ξ, ⟪FL f ξ, mulCj j S ξ⟫_ℂ := (integral_inner_FL h2 _).symm
  have hR2 : ∫ ξ, ⟪FL f ξ, mulCj j S ξ⟫_ℂ = -∫ ξ, ⟪cj j ξ • FL f ξ, H ξ⟫_ℂ := by
    rw [← integral_neg]
    congr 1 with ξ
    rw [mulCj_apply, inner_smul_right, inner_smul_left, conj_cj, hS]
    ring
  rw [hL, ← neg_neg (∫ x, ⟪dX j f x, (𝓕⁻ S : 𝓢(E3, C3)) x⟫_ℂ), ← hibp, hR, hR2, neg_neg]

/-! ### O teorema da convolução em `L²` -/

section Conv

variable (B : C3 →L[ℂ] C3 →L[ℂ] C3)

/-- Caso de Schwartz: `∫ B(𝓕p(η), 𝓕q(ξ − η)) dη = 𝓕[B(p, q)](ξ)`. -/
theorem conv_fourier_schwartz (p q : 𝓢(E3, C3)) (ξ : E3) :
    ∫ η, B ((𝓕 p : 𝓢(E3, C3)) η) ((𝓕 q : 𝓢(E3, C3)) (ξ - η)) =
      𝓕 (fun x => B (p x) (q x)) ξ := by
  set P : 𝓢(E3, C3) := 𝓕 p
  set Q : 𝓢(E3, C3) := 𝓕 q
  set h : E3 → C3 := (P : E3 → C3) ⋆[B] (Q : E3 → C3) with hh_def
  have hh : h = ⇑(SchwartzMap.convolution B P Q) := by
    funext x; exact (SchwartzMap.convolution_apply B P Q x).symm
  have hP : ∀ x, 𝓕 (⇑P) (-x) = p x := by
    intro x
    rw [← Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourierInv_coe]
    simp [P]
  have hQ : ∀ x, 𝓕 (⇑Q) (-x) = q x := by
    intro x
    rw [← Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourierInv_coe]
    simp [Q]
  have hinv : 𝓕⁻ h = fun x => B (p x) (q x) := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, hh_def,
      Real.fourier_bilin_convolution_eq B P.integrable Q.integrable, hP, hQ]
  have hcont : Continuous h := by rw [hh]; exact (SchwartzMap.convolution B P Q).continuous
  have hint : Integrable h := by rw [hh]; exact (SchwartzMap.convolution B P Q).integrable
  have hFint : Integrable (𝓕 h) := by
    rw [hh, ← SchwartzMap.fourier_coe]; exact (𝓕 (SchwartzMap.convolution B P Q)).integrable
  have h1 : 𝓕 (𝓕⁻ h) = h := hcont.fourier_fourierInv_eq hint hFint
  rw [← hinv, h1, hh_def, convolution_def]

theorem integrable_sq_norm_of_memLp {F : E3 → C3} (hF : MemLp F 2) :
    Integrable fun x => ‖F x‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF

/-- Cauchy–Schwarz com translação-reflexão: `∫ ‖F(η)‖‖G(ξ − η)‖ ≤ √∫‖F‖² √∫‖G‖²`. -/
theorem integral_norm_mul_sub_le {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) (ξ : E3) :
    ∫ η, ‖F η‖ * ‖G (ξ - η)‖ ≤ √(∫ η, ‖F η‖ ^ 2) * √(∫ η, ‖G η‖ ^ 2) := by
  have hGm : AEStronglyMeasurable (fun η => G (ξ - η)) volume :=
    hG.aestronglyMeasurable.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  have hG2 : Integrable fun η => ‖G (ξ - η)‖ ^ 2 :=
    (integrable_sq_norm_of_memLp hG).comp_sub_left ξ
  have h := ATK.NSEstimativas.cs_sq (f := fun η => ‖F η‖) (g := fun η => ‖G (ξ - η)‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hF.aestronglyMeasurable.norm hGm.norm
    (integrable_sq_norm_of_memLp hF) hG2
  have e : ∫ η, ‖G (ξ - η)‖ ^ 2 = ∫ η, ‖G η‖ ^ 2 :=
    integral_sub_left_eq_self (fun η => ‖G η‖ ^ 2) volume ξ
  rw [e] at h
  have h0 : 0 ≤ ∫ η, ‖F η‖ * ‖G (ξ - η)‖ :=
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [← Real.sqrt_mul (integral_nonneg fun _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

theorem integral_norm_mul_le {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) :
    ∫ x, ‖F x‖ * ‖G x‖ ≤ √(∫ x, ‖F x‖ ^ 2) * √(∫ x, ‖G x‖ ^ 2) := by
  have h := ATK.NSEstimativas.cs_sq (f := fun x => ‖F x‖) (g := fun x => ‖G x‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hF.aestronglyMeasurable.norm
    hG.aestronglyMeasurable.norm (integrable_sq_norm_of_memLp hF) (integrable_sq_norm_of_memLp hG)
  rw [← Real.sqrt_mul (integral_nonneg fun _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

theorem integrable_norm_mul_sub {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) (ξ : E3) :
    Integrable fun η => ‖F η‖ * ‖G (ξ - η)‖ := by
  have hGm : AEStronglyMeasurable (fun η => G (ξ - η)) volume :=
    hG.aestronglyMeasurable.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  have hGl : MemLp (fun η => G (ξ - η)) 2 :=
    hG.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  exact hF.norm.integrable_mul hGl.norm

theorem integrable_cvB {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) (ξ : E3) :
    Integrable fun η => B (F η) (G (ξ - η)) := by
  have hGm : AEStronglyMeasurable (fun η => G (ξ - η)) volume :=
    hG.aestronglyMeasurable.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  refine ((integrable_norm_mul_sub hF hG ξ).const_mul ‖B‖).mono'
    (B.aestronglyMeasurable_comp₂ hF.aestronglyMeasurable hGm) (Eventually.of_forall fun η => ?_)
  rw [← mul_assoc]
  exact B.le_opNorm₂ _ _

theorem integrable_prB {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) :
    Integrable fun x => B (F x) (G x) := by
  have h1 : Integrable fun x => ‖F x‖ * ‖G x‖ := by
    exact hF.norm.integrable_mul hG.norm
  refine (h1.const_mul ‖B‖).mono'
    (B.aestronglyMeasurable_comp₂ hF.aestronglyMeasurable hG.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [← mul_assoc]
  exact B.le_opNorm₂ _ _

theorem sqrt_integral_norm_sq_Lp (w : Lp C3 2 (volume : Measure E3)) :
    √(∫ x, ‖(w : E3 → C3) x‖ ^ 2) = ‖w‖ := by
  rw [← norm_sq_eq_integral, Real.sqrt_sq (norm_nonneg _)]

theorem norm_cvB_le {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) (ξ : E3) :
    ‖∫ η, B (F η) (G (ξ - η))‖ ≤ ‖B‖ * (√(∫ η, ‖F η‖ ^ 2) * √(∫ η, ‖G η‖ ^ 2)) := by
  calc ‖∫ η, B (F η) (G (ξ - η))‖ ≤ ∫ η, ‖B‖ * (‖F η‖ * ‖G (ξ - η)‖) := by
        refine norm_integral_le_of_norm_le ((integrable_norm_mul_sub hF hG ξ).const_mul _)
          (Eventually.of_forall fun η => ?_)
        rw [← mul_assoc]; exact B.le_opNorm₂ _ _
    _ = ‖B‖ * ∫ η, ‖F η‖ * ‖G (ξ - η)‖ := integral_const_mul _ _
    _ ≤ ‖B‖ * (√(∫ η, ‖F η‖ ^ 2) * √(∫ η, ‖G η‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (integral_norm_mul_sub_le hF hG ξ) (ContinuousLinearMap.opNorm_nonneg B)

theorem norm_prB_le {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) (ξ : E3) :
    ‖∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • B (F x) (G x)‖ ≤ ‖B‖ * (√(∫ x, ‖F x‖ ^ 2) * √(∫ x, ‖G x‖ ^ 2)) := by
  have h1 : Integrable fun x => ‖F x‖ * ‖G x‖ := hF.norm.integrable_mul hG.norm
  calc ‖∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • B (F x) (G x)‖ ≤ ∫ x, ‖B‖ * (‖F x‖ * ‖G x‖) := by
        refine norm_integral_le_of_norm_le (h1.const_mul _) (Eventually.of_forall fun x => ?_)
        rw [Circle.norm_smul, ← mul_assoc]; exact B.le_opNorm₂ _ _
    _ = ‖B‖ * ∫ x, ‖F x‖ * ‖G x‖ := integral_const_mul _ _
    _ ≤ ‖B‖ * (√(∫ x, ‖F x‖ ^ 2) * √(∫ x, ‖G x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (integral_norm_mul_le hF hG) (ContinuousLinearMap.opNorm_nonneg B)

theorem integrable_prB_e {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) (ξ : E3) :
    Integrable fun x => 𝐞 (-⟪x, ξ⟫_ℝ) • B (F x) (G x) := by
  refine (integrable_prB B hF hG).norm.mono' ?_ (Eventually.of_forall fun x => ?_)
  · have hc : Continuous fun x : E3 => (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) :=
      (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((continuous_id.inner continuous_const).neg)
    have : (fun x => 𝐞 (-⟪x, ξ⟫_ℝ) • B (F x) (G x)) =
        fun x => (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) • B (F x) (G x) := by
      funext x; rw [Circle.smul_def]
    rw [this]
    exact hc.aestronglyMeasurable.smul (integrable_prB B hF hG).aestronglyMeasurable
  · rw [Circle.norm_smul]

/-- O lado convolução para elementos de `L²`. -/
noncomputable def cvL (ξ : E3) (u v : Lp C3 2 (volume : Measure E3)) : C3 :=
  ∫ η, B ((𝓕 u : Lp C3 2 (volume : Measure E3)) η) ((𝓕 v : Lp C3 2 (volume : Measure E3)) (ξ - η))

/-- O lado produto para elementos de `L²`. -/
noncomputable def prL (ξ : E3) (u v : Lp C3 2 (volume : Measure E3)) : C3 :=
  ∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • B ((u : E3 → C3) x) ((v : E3 → C3) x)

theorem cvB_congr {F F' G G' : E3 → C3} (hF : F =ᵐ[volume] F') (hG : G =ᵐ[volume] G') (ξ : E3) :
    ∫ η, B (F η) (G (ξ - η)) = ∫ η, B (F' η) (G' (ξ - η)) := by
  have hG' : (fun η => G (ξ - η)) =ᵐ[volume] fun η => G' (ξ - η) :=
    (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq_comp hG
  apply integral_congr_ae
  filter_upwards [hF, hG'] with η h1 h2
  rw [h1, h2]

theorem prB_congr {F F' G G' : E3 → C3} (hF : F =ᵐ[volume] F') (hG : G =ᵐ[volume] G') (ξ : E3) :
    ∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • B (F x) (G x) = ∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • B (F' x) (G' x) := by
  apply integral_congr_ae
  filter_upwards [hF, hG] with x h1 h2
  rw [h1, h2]

theorem fourierL_sub (u u' : Lp C3 2 (volume : Measure E3)) :
    (𝓕 (u - u') : Lp C3 2 (volume : Measure E3)) = 𝓕 u - 𝓕 u' :=
  map_sub (Lp.fourierTransformₗᵢ E3 C3) u u'

theorem coeFn_fourier_toLp (p : 𝓢(E3, C3)) :
    ((𝓕 (p.toLp 2) : Lp C3 2 (volume : Measure E3)) : E3 → C3) =ᵐ[volume]
      ⇑(𝓕 p : 𝓢(E3, C3)) := by
  have e : (𝓕 (p.toLp 2) : Lp C3 2 (volume : Measure E3)) = (𝓕 p : 𝓢(E3, C3)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq p
  exact (EventuallyEq.of_eq (congrArg (fun u : Lp C3 2 (volume : Measure E3) =>
    (u : E3 → C3)) e)).trans ((𝓕 p : 𝓢(E3, C3)).coeFn_toLp 2)

theorem cvL_base (ξ : E3) (p q : 𝓢(E3, C3)) :
    cvL B ξ (p.toLp 2) (q.toLp 2) = prL B ξ (p.toLp 2) (q.toLp 2) := by
  have h1 := cvB_congr B (coeFn_fourier_toLp p) (coeFn_fourier_toLp q) ξ
  have h2 := prB_congr B (p.coeFn_toLp 2) (q.coeFn_toLp 2) ξ
  unfold cvL prL
  rw [h1, h2, conv_fourier_schwartz B p q ξ, Real.fourier_eq]

theorem dist_cvL_left (ξ : E3) (u u' v : Lp C3 2 (volume : Measure E3)) :
    dist (cvL B ξ u v) (cvL B ξ u' v) ≤ ‖B‖ * ‖v‖ * dist u u' := by
  rw [dist_eq_norm, dist_eq_norm]
  have hu := Lp.memLp (𝓕 u : Lp C3 2 (volume : Measure E3))
  have hu' := Lp.memLp (𝓕 u' : Lp C3 2 (volume : Measure E3))
  have hv := Lp.memLp (𝓕 v : Lp C3 2 (volume : Measure E3))
  have hd := Lp.memLp (𝓕 (u - u') : Lp C3 2 (volume : Measure E3))
  have e : cvL B ξ u v - cvL B ξ u' v =
      ∫ η, B ((𝓕 (u - u') : Lp C3 2 (volume : Measure E3)) η)
        ((𝓕 v : Lp C3 2 (volume : Measure E3)) (ξ - η)) := by
    unfold cvL
    rw [← integral_sub (integrable_cvB B hu hv ξ) (integrable_cvB B hu' hv ξ)]
    apply integral_congr_ae
    rw [fourierL_sub]
    filter_upwards [Lp.coeFn_sub (𝓕 u : Lp C3 2 (volume : Measure E3)) (𝓕 u')] with η hη
    rw [hη, Pi.sub_apply, ContinuousLinearMap.map_sub₂]
  rw [e]
  refine (norm_cvB_le B hd hv ξ).trans (le_of_eq ?_)
  rw [sqrt_integral_norm_sq_Lp, sqrt_integral_norm_sq_Lp, Lp.norm_fourier_eq, Lp.norm_fourier_eq]
  ring

theorem dist_cvL_right (ξ : E3) (u v v' : Lp C3 2 (volume : Measure E3)) :
    dist (cvL B ξ u v) (cvL B ξ u v') ≤ ‖B‖ * ‖u‖ * dist v v' := by
  rw [dist_eq_norm, dist_eq_norm]
  have hu := Lp.memLp (𝓕 u : Lp C3 2 (volume : Measure E3))
  have hv := Lp.memLp (𝓕 v : Lp C3 2 (volume : Measure E3))
  have hv' := Lp.memLp (𝓕 v' : Lp C3 2 (volume : Measure E3))
  have hd := Lp.memLp (𝓕 (v - v') : Lp C3 2 (volume : Measure E3))
  have e : cvL B ξ u v - cvL B ξ u v' =
      ∫ η, B ((𝓕 u : Lp C3 2 (volume : Measure E3)) η)
        ((𝓕 (v - v') : Lp C3 2 (volume : Measure E3)) (ξ - η)) := by
    unfold cvL
    rw [← integral_sub (integrable_cvB B hu hv ξ) (integrable_cvB B hu hv' ξ), fourierL_sub]
    have hG : (fun η => ((𝓕 v - 𝓕 v' : Lp C3 2 (volume : Measure E3)) : E3 → C3) (ξ - η)) =ᵐ[volume]
        fun η => ((𝓕 v : Lp C3 2 (volume : Measure E3)) : E3 → C3) (ξ - η) -
          ((𝓕 v' : Lp C3 2 (volume : Measure E3)) : E3 → C3) (ξ - η) :=
      (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_sub (𝓕 v : Lp C3 2 (volume : Measure E3)) (𝓕 v'))
    apply integral_congr_ae
    filter_upwards [hG] with η hη
    rw [hη, (B _).map_sub]
  rw [e]
  refine (norm_cvB_le B hu hd ξ).trans (le_of_eq ?_)
  rw [sqrt_integral_norm_sq_Lp, sqrt_integral_norm_sq_Lp, Lp.norm_fourier_eq, Lp.norm_fourier_eq]
  ring

theorem dist_prL_left (ξ : E3) (u u' v : Lp C3 2 (volume : Measure E3)) :
    dist (prL B ξ u v) (prL B ξ u' v) ≤ ‖B‖ * ‖v‖ * dist u u' := by
  rw [dist_eq_norm, dist_eq_norm]
  have e : prL B ξ u v - prL B ξ u' v =
      ∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • B (((u - u' : Lp C3 2 (volume : Measure E3)) : E3 → C3) x)
        ((v : E3 → C3) x) := by
    unfold prL
    rw [← integral_sub (integrable_prB_e B (Lp.memLp u) (Lp.memLp v) ξ)
      (integrable_prB_e B (Lp.memLp u') (Lp.memLp v) ξ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u u'] with x hx
    rw [hx, Pi.sub_apply, ContinuousLinearMap.map_sub₂, smul_sub]
  rw [e]
  refine (norm_prB_le B (Lp.memLp _) (Lp.memLp v) ξ).trans (le_of_eq ?_)
  rw [sqrt_integral_norm_sq_Lp, sqrt_integral_norm_sq_Lp]
  ring

theorem dist_prL_right (ξ : E3) (u v v' : Lp C3 2 (volume : Measure E3)) :
    dist (prL B ξ u v) (prL B ξ u v') ≤ ‖B‖ * ‖u‖ * dist v v' := by
  rw [dist_eq_norm, dist_eq_norm]
  have e : prL B ξ u v - prL B ξ u v' =
      ∫ x, 𝐞 (-⟪x, ξ⟫_ℝ) • B ((u : E3 → C3) x)
        (((v - v' : Lp C3 2 (volume : Measure E3)) : E3 → C3) x) := by
    unfold prL
    rw [← integral_sub (integrable_prB_e B (Lp.memLp u) (Lp.memLp v) ξ)
      (integrable_prB_e B (Lp.memLp u) (Lp.memLp v') ξ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub v v'] with x hx
    rw [hx, Pi.sub_apply, (B _).map_sub, smul_sub]
  rw [e]
  refine (norm_prB_le B (Lp.memLp u) (Lp.memLp _) ξ).trans (le_of_eq ?_)
  rw [sqrt_integral_norm_sq_Lp, sqrt_integral_norm_sq_Lp]
  ring

theorem continuous_of_dist_le {f : Lp C3 2 (volume : Measure E3) → C3} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ u u', dist (f u) (f u') ≤ K * dist u u') : Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := ⟨K, hK⟩) fun u u' => h u u').continuous

theorem cvL_eq_prL (ξ : E3) (u v : Lp C3 2 (volume : Measure E3)) :
    cvL B ξ u v = prL B ξ u v := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := C3) (E := E3) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top
  have step1 : ∀ (u : Lp C3 2 (volume : Measure E3)) (q : 𝓢(E3, C3)),
      cvL B ξ u (q.toLp 2) = prL B ξ u (q.toLp 2) := by
    intro u q
    refine DenseRange.induction_on (p := fun u => cvL B ξ u (q.toLp 2) = prL B ξ u (q.toLp 2))
      hd u (isClosed_eq ?_ ?_) (fun p => ?_)
    · exact continuous_of_dist_le (mul_nonneg (ContinuousLinearMap.opNorm_nonneg B) (norm_nonneg _))
        fun u u' => dist_cvL_left B ξ u u' _
    · exact continuous_of_dist_le (mul_nonneg (ContinuousLinearMap.opNorm_nonneg B) (norm_nonneg _))
        fun u u' => dist_prL_left B ξ u u' _
    · rw [SchwartzMap.toLpCLM_apply]; exact cvL_base B ξ p q
  refine DenseRange.induction_on (p := fun v => cvL B ξ u v = prL B ξ u v) hd v
    (isClosed_eq ?_ ?_) (fun q => ?_)
  · exact continuous_of_dist_le (mul_nonneg (ContinuousLinearMap.opNorm_nonneg B) (norm_nonneg _))
      fun v v' => dist_cvL_right B ξ u v v'
  · exact continuous_of_dist_le (mul_nonneg (ContinuousLinearMap.opNorm_nonneg B) (norm_nonneg _))
      fun v v' => dist_prL_right B ξ u v v'
  · rw [SchwartzMap.toLpCLM_apply]; exact step1 u q

/-- **Teorema da convolução em `L²`**: para `F, G ∈ L²(ℝ³, ℂ³)` e `B` bilinear,
`∫ B(𝓕F(η), 𝓕G(ξ − η)) dη = 𝓕[B(F, G)](ξ)` em todo `ξ`. -/
theorem conv_FL {F G : E3 → C3} (hF : MemLp F 2) (hG : MemLp G 2) (ξ : E3) :
    ∫ η, B (FL F η) (FL G (ξ - η)) = 𝓕 (fun x => B (F x) (G x)) ξ := by
  have h := cvL_eq_prL B ξ (hF.toLp F) (hG.toLp G)
  unfold cvL prL at h
  rw [FL_eq hF, FL_eq hG, h, prB_congr B hF.coeFn_toLp hG.coeFn_toLp ξ, Real.fourier_eq]

end Conv

end ATK.NSL2

#print axioms ATK.NSL2.FL_eq
#print axioms ATK.NSL2.memLp_FL
#print axioms ATK.NSL2.locallyIntegrable_FL
#print axioms ATK.NSL2.integral_norm_sq_FL
#print axioms ATK.NSL2.integral_inner_FL
#print axioms ATK.NSL2.inner_tk
#print axioms ATK.NSL2.contDiff_tk
#print axioms ATK.NSL2.hasCompactSupport_tk
#print axioms ATK.NSL2.integrable_inner_of_hasCompactSupport
#print axioms ATK.NSL2.ae_eq_of_integral_inner_eq
#print axioms ATK.NSL2.innR_apply
#print axioms ATK.NSL2.integral_inner_dX
#print axioms ATK.NSL2.integrable_inner_of_memLp
#print axioms ATK.NSL2.hasTemperateGrowth_coord
#print axioms ATK.NSL2.mulCj_apply
#print axioms ATK.NSL2.dX_fourierInv
#print axioms ATK.NSL2.conj_cj
#print axioms ATK.NSL2.locallyIntegrable_smul
#print axioms ATK.NSL2.FL_dX
#print axioms ATK.NSL2.conv_fourier_schwartz
#print axioms ATK.NSL2.integrable_sq_norm_of_memLp
#print axioms ATK.NSL2.integral_norm_mul_sub_le
#print axioms ATK.NSL2.integral_norm_mul_le
#print axioms ATK.NSL2.integrable_norm_mul_sub
#print axioms ATK.NSL2.integrable_cvB
#print axioms ATK.NSL2.integrable_prB
#print axioms ATK.NSL2.sqrt_integral_norm_sq_Lp
#print axioms ATK.NSL2.norm_cvB_le
#print axioms ATK.NSL2.norm_prB_le
#print axioms ATK.NSL2.integrable_prB_e
#print axioms ATK.NSL2.cvB_congr
#print axioms ATK.NSL2.prB_congr
#print axioms ATK.NSL2.fourierL_sub
#print axioms ATK.NSL2.coeFn_fourier_toLp
#print axioms ATK.NSL2.cvL_base
#print axioms ATK.NSL2.dist_cvL_left
#print axioms ATK.NSL2.dist_cvL_right
#print axioms ATK.NSL2.dist_prL_left
#print axioms ATK.NSL2.dist_prL_right
#print axioms ATK.NSL2.continuous_of_dist_le
#print axioms ATK.NSL2.cvL_eq_prL
#print axioms ATK.NSL2.conv_FL
