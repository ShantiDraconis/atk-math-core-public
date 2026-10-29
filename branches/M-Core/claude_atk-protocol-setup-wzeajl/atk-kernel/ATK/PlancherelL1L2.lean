import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# ATK — Plancherel na forma integral para `f ∈ L¹ ∩ L²` (reta real)

A Mathlib tem a transformada de Fourier em `L²` como isometria (`Lp.fourierTransformₗᵢ`) e a
identidade de Plancherel na forma integral só para funções de Schwartz. Falta a ponte com a
integral de Fourier usual para funções integráveis. Aqui:

* `fourier_toLp_ae_eq`: para `f ∈ L¹ ∩ L²`, o `𝓕` de `L²` coincide q.t.p. com a integral de
  Fourier `𝓕 f`;
* `memLp_two_fourier`: `𝓕 f ∈ L²`;
* `integral_norm_sq_fourier`: **`∫ ‖𝓕 f ξ‖² dξ = ∫ ‖f x‖² dx`**.

Prova: as duas funções têm a mesma ação contra toda função teste suave de suporte compacto
(fórmula de multiplicação `∫ 𝓕 f · g = ∫ f · 𝓕 g` e `Lp.fourier_toTemperedDistribution_eq`), logo
coincidem q.t.p. (`ae_eq_of_integral_contDiff_smul_eq`).

Primeiro passo da fórmula espectral de `D_N` (`ATK.EspectralDN`).
-/

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff InnerProductSpace

namespace ATK.PlancherelL1L2

variable {f : ℝ → ℂ}

/-- A transformada de Fourier de uma função integrável é contínua. -/
theorem continuous_fourier (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- Fórmula de multiplicação na reta: `∫ (𝓕 f) · g = ∫ f · (𝓕 g)`. -/
theorem integral_fourier_mul (hf : Integrable f) {g : ℝ → ℂ} (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext
    simp
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (e := Real.fourierChar) (L := innerₗ ℝ) Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf hg
  simp only [hflip, smul_eq_mul] at this
  exact this

/-- **O `𝓕` de `L²` concorda q.t.p. com a integral de Fourier** para `f ∈ L¹ ∩ L²`. -/
theorem fourier_toLp_ae_eq (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  set v : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hf2.toLp f) with hv_def
  have hv : LocallyIntegrable (v : ℝ → ℂ) volume :=
    (Lp.memLp v).locallyIntegrable (by norm_num)
  have hF : LocallyIntegrable (𝓕 f) volume := (continuous_fourier hf1).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hv hF ?_
  intro g hg hgs
  set gc : ℝ → ℂ := fun x => (g x : ℂ) with hgc
  have hgc_smooth : ContDiff ℝ ∞ gc := Complex.ofRealCLM.contDiff.comp hg
  have hgc_supp : HasCompactSupport gc := hgs.comp_left Complex.ofReal_zero
  set G : 𝓢(ℝ, ℂ) := hgc_supp.toSchwartzMap hgc_smooth with hG
  have hGx : ∀ x, G x = gc x := fun x => rfl
  have hGint : Integrable (G : ℝ → ℂ) := G.integrable
  -- lado esquerdo: ação de `v`
  have hL : ∫ x, g x • (v : ℝ → ℂ) x = ∫ x, G x • (v : ℝ → ℂ) x := by
    congr 1
  have hL2 : ∫ x, G x • (v : ℝ → ℂ) x =
      ∫ x, (𝓕 G) x • (hf2.toLp f : ℝ → ℂ) x := by
    rw [← Lp.toTemperedDistribution_apply, hv_def, ← Lp.fourier_toTemperedDistribution_eq,
      TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  have hL3 : ∫ x, (𝓕 G) x • (hf2.toLp f : ℝ → ℂ) x = ∫ x, (𝓕 (G : ℝ → ℂ)) x * f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.fourier_coe, smul_eq_mul]
  -- lado direito: fórmula de multiplicação
  have hR : ∫ x, g x • 𝓕 f x = ∫ x, (𝓕 (G : ℝ → ℂ)) x * f x := by
    have h := integral_fourier_mul hf1 hGint
    have e1 : ∫ x, g x • 𝓕 f x = ∫ ξ, 𝓕 f ξ * G ξ := by
      congr 1 with x
      rw [hGx, Complex.real_smul, mul_comm]
    have e2 : ∫ x, f x * 𝓕 (G : ℝ → ℂ) x = ∫ x, (𝓕 (G : ℝ → ℂ)) x * f x := by
      congr 1 with x
      rw [mul_comm]
    rw [e1, h, e2]
  rw [hL, hL2, hL3, hR]

/-- `𝓕 f ∈ L²` para `f ∈ L¹ ∩ L²`. -/
theorem memLp_two_fourier (hf1 : Integrable f) (hf2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (Lp.memLp _).ae_eq (fourier_toLp_ae_eq hf1 hf2)

/-- `‖u‖² = ∫ ‖u x‖²` para `u ∈ L²(ℝ)`. -/
theorem norm_sq_eq_integral (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖u‖ ^ 2 = ∫ x, ‖(u : ℝ → ℂ) x‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  have h1 : (Complex.ofRealLI (‖u‖ ^ 2) : ℂ) = ⟪u, u⟫_ℂ := by
    simp [inner_self_eq_norm_sq_to_K]
  have h2 : (Complex.ofRealLI (∫ x, ‖(u : ℝ → ℂ) x‖ ^ 2) : ℂ) =
      ∫ x, ⟪(u : ℝ → ℂ) x, (u : ℝ → ℂ) x⟫_ℂ := by
    rw [← LinearIsometry.integral_comp_comm]
    simp [inner_self_eq_norm_sq_to_K]
  rw [h1, h2, MeasureTheory.L2.inner_def]

/-- **Plancherel**: `∫ ‖𝓕 f ξ‖² dξ = ∫ ‖f x‖² dx` para `f ∈ L¹ ∩ L²`. -/
theorem integral_norm_sq_fourier (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h1 : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 =
      ∫ ξ, ‖((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [fourier_toLp_ae_eq hf1 hf2] with ξ h
    rw [h]
  have h2 : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖(hf2.toLp f : ℝ → ℂ) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x h
    rw [h]
  rw [h1, h2, ← norm_sq_eq_integral, ← norm_sq_eq_integral, Lp.norm_fourier_eq]

end ATK.PlancherelL1L2
#print axioms ATK.PlancherelL1L2.continuous_fourier
#print axioms ATK.PlancherelL1L2.integral_fourier_mul
#print axioms ATK.PlancherelL1L2.fourier_toLp_ae_eq
#print axioms ATK.PlancherelL1L2.memLp_two_fourier
#print axioms ATK.PlancherelL1L2.norm_sq_eq_integral
#print axioms ATK.PlancherelL1L2.integral_norm_sq_fourier
