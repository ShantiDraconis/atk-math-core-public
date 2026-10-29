import ATK.NSFisico
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# ATK — Plancherel em `ℝ³` para `f ∈ L¹ ∩ L²` (campos em `ℂ³`)

Camada 8 do ataque a B3 (energia e enstrofia). A Mathlib tem a transformada de Fourier em `L²`
como isometria (`Lp.fourierTransformₗᵢ`); falta a ponte com a integral de Fourier usual. Aqui
(generalizando `ATK.PlancherelL1L2` da reta para `ℝ³` e para campos vetoriais):

* `integral_smul_fourierInv`: fórmula de multiplicação `∫ G · 𝓕⁻f = ∫ 𝓕⁻G · f`;
* `fourierInv_toLp_ae_eq`: o `𝓕⁻` de `L²` coincide q.t.p. com a integral de Fourier;
* **`integral_norm_sq_Vf`**: `∫ ‖V[f](x)‖² dx = ∫ ‖f(ξ)‖² dξ` e `V[f] ∈ L²`.

**CLOSED_MATH continua false.**
-/

open MeasureTheory FourierTransform SchwartzMap Filter
open scoped ContDiff InnerProductSpace

namespace ATK.NSPlancherel

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave

variable {f : E3 → C3}

theorem Vf_eq_fourierInv (f : E3 → C3) (x : E3) : Vf f x = 𝓕⁻ f x := by
  rw [Real.fourierInv_eq']; rfl

theorem neg_innerₗ_flip : (-innerₗ E3 : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ).flip = -innerₗ E3 := by
  ext x y
  simp [real_inner_comm]

theorem fourierInv_eq_vector (h : E3 → C3) :
    𝓕⁻ h = VectorFourier.fourierIntegral 𝐞 volume (-innerₗ E3) h := by
  funext w
  rw [Real.fourierInv_eq, VectorFourier.fourierIntegral]
  simp

theorem fourierInv_eq_vector_scalar (h : E3 → ℂ) :
    𝓕⁻ h = VectorFourier.fourierIntegral 𝐞 volume (-innerₗ E3) h := by
  funext w
  rw [Real.fourierInv_eq, VectorFourier.fourierIntegral]
  simp

theorem continuous_neg_inner :
    Continuous fun p : E3 × E3 => (-innerₗ E3 : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ) p.1 p.2 := by
  refine ((continuous_inner : Continuous fun p : E3 × E3 => inner ℝ p.1 p.2).neg).congr
    (fun p => ?_)
  simp only [Pi.neg_apply, LinearMap.neg_apply, innerₗ_apply_apply]

theorem continuous_fourierInv (hf : Integrable f) : Continuous (𝓕⁻ f) := by
  rw [fourierInv_eq_vector]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_neg_inner hf

/-- **Fórmula de multiplicação**: `∫ G · 𝓕⁻ f = ∫ 𝓕⁻ G · f`. -/
theorem integral_smul_fourierInv {G : E3 → ℂ} (hG : Integrable G) (hf : Integrable f) :
    ∫ x, G x • 𝓕⁻ f x = ∫ ξ, 𝓕⁻ G ξ • f ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (e := Real.fourierChar) (L := -innerₗ E3) Real.continuous_fourierChar continuous_neg_inner
    hG hf
  rw [neg_innerₗ_flip] at h
  rw [fourierInv_eq_vector, fourierInv_eq_vector_scalar]
  exact h.symm

/-- **O `𝓕⁻` de `L²` concorda q.t.p. com a integral de Fourier** para `f ∈ L¹ ∩ L²`. -/
theorem fourierInv_toLp_ae_eq (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ((𝓕⁻ (hf2.toLp f) : Lp C3 2 (volume : Measure E3)) : E3 → C3) =ᵐ[volume] 𝓕⁻ f := by
  set v : Lp C3 2 (volume : Measure E3) := 𝓕⁻ (hf2.toLp f) with hv_def
  have hv : LocallyIntegrable (v : E3 → C3) volume :=
    (Lp.memLp v).locallyIntegrable (by norm_num)
  have hF : LocallyIntegrable (𝓕⁻ f) volume := (continuous_fourierInv hf1).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hv hF ?_
  intro g hg hgs
  set gc : E3 → ℂ := fun x => (g x : ℂ) with hgc
  have hgc_smooth : ContDiff ℝ ∞ gc := Complex.ofRealCLM.contDiff.comp hg
  have hgc_supp : HasCompactSupport gc := hgs.comp_left Complex.ofReal_zero
  set G : 𝓢(E3, ℂ) := hgc_supp.toSchwartzMap hgc_smooth with hG
  have hGx : ∀ x, G x = gc x := fun x => rfl
  have hGint : Integrable (G : E3 → ℂ) := G.integrable
  -- lado esquerdo: ação de `v`
  have hL : ∫ x, g x • (v : E3 → C3) x = ∫ x, G x • (v : E3 → C3) x := by
    congr 1 with x
  have hL2 : ∫ x, G x • (v : E3 → C3) x =
      ∫ x, (𝓕⁻ G) x • (hf2.toLp f : E3 → C3) x := by
    rw [← Lp.toTemperedDistribution_apply, hv_def, ← Lp.fourierInv_toTemperedDistribution_eq,
      TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  have hL3 : ∫ x, (𝓕⁻ G) x • (hf2.toLp f : E3 → C3) x = ∫ x, (𝓕⁻ (G : E3 → ℂ)) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.fourierInv_coe]
  -- lado direito: fórmula de multiplicação
  have hR : ∫ x, g x • 𝓕⁻ f x = ∫ x, (𝓕⁻ (G : E3 → ℂ)) x • f x := by
    rw [← integral_smul_fourierInv hGint hf1]
    congr 1 with x
  rw [hL, hL2, hL3, hR]

/-- `‖u‖² = ∫ ‖u x‖²` para `u ∈ L²(ℝ³, ℂ³)`. -/
theorem norm_sq_eq_integral (u : Lp C3 2 (volume : Measure E3)) :
    ‖u‖ ^ 2 = ∫ x, ‖(u : E3 → C3) x‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  have h1 : (Complex.ofRealLI (‖u‖ ^ 2) : ℂ) = ⟪u, u⟫_ℂ := by
    simp [inner_self_eq_norm_sq_to_K]
  have h2 : (Complex.ofRealLI (∫ x, ‖(u : E3 → C3) x‖ ^ 2) : ℂ) =
      ∫ x, ⟪(u : E3 → C3) x, (u : E3 → C3) x⟫_ℂ := by
    rw [← LinearIsometry.integral_comp_comm]
    simp [inner_self_eq_norm_sq_to_K]
  rw [h1, h2, MeasureTheory.L2.inner_def]

theorem norm_fourierInv_Lp (u : Lp C3 2 (volume : Measure E3)) : ‖𝓕⁻ u‖ = ‖u‖ := by
  rw [← Lp.norm_fourier_eq, FourierTransform.fourier_fourierInv_eq]

/-- `𝓕⁻ f ∈ L²` para `f ∈ L¹ ∩ L²`. -/
theorem memLp_two_fourierInv (hf1 : Integrable f) (hf2 : MemLp f 2) : MemLp (𝓕⁻ f) 2 :=
  (Lp.memLp _).ae_eq (fourierInv_toLp_ae_eq hf1 hf2)

/-- **Plancherel**: `∫ ‖𝓕⁻ f x‖² dx = ∫ ‖f ξ‖² dξ` para `f ∈ L¹ ∩ L²`. -/
theorem integral_norm_sq_fourierInv (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ x, ‖𝓕⁻ f x‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  have h1 : ∫ x, ‖𝓕⁻ f x‖ ^ 2 =
      ∫ x, ‖((𝓕⁻ (hf2.toLp f) : Lp C3 2 (volume : Measure E3)) : E3 → C3) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [fourierInv_toLp_ae_eq hf1 hf2] with x h
    rw [h]
  have h2 : ∫ ξ, ‖f ξ‖ ^ 2 = ∫ ξ, ‖(hf2.toLp f : E3 → C3) ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x h
    rw [h]
  rw [h1, h2, ← norm_sq_eq_integral, ← norm_sq_eq_integral, norm_fourierInv_Lp]

/-! ### Para as amplitudes de decaimento rápido -/

theorem memLp_two_of_bound {g : E3 → C3} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hC : ∀ ξ, ‖g ξ‖ ≤ C * (w 4 ξ)⁻¹) : MemLp g 2 := by
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC 0))
    (inv_pos.mpr (w_pos 4 0))
  rw [memLp_two_iff_integrable_sq_norm hg]
  refine (integrable_w_inv.const_mul (C * C)).mono' (hg.norm.pow 2) (Eventually.of_forall
    fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := hC ξ
  have h2 : C * (w 4 ξ)⁻¹ ≤ C := mul_le_of_le_one_right hC0 (inv_le_one_of_one_le₀ (one_le_w 4 ξ))
  calc ‖g ξ‖ ^ 2 = ‖g ξ‖ * ‖g ξ‖ := sq _
    _ ≤ C * (C * (w 4 ξ)⁻¹) :=
        mul_le_mul (h1.trans h2) h1 (norm_nonneg _) hC0
    _ = C * C * (w 4 ξ)⁻¹ := by ring

theorem integrable_of_bound {g : E3 → C3} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hC : ∀ ξ, ‖g ξ‖ ≤ C * (w 4 ξ)⁻¹) : Integrable g :=
  (integrable_w_inv.const_mul C).mono' hg (Eventually.of_forall hC)

/-- **Plancherel para `V`**: `∫ ‖V[g](x)‖² dx = ∫ ‖g(ξ)‖² dξ`, e `‖V[g]‖²` é integrável. -/
theorem integral_norm_sq_Vf {g : E3 → C3} (hg : AEStronglyMeasurable g) {C : ℝ}
    (hC : ∀ ξ, ‖g ξ‖ ≤ C * (w 4 ξ)⁻¹) :
    Integrable (fun x => ‖Vf g x‖ ^ 2) ∧ ∫ x, ‖Vf g x‖ ^ 2 = ∫ ξ, ‖g ξ‖ ^ 2 := by
  have h1 := integrable_of_bound hg hC
  have h2 := memLp_two_of_bound hg hC
  have e : (fun x => Vf g x) = 𝓕⁻ g := funext fun x => Vf_eq_fourierInv g x
  refine ⟨?_, ?_⟩
  · have hm := memLp_two_fourierInv h1 h2
    rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable] at hm
    simpa only [e] using hm
  · simp only [e]
    exact integral_norm_sq_fourierInv h1 h2

end ATK.NSPlancherel

#print axioms ATK.NSPlancherel.Vf_eq_fourierInv
#print axioms ATK.NSPlancherel.neg_innerₗ_flip
#print axioms ATK.NSPlancherel.fourierInv_eq_vector
#print axioms ATK.NSPlancherel.fourierInv_eq_vector_scalar
#print axioms ATK.NSPlancherel.continuous_neg_inner
#print axioms ATK.NSPlancherel.continuous_fourierInv
#print axioms ATK.NSPlancherel.integral_smul_fourierInv
#print axioms ATK.NSPlancherel.fourierInv_toLp_ae_eq
#print axioms ATK.NSPlancherel.norm_sq_eq_integral
#print axioms ATK.NSPlancherel.norm_fourierInv_Lp
#print axioms ATK.NSPlancherel.memLp_two_fourierInv
#print axioms ATK.NSPlancherel.integral_norm_sq_fourierInv
#print axioms ATK.NSPlancherel.memLp_two_of_bound
#print axioms ATK.NSPlancherel.integrable_of_bound
#print axioms ATK.NSPlancherel.integral_norm_sq_Vf
