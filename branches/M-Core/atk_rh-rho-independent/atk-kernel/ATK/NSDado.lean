import ATK.NSFisico
import ATK.NSMild
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# ATK — Navier–Stokes: o dado inicial no lado de Fourier

Camada 7 do ataque a B3. Para `u₀` de Schwartz em `ℝ³` com `div u₀ = 0` (o dado admissível do
modelo genuíno `ATK.LigacaoNS.modeloNS`), a transformada `â₀ = 𝓕(u₀)` (da Mathlib, em `ℂ³`):

* é contínua com **todas** as cotas `‖â₀(ξ)‖ ≤ C_m (1 + ‖ξ‖)^{−m}` (`ahat_bound`, seminormas de
  Schwartz da transformada);
* tem **divergência nula** `⟪ξ, â₀(ξ)⟫ = 0` (`ahat_div`, transformada da derivada);
* é **hermitiana** (`ahat_herm`: `u₀` é real);
* **reconstrói `u₀`** (`Vf_ahat`: `∫ e^{2πi⟪ξ,x⟫} â₀(ξ) dξ = u₀(x)`, inversão de Fourier).

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology ComplexConjugate FourierTransform
open scoped Real

namespace ATK.NSDado

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSSimetria ATK.NSFisico ATK.NSMild

/-- `cpx` como aplicação `ℝ`-linear contínua. -/
noncomputable def cpxL : E3 →L[ℝ] C3 :=
  LinearMap.mkContinuous
    { toFun := cpx
      map_add' := fun x y => by ext k; simp [cpx]
      map_smul' := fun r x => by ext k; simp [cpx, Complex.real_smul] }
    1 (fun x => by simp [norm_cpx])

theorem cpxL_apply (x : E3) : cpxL x = cpx x := rfl

/-- O dado complexificado `ũ₀ = cpx ∘ u₀`, de Schwartz. -/
noncomputable def uc (u₀ : SchwartzMap E3 E3) : SchwartzMap E3 C3 :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) cpxL u₀

theorem uc_apply (u₀ : SchwartzMap E3 E3) (x : E3) : uc u₀ x = cpx (u₀ x) := rfl

/-- A transformada de Fourier do dado, `â₀ = 𝓕 ũ₀`. -/
noncomputable def ahat (u₀ : SchwartzMap E3 E3) : E3 → C3 := 𝓕 (uc u₀ : E3 → C3)

theorem ahat_eq (u₀ : SchwartzMap E3 E3) : ahat u₀ = ⇑(𝓕 (uc u₀) : SchwartzMap E3 C3) := rfl

theorem ahat_cont (u₀ : SchwartzMap E3 E3) : Continuous (ahat u₀) := by
  rw [ahat_eq]; exact (𝓕 (uc u₀) : SchwartzMap E3 C3).continuous

/-- **Decaimento rápido** de `â₀`. -/
theorem ahat_bound (u₀ : SchwartzMap E3 E3) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ ξ, ‖ahat u₀ ξ‖ ≤ C * (w m ξ)⁻¹ := by
  set f : SchwartzMap E3 C3 := 𝓕 (uc u₀)
  set C := 2 ^ m * (Finset.Iic (m, 0)).sup (fun q => SchwartzMap.seminorm ℝ q.1 q.2) f
  refine ⟨C, by positivity, fun ξ => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0)
    le_rfl le_rfl f ξ
  rw [norm_iteratedFDeriv_zero] at h
  rw [ahat_eq, ← div_eq_mul_inv, le_div_iff₀ (w_pos m ξ), mul_comm]
  exact h

theorem ahat_dado (u₀ : SchwartzMap E3 E3) : ∃ M, Dado (ahat u₀) M := by
  obtain ⟨C, -, hC⟩ := ahat_bound u₀ 4
  exact ⟨C, ahat_cont u₀, hC⟩

/-- **Inversão**: `∫ e^{2πi⟪ξ, x⟫} â₀(ξ) dξ = cpx(u₀ x)`. -/
theorem Vf_ahat (u₀ : SchwartzMap E3 E3) (x : E3) : Vf (ahat u₀) x = cpx (u₀ x) := by
  have hinv := Continuous.fourierInv_fourier_eq (uc u₀).continuous (uc u₀).integrable
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 (uc u₀) : SchwartzMap E3 C3).integrable)
  have h := congrFun hinv x
  rw [Real.fourierInv_eq'] at h
  rw [← uc_apply, ← h]
  rfl

/-- **Simetria hermitiana** de `â₀` (o dado é real). -/
theorem ahat_herm (u₀ : SchwartzMap E3 E3) : Herm (ahat u₀) := by
  intro ξ
  unfold ahat
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_cj3]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [cj3_smul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, uc_apply]
  have hr : cj3 (cpx (u₀ v)) = cpx (u₀ v) := by ext k; simp [cpx]
  rw [hr, inner_neg_right]
  congr 2
  push_cast
  ring

/-- **Divergência nula no lado de Fourier**: `⟪ξ, â₀(ξ)⟫ = 0`. -/
theorem ahat_div (u₀ : SchwartzMap E3 E3) (hdiv : ∀ x, div u₀ x = 0) (ξ : E3) :
    inner ℂ (cpx ξ) (ahat u₀ ξ) = 0 := by
  set g : E3 → C3 := ⇑(uc u₀) with hg
  have hg_int : Integrable g := (uc u₀).integrable
  have hg_diff : Differentiable ℝ g := (uc u₀).differentiable
  have hfd : ∀ x, fderiv ℝ g x = cpxL.comp (fderiv ℝ u₀ x) := by
    intro x
    have h1 : HasFDerivAt g (cpxL.comp (fderiv ℝ u₀ x)) x :=
      cpxL.hasFDerivAt.comp x (u₀.differentiableAt.hasFDerivAt)
    exact h1.fderiv
  have hgd_int : Integrable (fderiv ℝ g) := by
    have := (SchwartzMap.fderivCLM ℝ E3 C3 (uc u₀)).integrable (μ := volume)
    have e : (⇑(SchwartzMap.fderivCLM ℝ E3 C3 (uc u₀)) : E3 → E3 →L[ℝ] C3) = fderiv ℝ g := by
      funext x; rfl
    rw [← e]; exact this
  have hF := Real.fourier_fderiv hg_int hg_diff hgd_int
  -- avaliação `F ↦ Σ_j (F e_j)_j`
  set Φ : (E3 →L[ℝ] C3) →L[ℝ] ℂ :=
    ∑ j : Fin 3, ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).restrictScalars ℝ).comp
      (ContinuousLinearMap.apply ℝ C3 (e j)) with hΦ
  have hΦapp : ∀ F : E3 →L[ℝ] C3, Φ F = ∑ j, F (e j) j := by
    intro F
    simp [hΦ]
  -- `Φ` aplicado à derivada é a divergência (nula)
  have hdivx : ∀ x, Φ (fderiv ℝ g x) = 0 := by
    intro x
    rw [hΦapp, hfd]
    have : ∑ j, (cpxL.comp (fderiv ℝ u₀ x)) (e j) j = ((div u₀ x : ℝ) : ℂ) := by
      simp only [ContinuousLinearMap.comp_apply, cpxL_apply, div, dX]
      push_cast
      simp [cpx]
    rw [this, hdiv x, Complex.ofReal_zero]
  have hΦsmul : ∀ (c : ℂ) (F : E3 →L[ℝ] C3), Φ (c • F) = c * Φ F := by
    intro c F
    rw [hΦapp, hΦapp, Finset.mul_sum]
    simp [PiLp.smul_apply, smul_eq_mul]
  -- lado esquerdo: `Φ(𝓕(Dg)(ξ)) = 0`
  have hL : Φ (𝓕 (fderiv ℝ g) ξ) = 0 := by
    rw [Real.fourier_eq]
    have hint : Integrable fun v => 𝐞 (-inner ℝ v ξ) • fderiv ℝ g v :=
      (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ E3) (by simpa using continuous_inner) ξ).mpr hgd_int
    rw [← Φ.integral_comp_comm hint]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun v => ?_)
    simp only [Pi.zero_apply]
    rw [Circle.smul_def, hΦsmul, hdivx v, mul_zero]
  -- lado direito: `Φ(𝓕(Dg)(ξ)) = 2πi ⟪ξ, â₀(ξ)⟫`
  have hR : Φ (𝓕 (fderiv ℝ g) ξ) =
      ((2 * π : ℝ) * Complex.I : ℂ) * inner ℂ (cpx ξ) (ahat u₀ ξ) := by
    rw [hF, hΦapp, inner_cpx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [VectorFourier.fourierSMulRight_apply, ContinuousLinearMap.neg_apply,
      innerSL_apply_apply, PiLp.smul_apply, smul_eq_mul, e, EuclideanSpace.inner_single_right]
    simp only [Complex.real_smul, PiLp.smul_apply, smul_eq_mul, map_one, one_mul]
    rw [show ahat u₀ = 𝓕 g from rfl]
    have hin : ((innerSL ℝ) ξ) (EuclideanSpace.single j (1 : ℝ)) = ξ j := by
      rw [innerSL_apply_apply ℝ, EuclideanSpace.inner_single_right]; simp
    rw [hin]
    push_cast
    ring
  rw [hR] at hL
  rcases mul_eq_zero.mp hL with h | h
  · exfalso
    have h2 : ((2 * π : ℝ) : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)) Complex.I_ne_zero
    exact h2 h
  · exact h

end ATK.NSDado

#print axioms ATK.NSDado.cpxL_apply
#print axioms ATK.NSDado.uc_apply
#print axioms ATK.NSDado.ahat_eq
#print axioms ATK.NSDado.ahat_cont
#print axioms ATK.NSDado.ahat_bound
#print axioms ATK.NSDado.ahat_dado
#print axioms ATK.NSDado.Vf_ahat
#print axioms ATK.NSDado.ahat_herm
#print axioms ATK.NSDado.ahat_div
