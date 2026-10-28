import ATK.NSEquacao
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# ATK — Navier–Stokes, marco NS5a: Plancherel para campos `ℝ³ → ℂ³` em `L¹ ∩ L²`

Ponte B3. Generaliza `ATK.PlancherelL1L2` (reta, escalar) para `f : ℝ³ → ℂ³`:

* `fourier_toLp_ae_eq`: o `𝓕` de `L²` coincide q.t.p. com a integral de Fourier;
* **`integral_norm_sq_fourier`**: `∫ ‖𝓕 f‖² = ∫ ‖f‖²`, e `𝓕 f ∈ L²`;
* **`integral_norm_sq_fourierInv`**: o mesmo para `𝓕⁻`.

Prova: as duas funções têm a mesma ação contra toda função teste suave de suporte compacto
(fórmula de multiplicação e `Lp.fourier_toTemperedDistribution_eq`), logo coincidem q.t.p.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory FourierTransform SchwartzMap Real
open scoped ContDiff InnerProductSpace
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSFisico ATK.NSCampos ATK.NSEquacao
open Set

namespace ATK.NSPlancherel

variable {f : E3 → C3}

theorem continuous_fourier (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-- Fórmula de multiplicação: `∫ (𝓕 G) • f = ∫ G • 𝓕 f`. -/
theorem integral_fourier_smul (hf : Integrable f) {G : E3 → ℂ} (hG : Integrable G) :
    ∫ x, (𝓕 G) x • f x = ∫ ξ, G ξ • 𝓕 f ξ := by
  have hflip : (innerₗ E3 : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ).flip = innerₗ E3 := by
    ext
    simp
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (e := Real.fourierChar) (L := innerₗ E3) Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hG hf
  rw [hflip] at this
  exact this

/-- **O `𝓕` de `L²` concorda q.t.p. com a integral de Fourier** para `f ∈ L¹ ∩ L²`. -/
theorem fourier_toLp_ae_eq (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ((𝓕 (hf2.toLp f) : Lp C3 2 (volume : Measure E3)) : E3 → C3) =ᵐ[volume] 𝓕 f := by
  set v : Lp C3 2 (volume : Measure E3) := 𝓕 (hf2.toLp f) with hv_def
  have hv : LocallyIntegrable (v : E3 → C3) volume :=
    (Lp.memLp v).locallyIntegrable (by norm_num)
  have hF : LocallyIntegrable (𝓕 f) volume := (continuous_fourier hf1).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hv hF ?_
  intro g hg hgs
  set gc : E3 → ℂ := fun x => (g x : ℂ) with hgc
  have hgc_smooth : ContDiff ℝ ∞ gc := Complex.ofRealCLM.contDiff.comp hg
  have hgc_supp : HasCompactSupport gc := hgs.comp_left Complex.ofReal_zero
  set G : 𝓢(E3, ℂ) := hgc_supp.toSchwartzMap hgc_smooth with hG
  have hGx : ∀ x, G x = gc x := fun x => rfl
  have hGint : Integrable (G : E3 → ℂ) := G.integrable
  have hL : ∫ x, g x • (v : E3 → C3) x = ∫ x, G x • (v : E3 → C3) x := by
    congr 1 with x
  have hL2 : ∫ x, G x • (v : E3 → C3) x =
      ∫ x, (𝓕 G) x • (hf2.toLp f : E3 → C3) x := by
    rw [← Lp.toTemperedDistribution_apply, hv_def, ← Lp.fourier_toTemperedDistribution_eq,
      TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  have hL3 : ∫ x, (𝓕 G) x • (hf2.toLp f : E3 → C3) x = ∫ x, (𝓕 (G : E3 → ℂ)) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.fourier_coe]
  have hR : ∫ x, g x • 𝓕 f x = ∫ x, (𝓕 (G : E3 → ℂ)) x • f x := by
    rw [integral_fourier_smul hf1 hGint]
    congr 1 with x
  rw [hL, hL2, hL3, hR]

/-- `𝓕 f ∈ L²` para `f ∈ L¹ ∩ L²`. -/
theorem memLp_two_fourier (hf1 : Integrable f) (hf2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (Lp.memLp _).ae_eq (fourier_toLp_ae_eq hf1 hf2)

/-- `‖u‖² = ∫ ‖u x‖²` para `u ∈ L²`. -/
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

/-- **Plancherel**: `∫ ‖𝓕 f ξ‖² dξ = ∫ ‖f x‖² dx` para `f ∈ L¹ ∩ L²`. -/
theorem integral_norm_sq_fourier (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h1 : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 =
      ∫ ξ, ‖((𝓕 (hf2.toLp f) : Lp C3 2 (volume : Measure E3)) : E3 → C3) ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [fourier_toLp_ae_eq hf1 hf2] with ξ h
    rw [h]
  have h2 : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖(hf2.toLp f : E3 → C3) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x h
    rw [h]
  rw [h1, h2, ← norm_sq_eq_integral, ← norm_sq_eq_integral, Lp.norm_fourier_eq]

theorem integrable_norm_sq_fourier (hf1 : Integrable f) (hf2 : MemLp f 2) :
    Integrable fun ξ => ‖𝓕 f ξ‖ ^ 2 :=
  (memLp_two_fourier hf1 hf2).integrable_norm_pow (by norm_num)

/-- **Plancherel para `𝓕⁻`.** -/
theorem integral_norm_sq_fourierInv (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ x, ‖𝓕⁻ f x‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  simp_rw [Real.fourierInv_eq_fourier_neg]
  rw [integral_neg_eq_self (fun x => ‖𝓕 f x‖ ^ 2), integral_norm_sq_fourier hf1 hf2]

theorem integrable_norm_sq_fourierInv (hf1 : Integrable f) (hf2 : MemLp f 2) :
    Integrable fun x => ‖𝓕⁻ f x‖ ^ 2 := by
  simp_rw [Real.fourierInv_eq_fourier_neg]
  exact (integrable_norm_sq_fourier hf1 hf2).comp_neg

/-! ### Energia e enstrofia dos campos físicos -/

theorem memLp_slice {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) {t : ℝ} (ht : t ∈ Icc 0 T) :
    MemLp (fun ξ => V (ξ, t)) 2 := by
  obtain ⟨C, hC⟩ := hV.2 4
  have hC0 : 0 ≤ C := (hC t ht).nonneg
  rw [memLp_two_iff_integrable_sq_norm (hV.1 t ht).aestronglyMeasurable]
  refine ((integrable_inv_pow (m := 4) le_rfl).const_mul (C * C)).mono'
    ((hV.1 t ht).norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := (hC t ht).le_inv ξ
  have h2 := (hC t ht).le ξ
  have hinv : 0 ≤ ((1 + ‖ξ‖) ^ 4)⁻¹ := by positivity
  calc ‖V (ξ, t)‖ ^ 2 = ‖V (ξ, t)‖ * ‖V (ξ, t)‖ := sq _
    _ ≤ C * (C * ((1 + ‖ξ‖) ^ 4)⁻¹) := mul_le_mul h2 h1 (norm_nonneg _) hC0
    _ = C * C * ((1 + ‖ξ‖) ^ 4)⁻¹ := by ring

/-- **Plancherel para `Fi`**: `∫ ‖Fi V (x, t)‖² dx = ∫ ‖V(ξ, t)‖² dξ`. -/
theorem energia_Fi {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x => ‖Fi V (x, t)‖ ^ 2) ∧
      ∫ x, ‖Fi V (x, t)‖ ^ 2 = ∫ ξ, ‖V (ξ, t)‖ ^ 2 := by
  have h1 := integrable_slice hV ht
  have h2 := memLp_slice hV ht
  simp_rw [Fi_eq_fourierInv_xt]
  exact ⟨integrable_norm_sq_fourierInv h1 h2, integral_norm_sq_fourierInv h1 h2⟩

theorem norm_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (z : E3 × ℝ) :
    ‖Ufis v z‖ = ‖Fi v z‖ := by
  rw [← h.cx_Ufis z, norm_cx]

/-- **A energia** da velocidade física é a do lado de Fourier. -/
theorem energia_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x => ‖Ufis v (x, t)‖ ^ 2) ∧
      ∫ x, ‖Ufis v (x, t)‖ ^ 2 = ∫ ξ, ‖v (ξ, t)‖ ^ 2 := by
  simp_rw [norm_Ufis h]
  exact energia_Fi h.reg0 ht

theorem herm_mj {V : E3 × ℝ → C3} (hV : ∀ ξ t, V (-ξ, t) = cj (V (ξ, t))) (j : Fin 3) :
    ∀ ξ t, mj j (-ξ) • V (-ξ, t) = cj (mj j ξ • V (ξ, t)) := by
  intro ξ t
  rw [hV, cj_smul]
  congr 1
  simp [mj, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]

/-- `‖∂_j U‖ = ‖Fi(2πiξ_j v)‖` (o campo derivado também é real). -/
theorem norm_dX_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (j : Fin 3) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ‖ATK.LigacaoNS.dX j (ATK.LigacaoNS.fatia (Ufis v) t) x‖ =
      ‖Fi (fun q => mj j q.1 • v q) (x, t)‖ := by
  rw [dX_Ufis h.reg0 (Suave.reg0 (h.suave_dv 0)) h.deq j x ht]
  have hr := cx_reV (cj_Fi (V := fun q => mj j q.1 • v q)
    (fun ξ t => herm_mj h.herm j ξ t) (x, t))
  rw [← hr, norm_cx, hr]

/-- **A enstrofia** `∫ |∇U|² = 4π² ∫ |ξ|² ‖v‖²`. -/
theorem enstrofia_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    Integrable (ATK.LigacaoNS.gradSq (ATK.LigacaoNS.fatia (Ufis v) t)) ∧
      ∫ x, ATK.LigacaoNS.gradSq (ATK.LigacaoNS.fatia (Ufis v) t) x =
        ∫ ξ, 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2 := by
  have hj : ∀ j : Fin 3, Integrable (fun x => ‖Fi (fun q => mj j q.1 • v q) (x, t)‖ ^ 2) ∧
      ∫ x, ‖Fi (fun q => mj j q.1 • v q) (x, t)‖ ^ 2 = ∫ ξ, ‖mj j ξ • v (ξ, t)‖ ^ 2 :=
    fun j => energia_Fi (Reg0.mj h.reg0 j) ht
  have hg : ATK.LigacaoNS.gradSq (ATK.LigacaoNS.fatia (Ufis v) t) =
      fun x => ∑ j : Fin 3, ‖Fi (fun q => mj j q.1 • v q) (x, t)‖ ^ 2 := by
    funext x
    unfold ATK.LigacaoNS.gradSq
    simp_rw [norm_dX_Ufis h _ x ht]
  rw [hg]
  refine ⟨integrable_finsetSum _ fun j _ => (hj j).1, ?_⟩
  rw [integral_finsetSum _ fun j _ => (hj j).1]
  simp_rw [fun j => (hj j).2]
  have hint : ∀ j : Fin 3, Integrable fun ξ => ‖mj j ξ • v (ξ, t)‖ ^ 2 := fun j => by
    have := memLp_slice (Reg0.mj h.reg0 j) ht
    exact this.integrable_norm_pow (by norm_num)
  rw [← integral_finsetSum _ fun j _ => hint j]
  congr 1
  funext ξ
  simp only [norm_smul, mul_pow]
  rw [← Finset.sum_mul]
  congr 1
  have hn : ∑ j : Fin 3, ‖mj j ξ‖ ^ 2 = 4 * π ^ 2 * ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : mj j ξ = ((2 * π * ξ j : ℝ) : ℂ) * Complex.I := by
      unfold mj
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.norm_eq_abs, sq_abs]
    ring
  exact hn

end ATK.NSPlancherel

#print axioms ATK.NSPlancherel.continuous_fourier
#print axioms ATK.NSPlancherel.integral_fourier_smul
#print axioms ATK.NSPlancherel.fourier_toLp_ae_eq
#print axioms ATK.NSPlancherel.memLp_two_fourier
#print axioms ATK.NSPlancherel.norm_sq_eq_integral
#print axioms ATK.NSPlancherel.integral_norm_sq_fourier
#print axioms ATK.NSPlancherel.integrable_norm_sq_fourier
#print axioms ATK.NSPlancherel.integral_norm_sq_fourierInv
#print axioms ATK.NSPlancherel.integrable_norm_sq_fourierInv
#print axioms ATK.NSPlancherel.memLp_slice
#print axioms ATK.NSPlancherel.energia_Fi
#print axioms ATK.NSPlancherel.norm_Ufis
#print axioms ATK.NSPlancherel.energia_Ufis
#print axioms ATK.NSPlancherel.herm_mj
#print axioms ATK.NSPlancherel.norm_dX_Ufis
#print axioms ATK.NSPlancherel.enstrofia_Ufis
