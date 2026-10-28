import ATK.NSCampos

/-!
# ATK — Navier–Stokes, marco NS4b (parte 2): os campos físicos e a equação ponto a ponto

Ponte B3. Para `u₀ ∈ 𝓢(ℝ³, ℝ³)` de divergência nula:

* `v₀ = 𝓕 u₀` (complexificado) é contínuo, tem cotas de todos os pesos (`cota_v0`), divergência
  nula no lado de Fourier (`ip_v0`) e simetria hermitiana (`herm_v0`); inversão `𝓕⁻ v₀ = u₀`;
* `dadoNS ν u₀`: o `NSPicard.Dado` com `c = 4π²ν`;
* para a solução de Fourier `v` (`SolF`), a velocidade `Ufis v = Re 𝓕⁻ v` e a pressão
  `Pfis v = 𝓕⁻(ξ·Ñ(v,v)/(2πi|ξ|²))` (com o símbolo singular `LP`):
  - **`contDiffOn_Ufis`, `contDiffOn_Pfis`**: `C^∞` em `ℝ³ × [0, T]`;
  - **`NSEq_fis`**: `∂ₜU + (U·∇)U = νΔU − ∇P` ponto a ponto em `(0, T)` (lado de Fourier:
    `∂ₜv = −c|ξ|²v + 𝐏Ñ`, `(U·∇)U ↔ −Ñ` pela convolução e `ξ·v = 0`, `∇P ↔ Ñ − 𝐏Ñ`);
  - **`div_Ufis`**: `div U = 0`; **`Ufis_zero`**: `U(x, 0) = u₀(x)`.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Filter Topology Set SchwartzMap
open scoped ContDiff Convolution
open FourierTransform
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSFisico ATK.NSCampos

namespace ATK.NSEquacao

/-! ### Complexificação -/

/-- `cx` como aplicação `ℝ`-linear contínua. -/
noncomputable def cxL : E3 →L[ℝ] C3 :=
  LinearMap.toContinuousLinearMap
    { toFun := cx
      map_add' := fun a b => by ext j; simp
      map_smul' := fun r a => by ext j; simp [Complex.real_smul] }

theorem cxL_apply (a : E3) : cxL a = cx a := rfl

theorem reV_cx (a : E3) : reV (cx a) = a := by
  ext j
  simp

/-- O dado complexificado, como função de Schwartz. -/
noncomputable def u0c (u₀ : 𝓢(E3, E3)) : 𝓢(E3, C3) := SchwartzMap.postcompCLM cxL u₀

theorem u0c_apply (u₀ : 𝓢(E3, E3)) (x : E3) : u0c u₀ x = cx (u₀ x) := rfl

/-- `v₀ = 𝓕 u₀` (função de Schwartz). -/
noncomputable def v0S (u₀ : 𝓢(E3, E3)) : 𝓢(E3, C3) := 𝓕 (u0c u₀)

theorem v0S_eq (u₀ : 𝓢(E3, E3)) : ⇑(v0S u₀) = 𝓕 ⇑(u0c u₀) := fourier_coe _

/-! ### Cotas de todos os pesos -/

theorem cota_schwartz (f : 𝓢(E3, C3)) (m : ℕ) : ∃ M, Cota m M f := by
  refine ⟨2 ^ m * ((Finset.Iic (m, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f,
    fun ζ => ?_⟩
  have := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0) le_rfl le_rfl f ζ
  rw [norm_iteratedFDeriv_zero] at this
  linarith [mul_comm (‖f ζ‖) ((1 + ‖ζ‖) ^ m)]

theorem cota_v0 (u₀ : 𝓢(E3, E3)) (m : ℕ) : ∃ M, Cota m M (v0S u₀) := cota_schwartz _ m

/-! ### Simetria hermitiana -/

theorem herm_v0 (u₀ : 𝓢(E3, E3)) (ξ : E3) : v0S u₀ (-ξ) = cj (v0S u₀ ξ) := by
  rw [v0S_eq, Real.fourier_eq, Real.fourier_eq, ← cj_integral]
  congr 1
  funext x
  rw [Circle.smul_def, Circle.smul_def, cj_smul, u0c_apply, cj_cx, inner_neg_right, neg_neg]
  congr 1
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-! ### Divergência nula no lado de Fourier -/

theorem proj_integral {f : E3 → C3} (hf : Integrable f) (j : Fin 3) :
    (∫ x, f x) j = ∫ x, f x j := by
  have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).integral_comp_comm hf
  simpa using this.symm

theorem lineDeriv_u0c (u₀ : 𝓢(E3, E3)) (j : Fin 3) (x : E3) :
    LineDeriv.lineDerivOp (ATK.LigacaoNS.e j) (u0c u₀) x =
      cx (fderiv ℝ u₀ x (ATK.LigacaoNS.e j)) := by
  rw [lineDerivOp_apply_eq_fderiv]
  have h : HasFDerivAt (fun y => cxL (u₀ y)) (cxL.comp (fderiv ℝ u₀ x)) x :=
    cxL.hasFDerivAt.comp x (u₀.differentiableAt.hasFDerivAt)
  have he : ⇑(u0c u₀) = fun y => cxL (u₀ y) := rfl
  rw [he, h.fderiv]
  rfl

/-- **`ξ · v₀(ξ) = 0`** se `div u₀ = 0`. -/
theorem ip_v0 (u₀ : 𝓢(E3, E3)) (hdiv : ∀ x, ATK.LigacaoNS.div u₀ x = 0) (ξ : E3) :
    ip ξ (v0S u₀ ξ) = 0 := by
  have hj : ∀ j : Fin 3, 𝓕 (⇑(LineDeriv.lineDerivOp (ATK.LigacaoNS.e j) (u0c u₀))) ξ =
      (2 * (π : ℂ) * Complex.I) • ((ξ j : ℂ) • v0S u₀ ξ) := by
    intro j
    have ht : (fun x : E3 => inner ℝ x (ATK.LigacaoNS.e j)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (ATK.LigacaoNS.e j)).hasTemperateGrowth
    have h := fourier_lineDerivOp_eq (u0c u₀) (ATK.LigacaoNS.e j)
    have h' : (𝓕 (LineDeriv.lineDerivOp (ATK.LigacaoNS.e j) (u0c u₀))) ξ =
        ((2 * (π : ℂ) * Complex.I) • smulLeftCLM C3 (fun x => inner ℝ x (ATK.LigacaoNS.e j))
          (𝓕 (u0c u₀))) ξ := by rw [h]
    rw [← fourier_coe, h', smul_apply, smulLeftCLM_apply ht]
    beta_reduce
    rw [inner_e, ← Complex.coe_smul]
    rfl
  -- somamos as coordenadas `j`
  set g : Fin 3 → E3 → C3 := fun j => ⇑(LineDeriv.lineDerivOp (ATK.LigacaoNS.e j) (u0c u₀))
  have hint : ∀ j : Fin 3, Integrable fun x => 𝐞 (-inner ℝ x ξ) • g j x := fun j =>
    (Real.fourierIntegral_convergent_iff ξ).mpr (SchwartzMap.integrable _)
  have hint' : ∀ j : Fin 3, Integrable fun x => (𝐞 (-inner ℝ x ξ) • g j x) j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).integrable_comp (hint j)
  have hsum : ∑ j : Fin 3, (𝓕 (g j) ξ) j = 0 := by
    simp_rw [Real.fourier_eq]
    rw [Finset.sum_congr rfl fun j _ => proj_integral (hint j) j,
      ← integral_finsetSum _ (fun j _ => hint' j)]
    have h0 : ∀ x, ∑ j : Fin 3, (𝐞 (-inner ℝ x ξ) • g j x) j = 0 := by
      intro x
      simp only [g, Circle.smul_def, PiLp.smul_apply, lineDeriv_u0c, cx_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      have h1 := hdiv x
      unfold ATK.LigacaoNS.div ATK.LigacaoNS.dX at h1
      have h2 : ∑ j : Fin 3, ((((fderiv ℝ (⇑u₀) x) (ATK.LigacaoNS.e j)) j : ℝ) : ℂ) = 0 := by
        exact_mod_cast h1
      rw [h2, mul_zero]
    simp [h0]
  have hcomp : ∑ j : Fin 3, (𝓕 (g j) ξ) j = (2 * (π : ℂ) * Complex.I) * ip ξ (v0S u₀ ξ) := by
    simp only [g, hj, PiLp.smul_apply, smul_eq_mul, ip, Finset.mul_sum]
  rw [hcomp] at hsum
  have hne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    simp [this, Complex.I_ne_zero]
  exact (mul_eq_zero.mp hsum).resolve_left hne

/-! ### Inversão e o dado -/

theorem integrable_v0 (u₀ : 𝓢(E3, E3)) : Integrable (𝓕 ⇑(u0c u₀)) := by
  rw [← v0S_eq]
  exact (v0S u₀).integrable

/-- **Inversão de Fourier**: `𝓕⁻ v₀ = u₀` (complexificado). -/
theorem fourierInv_v0 (u₀ : 𝓢(E3, E3)) (x : E3) : 𝓕⁻ (⇑(v0S u₀)) x = cx (u₀ x) := by
  rw [v0S_eq, (u0c u₀).continuous.fourierInv_fourier_eq (u0c u₀).integrable (integrable_v0 u₀)]
  rfl

/-- O dado de Fourier do problema de Navier–Stokes com viscosidade `ν` (`c = 4π²ν`). -/
noncomputable def dadoNS (ν : ℝ) (hν : 0 < ν) (u₀ : 𝓢(E3, E3)) : Dado where
  c := 4 * π ^ 2 * ν
  hc := by positivity
  v₀ := v0S u₀
  cont := (v0S u₀).continuous
  M₀ := Classical.choose (cota_v0 u₀ 4)
  cota := Classical.choose_spec (cota_v0 u₀ 4)

theorem dadoNS_c (ν : ℝ) (hν : 0 < ν) (u₀ : 𝓢(E3, E3)) :
    (dadoNS ν hν u₀).c = 4 * π ^ 2 * ν := rfl

theorem dadoNS_v₀ (ν : ℝ) (hν : 0 < ν) (u₀ : 𝓢(E3, E3)) :
    (dadoNS ν hν u₀).v₀ = v0S u₀ := rfl

/-! ### Álgebra de `Fi` -/

theorem integrable_Fi {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) : Integrable fun ξ => ex ξ x • V (ξ, t) := by
  have := integrable_integrand aesm_idL idL_bound hV x ht
  simpa using this

theorem integrable_slice {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) {t : ℝ}
    (ht : t ∈ Icc 0 T) : Integrable fun ξ => V (ξ, t) := by
  obtain ⟨C, hC⟩ := hV.2 4
  exact ((integrable_inv_pow (m := 4) le_rfl).const_mul C).mono'
    (hV.1 t ht).aestronglyMeasurable (Eventually.of_forall fun ξ => (hC t ht).le_inv ξ)

theorem Fi_add {T : ℝ} {V V' : E3 × ℝ → C3} (hV : Reg0 T V) (hV' : Reg0 T V') (x : E3)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Fi (V + V') (x, t) = Fi V (x, t) + Fi V' (x, t) := by
  simp only [Fi_apply, Pi.add_apply, smul_add]
  exact integral_add (integrable_Fi hV x ht) (integrable_Fi hV' x ht)

theorem Fi_sub {T : ℝ} {V V' : E3 × ℝ → C3} (hV : Reg0 T V) (hV' : Reg0 T V') (x : E3)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Fi (V - V') (x, t) = Fi V (x, t) - Fi V' (x, t) := by
  simp only [Fi_apply, Pi.sub_apply, smul_sub]
  exact integral_sub (integrable_Fi hV x ht) (integrable_Fi hV' x ht)

theorem Fi_neg (V : E3 × ℝ → C3) (z : E3 × ℝ) : Fi (-V) z = -Fi V z := by
  simp only [Fi_apply, Pi.neg_apply, smul_neg, integral_neg]

theorem Fi_real_smul (r : ℝ) (V : E3 × ℝ → C3) (z : E3 × ℝ) : Fi (r • V) z = r • Fi V z := by
  simp only [Fi_apply, Pi.smul_apply]
  rw [← integral_smul]
  congr 1
  funext ξ
  rw [smul_comm]

theorem Fi_coord {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) (j : Fin 3) : Fi V (x, t) j = 𝓕⁻ (fun ξ => V (ξ, t) j) x := by
  rw [Fi_apply, proj_integral (integrable_Fi hV x ht), fourierInv_scalar_eq]
  rfl

theorem ip_sub_left (a b : E3) (w : C3) : ip (a - b) w = ip a w - ip b w := by
  simp [ip, sub_mul, Finset.sum_sub_distrib]

/-! ### A solução de Fourier e a velocidade física -/

/-- Hipóteses sobre a solução de Fourier `v` em `[0, T]`. -/
structure SolF (c T : ℝ) (v : E3 × ℝ → C3) : Prop where
  hc : 0 < c
  pos : 0 < T
  suave : ∀ k, Suave T k v
  deq : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => v (ξ, s)) (dv c v (ξ, t)) (Icc 0 T) t
  div : ∀ p : E3 × ℝ, ip p.1 (v p) = 0
  herm : ∀ ξ t, v (-ξ, t) = cj (v (ξ, t))

/-- **A velocidade física** `U(x, t) = Re ∫ e^{2πi⟨ξ,x⟩} v(ξ, t) dξ`. -/
noncomputable def Ufis (v : E3 × ℝ → C3) (z : E3 × ℝ) : E3 := reV (Fi v z)

theorem SolF.reg0 {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) : Reg0 T v := h.suave 0

theorem SolF.suave_dv {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (k : ℕ) :
    Suave T k (dv c v) :=
  (Suave.smul_left (continuous_phiC c) (abs_phiC_le h.hc.le) (h.suave k)).add
    (Suave.bil (h.suave k) (h.suave k))

theorem SolF.cx_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (z : E3 × ℝ) :
    cx (Ufis v z) = Fi v z := cx_reV (cj_Fi h.herm z)

theorem dX_reV {f : E3 → C3} {x : E3} (hf : DifferentiableAt ℝ f x) (j : Fin 3) :
    ATK.LigacaoNS.dX j (fun y => reV (f y)) x = reV (ATK.LigacaoNS.dX j f x) := by
  unfold ATK.LigacaoNS.dX
  have h := reV.hasFDerivAt.comp x hf.hasFDerivAt
  rw [show (fun y => reV (f y)) = ⇑reV ∘ f from rfl, h.fderiv]
  rfl

/-- Derivada parcial da velocidade física. -/
theorem dX_Ufis {T : ℝ} {V V' : E3 × ℝ → C3} (hV : Reg0 T V) (hV' : Reg0 T V')
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    (j : Fin 3) (x : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ATK.LigacaoNS.dX j (ATK.LigacaoNS.fatia (Ufis V) t) x =
      reV (Fi (fun q => mj j q.1 • V q) (x, t)) := by
  have hd : DifferentiableAt ℝ (fun y => Fi V (y, t)) x :=
    (hasFDerivAt_Φ_x aesm_idL zero_le_one idL_bound hV hV' hdV x ht).differentiableAt
  rw [show ATK.LigacaoNS.fatia (Ufis V) t = fun y => reV (Fi V (y, t)) from rfl, dX_reV hd,
    dX_Fi hV hV' hdV j x ht]

/-! ### A identidade da convolução -/

/-- **`Σ_j v_j ⋆ (2πi ξ_j v) = −Ñ(v, v)`** (usa `ξ · v = 0`). -/
theorem sum_conv_eq {f : E3 → C3} (hf : Continuous f) {A : ℝ} (hA : Cota 4 A f)
    (hdiv : ∀ ξ, ip ξ (f ξ) = 0) (ζ : E3) :
    ∑ j : Fin 3, ((fun ξ => f ξ j) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (fun ξ => mj j ξ • f ξ)) ζ =
      -(cI • nl f f ζ) := by
  have hA0 : 0 ≤ A := hA.nonneg
  -- integrabilidade de cada termo
  have hint : ∀ j : Fin 3, Integrable fun η => f η j • (mj j (ζ - η) • f (ζ - η)) := by
    intro j
    have hm : AEStronglyMeasurable (fun η => f η j • (mj j (ζ - η) • f (ζ - η))) := by
      have h1 : Continuous fun η => f η j :=
        (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).continuous.comp hf
      have h2 : Continuous fun η => mj j (ζ - η) • f (ζ - η) :=
        ((continuous_mj j).comp (continuous_const.sub continuous_id)).smul
          (hf.comp (continuous_const.sub continuous_id))
      exact (h1.smul h2).aestronglyMeasurable
    refine (((integrable_inv_pow (m := 4) le_rfl).const_mul A).const_mul (2 * π * A)).mono' hm
      (Eventually.of_forall fun η => ?_)
    rw [norm_smul, norm_smul]
    have e1 : ‖f η j‖ ≤ ‖f η‖ := by
      have := PiLp.norm_apply_le (f η) j
      exact this
    have e2 := hA.le_inv η
    have e3 := norm_mj_le j (ζ - η)
    have e4 : ‖f (ζ - η)‖ * (1 + ‖ζ - η‖) ≤ A := by
      have := hA (ζ - η)
      have hw : (1 + ‖ζ - η‖) ≤ (1 + ‖ζ - η‖) ^ 4 :=
        le_self_pow₀ (by linarith [norm_nonneg (ζ - η)]) (by norm_num)
      nlinarith [norm_nonneg (f (ζ - η))]
    calc ‖f η j‖ * (‖mj j (ζ - η)‖ * ‖f (ζ - η)‖)
        ≤ (A * ((1 + ‖η‖) ^ 4)⁻¹) * ((2 * π * (1 + ‖ζ - η‖) ^ 1) * ‖f (ζ - η)‖) := by
          gcongr
          exact e1.trans e2
      _ = (A * ((1 + ‖η‖) ^ 4)⁻¹) * (2 * π * (‖f (ζ - η)‖ * (1 + ‖ζ - η‖))) := by ring
      _ ≤ (A * ((1 + ‖η‖) ^ 4)⁻¹) * (2 * π * A) := by gcongr
      _ = 2 * π * A * (A * ((1 + ‖η‖) ^ 4)⁻¹) := by ring
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [← integral_finsetSum _ (fun j _ => hint j)]
  -- a soma em `j`
  have hpt : ∀ η, ∑ j : Fin 3, f η j • (mj j (ζ - η) • f (ζ - η)) =
      (2 * (π : ℂ) * Complex.I * ip (ζ - η) (f η)) • f (ζ - η) := by
    intro η
    simp only [smul_smul, ← Finset.sum_smul, ip, Finset.mul_sum, mj]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [PiLp.sub_apply]
    ring
  simp_rw [hpt]
  -- mudança de variáveis `η ↦ ζ − η`
  have hcv : ∫ η, (2 * (π : ℂ) * Complex.I * ip (ζ - η) (f η)) • f (ζ - η) =
      ∫ μ, (2 * (π : ℂ) * Complex.I * ip μ (f (ζ - μ))) • f μ := by
    have := integral_sub_left_eq_self
      (fun μ : E3 => (2 * (π : ℂ) * Complex.I * ip μ (f (ζ - μ))) • f μ) volume ζ
    simpa [sub_sub_cancel] using this
  rw [hcv]
  -- divergência nula
  have hdv : ∀ μ, ip μ (f (ζ - μ)) = ip ζ (f (ζ - μ)) := by
    intro μ
    have h1 : ip μ (f (ζ - μ)) = ip (ζ - (ζ - μ)) (f (ζ - μ)) := by rw [sub_sub_cancel]
    rw [h1, ip_sub_left, hdiv (ζ - μ), sub_zero]
  have hsm : ∀ μ, (2 * (π : ℂ) * Complex.I * ip ζ (f (ζ - μ))) • f μ =
      (2 * (π : ℂ) * Complex.I) • (ip ζ (f (ζ - μ)) • f μ) := fun μ => mul_smul _ _ _
  simp_rw [hdv, hsm]
  rw [integral_smul]
  unfold cI nl
  rw [neg_smul, neg_neg]

theorem Fi_eq_fourierInv_xt (V : E3 × ℝ → C3) (x : E3) (t : ℝ) :
    Fi V (x, t) = 𝓕⁻ (fun ξ => V (ξ, t)) x := Fi_eq_fourierInv V (x, t)

theorem integrable_coord {f : E3 → C3} (hf : Integrable f) (j : Fin 3) :
    Integrable fun ξ => f ξ j :=
  (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).integrable_comp hf

theorem integrable_fourierInv_integrand {g : E3 → C3} (hg : Integrable g) (x : E3) :
    Integrable fun v => 𝐞 (inner ℝ v x) • g v := by
  have := (Real.fourierIntegral_convergent_iff (μ := volume) (f := g) (-x)).mpr hg
  simpa [inner_neg_right] using this

theorem fourierInv_sum {g : Fin 3 → E3 → C3} (hg : ∀ j, Integrable (g j)) (x : E3) :
    ∑ j, 𝓕⁻ (g j) x = 𝓕⁻ (fun ξ => ∑ j, g j ξ) x := by
  simp_rw [Real.fourierInv_eq]
  rw [← integral_finsetSum _ (fun j _ => integrable_fourierInv_integrand (hg j) x)]
  congr 1
  funext ξ
  rw [Finset.smul_sum]

/-- **O termo convectivo** `(U·∇)U` é a transformada de `−Ñ(v, v)`. -/
theorem conv_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ATK.LigacaoNS.conv (ATK.LigacaoNS.fatia (Ufis v) t) x = reV (Fi (-(Nl v v)) (x, t)) := by
  have hv := h.reg0
  have hdv := h.suave_dv 0
  have hmj : ∀ j, Reg0 T (fun q => mj j q.1 • v q) := fun j =>
    Reg0.smulC (continuous_mj j) (norm_mj_le j) hv
  obtain ⟨A, hA⟩ := hv.2 4
  have hsl : Integrable fun ξ => v (ξ, t) := integrable_slice hv ht
  have hcj : ∀ j, Integrable fun ξ => v (ξ, t) j := fun j => integrable_coord hsl j
  have hmsl : ∀ j, Integrable fun ξ => mj j ξ • v (ξ, t) := fun j => integrable_slice (hmj j) ht
  -- cada termo `u_j ∂_j u`
  have hterm : ∀ j, (ATK.LigacaoNS.fatia (Ufis v) t x j) •
      ATK.LigacaoNS.dX j (ATK.LigacaoNS.fatia (Ufis v) t) x =
      reV (𝓕⁻ ((fun ξ => v (ξ, t) j) ⋆[ContinuousLinearMap.lsmul ℂ ℂ]
        (fun ξ => mj j ξ • v (ξ, t))) x) := by
    intro j
    rw [dX_Ufis hv hdv (h.deq) j x ht]
    have hre : ((ATK.LigacaoNS.fatia (Ufis v) t x j : ℝ) : ℂ) = Fi v (x, t) j := by
      have := congrArg (fun a : C3 => a j) (h.cx_Ufis (x, t))
      simpa [ATK.LigacaoNS.fatia] using this
    rw [← mul_fourierInv (hcj j) (hmsl j), ← Fi_coord hv x ht j, ← hre, Complex.coe_smul,
      map_smul]
    congr 2
    exact Fi_eq_fourierInv_xt _ x t
  unfold ATK.LigacaoNS.conv
  simp_rw [hterm]
  rw [← map_sum, fourierInv_sum (fun j => (hcj j).integrable_convolution _ (hmsl j)),
    Fi_eq_fourierInv_xt]
  refine congrArg reV (congrArg (fun g : E3 → C3 => 𝓕⁻ g x) (funext fun ζ => ?_))
  rw [sum_conv_eq ((hv.1 t ht)) (hA t ht) (fun ξ => h.div (ξ, t)) ζ]
  rfl

/-! ### Derivada temporal, laplaciano e divergência -/

theorem Reg0.mj {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) (j : Fin 3) :
    Reg0 T (fun q => mj j q.1 • V q) :=
  Reg0.smulC (continuous_mj j) (norm_mj_le j) hV

theorem hasDerivWithinAt_mj {T : ℝ} {V V' : E3 × ℝ → C3}
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    (j : Fin 3) : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => mj j ξ • V (ξ, s))
      (mj j ξ • V' (ξ, t)) (Icc 0 T) t :=
  fun ξ t ht => (hdV ξ t ht).const_smul (mj j ξ)

/-- **Derivada temporal** da velocidade física (tempos interiores). -/
theorem hasDerivAt_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (x : E3) {t : ℝ}
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => Ufis v (x, s)) (reV (Fi (dv c v) (x, t))) t :=
  reV.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_Fi_t h.reg0 (h.suave_dv 0) h.deq x ht)

theorem Fi_sum {T : ℝ} {W : Fin 3 → E3 × ℝ → C3} (hW : ∀ j, Reg0 T (W j)) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ∑ j, Fi (W j) (x, t) = Fi (fun q => ∑ j, W j q) (x, t) := by
  simp only [Fi_apply]
  rw [← integral_finsetSum _ (fun j _ => integrable_Fi (hW j) x ht)]
  congr 1
  funext ξ
  rw [Finset.smul_sum]

theorem sum_mj_sq (ξ : E3) :
    ∑ j : Fin 3, mj j ξ * mj j ξ = ((-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  have h1 : ‖ξ‖ ^ 2 = ∑ j : Fin 3, (ξ j) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [h1]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mj]
  linear_combination (4 * (π : ℂ) ^ 2 * ((ξ j : ℝ) : ℂ) ^ 2) * Complex.I_mul_I

/-- **O laplaciano** da velocidade física. -/
theorem lap_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ATK.LigacaoNS.lap (ATK.LigacaoNS.fatia (Ufis v) t) x =
      reV (Fi (fun q => phiC (4 * π ^ 2) q.1 • v q) (x, t)) := by
  have hv := h.reg0
  have hdv := (h.suave_dv 0)
  have hd1 : ∀ j, ATK.LigacaoNS.dX j (ATK.LigacaoNS.fatia (Ufis v) t) =
      ATK.LigacaoNS.fatia (Ufis (fun q => mj j q.1 • v q)) t := by
    intro j
    funext y
    exact dX_Ufis hv hdv h.deq j y ht
  unfold ATK.LigacaoNS.lap
  simp_rw [hd1]
  have hd2 : ∀ j, ATK.LigacaoNS.dX j (ATK.LigacaoNS.fatia (Ufis (fun q => mj j q.1 • v q)) t) x =
      reV (Fi (fun q => mj j q.1 • (mj j q.1 • v q)) (x, t)) := fun j =>
    dX_Ufis (Reg0.mj hv j) (Reg0.mj hdv j) (hasDerivWithinAt_mj h.deq j) j x ht
  simp_rw [hd2]
  rw [← map_sum, Fi_sum (fun j => Reg0.mj (Reg0.mj hv j) j) x ht]
  congr 2
  funext q
  simp only [smul_smul, ← Finset.sum_smul, sum_mj_sq]
  rw [Complex.coe_smul]
  rfl

/-- **Divergência nula** da velocidade física. -/
theorem div_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ATK.LigacaoNS.div (ATK.LigacaoNS.fatia (Ufis v) t) x = 0 := by
  have hv := h.reg0
  have hdv := (h.suave_dv 0)
  unfold ATK.LigacaoNS.div
  simp_rw [dX_Ufis hv hdv h.deq _ x ht, reV_apply]
  rw [← Complex.re_sum]
  have hsum : ∑ j : Fin 3, Fi (fun q => mj j q.1 • v q) (x, t) j = 0 := by
    have hint : ∀ j : Fin 3, Integrable fun ξ => (ex ξ x • (mj j ξ • v (ξ, t))) j :=
      fun j => integrable_coord (integrable_Fi (Reg0.mj hv j) x ht) j
    simp only [Fi_apply]
    rw [Finset.sum_congr rfl fun j _ => proj_integral (integrable_Fi (Reg0.mj hv j) x ht) j,
      ← integral_finsetSum _ (fun j _ => hint j)]
    have h0 : ∀ ξ, ∑ j : Fin 3, (ex ξ x • (mj j ξ • v (ξ, t))) j = 0 := by
      intro ξ
      simp only [PiLp.smul_apply, smul_eq_mul]
      have hd := h.div (ξ, t)
      simp only [ip] at hd
      have : ∑ j : Fin 3, ex ξ x * (mj j ξ * v (ξ, t) j) =
          ex ξ x * (2 * π * Complex.I) * ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * v (ξ, t) j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [mj]
        ring
      rw [this, hd, mul_zero]
    have hz : (fun ξ => ∑ j : Fin 3, (ex ξ x • (mj j ξ • v (ξ, t))) j) = fun _ => 0 := funext h0
    rw [hz, integral_zero]
  rw [hsum, Complex.zero_re]

/-! ### A pressão -/

/-- `κ(ξ) = (2πi|ξ|²)⁻¹` (`= 0` em `ξ = 0`). -/
noncomputable def kap (ξ : E3) : ℂ := (2 * π * Complex.I * ((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹

theorem measurable_kap : Measurable kap := by
  unfold kap
  fun_prop

theorem norm_kap_mul (ξ : E3) : ‖kap ξ‖ * ‖ξ‖ ^ 2 ≤ 1 / (2 * π) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [kap]
    positivity
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  unfold kap
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ‖ξ‖ ^ 2)]
  have : ‖(2 * (π : ℂ))‖ = 2 * π := by
    rw [norm_mul]
    simp [abs_of_pos pi_pos]
  rw [this]
  field_simp
  rfl

/-- `ξ · a` como aplicação `ℝ`-linear, contínua em `ξ`. -/
noncomputable def ipR (ξ : E3) : C3 →L[ℝ] ℂ :=
  ∑ j : Fin 3, (ξ j) • (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).restrictScalars ℝ

theorem ipR_apply (ξ : E3) (a : C3) : ipR ξ a = ip ξ a := by
  simp [ipR, ip, Complex.real_smul]

theorem continuous_ipR : Continuous ipR := by
  unfold ipR
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).continuous).smul continuous_const

/-- **O símbolo da pressão** `a ↦ Re(κ(ξ) ξ·a)`. -/
noncomputable def LP (ξ : E3) : C3 →L[ℝ] ℝ := Complex.reCLM.comp (kap ξ • ipR ξ)

theorem LP_apply (ξ : E3) (a : C3) : LP ξ a = (kap ξ * ip ξ a).re := by
  simp [LP, ipR_apply]

theorem aesm_LP : AEStronglyMeasurable LP := by
  have h1 : AEStronglyMeasurable (fun ξ => kap ξ • ipR ξ) :=
    measurable_kap.aestronglyMeasurable.smul continuous_ipR.aestronglyMeasurable
  exact (ContinuousLinearMap.compL ℝ C3 ℂ ℝ Complex.reCLM).continuous.comp_aestronglyMeasurable h1

theorem LP_bound (ξ : E3) : ‖LP ξ‖ * ‖ξ‖ ≤ 1 * (1 + ‖ξ‖) ^ 0 := by
  have h1 : ‖LP ξ‖ ≤ ‖kap ξ‖ * ‖ξ‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    rw [LP_apply, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_ip_le ξ a) (norm_nonneg _)
  have h2 := norm_kap_mul ξ
  have h3 : 1 / (2 * π) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.two_le_pi]
  calc ‖LP ξ‖ * ‖ξ‖ ≤ ‖kap ξ‖ * ‖ξ‖ * ‖ξ‖ := by gcongr
    _ = ‖kap ξ‖ * ‖ξ‖ ^ 2 := by ring
    _ ≤ 1 := h2.trans h3
    _ = 1 * (1 + ‖ξ‖) ^ 0 := by simp

/-- **A pressão física** `P(x, t) = ∫ Re(κ(ξ) ξ·(e^{2πi⟨ξ,x⟩} Ñ(v,v)(ξ,t))) dξ`. -/
noncomputable def Pfis (v : E3 × ℝ → C3) (z : E3 × ℝ) : ℝ := NSFisico.Φ LP (Nl v v) z

theorem SolF.suave_Nl {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (k : ℕ) :
    Suave T k (Nl v v) := Suave.nls (h.suave k) (h.suave k)

theorem SolF.suave_Bil {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (k : ℕ) :
    Suave T k (Bil v v) := Suave.bil (h.suave k) (h.suave k)

/-- `Ñ − 𝐏 Ñ = (ξ·Ñ/|ξ|²) ξ`. -/
theorem sub_leray (ξ : E3) (a : C3) :
    a - leray ξ a = ((((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ * ip ξ a) • cx ξ := by
  rw [leray_apply]
  abel

/-- O integrando da derivada da pressão. -/
theorem dP_integrand (ξ x : E3) (a : C3) (j : Fin 3) :
    LA LP ξ (ex ξ x • a) (ATK.LigacaoNS.e j) = (ex ξ x * (a - leray ξ a) j).re := by
  rw [LA_apply, inner_e, LP_apply, sub_leray, smul_eq_mul, ip_smul, ip_smul]
  simp only [PiLp.smul_apply, cx_apply, smul_eq_mul]
  by_cases hξ : ξ = 0
  · subst hξ
    simp
  have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    exact_mod_cast pow_ne_zero 2 this
  have hk : kap ξ * (2 * π * Complex.I) = (((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    unfold kap
    have hI : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
      simp [this, Complex.I_ne_zero]
    field_simp
  rw [← Complex.re_ofReal_mul]
  congr 1
  push_cast at hk ⊢
  linear_combination (((ξ j : ℝ) : ℂ) * ex ξ x * ip ξ a) * hk

/-- **O gradiente da pressão** é a transformada de `Ñ − 𝐏Ñ`. -/
theorem grad_Pfis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    ATK.LigacaoNS.grad (ATK.LigacaoNS.fatia (Pfis v) t) x =
      reV (Fi (Nl v v - Bil v v) (x, t)) := by
  have hN := h.suave_Nl
  obtain ⟨hNd, hdN⟩ := suave_dt h.pos hN
  have hfd := hasFDerivAt_Φ_x aesm_LP zero_le_one LP_bound (hN 0) (hNd 0) hdN x ht
  have hint : Integrable fun ξ => LA LP ξ (ex ξ x • Nl v v (ξ, t)) :=
    integrable_integrand (aesm_LA aesm_LP) (LA_bound LP_bound) (hN 0) x ht
  have hcomp : ∀ j, ATK.LigacaoNS.dX j (ATK.LigacaoNS.fatia (Pfis v) t) x =
      (Fi (Nl v v - Bil v v) (x, t) j).re := by
    intro j
    unfold ATK.LigacaoNS.dX
    rw [show ATK.LigacaoNS.fatia (Pfis v) t = fun y => NSFisico.Φ LP (Nl v v) (y, t) from rfl,
      hfd.fderiv]
    unfold NSFisico.Φ
    rw [ContinuousLinearMap.integral_apply hint]
    have hI : Integrable fun ξ => ex ξ x • (Nl v v - Bil v v) (ξ, t) :=
      integrable_Fi (Suave.reg0 (ATK.NSCampos.Suave.sub (hN 0) (h.suave_Bil 0))) x ht
    rw [Fi_apply, proj_integral hI, ← Complex.reCLM_apply,
      ← Complex.reCLM.integral_comp_comm (integrable_coord hI j)]
    congr 1
    funext ξ
    rw [dP_integrand, Pi.sub_apply, Bil_eq_leray_Nl]
    simp [smul_eq_mul]
  unfold ATK.LigacaoNS.grad
  simp_rw [hcomp]
  rw [← ATK.LigacaoNS.sum_coord (reV (Fi (Nl v v - Bil v v) (x, t)))]
  simp [reV_apply]

/-! ### A equação de Navier–Stokes ponto a ponto -/

theorem Reg0.const_smul {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) (r : ℝ) : Reg0 T (r • V) := by
  refine ⟨fun t ht => (hV.1 t ht).const_smul r, fun m => ?_⟩
  obtain ⟨C, hC⟩ := hV.2 m
  refine ⟨|r| * C, fun t ht ζ => ?_⟩
  have := hC t ht ζ
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg r)

/-- **Navier–Stokes ponto a ponto**: `∂ₜU + (U·∇)U = νΔU − ∇P` nos tempos interiores. -/
theorem NSEq_fis {ν T : ℝ} {v : E3 × ℝ → C3} (h : SolF (4 * π ^ 2 * ν) T v) (x : E3) {t : ℝ}
    (ht : t ∈ Ioo 0 T) : ATK.LigacaoNS.NSEq ν (Ufis v) (Pfis v) x t := by
  have htc := Ioo_subset_Icc_self ht
  have hv := h.reg0
  have hdv : Reg0 T (dv (4 * π ^ 2 * ν) v) := Suave.reg0 (h.suave_dv 0)
  have hN : Reg0 T (Nl v v) := Suave.reg0 (h.suave_Nl 0)
  have hB : Reg0 T (Bil v v) := Suave.reg0 (h.suave_Bil 0)
  have hφ : Reg0 T (fun q => phiC (4 * π ^ 2) q.1 • v q) :=
    Reg0.smul_left (continuous_phiC _) (abs_phiC_le (by positivity)) hv
  unfold ATK.LigacaoNS.NSEq
  rw [(hasDerivAt_Ufis h x ht).deriv, conv_Ufis h x htc, lap_Ufis h x htc, grad_Pfis h x htc,
    ← map_add, ← map_smul, ← map_sub]
  congr 1
  rw [← Fi_add hdv (Reg0.neg hN) x htc, ← Fi_real_smul,
    ← Fi_sub (Reg0.const_smul hφ ν) (Suave.reg0 (ATK.NSCampos.Suave.sub (h.suave_Nl 0)
      (h.suave_Bil 0))) x htc]
  congr 1
  funext q
  simp only [dv, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_smul]
  have : phiC (4 * π ^ 2 * ν) q.1 = ν * phiC (4 * π ^ 2) q.1 := by
    unfold phiC
    ring
  rw [this]
  abel

/-! ### A solução local e os campos físicos -/

theorem solF_of_sol {ν : ℝ} (hν : 0 < ν) {u₀ : 𝓢(E3, E3)} {T : ℝ} (hT : 0 < T)
    {v : E3 × ℝ → C3} (hv : Sol (dadoNS ν hν u₀) T v) (hdiv : ∀ p : E3 × ℝ, ip p.1 (v p) = 0)
    (herm : ∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) : SolF (4 * π ^ 2 * ν) T v :=
  ⟨by positivity, hT, sol_suave hT.le hv (cota_v0 u₀), fun ξ t ht => sol_hasDerivWithinAt hv ξ ht,
    hdiv, herm⟩

theorem sol_zero {D : Dado} {T : ℝ} (hT : 0 ≤ T) {v : E3 × ℝ → C3} (hv : Sol D T v) (ξ : E3) :
    v (ξ, 0) = D.v₀ ξ := by
  rw [hv.eq_of_mem ⟨le_rfl, hT⟩]
  simp [hk, Iduh]

/-- **O dado inicial**: `U(x, 0) = u₀(x)`. -/
theorem Ufis_zero {ν : ℝ} (hν : 0 < ν) {u₀ : 𝓢(E3, E3)} {T : ℝ} (hT : 0 ≤ T)
    {v : E3 × ℝ → C3} (hv : Sol (dadoNS ν hν u₀) T v) (x : E3) : Ufis v (x, 0) = u₀ x := by
  rw [Ufis, Fi_eq_fourierInv_xt]
  have : (fun ξ => v (ξ, 0)) = ⇑(v0S u₀) := funext fun ξ => sol_zero hT hv ξ
  rw [this, fourierInv_v0, reV_cx]

theorem contDiffOn_Ufis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) :
    ContDiffOn ℝ ∞ (Ufis v) ((univ : Set E3) ×ˢ Icc 0 T) :=
  reV.contDiff.comp_contDiffOn (contDiffOn_Φ_top h.pos aesm_idL zero_le_one idL_bound h.suave)

theorem contDiffOn_Pfis {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) :
    ContDiffOn ℝ ∞ (Pfis v) ((univ : Set E3) ×ˢ Icc 0 T) :=
  contDiffOn_Φ_top h.pos aesm_LP zero_le_one LP_bound h.suave_Nl

end ATK.NSEquacao

#print axioms ATK.NSEquacao.cxL
#print axioms ATK.NSEquacao.cxL_apply
#print axioms ATK.NSEquacao.reV_cx
#print axioms ATK.NSEquacao.u0c
#print axioms ATK.NSEquacao.u0c_apply
#print axioms ATK.NSEquacao.v0S
#print axioms ATK.NSEquacao.v0S_eq
#print axioms ATK.NSEquacao.cota_schwartz
#print axioms ATK.NSEquacao.cota_v0
#print axioms ATK.NSEquacao.herm_v0
#print axioms ATK.NSEquacao.proj_integral
#print axioms ATK.NSEquacao.lineDeriv_u0c
#print axioms ATK.NSEquacao.ip_v0
#print axioms ATK.NSEquacao.integrable_v0
#print axioms ATK.NSEquacao.fourierInv_v0
#print axioms ATK.NSEquacao.dadoNS
#print axioms ATK.NSEquacao.dadoNS_c
#print axioms ATK.NSEquacao.dadoNS_v₀
#print axioms ATK.NSEquacao.integrable_Fi
#print axioms ATK.NSEquacao.integrable_slice
#print axioms ATK.NSEquacao.Fi_add
#print axioms ATK.NSEquacao.Fi_sub
#print axioms ATK.NSEquacao.Fi_neg
#print axioms ATK.NSEquacao.Fi_real_smul
#print axioms ATK.NSEquacao.Fi_coord
#print axioms ATK.NSEquacao.ip_sub_left
#print axioms ATK.NSEquacao.SolF
#print axioms ATK.NSEquacao.Ufis
#print axioms ATK.NSEquacao.SolF.reg0
#print axioms ATK.NSEquacao.SolF.suave_dv
#print axioms ATK.NSEquacao.SolF.cx_Ufis
#print axioms ATK.NSEquacao.dX_reV
#print axioms ATK.NSEquacao.dX_Ufis
#print axioms ATK.NSEquacao.sum_conv_eq
#print axioms ATK.NSEquacao.Fi_eq_fourierInv_xt
#print axioms ATK.NSEquacao.integrable_coord
#print axioms ATK.NSEquacao.integrable_fourierInv_integrand
#print axioms ATK.NSEquacao.fourierInv_sum
#print axioms ATK.NSEquacao.conv_Ufis
#print axioms ATK.NSEquacao.Reg0.mj
#print axioms ATK.NSEquacao.hasDerivWithinAt_mj
#print axioms ATK.NSEquacao.hasDerivAt_Ufis
#print axioms ATK.NSEquacao.Fi_sum
#print axioms ATK.NSEquacao.sum_mj_sq
#print axioms ATK.NSEquacao.lap_Ufis
#print axioms ATK.NSEquacao.div_Ufis
#print axioms ATK.NSEquacao.kap
#print axioms ATK.NSEquacao.measurable_kap
#print axioms ATK.NSEquacao.norm_kap_mul
#print axioms ATK.NSEquacao.ipR
#print axioms ATK.NSEquacao.ipR_apply
#print axioms ATK.NSEquacao.continuous_ipR
#print axioms ATK.NSEquacao.LP
#print axioms ATK.NSEquacao.LP_apply
#print axioms ATK.NSEquacao.aesm_LP
#print axioms ATK.NSEquacao.LP_bound
#print axioms ATK.NSEquacao.Pfis
#print axioms ATK.NSEquacao.SolF.suave_Nl
#print axioms ATK.NSEquacao.SolF.suave_Bil
#print axioms ATK.NSEquacao.sub_leray
#print axioms ATK.NSEquacao.dP_integrand
#print axioms ATK.NSEquacao.grad_Pfis
#print axioms ATK.NSEquacao.Reg0.const_smul
#print axioms ATK.NSEquacao.NSEq_fis
#print axioms ATK.NSEquacao.solF_of_sol
#print axioms ATK.NSEquacao.sol_zero
#print axioms ATK.NSEquacao.Ufis_zero
#print axioms ATK.NSEquacao.contDiffOn_Ufis
#print axioms ATK.NSEquacao.contDiffOn_Pfis
