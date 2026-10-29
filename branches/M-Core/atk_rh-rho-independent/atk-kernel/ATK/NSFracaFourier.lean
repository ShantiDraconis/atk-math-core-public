import ATK.NSL2
import ATK.NSCorte
import ATK.NSDado

/-!
# ATK — Navier–Stokes: a formulação fraca no lado de Fourier

Camada 19 do ataque a B3 (unicidade fraca–forte, passo U-3). A formulação fraca
`ATK.NSCorte.formulacao_fraca_rot` (campos-teste `rot Ψ`, `Ψ` real de Schwartz) é combinada em
campos-teste complexos e lida no lado de Fourier: para `G` de Schwartz (no lado de Fourier), o
campo físico `Φ = 𝓕⁻(2πi ξ × G)` é o rotacional de `𝓕⁻ G`, e

`∫ ⟪b(t), m⟫ − ∫ ⟪â₀, m⟫ = ∫₀ᵗ (ν ∫ ⟪b(s), −4π²‖ξ‖² m⟫ − ∫ ⟪N(s), m⟫) ds`, `m = 2πi ξ × G`,

com `b(s) = 𝓕[u(s)]` (transformada `L²`) e `N(s) = 2πi 𝓕[⟪ξ, u(s)⟫ u(s)]` (transformada de `L¹`
de `div(u ⊗ u)`). Nenhuma hipótese sobre a pressão.

**CLOSED_MATH continua false.**
-/

open MeasureTheory FourierTransform SchwartzMap Filter Set ComplexConjugate
open scoped ContDiff InnerProductSpace Real

namespace ATK.NSFracaFourier

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSFisico ATK.NSFraca ATK.NSCorte ATK.NSL2
  ATK.NSDado

/-! ### Álgebra em `ℂ³`: parte imaginária e produto vetorial -/

/-- Parte imaginária componente a componente. -/
noncomputable def im3 (v : C3) : E3 := WithLp.toLp 2 fun k => (v k).im

@[simp] theorem im3_apply (v : C3) (k : Fin 3) : im3 v k = (v k).im := rfl

/-- `im₃` como aplicação `ℝ`-linear contínua. -/
noncomputable def im3L : C3 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := im3
      map_add' := fun v w => by ext k; simp
      map_smul' := fun r v => by ext k; simp [Complex.real_smul] }

theorem im3L_apply (v : C3) : im3L v = im3 v := rfl

theorem decomp (v : C3) : cpx (re3 v) + Complex.I • cpx (im3 v) = v := by
  ext k
  simp only [PiLp.add_apply, PiLp.smul_apply, cpx_apply, re3_apply, im3_apply, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im (v k)

/-- O vetor `eₖ` de `ℂ³`. -/
noncomputable abbrev eC (j : Fin 3) : C3 := EuclideanSpace.single j (1 : ℂ)

/-- Produto vetorial em `ℂ³`. -/
noncomputable def cr (v w : C3) : C3 :=
  WithLp.toLp 2 ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0]

theorem cr_apply0 (v w : C3) : cr v w 0 = v 1 * w 2 - v 2 * w 1 := rfl
theorem cr_apply1 (v w : C3) : cr v w 1 = v 2 * w 0 - v 0 * w 2 := rfl
theorem cr_apply2 (v w : C3) : cr v w 2 = v 0 * w 1 - v 1 * w 0 := rfl

theorem cr_add_right (v w w' : C3) : cr v (w + w') = cr v w + cr v w' := by
  ext k; fin_cases k <;> simp [cr_apply0, cr_apply1, cr_apply2] <;> ring

theorem cr_smul_right (v w : C3) (c : ℂ) : cr v (c • w) = c • cr v w := by
  ext k; fin_cases k <;> simp [cr_apply0, cr_apply1, cr_apply2] <;> ring

/-- `w ↦ eⱼ × w`, `ℂ`-linear. -/
noncomputable def crL (j : Fin 3) : C3 →L[ℂ] C3 :=
  LinearMap.toContinuousLinearMap
    { toFun := cr (eC j)
      map_add' := fun v w => cr_add_right _ v w
      map_smul' := fun c v => cr_smul_right _ v c }

theorem crL_apply (j : Fin 3) (w : C3) : crL j w = cr (eC j) w := rfl

/-! ### O campo-teste no lado de Fourier -/

/-- `m(ξ) = 2πi ξ × G(ξ)` (como campo de Schwartz). -/
noncomputable def Ms (G : 𝓢(E3, C3)) : 𝓢(E3, C3) :=
  SchwartzMap.postcompCLM (crL 0) (mulCj 0 G) + SchwartzMap.postcompCLM (crL 1) (mulCj 1 G) +
    SchwartzMap.postcompCLM (crL 2) (mulCj 2 G)

/-- A forma pontual do campo-teste. -/
noncomputable def mtf (G : E3 → C3) (ξ : E3) : C3 :=
  ((2 * π : ℝ) * Complex.I : ℂ) • cr (cpx ξ) (G ξ)

theorem Ms_apply (G : 𝓢(E3, C3)) (ξ : E3) : Ms G ξ = mtf G ξ := by
  have h : Ms G ξ = crL 0 (mulCj 0 G ξ) + crL 1 (mulCj 1 G ξ) + crL 2 (mulCj 2 G ξ) := rfl
  rw [h, mulCj_apply, mulCj_apply, mulCj_apply, crL_apply, crL_apply, crL_apply, mtf]
  ext k
  fin_cases k <;> simp [cr_apply0, cr_apply1, cr_apply2, cj, cpx_apply] <;> ring

/-- O laplaciano no lado de Fourier: `S ↦ Σⱼ (2πi ξⱼ)² S`. -/
noncomputable def lapS (S : 𝓢(E3, C3)) : 𝓢(E3, C3) :=
  mulCj 0 (mulCj 0 S) + mulCj 1 (mulCj 1 S) + mulCj 2 (mulCj 2 S)

theorem lapS_apply (S : 𝓢(E3, C3)) (ξ : E3) :
    lapS S ξ = (-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) • S ξ := by
  have h : lapS S ξ = mulCj 0 (mulCj 0 S) ξ + mulCj 1 (mulCj 1 S) ξ +
      mulCj 2 (mulCj 2 S) ξ := rfl
  rw [h, mulCj_apply, mulCj_apply, mulCj_apply, mulCj_apply, mulCj_apply, mulCj_apply,
    smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul]
  congr 1
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [cj, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### O lado físico -/

theorem fourierInv_postcomp (L : C3 →L[ℂ] C3) (f : 𝓢(E3, C3)) (x : E3) :
    (𝓕⁻ (SchwartzMap.postcompCLM L f) : 𝓢(E3, C3)) x = L ((𝓕⁻ f : 𝓢(E3, C3)) x) := by
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    Real.fourierInv_eq, ← L.integral_comp_comm]
  · congr 1 with ξ
    rw [SchwartzMap.postcompCLM_apply, Circle.smul_def, Circle.smul_def, L.map_smul]
  · have h := (Real.fourierIntegral_convergent_iff (μ := volume) (f := ⇑f) (-x)).mpr f.integrable
    simpa [inner_neg_right] using h

theorem fourierInv_add_apply (f g : 𝓢(E3, C3)) (x : E3) :
    (𝓕⁻ (f + g) : 𝓢(E3, C3)) x = (𝓕⁻ f : 𝓢(E3, C3)) x + (𝓕⁻ g : 𝓢(E3, C3)) x := by
  rw [FourierTransform.fourierInv_add]; rfl

/-- O campo físico `Φ = 𝓕⁻ m` é `Σⱼ eⱼ × ∂ⱼ(𝓕⁻ G)`. -/
theorem fourierInv_Ms (G : 𝓢(E3, C3)) (x : E3) :
    (𝓕⁻ (Ms G) : 𝓢(E3, C3)) x =
      cr (eC 0) (dX 0 (⇑(𝓕⁻ G : 𝓢(E3, C3))) x) + cr (eC 1) (dX 1 (⇑(𝓕⁻ G : 𝓢(E3, C3))) x) +
        cr (eC 2) (dX 2 (⇑(𝓕⁻ G : 𝓢(E3, C3))) x) := by
  rw [Ms, fourierInv_add_apply, fourierInv_add_apply, fourierInv_postcomp, fourierInv_postcomp,
    fourierInv_postcomp, dX_fourierInv, dX_fourierInv, dX_fourierInv, crL_apply, crL_apply,
    crL_apply]

/-- Parte real do campo físico `𝓕⁻ G`. -/
noncomputable def Psr (G : 𝓢(E3, C3)) : SchwartzMap E3 E3 :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) re3L (𝓕⁻ G)

/-- Parte imaginária do campo físico `𝓕⁻ G`. -/
noncomputable def Psi (G : 𝓢(E3, C3)) : SchwartzMap E3 E3 :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) im3L (𝓕⁻ G)

theorem fderiv_postcomp {F : E3 → C3} (hF : Differentiable ℝ F) (L : C3 →L[ℝ] E3) (x : E3) :
    fderiv ℝ (fun y => L (F y)) x = L.comp (fderiv ℝ F x) :=
  (L.hasFDerivAt.comp x (hF x).hasFDerivAt).fderiv

theorem rot_Psr (G : 𝓢(E3, C3)) (x : E3) : rot (Psr G) x = re3 ((𝓕⁻ (Ms G) : 𝓢(E3, C3)) x) := by
  have hd : Differentiable ℝ (⇑(𝓕⁻ G : 𝓢(E3, C3))) := (𝓕⁻ G : 𝓢(E3, C3)).differentiable
  have hf : (⇑(Psr G) : E3 → E3) = fun y => re3L ((𝓕⁻ G : 𝓢(E3, C3)) y) := rfl
  rw [rot, hf, fderiv_postcomp hd re3L x, fourierInv_Ms]
  ext a
  rw [rotL_apply]
  simp only [ContinuousLinearMap.comp_apply, re3L_apply, re3_apply]
  have h0 : ∀ j, fderiv ℝ (⇑(𝓕⁻ G : 𝓢(E3, C3))) x (e j) = dX j (⇑(𝓕⁻ G : 𝓢(E3, C3))) x :=
    fun j => rfl
  simp only [h0]
  fin_cases a <;> simp [cr_apply0, cr_apply1, cr_apply2] <;> ring

theorem rot_Psi (G : 𝓢(E3, C3)) (x : E3) : rot (Psi G) x = im3 ((𝓕⁻ (Ms G) : 𝓢(E3, C3)) x) := by
  have hd : Differentiable ℝ (⇑(𝓕⁻ G : 𝓢(E3, C3))) := (𝓕⁻ G : 𝓢(E3, C3)).differentiable
  have hf : (⇑(Psi G) : E3 → E3) = fun y => im3L ((𝓕⁻ G : 𝓢(E3, C3)) y) := rfl
  rw [rot, hf, fderiv_postcomp hd im3L x, fourierInv_Ms]
  ext a
  rw [rotL_apply]
  simp only [ContinuousLinearMap.comp_apply, im3L_apply, im3_apply]
  have h0 : ∀ j, fderiv ℝ (⇑(𝓕⁻ G : 𝓢(E3, C3))) x (e j) = dX j (⇑(𝓕⁻ G : 𝓢(E3, C3))) x :=
    fun j => rfl
  simp only [h0]
  fin_cases a <;> simp [cr_apply0, cr_apply1, cr_apply2] <;> ring

/-! ### Derivadas do campo físico -/

theorem dX_fourierInv_fun (S : 𝓢(E3, C3)) (j : Fin 3) :
    dX j (⇑(𝓕⁻ S : 𝓢(E3, C3))) = ⇑(𝓕⁻ (mulCj j S) : 𝓢(E3, C3)) :=
  funext (dX_fourierInv S j)

theorem lap_fourierInv (S : 𝓢(E3, C3)) (x : E3) :
    lap (⇑(𝓕⁻ S : 𝓢(E3, C3))) x = (𝓕⁻ (lapS S) : 𝓢(E3, C3)) x := by
  rw [lap, Fin.sum_univ_three, dX_fourierInv_fun S 0, dX_fourierInv_fun S 1,
    dX_fourierInv_fun S 2, dX_fourierInv (mulCj 0 S), dX_fourierInv (mulCj 1 S),
    dX_fourierInv (mulCj 2 S), lapS, fourierInv_add_apply, fourierInv_add_apply]

theorem dX_re3 {Φ : E3 → C3} (hΦ : Differentiable ℝ Φ) (j : Fin 3) (x : E3) :
    dX j (fun y => re3 (Φ y)) x = re3 (dX j Φ x) := by
  have h : (fun y => re3 (Φ y)) = fun y => re3L (Φ y) := rfl
  rw [dX, h, fderiv_postcomp hΦ re3L x]; rfl

theorem dX_im3 {Φ : E3 → C3} (hΦ : Differentiable ℝ Φ) (j : Fin 3) (x : E3) :
    dX j (fun y => im3 (Φ y)) x = im3 (dX j Φ x) := by
  have h : (fun y => im3 (Φ y)) = fun y => im3L (Φ y) := rfl
  rw [dX, h, fderiv_postcomp hΦ im3L x]; rfl

theorem re3_add (v w : C3) : re3 (v + w) = re3 v + re3 w := re3L.map_add v w
theorem im3_add (v w : C3) : im3 (v + w) = im3 v + im3 w := im3L.map_add v w

theorem lap_re3 (S : 𝓢(E3, C3)) (x : E3) :
    lap (fun y => re3 ((𝓕⁻ S : 𝓢(E3, C3)) y)) x = re3 ((𝓕⁻ (lapS S) : 𝓢(E3, C3)) x) := by
  have h1 : ∀ j, dX j (fun y => re3 ((𝓕⁻ S : 𝓢(E3, C3)) y)) =
      fun y => re3 ((𝓕⁻ (mulCj j S) : 𝓢(E3, C3)) y) := by
    intro j; funext y
    rw [dX_re3 (𝓕⁻ S : 𝓢(E3, C3)).differentiable, dX_fourierInv]
  rw [lap, Fin.sum_univ_three, h1, h1, h1, dX_re3 (𝓕⁻ _ : 𝓢(E3, C3)).differentiable,
    dX_re3 (𝓕⁻ _ : 𝓢(E3, C3)).differentiable, dX_re3 (𝓕⁻ _ : 𝓢(E3, C3)).differentiable,
    dX_fourierInv, dX_fourierInv, dX_fourierInv, lapS, fourierInv_add_apply,
    fourierInv_add_apply, re3_add, re3_add]

theorem lap_im3 (S : 𝓢(E3, C3)) (x : E3) :
    lap (fun y => im3 ((𝓕⁻ S : 𝓢(E3, C3)) y)) x = im3 ((𝓕⁻ (lapS S) : 𝓢(E3, C3)) x) := by
  have h1 : ∀ j, dX j (fun y => im3 ((𝓕⁻ S : 𝓢(E3, C3)) y)) =
      fun y => im3 ((𝓕⁻ (mulCj j S) : 𝓢(E3, C3)) y) := by
    intro j; funext y
    rw [dX_im3 (𝓕⁻ S : 𝓢(E3, C3)).differentiable, dX_fourierInv]
  rw [lap, Fin.sum_univ_three, h1, h1, h1, dX_im3 (𝓕⁻ _ : 𝓢(E3, C3)).differentiable,
    dX_im3 (𝓕⁻ _ : 𝓢(E3, C3)).differentiable, dX_im3 (𝓕⁻ _ : 𝓢(E3, C3)).differentiable,
    dX_fourierInv, dX_fourierInv, dX_fourierInv, lapS, fourierInv_add_apply,
    fourierInv_add_apply, im3_add, im3_add]

theorem rot_Psr_fun (G : 𝓢(E3, C3)) :
    rot (Psr G) = fun x => re3 ((𝓕⁻ (Ms G) : 𝓢(E3, C3)) x) := funext (rot_Psr G)

theorem rot_Psi_fun (G : 𝓢(E3, C3)) :
    rot (Psi G) = fun x => im3 ((𝓕⁻ (Ms G) : 𝓢(E3, C3)) x) := funext (rot_Psi G)

theorem inner_cpx_eq (v : E3) (w : C3) :
    ⟪cpx v, w⟫_ℂ = (inner ℝ v (re3 w) : ℂ) + Complex.I * (inner ℝ v (im3 w) : ℂ) := by
  rw [inner_cpx, inner_E3, inner_E3]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [re3_apply, im3_apply]
  conv_lhs => rw [← Complex.re_add_im (w k)]
  ring

/-! ### Integrabilidade -/

section Phys

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem memLp_U (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    MemLp (fun x => U (x, s)) 2 := by
  obtain ⟨C, hC⟩ := h.2.2.2.2.2 s hs.2
  have hi := ((hC s ⟨hs.1, le_rfl⟩).1).1
  exact (memLp_two_iff_integrable_sq_norm (continuous_fatia_U h.1 hs).aestronglyMeasurable).mpr hi

theorem memLp_cU (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    MemLp (fun x => cpx (U (x, s))) 2 :=
  cpxL.comp_memLp' (memLp_U h hs)

theorem exists_energy (h : SolucaoLocal ν u₀ T U P) {t : ℝ} (ht : t < T) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc 0 t, ∫ x, ‖U (x, s)‖ ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := h.2.2.2.2.2 t ht
  exact ⟨max C 0, le_max_right _ _, fun s hs => ((hC s hs).1.2).trans (le_max_left _ _)⟩

theorem integrable_sq_U (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    Integrable fun x => ‖U (x, s)‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (memLp_U h hs).aestronglyMeasurable).mp (memLp_U h hs)

theorem integrable_inner_real {f g : E3 → E3} (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable fun x => inner ℝ (f x) (g x) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  refine h.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem memLp_re3_schwartz (S : 𝓢(E3, C3)) : MemLp (fun x => re3 (S x)) 2 :=
  re3L.comp_memLp' (S.memLp 2)

theorem memLp_im3_schwartz (S : 𝓢(E3, C3)) : MemLp (fun x => im3 (S x)) 2 :=
  im3L.comp_memLp' (S.memLp 2)

theorem exists_bound_schwartz (S : 𝓢(E3, C3)) : ∃ K, 0 ≤ K ∧ ∀ x, ‖S x‖ ≤ K :=
  ⟨‖S.toBoundedContinuousFunction‖, norm_nonneg _,
    fun x => S.toBoundedContinuousFunction.norm_coe_le_norm x⟩

theorem abs_mul_le_sq (v : E3) (j k : Fin 3) : |v j * v k| ≤ ‖v‖ ^ 2 := by
  have hj : |v j| ≤ ‖v‖ := by
    have := PiLp.norm_apply_le v j; rwa [Real.norm_eq_abs] at this
  have hk : |v k| ≤ ‖v‖ := by
    have := PiLp.norm_apply_le v k; rwa [Real.norm_eq_abs] at this
  rw [abs_mul, sq]
  exact mul_le_mul hj hk (abs_nonneg _) (norm_nonneg _)

theorem continuous_coord {f : E3 → E3} (hf : Continuous f) (j : Fin 3) :
    Continuous fun x => f x j :=
  (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hf

/-- O termo convectivo é integrável contra derivadas limitadas. -/
theorem integrable_conv_term {f : E3 → E3} (hf : Continuous f)
    (hf2 : Integrable fun x => ‖f x‖ ^ 2) {D : Fin 3 → Fin 3 → E3 → ℂ}
    (hD : ∀ j k, Continuous (D j k)) {K : ℝ} (hK : ∀ j k x, ‖D j k x‖ ≤ K) :
    Integrable fun x => ∑ j, ∑ k, ((f x j * f x k : ℝ) : ℂ) * D j k x := by
  refine integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => ?_
  refine (hf2.const_mul K).mono' ?_ (Eventually.of_forall fun x => ?_)
  · have hc : Continuous fun x => ((f x j * f x k : ℝ) : ℂ) * D j k x :=
      (Complex.continuous_ofReal.comp ((continuous_coord hf j).mul
        (continuous_coord hf k))).mul (hD j k)
    exact hc.aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm K]
    exact mul_le_mul (abs_mul_le_sq _ j k) (hK j k x) (norm_nonneg _) (sq_nonneg _)

theorem integrable_conv_term_real {f : E3 → E3} (hf : Continuous f)
    (hf2 : Integrable fun x => ‖f x‖ ^ 2) {D : Fin 3 → Fin 3 → E3 → ℝ}
    (hD : ∀ j k, Continuous (D j k)) {K : ℝ} (hK : ∀ j k x, |D j k x| ≤ K) :
    Integrable fun x => ∑ j, ∑ k, f x j * f x k * D j k x := by
  refine integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => ?_
  refine (hf2.const_mul K).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (((continuous_coord hf j).mul (continuous_coord hf k)).mul (hD j k)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, mul_comm K]
    exact mul_le_mul (abs_mul_le_sq _ j k) (hK j k x) (abs_nonneg _) (sq_nonneg _)

/-! ### Integrabilidade no tempo de integrais paramétricas -/

/-- Uma integral paramétrica de integrando contínuo em `ℝ³ × [0, t]` e limitada é integrável
em `[0, t]`. -/
theorem intervalIntegrable_param {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : E3 × ℝ → W} {t : ℝ} (ht : 0 ≤ t)
    (hF : ContinuousOn F (univ ×ˢ Icc 0 t)) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 t, ‖∫ x, F (x, s)‖ ≤ M) :
    IntervalIntegrable (fun s => ∫ x, F (x, s)) volume 0 t := by
  set c : ℝ → ℝ := fun s => max 0 (min s t) with hc_def
  have hc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcm : ∀ s, c s ∈ Icc 0 t := fun s => ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩
  have hcs : ∀ s ∈ Icc 0 t, c s = s := fun s hs => by
    simp only [hc_def, min_eq_left hs.2, max_eq_right hs.1]
  set G : E3 × ℝ → W := fun p => F (p.1, c p.2) with hG_def
  have hG : Continuous G :=
    hF.comp_continuous (continuous_fst.prodMk (hc.comp continuous_snd))
      (fun p => ⟨mem_univ _, hcm _⟩)
  have hg : StronglyMeasurable fun s => ∫ x, G (x, s) :=
    hG.stronglyMeasurable.integral_prod_left'
  have hI : IntegrableOn (fun s => ∫ x, G (x, s)) (Ioc 0 t) volume :=
    Measure.integrableOn_of_bounded (M := M) (by simp) hg.aestronglyMeasurable
      (Eventually.of_forall fun s => hM (c s) (hcm s))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  refine hI.congr_fun (fun s hs => ?_) measurableSet_Ioc
  simp only [hG_def, hcs s (Ioc_subset_Icc_self hs)]

end Phys

theorem norm_re3_le (v : C3) : ‖re3 v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  simp only [re3_apply, Real.norm_eq_abs, sq_abs]
  have := Complex.abs_re_le_norm (v k)
  nlinarith [abs_nonneg (v k).re, sq_abs (v k).re]

theorem norm_im3_le (v : C3) : ‖im3 v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  simp only [im3_apply, Real.norm_eq_abs, sq_abs]
  have := Complex.abs_im_le_norm (v k)
  nlinarith [abs_nonneg (v k).im, sq_abs (v k).im]

theorem norm_inner_le_half (a b : E3) : ‖inner ℝ a b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  have h1 := norm_inner_le_norm (𝕜 := ℝ) a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem abs_conv_sum_le (v : E3) {K : ℝ} (D : Fin 3 → E3) (hD : ∀ j, ‖D j‖ ≤ K) :
    |∑ j, ∑ k, v j * v k * D j k| ≤ 9 * K * ‖v‖ ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hD 0)
  calc |∑ j, ∑ k, v j * v k * D j k| ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖v‖ ^ 2 * K := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul]
        have h2 : |D j k| ≤ K := by
          have := PiLp.norm_apply_le (D j) k
          rw [Real.norm_eq_abs] at this
          exact this.trans (hD j)
        exact mul_le_mul (abs_mul_le_sq v j k) h2 (abs_nonneg _) (sq_nonneg _)
    _ = 9 * K * ‖v‖ ^ 2 := by simp [Finset.sum_const]; ring

section Weak

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

/-- O lado direito da formulação fraca é integrável no tempo. -/
theorem intervalIntegrable_Bw (h : SolucaoLocal ν u₀ T U P) {φ : E3 → E3}
    (hlap : Continuous (lap φ)) (hlap2 : Integrable fun x => ‖lap φ x‖ ^ 2)
    (hd : ∀ j, Continuous (dX j φ)) {K : ℝ} (hK : ∀ j x, ‖dX j φ x‖ ≤ K) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < T) : IntervalIntegrable (Bw ν U φ) volume 0 t := by
  obtain ⟨C, hC0, hC⟩ := exists_energy h ht
  have hUc : ContinuousOn U (univ ×ˢ Icc 0 t) :=
    h.1.continuousOn.mono (fun p hp => ⟨mem_univ _, hp.2.1, hp.2.2.trans_lt ht⟩)
  have hs' : ∀ s ∈ Icc 0 t, s ∈ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt ht⟩
  have h1 : IntervalIntegrable (fun s => ∫ x, inner ℝ (U (x, s)) (lap φ x)) volume 0 t := by
    refine intervalIntegrable_param (F := fun p => inner ℝ (U p) (lap φ p.1)) ht0
      (hUc.inner (hlap.comp continuous_fst).continuousOn)
      (M := (C + ∫ x, ‖lap φ x‖ ^ 2) / 2) (fun s hs => ?_)
    have hi := integrable_sq_U h (hs' s hs)
    calc ‖∫ x, inner ℝ (U (x, s)) (lap φ x)‖
        ≤ ∫ x, (‖U (x, s)‖ ^ 2 + ‖lap φ x‖ ^ 2) / 2 :=
          norm_integral_le_of_norm_le ((hi.add hlap2).div_const 2)
            (Eventually.of_forall fun x => norm_inner_le_half _ _)
      _ = ((∫ x, ‖U (x, s)‖ ^ 2) + ∫ x, ‖lap φ x‖ ^ 2) / 2 := by
          rw [integral_div, integral_add hi hlap2]
      _ ≤ (C + ∫ x, ‖lap φ x‖ ^ 2) / 2 := by
          have := hC s hs
          linarith
  have h2 : IntervalIntegrable
      (fun s => ∫ x, ∑ j, ∑ k, U (x, s) j * U (x, s) k * dX j φ x k) volume 0 t := by
    have hcont : ContinuousOn (fun p : E3 × ℝ => ∑ j, ∑ k, U p j * U p k * dX j φ p.1 k)
        (univ ×ˢ Icc 0 t) := by
      refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
      have hj : ContinuousOn (fun p : E3 × ℝ => U p j) (univ ×ˢ Icc 0 t) :=
        (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn hUc
      have hk : ContinuousOn (fun p : E3 × ℝ => U p k) (univ ×ˢ Icc 0 t) :=
        (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn hUc
      exact (hj.mul hk).mul (((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp
        ((hd j).comp continuous_fst)).continuousOn)
    refine intervalIntegrable_param
      (F := fun p : E3 × ℝ => ∑ j, ∑ k, U p j * U p k * dX j φ p.1 k) ht0 hcont
      (M := 9 * K * C) (fun s hs => ?_)
    have hi := integrable_sq_U h (hs' s hs)
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 0)
    calc ‖∫ x, ∑ j, ∑ k, U (x, s) j * U (x, s) k * dX j φ x k‖
        ≤ ∫ x, 9 * K * ‖U (x, s)‖ ^ 2 :=
          norm_integral_le_of_norm_le (hi.const_mul _) (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs]
            exact abs_conv_sum_le (U (x, s)) (fun j => dX j φ x) (fun j => hK j x))
      _ = 9 * K * ∫ x, ‖U (x, s)‖ ^ 2 := integral_const_mul _ _
      _ ≤ 9 * K * C := mul_le_mul_of_nonneg_left (hC s hs) (by positivity)
  have e : Bw ν U φ = fun s => ν * (∫ x, inner ℝ (U (x, s)) (lap φ x)) +
      ∫ x, ∑ j, ∑ k, U (x, s) j * U (x, s) k * dX j φ x k := rfl
  rw [e]
  exact (h1.const_mul ν).add h2

theorem integral_cpx_inner {f : E3 → E3} (hf : MemLp f 2) (S : 𝓢(E3, C3)) :
    ∫ x, ⟪cpx (f x), S x⟫_ℂ = ((∫ x, inner ℝ (f x) (re3 (S x)) : ℝ) : ℂ) +
      Complex.I * ((∫ x, inner ℝ (f x) (im3 (S x)) : ℝ) : ℂ) := by
  simp_rw [inner_cpx_eq]
  rw [integral_add ((integrable_inner_real hf (memLp_re3_schwartz S)).ofReal)
    (((integrable_inner_real hf (memLp_im3_schwartz S)).ofReal).const_mul _),
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

theorem dX_rot_Psr (G : 𝓢(E3, C3)) (j : Fin 3) (x : E3) :
    dX j (rot (Psr G)) x = re3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) := by
  rw [rot_Psr_fun, dX_re3 (𝓕⁻ (Ms G) : 𝓢(E3, C3)).differentiable, dX_fourierInv]

theorem dX_rot_Psi (G : 𝓢(E3, C3)) (j : Fin 3) (x : E3) :
    dX j (rot (Psi G)) x = im3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) := by
  rw [rot_Psi_fun, dX_im3 (𝓕⁻ (Ms G) : 𝓢(E3, C3)).differentiable, dX_fourierInv]

theorem lap_rot_Psr (G : 𝓢(E3, C3)) (x : E3) :
    lap (rot (Psr G)) x = re3 ((𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)) x) := by
  rw [rot_Psr_fun, lap_re3]

theorem lap_rot_Psi (G : 𝓢(E3, C3)) (x : E3) :
    lap (rot (Psi G)) x = im3 ((𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)) x) := by
  rw [rot_Psi_fun, lap_im3]

theorem exists_bound_D (G : 𝓢(E3, C3)) :
    ∃ K, 0 ≤ K ∧ ∀ j x, ‖(𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x‖ ≤ K := by
  have hb : ∀ j : Fin 3, ∃ K, 0 ≤ K ∧ ∀ x, ‖(𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x‖ ≤ K :=
    fun j => exists_bound_schwartz _
  choose Kf hKf0 hKf using hb
  refine ⟨∑ j, Kf j, Finset.sum_nonneg fun j _ => hKf0 j, fun j x => (hKf j x).trans ?_⟩
  exact Finset.single_le_sum (fun i _ => hKf0 i) (Finset.mem_univ j)

/-- O integrando complexo da formulação fraca. -/
noncomputable def BwC (ν : ℝ) (U : E3 × ℝ → E3) (G : 𝓢(E3, C3)) (s : ℝ) : ℂ :=
  (ν : ℂ) * (∫ x, ⟪cpx (U (x, s)), (𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)) x⟫_ℂ) +
    ∫ x, ∑ j, ∑ k, ((U (x, s) j * U (x, s) k : ℝ) : ℂ) * (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x k

theorem Bw_combo (h : SolucaoLocal ν u₀ T U P) (G : 𝓢(E3, C3)) {s : ℝ} (hs : s ∈ Ico 0 T) :
    ((Bw ν U (rot (Psr G)) s : ℝ) : ℂ) + Complex.I * ((Bw ν U (rot (Psi G)) s : ℝ) : ℂ) =
      BwC ν U G s := by
  have hU := memLp_U h hs
  have hU2 := integrable_sq_U h hs
  have hUc := continuous_fatia_U h.1 hs
  obtain ⟨K, hK0, hK⟩ := exists_bound_D G
  unfold Bw BwC
  simp only [lap_rot_Psr, lap_rot_Psi, dX_rot_Psr, dX_rot_Psi]
  rw [integral_cpx_inner hU (𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3))]
  have i1 := integrable_conv_term_real hUc hU2
    (D := fun j k x => re3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) k)
    (fun j k => continuous_coord (re3L.continuous.comp (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)).continuous) k)
    (fun j k x => by
      have := PiLp.norm_apply_le (re3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x)) k
      rw [Real.norm_eq_abs] at this
      exact this.trans ((norm_re3_le _).trans (hK j x)))
  have i2 := integrable_conv_term_real hUc hU2
    (D := fun j k x => im3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) k)
    (fun j k => continuous_coord (im3L.continuous.comp (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)).continuous) k)
    (fun j k x => by
      have := PiLp.norm_apply_le (im3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x)) k
      rw [Real.norm_eq_abs] at this
      exact this.trans ((norm_im3_le _).trans (hK j x)))
  have hN : ∫ x, ∑ j, ∑ k, ((U (x, s) j * U (x, s) k : ℝ) : ℂ) *
        (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x k =
      ((∫ x, ∑ j, ∑ k, U (x, s) j * U (x, s) k *
          re3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) k : ℝ) : ℂ) +
        Complex.I * ((∫ x, ∑ j, ∑ k, U (x, s) j * U (x, s) k *
          im3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) k : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
      ← integral_add i1.ofReal (i2.ofReal.const_mul _)]
    congr 1 with x
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [re3_apply, im3_apply]
    conv_lhs => rw [← Complex.re_add_im ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x k)]
    ring
  rw [hN]
  push_cast
  ring

/-- **Formulação fraca com campo-teste complexo** `Φ = 𝓕⁻ m` (rotacional de `𝓕⁻ G`). -/
theorem fraca_complexa (h : SolucaoLocal ν u₀ T U P) (G : 𝓢(E3, C3)) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    (∫ x, ⟪cpx (U (x, t)), (𝓕⁻ (Ms G) : 𝓢(E3, C3)) x⟫_ℂ) -
        ∫ x, ⟪cpx (u₀ x), (𝓕⁻ (Ms G) : 𝓢(E3, C3)) x⟫_ℂ =
      ∫ s in (0 : ℝ)..t, BwC ν U G s := by
  have hr := formulacao_fraca_rot h (Psr G) ht
  have hi := formulacao_fraca_rot h (Psi G) ht
  simp only [rot_Psr, rot_Psi] at hr hi
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, ht.1.trans_lt ht.2⟩
  have hu0 : MemLp u₀ 2 := by
    have := memLp_U h h0
    rwa [show (fun x => U (x, 0)) = u₀ from funext h.2.2.1] at this
  rw [integral_cpx_inner (memLp_U h ht), integral_cpx_inner hu0]
  -- integrabilidade no tempo
  obtain ⟨K, hK0, hK⟩ := exists_bound_D G
  have iR : IntervalIntegrable (Bw ν U (rot (Psr G))) volume 0 t := by
    refine intervalIntegrable_Bw h (K := K) ?_ ?_ (fun j => ?_) (fun j x => ?_) ht.1 ht.2
    · rw [show lap (rot (Psr G)) = fun x => re3 ((𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)) x) from
        funext (lap_rot_Psr G)]
      exact re3L.continuous.comp (𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)).continuous
    · rw [show lap (rot (Psr G)) = fun x => re3 ((𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)) x) from
        funext (lap_rot_Psr G)]
      have hm := memLp_re3_schwartz (𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3))
      exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    · rw [show dX j (rot (Psr G)) = fun x => re3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) from
        funext (dX_rot_Psr G j)]
      exact re3L.continuous.comp (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)).continuous
    · rw [dX_rot_Psr]; exact (norm_re3_le _).trans (hK j x)
  have iI : IntervalIntegrable (Bw ν U (rot (Psi G))) volume 0 t := by
    refine intervalIntegrable_Bw h (K := K) ?_ ?_ (fun j => ?_) (fun j x => ?_) ht.1 ht.2
    · rw [show lap (rot (Psi G)) = fun x => im3 ((𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)) x) from
        funext (lap_rot_Psi G)]
      exact im3L.continuous.comp (𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)).continuous
    · rw [show lap (rot (Psi G)) = fun x => im3 ((𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3)) x) from
        funext (lap_rot_Psi G)]
      have hm := memLp_im3_schwartz (𝓕⁻ (lapS (Ms G)) : 𝓢(E3, C3))
      exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    · rw [show dX j (rot (Psi G)) = fun x => im3 ((𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x) from
        funext (dX_rot_Psi G j)]
      exact im3L.continuous.comp (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)).continuous
    · rw [dX_rot_Psi]; exact (norm_im3_le _).trans (hK j x)
  have hcongr : ∫ s in (0 : ℝ)..t, BwC ν U G s = ∫ s in (0 : ℝ)..t,
      (((Bw ν U (rot (Psr G)) s : ℝ) : ℂ) + Complex.I * ((Bw ν U (rot (Psi G)) s : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le ht.1] at hs
    exact (Bw_combo h G ⟨hs.1, hs.2.trans_lt ht.2⟩).symm
  have iRc : IntervalIntegrable (fun s => ((Bw ν U (rot (Psr G)) s : ℝ) : ℂ)) volume 0 t :=
    ⟨iR.1.ofReal, iR.2.ofReal⟩
  have iIc : IntervalIntegrable (fun s => ((Bw ν U (rot (Psi G)) s : ℝ) : ℂ)) volume 0 t :=
    ⟨iI.1.ofReal, iI.2.ofReal⟩
  rw [hcongr, intervalIntegral.integral_add iRc (iIc.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, ← hr, ← hi]
  push_cast
  ring

end Weak

/-! ### Tradução para o lado de Fourier -/

/-- O pareamento `L¹`–integrável: `∫ ⟪𝓕 f, g⟫ = ∫ ⟪f, 𝓕⁻ g⟫`. -/
theorem integral_inner_fourier_L1 {f g : E3 → C3} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, ⟪𝓕 f ξ, g ξ⟫_ℂ = ∫ x, ⟪f x, 𝓕⁻ g x⟫_ℂ := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (μ := volume) (ν := volume)
    (e := Real.fourierChar) (L := innerₗ E3) (innerSL ℂ) Real.continuous_fourierChar
    continuous_inner hf hg
  have hflip : (-(innerₗ E3 : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ).flip) = -innerₗ E3 := by
    ext x y; simp
  rw [hflip, ← ATK.NSPlancherel.fourierInv_eq_vector] at h
  simp only [innerSL_apply_apply] at h
  exact h

/-- A transformada `L²` da solução no instante `s`. -/
noncomputable def bF (U : E3 × ℝ → E3) (s : ℝ) : E3 → C3 := FL fun x => cpx (U (x, s))

/-- O termo não linear no lado de Fourier: `N(s, ξ) = 2πi 𝓕[⟪ξ, u⟫ u](ξ)`. -/
noncomputable def NU (U : E3 × ℝ → E3) (s : ℝ) (ξ : E3) : C3 :=
  ((2 * π : ℝ) * Complex.I : ℂ) •
    𝓕 (fun x => ⟪cpx ξ, cpx (U (x, s))⟫_ℂ • cpx (U (x, s))) ξ

section Trad

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem integrable_cpx_mul (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T)
    (j : Fin 3) : Integrable fun x => cpx (U (x, s) j • U (x, s)) := by
  have hUc := continuous_fatia_U h.1 hs
  refine (integrable_sq_U h hs).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (cpxL.continuous.comp ((continuous_coord hUc j).smul hUc)).aestronglyMeasurable
  · rw [norm_cpx, norm_smul, Real.norm_eq_abs, sq]
    have := PiLp.norm_apply_le (U (x, s)) j
    rw [Real.norm_eq_abs] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem integral_inner_bounded {f : E3 → C3} (hf : Integrable f) {g : E3 → C3}
    (hg : Continuous g) {K : ℝ} (hK : ∀ x, ‖g x‖ ≤ K) : Integrable fun x => ⟪f x, g x⟫_ℂ := by
  refine (hf.norm.mul_const K).mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hK x) (norm_nonneg _))

theorem norm_fourier_le_L1 {f : E3 → C3} (ξ : E3) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1 with x
  rw [Circle.norm_smul]

theorem fourier_smul_sum {f : Fin 3 → E3 → C3} (hf : ∀ j, Integrable (f j)) (c : Fin 3 → ℂ)
    (ξ : E3) : ∑ j, c j • 𝓕 (f j) ξ = 𝓕 (fun x => ∑ j, c j • f j x) ξ := by
  simp only [Real.fourier_eq]
  have hi : ∀ j, Integrable fun x => 𝐞 (-⟪x, ξ⟫_ℝ) • f j x := fun j =>
    (Real.fourierIntegral_convergent_iff (μ := volume) ξ).mpr (hf j)
  simp_rw [← integral_smul]
  rw [← integral_finsetSum _ fun j _ =>
    ((hi j).smul (c j) : Integrable (fun x => c j • (𝐞 (-⟪x, ξ⟫_ℝ) • f j x)))]
  congr 1
  funext x
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

theorem cj_sum_cpx (v ξ : E3) :
    ∑ j, cj j ξ • cpx (v j • v) = ((2 * π : ℝ) * Complex.I : ℂ) • (⟪cpx ξ, cpx v⟫_ℂ • cpx v) := by
  ext k
  simp only [Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cpx_apply,
    inner_cpx, cj]
  push_cast
  ring

theorem NU_eq (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) (ξ : E3) :
    NU U s ξ = ∑ j, cj j ξ • 𝓕 (fun x => cpx (U (x, s) j • U (x, s))) ξ := by
  rw [fourier_smul_sum (fun j => integrable_cpx_mul h hs j), NU, Real.fourier_eq,
    Real.fourier_eq, ← integral_smul]
  congr 1 with x
  rw [cj_sum_cpx, smul_comm]

theorem continuous_fourier_L1 {f : E3 → C3} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

theorem integrable_inner_of_bounded_left {f g : E3 → C3} (hf : AEStronglyMeasurable f volume)
    {K : ℝ} (hK : ∀ x, ‖f x‖ ≤ K) (hg : Integrable g) : Integrable fun x => ⟪f x, g x⟫_ℂ := by
  refine (hg.norm.const_mul K).mono' (hf.inner hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))

theorem term_A (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) (S : 𝓢(E3, C3)) :
    ∫ x, ⟪cpx (U (x, s)), (𝓕⁻ S : 𝓢(E3, C3)) x⟫_ℂ = ∫ ξ, ⟪bF U s ξ, S ξ⟫_ℂ :=
  (integral_inner_FL (memLp_cU h hs) S).symm

theorem term_C (h : SolucaoLocal ν u₀ T U P) (G : 𝓢(E3, C3)) {s : ℝ} (hs : s ∈ Ico 0 T) :
    ∫ x, ∑ j, ∑ k, ((U (x, s) j * U (x, s) k : ℝ) : ℂ) * (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x k =
      -∫ ξ, ⟪NU U s ξ, mtf G ξ⟫_ℂ := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_D G
  have e1 : ∀ x, ∑ j, ∑ k, ((U (x, s) j * U (x, s) k : ℝ) : ℂ) *
      (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x k =
      ∑ j, ⟪cpx (U (x, s) j • U (x, s)), (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x⟫_ℂ := by
    intro x
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_cpx]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
  simp_rw [e1]
  rw [integral_finsetSum _ fun j _ => integral_inner_bounded (integrable_cpx_mul h hs j)
    (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)).continuous (hK j)]
  have e2 : ∀ j, ∫ x, ⟪cpx (U (x, s) j • U (x, s)), (𝓕⁻ (mulCj j (Ms G)) : 𝓢(E3, C3)) x⟫_ℂ =
      ∫ ξ, ⟪𝓕 (fun x => cpx (U (x, s) j • U (x, s))) ξ, mulCj j (Ms G) ξ⟫_ℂ := by
    intro j
    rw [integral_inner_fourier_L1 (integrable_cpx_mul h hs j) (mulCj j (Ms G)).integrable,
      SchwartzMap.fourierInv_coe]
  simp_rw [e2]
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable fun ξ =>
      ⟪𝓕 (fun x => cpx (U (x, s) j • U (x, s))) ξ, mulCj j (Ms G) ξ⟫_ℂ := fun j _ =>
    integrable_inner_of_bounded_left
      (continuous_fourier_L1 (integrable_cpx_mul h hs j)).aestronglyMeasurable
      (fun ξ => norm_fourier_le_L1 ξ) (mulCj j (Ms G)).integrable
  rw [← integral_finsetSum _ hint, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [NU_eq h hs ξ, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulCj_apply, Ms_apply, inner_smul_right, inner_smul_left, conj_cj]
  ring

theorem term_D (u₀S : SchwartzMap E3 E3) (G : 𝓢(E3, C3)) :
    ∫ x, ⟪cpx (u₀S x), (𝓕⁻ (Ms G) : 𝓢(E3, C3)) x⟫_ℂ = ∫ ξ, ⟪ahat u₀S ξ, mtf G ξ⟫_ℂ := by
  have h := SchwartzMap.integral_sesq_fourier_eq (uc u₀S) (Ms G) (innerSL ℂ)
  simp only [innerSL_apply_apply] at h
  rw [ahat_eq]
  simp_rw [← Ms_apply G]
  rw [h]
  rfl

/-- **A formulação fraca no lado de Fourier.** Para `G` de Schwartz e `m = 2πi ξ × G`:
`∫ ⟪b(t), m⟫ − ∫ ⟪â₀, m⟫ = ∫₀ᵗ (ν ∫ ⟪b(s), −4π²‖ξ‖² m⟫ − ∫ ⟪N(s), m⟫) ds`. -/
theorem fraca_fourier (h : SolucaoLocal ν u₀ T U P) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) (G : 𝓢(E3, C3)) {t : ℝ} (ht : t ∈ Ico 0 T) :
    (∫ ξ, ⟪bF U t ξ, mtf G ξ⟫_ℂ) - ∫ ξ, ⟪ahat u₀S ξ, mtf G ξ⟫_ℂ =
      ∫ s in (0 : ℝ)..t, ((ν : ℂ) * (∫ ξ, ⟪bF U s ξ,
          (-(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) • mtf G ξ⟫_ℂ) - ∫ ξ, ⟪NU U s ξ, mtf G ξ⟫_ℂ) := by
  have hc := fraca_complexa h G ht
  have hu : (fun x => cpx (u₀ x)) = fun x => cpx (u₀S x) := funext fun x => by rw [hu₀]
  rw [term_A h ht, show (fun x => ⟪cpx (u₀ x), (𝓕⁻ (Ms G) : 𝓢(E3, C3)) x⟫_ℂ) =
    fun x => ⟪cpx (u₀S x), (𝓕⁻ (Ms G) : 𝓢(E3, C3)) x⟫_ℂ from funext fun x => by rw [hu₀],
    term_D] at hc
  simp_rw [Ms_apply] at hc
  rw [hc]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [uIcc_of_le ht.1] at hs
  have hs' : s ∈ Ico 0 T := ⟨hs.1, hs.2.trans_lt ht.2⟩
  simp only [BwC]
  rw [term_A h hs', term_C h G hs']
  simp_rw [lapS_apply, Ms_apply]
  rw [sub_eq_add_neg]

end Trad

end ATK.NSFracaFourier

#print axioms ATK.NSFracaFourier.im3L_apply
#print axioms ATK.NSFracaFourier.decomp
#print axioms ATK.NSFracaFourier.cr_apply0
#print axioms ATK.NSFracaFourier.cr_apply1
#print axioms ATK.NSFracaFourier.cr_apply2
#print axioms ATK.NSFracaFourier.cr_add_right
#print axioms ATK.NSFracaFourier.cr_smul_right
#print axioms ATK.NSFracaFourier.crL_apply
#print axioms ATK.NSFracaFourier.Ms_apply
#print axioms ATK.NSFracaFourier.lapS_apply
#print axioms ATK.NSFracaFourier.fourierInv_postcomp
#print axioms ATK.NSFracaFourier.fourierInv_add_apply
#print axioms ATK.NSFracaFourier.fourierInv_Ms
#print axioms ATK.NSFracaFourier.fderiv_postcomp
#print axioms ATK.NSFracaFourier.rot_Psr
#print axioms ATK.NSFracaFourier.rot_Psi
#print axioms ATK.NSFracaFourier.dX_fourierInv_fun
#print axioms ATK.NSFracaFourier.lap_fourierInv
#print axioms ATK.NSFracaFourier.dX_re3
#print axioms ATK.NSFracaFourier.dX_im3
#print axioms ATK.NSFracaFourier.re3_add
#print axioms ATK.NSFracaFourier.im3_add
#print axioms ATK.NSFracaFourier.lap_re3
#print axioms ATK.NSFracaFourier.lap_im3
#print axioms ATK.NSFracaFourier.rot_Psr_fun
#print axioms ATK.NSFracaFourier.rot_Psi_fun
#print axioms ATK.NSFracaFourier.inner_cpx_eq
#print axioms ATK.NSFracaFourier.memLp_U
#print axioms ATK.NSFracaFourier.memLp_cU
#print axioms ATK.NSFracaFourier.exists_energy
#print axioms ATK.NSFracaFourier.integrable_sq_U
#print axioms ATK.NSFracaFourier.integrable_inner_real
#print axioms ATK.NSFracaFourier.memLp_re3_schwartz
#print axioms ATK.NSFracaFourier.memLp_im3_schwartz
#print axioms ATK.NSFracaFourier.exists_bound_schwartz
#print axioms ATK.NSFracaFourier.abs_mul_le_sq
#print axioms ATK.NSFracaFourier.continuous_coord
#print axioms ATK.NSFracaFourier.integrable_conv_term
#print axioms ATK.NSFracaFourier.integrable_conv_term_real
#print axioms ATK.NSFracaFourier.intervalIntegrable_param
#print axioms ATK.NSFracaFourier.norm_re3_le
#print axioms ATK.NSFracaFourier.norm_im3_le
#print axioms ATK.NSFracaFourier.norm_inner_le_half
#print axioms ATK.NSFracaFourier.abs_conv_sum_le
#print axioms ATK.NSFracaFourier.intervalIntegrable_Bw
#print axioms ATK.NSFracaFourier.integral_cpx_inner
#print axioms ATK.NSFracaFourier.dX_rot_Psr
#print axioms ATK.NSFracaFourier.dX_rot_Psi
#print axioms ATK.NSFracaFourier.lap_rot_Psr
#print axioms ATK.NSFracaFourier.lap_rot_Psi
#print axioms ATK.NSFracaFourier.exists_bound_D
#print axioms ATK.NSFracaFourier.Bw_combo
#print axioms ATK.NSFracaFourier.fraca_complexa
#print axioms ATK.NSFracaFourier.integral_inner_fourier_L1
#print axioms ATK.NSFracaFourier.integrable_cpx_mul
#print axioms ATK.NSFracaFourier.integral_inner_bounded
#print axioms ATK.NSFracaFourier.norm_fourier_le_L1
#print axioms ATK.NSFracaFourier.fourier_smul_sum
#print axioms ATK.NSFracaFourier.cj_sum_cpx
#print axioms ATK.NSFracaFourier.NU_eq
#print axioms ATK.NSFracaFourier.continuous_fourier_L1
#print axioms ATK.NSFracaFourier.integrable_inner_of_bounded_left
#print axioms ATK.NSFracaFourier.term_A
#print axioms ATK.NSFracaFourier.term_C
#print axioms ATK.NSFracaFourier.term_D
#print axioms ATK.NSFracaFourier.fraca_fourier
