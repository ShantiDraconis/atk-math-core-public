import ATK.NSDuhamel

/-!
# ATK — Navier–Stokes: a solução suave qualquer no lado de Fourier

Camada 21 do ataque a B3 (unicidade fraca–forte, passo U-5). Para uma solução suave qualquer
`(U, P)` do modelo genuíno, com `b(s) = 𝓕[u(s)]` (transformada `L²`):

* **divergência nula e enstrofia no lado de Fourier**: `⟪ξ, b(s, ξ)⟫ = 0` q.t.p. e
  `4π² ∫ ‖ξ‖² ‖b(s)‖² = ∫ |∇u(s)|²` (a partir de `𝓕(∂ⱼ f) = 2πi ξⱼ 𝓕 f`);
* a amplitude branda `bt(t, ξ) = e^{−q t} â₀ − ∫₀ᵗ e^{−q(t−s)} P(ξ) N(s, ξ) ds`, conjuntamente
  mensurável, coincide q.t.p. com `b(t)` (fórmula de Duhamel + lema fundamental + `ξ × v = 0`,
  `⟪ξ, v⟫ = 0 ⇒ v = 0`);
* `N(s) = N(bt(s), bt(s))` (teorema da convolução em `L²`): `bt` resolve a equação branda da
  classe de Fourier.

**CLOSED_MATH continua false.**
-/

open MeasureTheory FourierTransform SchwartzMap Filter Set ComplexConjugate
open scoped ContDiff InnerProductSpace Real

namespace ATK.NSIdent

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSFisico ATK.NSFraca ATK.NSCorte ATK.NSL2
  ATK.NSDado ATK.NSPicard ATK.NSFracaFourier ATK.NSDuhamel

/-! ### Divergência nula no lado de Fourier -/

/-- O campo-teste `φ eₖ` como campo de Schwartz. -/
noncomputable def tkS {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (k : Fin 3) : 𝓢(E3, C3) :=
  (hasCompactSupport_tk hφs k).toSchwartzMap (contDiff_tk hφ k)

/-- O campo escalar `φ` (como função complexa) de Schwartz. -/
noncomputable def phS {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    𝓢(E3, ℂ) :=
  (hφs.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)

theorem fourierInv_tkS {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (k : Fin 3) (x : E3) :
    (𝓕⁻ (tkS hφ hφs k) : 𝓢(E3, C3)) x =
      (𝓕⁻ (phS hφ hφs) : 𝓢(E3, ℂ)) x • EuclideanSpace.single k (1 : ℂ) := by
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    Real.fourierInv_eq, ← integral_smul_const]
  congr 1 with ξ
  simp only [tkS, phS, HasCompactSupport.toSchwartzMap, tk, Circle.smul_def, smul_assoc]
  rfl

theorem integrable_FL_coord (f : E3 → C3) (j : Fin 3) :
    LocallyIntegrable (fun ξ => FL f ξ j) volume :=
  locallyIntegrableOn_univ.mp ((EuclideanSpace.proj (𝕜 := ℂ) j).locallyIntegrableOn_comp
    ((locallyIntegrable_FL f).locallyIntegrableOn univ))

/-- **`div f = 0` ⇒ `⟪ξ, 𝓕 f(ξ)⟫ = 0` q.t.p.** -/
theorem inner_cpx_FL_eq_zero {f : E3 → C3} (hf : Differentiable ℝ f) (h2 : MemLp f 2)
    (hd : ∀ j, MemLp (dX j f) 2) (hdiv : ∀ x, ∑ j, dX j f x j = 0) :
    ∀ᵐ ξ ∂volume, ⟪cpx ξ, FL f ξ⟫_ℂ = 0 := by
  -- passo A: `Σⱼ (𝓕 ∂ⱼ f)ⱼ = 0` q.t.p.
  have hA : ∀ᵐ ξ ∂volume, conj (∑ j, FL (dX j f) ξ j) = 0 := by
    have hloc : LocallyIntegrable (fun ξ => conj (∑ j, FL (dX j f) ξ j)) volume := by
      have hs : LocallyIntegrable (fun ξ => ∑ j, FL (dX j f) ξ j) volume := by
        have e : (fun ξ => ∑ j, FL (dX j f) ξ j) =
            fun ξ => FL (dX 0 f) ξ 0 + FL (dX 1 f) ξ 1 + FL (dX 2 f) ξ 2 := by
          funext ξ; rw [Fin.sum_univ_three]
        rw [e]
        exact ((integrable_FL_coord _ 0).add (integrable_FL_coord _ 1)).add
          (integrable_FL_coord _ 2)
      exact locallyIntegrableOn_univ.mp
        (Complex.conjCLE.toContinuousLinearMap.locallyIntegrableOn_comp
          (hs.locallyIntegrableOn univ))
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun φ hφ hφs => ?_)
    have hj : ∀ j, ∫ ξ, φ ξ • conj (FL (dX j f) ξ j) =
        ∫ x, (𝓕⁻ (phS hφ hφs) : 𝓢(E3, ℂ)) x * conj (dX j f x j) := by
      intro j
      have h1 := integral_inner_FL (hd j) (tkS hφ hφs j)
      have e1 : ∀ ξ, ⟪FL (dX j f) ξ, tkS hφ hφs j ξ⟫_ℂ = φ ξ • conj (FL (dX j f) ξ j) := by
        intro ξ
        have : tkS hφ hφs j ξ = tk φ j ξ := rfl
        rw [this, inner_tk, Complex.real_smul]
      have e2 : ∀ x, ⟪dX j f x, (𝓕⁻ (tkS hφ hφs j) : 𝓢(E3, C3)) x⟫_ℂ =
          (𝓕⁻ (phS hφ hφs) : 𝓢(E3, ℂ)) x * conj (dX j f x j) := by
        intro x
        rw [fourierInv_tkS, inner_smul_right, EuclideanSpace.inner_single_right, one_mul]
      simp_rw [e1, e2] at h1
      exact h1
    have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable fun x =>
        (𝓕⁻ (phS hφ hφs) : 𝓢(E3, ℂ)) x * conj (dX j f x j) := by
      intro j _
      have hc : MemLp (fun x => conj (dX j f x j)) 2 :=
        (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp
          ((EuclideanSpace.proj (𝕜 := ℂ) j : C3 →L[ℂ] ℂ).restrictScalars ℝ)).comp_memLp' (hd j)
      exact ((𝓕⁻ (phS hφ hφs) : 𝓢(E3, ℂ)).memLp 2).integrable_mul hc
    have hint2 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable fun ξ =>
        φ ξ • conj (FL (dX j f) ξ j) := by
      intro j _
      have hl : LocallyIntegrable (fun ξ => conj (FL (dX j f) ξ j)) volume :=
        locallyIntegrableOn_univ.mp
          (Complex.conjCLE.toContinuousLinearMap.locallyIntegrableOn_comp
            ((integrable_FL_coord _ j).locallyIntegrableOn univ))
      exact hl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφs
    have e : (fun ξ => φ ξ • conj (∑ j, FL (dX j f) ξ j)) =
        fun ξ => ∑ j, φ ξ • conj (FL (dX j f) ξ j) := by
      funext ξ; rw [map_sum, Finset.smul_sum]
    rw [e, integral_finsetSum _ hint2]
    simp_rw [hj]
    rw [← integral_finsetSum _ hint]
    have e2 : ∀ x, ∑ j, (𝓕⁻ (phS hφ hφs) : 𝓢(E3, ℂ)) x * conj (dX j f x j) = 0 := by
      intro x
      rw [← Finset.mul_sum, ← map_sum, hdiv x, map_zero, mul_zero]
    simp_rw [e2]
    exact integral_zero _ _
  -- passo B: componentes de `𝓕 ∂ⱼ f`
  have hB : ∀ j : Fin 3, ∀ᵐ ξ ∂volume, FL (dX j f) ξ j = cj j ξ * FL f ξ j := by
    intro j
    filter_upwards [FL_dX j hf h2 (hd j)] with ξ hξ
    rw [hξ]; rfl
  have hB' : ∀ᵐ ξ ∂volume, ∀ j : Fin 3, FL (dX j f) ξ j = cj j ξ * FL f ξ j := ae_all_iff.mpr hB
  filter_upwards [hA, hB'] with ξ h1 h2
  rw [map_eq_zero] at h1
  simp_rw [h2] at h1
  have e3 : ⟪cpx ξ, FL f ξ⟫_ℂ * ((2 * π : ℝ) * Complex.I : ℂ) = ∑ j, cj j ξ * FL f ξ j := by
    rw [inner_cpx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cj]; push_cast; ring
  have hne : ((2 * π : ℝ) * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [h1] at e3
  exact (mul_eq_zero.mp e3).resolve_right hne

/-! ### Enstrofia no lado de Fourier -/

theorem norm_cj (j : Fin 3) (ξ : E3) : ‖cj j ξ‖ = 2 * π * |ξ j| := by
  rw [cj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- **Enstrofia no lado de Fourier**: `4π² ∫ ‖ξ‖² ‖𝓕 f‖² = Σⱼ ∫ ‖∂ⱼ f‖²`. -/
theorem enstrofia_FL {f : E3 → C3} (hf : Differentiable ℝ f) (h2 : MemLp f 2)
    (hd : ∀ j, MemLp (dX j f) 2) :
    Integrable (fun ξ => ‖ξ‖ ^ 2 * ‖FL f ξ‖ ^ 2) ∧
      4 * π ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖FL f ξ‖ ^ 2 = ∑ j, ∫ x, ‖dX j f x‖ ^ 2 := by
  have hae : ∀ j, (fun ξ => ‖FL (dX j f) ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => (2 * π * ξ j) ^ 2 * ‖FL f ξ‖ ^ 2 := by
    intro j
    filter_upwards [FL_dX j hf h2 (hd j)] with ξ hξ
    rw [hξ, norm_smul, norm_cj, mul_pow, mul_pow, sq_abs]
    ring
  have hint : ∀ j, Integrable fun ξ => (2 * π * ξ j) ^ 2 * ‖FL f ξ‖ ^ 2 := fun j =>
    (integrable_sq_norm_of_memLp (memLp_FL _)).congr (hae j)
  have hval : ∀ j, ∫ ξ, (2 * π * ξ j) ^ 2 * ‖FL f ξ‖ ^ 2 = ∫ x, ‖dX j f x‖ ^ 2 := fun j => by
    rw [← integral_congr_ae (hae j), integral_norm_sq_FL (hd j)]
  have hpt : (fun ξ : E3 => ‖ξ‖ ^ 2 * ‖FL f ξ‖ ^ 2) =
      fun ξ => (1 / (4 * π ^ 2)) * ∑ j, (2 * π * ξ j) ^ 2 * ‖FL f ξ‖ ^ 2 := by
    funext ξ
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
    field_simp
    ring
  have hI : Integrable fun ξ => ∑ j, (2 * π * ξ j) ^ 2 * ‖FL f ξ‖ ^ 2 :=
    integrable_finsetSum _ fun j _ => hint j
  refine ⟨?_, ?_⟩
  · rw [hpt]; exact hI.const_mul _
  · rw [hpt, integral_const_mul, integral_finsetSum _ fun j _ => hint j]
    simp_rw [hval]
    field_simp

/-! ### A solução suave no lado de Fourier -/

theorem inner_cpx_mtf (G : E3 → C3) (ξ : E3) : ⟪cpx ξ, mtf G ξ⟫_ℂ = 0 := by
  rw [mtf, inner_smul_right, inner_cpx, Fin.sum_univ_three, cr_apply0, cr_apply1, cr_apply2]
  simp only [cpx_apply]
  ring

theorem inner_lp_mtf (G : E3 → C3) (ξ : E3) (v : C3) :
    ⟪lp ξ v, mtf G ξ⟫_ℂ = ⟪v, mtf G ξ⟫_ℂ := by
  rw [← inner_conj_symm, ATK.NSEnergia.inner_lp_of_div (inner_cpx_mtf G ξ) v, inner_conj_symm]

section Sol

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem contDiff_cU (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    ContDiff ℝ ∞ fun x => cpx (U (x, s)) :=
  cpxL.contDiff.comp (ATK.NSReducao.contDiff_fatia h.1 hs)

theorem dX_cU (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) (j : Fin 3) (x : E3) :
    dX j (fun y => cpx (U (y, s))) x = cpx (dX j (fatia U s) x) := by
  have hd : Differentiable ℝ (fatia U s) :=
    (ATK.NSReducao.contDiff_fatia h.1 hs).differentiable (by simp)
  have e : (fun y => cpx (U (y, s))) = fun y => cpxL (fatia U s y) := rfl
  rw [dX, e, show (fun y => cpxL (fatia U s y)) = ⇑cpxL ∘ fatia U s from rfl,
    (cpxL.hasFDerivAt.comp x (hd x).hasFDerivAt).fderiv]
  rfl

theorem exists_grad (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    Integrable (gradSq (fatia U s)) := by
  obtain ⟨C, hC⟩ := h.2.2.2.2.2 s hs.2
  exact ((hC s ⟨hs.1, le_rfl⟩).2).1

theorem exists_enstrophy (h : SolucaoLocal ν u₀ T U P) {t : ℝ} (ht : t < T) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc 0 t, ∫ x, gradSq (fatia U s) x ≤ C := by
  obtain ⟨C, hC⟩ := h.2.2.2.2.2 t ht
  exact ⟨max C 0, le_max_right _ _, fun s hs => ((hC s hs).2.2).trans (le_max_left _ _)⟩

theorem memLp_dX_cU (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) (j : Fin 3) :
    MemLp (dX j fun y => cpx (U (y, s))) 2 := by
  have hc : Continuous (dX j fun y => cpx (U (y, s))) :=
    contDiff_dX (contDiff_cU h hs) j |>.continuous
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr ?_
  refine (exists_grad h hs).mono' (hc.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [dX_cU h hs, norm_cpx, Real.norm_of_nonneg (sq_nonneg _), gradSq]
  exact Finset.single_le_sum (f := fun j => ‖dX j (fatia U s) x‖ ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)

/-- `⟪ξ, b(s, ξ)⟫ = 0` q.t.p. -/
theorem div_bF (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    ∀ᵐ ξ ∂volume, ⟪cpx ξ, bF U s ξ⟫_ℂ = 0 := by
  refine inner_cpx_FL_eq_zero ((contDiff_cU h hs).differentiable (by simp)) (memLp_cU h hs)
    (memLp_dX_cU h hs) (fun x => ?_)
  simp_rw [dX_cU h hs, cpx_apply]
  have := h.2.2.2.2.1 x s hs
  rw [div] at this
  exact_mod_cast this

/-- **Enstrofia no lado de Fourier**: `4π² ∫ ‖ξ‖² ‖b(s)‖² = ∫ |∇u(s)|²`. -/
theorem enstrofia_bF (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    Integrable (fun ξ => ‖ξ‖ ^ 2 * ‖bF U s ξ‖ ^ 2) ∧
      4 * π ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖bF U s ξ‖ ^ 2 = ∫ x, gradSq (fatia U s) x := by
  obtain ⟨h1, h2⟩ := enstrofia_FL ((contDiff_cU h hs).differentiable (by simp)) (memLp_cU h hs)
    (memLp_dX_cU h hs)
  refine ⟨h1, ?_⟩
  rw [bF, h2]
  simp_rw [dX_cU h hs, norm_cpx]
  rw [← integral_finsetSum]
  · rfl
  · intro j _
    have := memLp_dX_cU h hs j
    have h3 := integrable_sq_norm_of_memLp this
    simp_rw [dX_cU h hs, norm_cpx] at h3
    exact h3

end Sol

/-! ### A amplitude branda da solução suave -/

/-- `bt(t, ξ) = e^{−q t} â₀(ξ) − ∫₀ᵗ e^{−q(t−s)} P(ξ) N(s, ξ) ds`. -/
noncomputable def bt (ν : ℝ) (U : E3 × ℝ → E3) (u₀S : SchwartzMap E3 E3) (t : ℝ) (ξ : E3) : C3 :=
  heat ν t ξ • ahat u₀S ξ - ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)

theorem measurable_lp : Measurable fun p : E3 × C3 => ATK.NSFourierBase.lp p.1 p.2 := by
  have h1 : Measurable fun p : E3 × C3 => ⟪cpx p.1, p.2⟫_ℂ :=
    ((continuous_cpx.comp continuous_fst).inner continuous_snd).measurable
  have h2 : Measurable fun p : E3 × C3 => (((‖p.1‖ ^ 2 : ℝ)) : ℂ) :=
    (Complex.continuous_ofReal.comp ((continuous_norm.comp continuous_fst).pow 2)).measurable
  have h3 : Measurable fun p : E3 × C3 => cpx p.1 := (continuous_cpx.comp continuous_fst).measurable
  unfold ATK.NSFourierBase.lp
  exact measurable_snd.sub ((h1.div h2).smul h3)

theorem norm_np_integrand_le {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) {C : ℝ}
    (hC : ∫ x, ‖U (x, s)‖ ^ 2 ≤ C) {R M : ℝ} (hR : 0 ≤ R) {H : E3 → C3} (hH : Loc R M H)
    (ξ : E3) : ‖⟪NU U s ξ, mtf H ξ⟫_ℂ‖ ≤ 16 * π ^ 2 * R ^ 2 * C * M * chiB R ξ := by
  have hC0 : 0 ≤ ∫ x, ‖U (x, s)‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hM : 0 ≤ M := (norm_nonneg _).trans (hH.bound 0)
  have h1 := hH.norm_mt_le hR ξ
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (NU U s ξ) (mtf H ξ)
  have h3 := (norm_NU_le h hs ξ).trans (mul_le_mul_of_nonneg_left hC (by positivity))
  have hc := chiB_nonneg R ξ
  have hC' : 0 ≤ C := hC0.trans hC
  have h4 : ‖ξ‖ * chiB R ξ ≤ R * chiB R ξ := by
    by_cases hξ : ‖ξ‖ ≤ R
    · exact mul_le_mul_of_nonneg_right hξ hc
    · have : chiB R ξ = 0 := by
        unfold chiB; rw [indicator_of_notMem (by simpa using hξ)]
      rw [this]; simp
  calc ‖⟪NU U s ξ, mtf H ξ⟫_ℂ‖ ≤ (2 * π * ‖ξ‖ * C) * (8 * π * R * M * chiB R ξ) :=
        h2.trans (mul_le_mul h3 h1 (norm_nonneg _) (by positivity))
    _ = 16 * π ^ 2 * R * C * M * (‖ξ‖ * chiB R ξ) := by ring
    _ ≤ 16 * π ^ 2 * R * C * M * (R * chiB R ξ) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 16 * π ^ 2 * R ^ 2 * C * M * chiB R ξ := by ring

theorem integral_inner_left {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → C3}
    (hf : Integrable f μ) (c : C3) : ∫ x, ⟪f x, c⟫_ℂ ∂μ = ⟪∫ x, f x ∂μ, c⟫_ℂ := by
  have e : ∀ x, ⟪f x, c⟫_ℂ = conj ⟪c, f x⟫_ℂ := fun x => (inner_conj_symm _ _).symm
  simp_rw [e]
  rw [integral_conj, integral_inner hf c, inner_conj_symm]

theorem inner_real_smul_left (r : ℝ) (v w : C3) : ⟪r • v, w⟫_ℂ = (r : ℂ) * ⟪v, w⟫_ℂ := by
  rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal]

theorem mtf_tst_hk (G : E3 → C3) (ν τ : ℝ) (ξ : E3) :
    mtf (tst G (hk ν τ)) ξ = hk ν τ ξ • mtf G ξ := mt_smul G (hk ν τ) ξ

section Pair

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem np_integrand_eq (G : E3 → C3) (t s : ℝ) (ξ : E3) :
    ⟪NU U s ξ, mtf (tst G (hk ν (t - s))) ξ⟫_ℂ =
      ⟪heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ), mtf G ξ⟫_ℂ := by
  rw [mtf_tst_hk, inner_smul_right, inner_real_smul_left, inner_lp_mtf, hk]

/-- O integrando de Duhamel truncado no tempo é conjuntamente mensurável. -/
theorem stronglyMeasurable_gc (h : SolucaoLocal ν u₀ T U P) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < T) :
    StronglyMeasurable fun p : ℝ × E3 =>
      heat ν (t - p.1) p.2 • ATK.NSFourierBase.lp p.2 (NU U (max 0 (min p.1 t)) p.2) := by
  have h1 : Measurable fun p : ℝ × E3 => heat ν (t - p.1) p.2 :=
    ((continuous_heat ν).comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).measurable
  have h2 : Measurable fun p : ℝ × E3 =>
      ATK.NSFourierBase.lp p.2 (NU U (max 0 (min p.1 t)) p.2) :=
    measurable_lp.comp (measurable_snd.prodMk (stronglyMeasurable_NUc h ht0 ht).measurable)
  exact (h1.smul h2).stronglyMeasurable

theorem norm_g_le (h : SolucaoLocal ν u₀ T U P) {t : ℝ} (hν : 0 ≤ ν) {s : ℝ} (hs : s ∈ Icc 0 t)
    (ht : t < T) {C : ℝ} (hC : ∫ x, ‖U (x, s)‖ ^ 2 ≤ C) (ξ : E3) :
    ‖heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)‖ ≤ 2 * π * ‖ξ‖ * C := by
  have hs' : s ∈ Ico 0 T := ⟨hs.1, hs.2.trans_lt ht⟩
  rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
  calc heat ν (t - s) ξ * ‖ATK.NSFourierBase.lp ξ (NU U s ξ)‖ ≤ 1 * ‖NU U s ξ‖ :=
        mul_le_mul (heat_le_one hν (by linarith [hs.2]) ξ) (norm_lp_le _ _) (norm_nonneg _)
          zero_le_one
    _ ≤ 2 * π * ‖ξ‖ * C := by
        rw [one_mul]
        exact (norm_NU_le h hs' ξ).trans (mul_le_mul_of_nonneg_left hC (by positivity))

theorem integrableOn_g (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < T) (ξ : E3) :
    IntegrableOn (fun s => heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)) (Ioc 0 t) := by
  obtain ⟨C, hC0, hC⟩ := exists_energy h ht
  have hm : StronglyMeasurable fun s : ℝ =>
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U (max 0 (min s t)) ξ) :=
    by
      have h0 := (stronglyMeasurable_gc h ht0 ht).comp_measurable
        (measurable_id.prodMk (measurable_const (a := ξ)))
      exact h0
  have heq : EqOn (fun s : ℝ =>
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U (max 0 (min s t)) ξ))
      (fun s => heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)) (Ioc 0 t) := by
    intro s hs
    simp only [min_eq_left hs.2, max_eq_right hs.1.le]
  refine (Measure.integrableOn_of_bounded (M := 2 * π * ‖ξ‖ * C) (by simp)
    hm.aestronglyMeasurable ?_).congr_fun heq measurableSet_Ioc
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
  simp only [min_eq_left hs.2, max_eq_right hs.1.le]
  exact norm_g_le h hν (Ioc_subset_Icc_self hs) ht (hC s (Ioc_subset_Icc_self hs)) ξ

/-- **O pareamento de `b(t)` é o de `bt(t)`** contra os campos-teste de suporte compacto. -/
theorem pair_bt (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) {G : E3 → C3} (hG : ContDiff ℝ ∞ G) (hGs : HasCompactSupport G)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    (Integrable fun ξ => ⟪bt ν U u₀S t ξ, mtf G ξ⟫_ℂ) ∧
      ∫ ξ, ⟪bF U t ξ, mtf G ξ⟫_ℂ = ∫ ξ, ⟪bt ν U u₀S t ξ, mtf G ξ⟫_ℂ := by
  obtain ⟨R, hR0, hR⟩ := exists_R hG hGs
  obtain ⟨MG, hMG0, hMG⟩ := exists_MG hG hGs
  obtain ⟨C, hC0, hC⟩ := exists_energy h ht.2
  have ht0' : 0 ≤ t := ht.1
  have hD := duhamel h hν u₀S hu₀ hG hGs ht
  unfold Ap at hD
  set g : ℝ → E3 → C3 := fun s ξ => heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)
    with hg_def
  have hmc : Continuous (mtf G) := continuous_mt hG.continuous
  have hmcs : HasCompactSupport (mtf G) := by
    refine HasCompactSupport.intro hGs.isCompact fun ξ hξ => ?_
    rw [mtf, image_eq_zero_of_notMem_tsupport hξ]
    have hz : cr (cpx ξ) 0 = 0 := by
      ext k; fin_cases k <;> simp [cr_apply0, cr_apply1, cr_apply2]
    rw [hz, smul_zero]
  have hLoc : Loc R (MG * 1) G := by
    refine ⟨hG.continuous, fun ξ => by rw [mul_one]; exact hMG ξ, hR⟩
  -- a parte do dado
  have hA0 : A0 u₀S (tst G (hk ν t)) = ∫ ξ, ⟪heat ν t ξ • ahat u₀S ξ, mtf G ξ⟫_ℂ := by
    unfold A0
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [mtf_tst_hk, inner_smul_right, inner_real_smul_left, hk]
  -- a parte de Duhamel: Fubini
  have hloct : ∀ s ∈ Icc 0 t, Loc R (MG * 1) (tst G (hk ν (t - s))) := fun s hs =>
    loc_tst hG hGs hR hMG0 hMG (contDiff_hk _ _).continuous zero_le_one
      (fun ξ _ => norm_hk_le hν (by linarith [hs.2]) ξ)
  set c : ℝ → ℝ := fun s => max 0 (min s t) with hc_def
  have hcs : ∀ s ∈ Icc 0 t, c s = s := fun s hs => by
    simp only [hc_def, min_eq_left hs.2, max_eq_right hs.1]
  have hint : Integrable (Function.uncurry fun s ξ => ⟪g s ξ, mtf G ξ⟫_ℂ)
      ((volume.restrict (Ioc 0 t)).prod volume) := by
    have hdom : Integrable (fun p : ℝ × E3 => (1 : ℝ) *
        (16 * π ^ 2 * R ^ 2 * C * (MG * 1) * chiB R p.2))
        ((volume.restrict (Ioc 0 t)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod ((integrable_chiB R).const_mul _)
    have hae : ∀ᵐ p ∂((volume.restrict (Ioc 0 t)).prod volume), p.1 ∈ Ioc 0 t :=
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc (0 : ℝ) t))
        (ν := (volume : Measure E3))).ae (ae_restrict_mem measurableSet_Ioc)
    have hmeas : AEStronglyMeasurable (Function.uncurry fun s ξ => ⟪g s ξ, mtf G ξ⟫_ℂ)
        ((volume.restrict (Ioc 0 t)).prod volume) := by
      have hm : StronglyMeasurable fun p : ℝ × E3 =>
          ⟪heat ν (t - p.1) p.2 • ATK.NSFourierBase.lp p.2 (NU U (c p.1) p.2), mtf G p.2⟫_ℂ :=
        StronglyMeasurable.inner (𝕜 := ℂ) (stronglyMeasurable_gc h ht.1 ht.2)
          (hmc.comp continuous_snd).stronglyMeasurable
      refine hm.aestronglyMeasurable.congr ?_
      filter_upwards [hae] with p hp
      simp only [Function.uncurry, hg_def, hcs p.1 (Ioc_subset_Icc_self hp)]
    refine hdom.mono' hmeas ?_
    filter_upwards [hae] with p hp
    have hp2 := Ioc_subset_Icc_self hp
    simp only [Function.uncurry, hg_def, one_mul]
    rw [← np_integrand_eq]
    exact norm_np_integrand_le h ⟨hp2.1, hp2.2.trans_lt ht.2⟩ (hC p.1 hp2) hR0 (hloct p.1 hp2) p.2
  have hnp : ∫ s in (0 : ℝ)..t, np U s (tst G (hk ν (t - s))) =
      ∫ ξ, ⟪∫ s in (0 : ℝ)..t, g s ξ, mtf G ξ⟫_ℂ := by
    rw [intervalIntegral.integral_of_le ht.1]
    unfold np
    simp_rw [np_integrand_eq]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [intervalIntegral.integral_of_le ht.1]
    exact integral_inner_left (integrableOn_g h hν ht.1 ht.2 ξ) (mtf G ξ)
  -- integrabilidade das duas partes
  have hmint : Integrable (mtf G) := hmc.integrable_of_hasCompactSupport hmcs
  obtain ⟨Ca, hCa0, hCa⟩ := ahat_bound u₀S 0
  have i1 : Integrable fun ξ => ⟪heat ν t ξ • ahat u₀S ξ, mtf G ξ⟫_ℂ := by
    refine integrable_inner_of_bounded_left (K := Ca)
      ((((continuous_heat ν).comp (continuous_const.prodMk continuous_id)).smul
        (ahat_cont u₀S)).aestronglyMeasurable) (fun ξ => ?_) hmint
    rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
    have h1 := hCa ξ
    simp only [w, pow_zero, inv_one, mul_one] at h1
    calc heat ν t ξ * ‖ahat u₀S ξ‖ ≤ 1 * Ca :=
          mul_le_mul (heat_le_one hν ht.1 ξ) h1 (norm_nonneg _) zero_le_one
      _ = Ca := one_mul _
  have hgm : StronglyMeasurable fun ξ => ∫ s in Ioc 0 t,
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U (max 0 (min s t)) ξ) :=
    MeasureTheory.StronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) t))
      (stronglyMeasurable_gc h ht.1 ht.2)
  have hgeq : ∀ ξ, ∫ s in (0 : ℝ)..t, g s ξ = ∫ s in Ioc 0 t,
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U (max 0 (min s t)) ξ) := by
    intro ξ
    rw [intervalIntegral.integral_of_le ht.1]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    simp only [hg_def, min_eq_left hs.2, max_eq_right hs.1.le]
  have i2 : Integrable fun ξ => ⟪∫ s in (0 : ℝ)..t, g s ξ, mtf G ξ⟫_ℂ := by
    have hdom : Integrable fun ξ => t * (2 * π * R * C) * (8 * π * R * (MG * 1) * chiB R ξ) :=
      ((integrable_chiB R).const_mul _).const_mul _
    refine hdom.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · simp_rw [hgeq]
      exact (StronglyMeasurable.inner (𝕜 := ℂ) hgm hmc.stronglyMeasurable).aestronglyMeasurable
    · have hb1 : ‖∫ s in (0 : ℝ)..t, g s ξ‖ ≤ 2 * π * ‖ξ‖ * C * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
          rw [uIoc_of_le ht.1] at hs
          exact norm_g_le h hν (Ioc_subset_Icc_self hs) ht.2 (hC s (Ioc_subset_Icc_self hs)) ξ)
      rw [sub_zero, abs_of_nonneg ht.1] at hb1
      have hb2 := hLoc.norm_mt_le hR0 ξ
      have hc := chiB_nonneg R ξ
      refine (norm_inner_le_norm _ _).trans ?_
      by_cases hξ : ‖ξ‖ ≤ R
      · have hK : 0 ≤ 8 * π * R * (MG * 1) * chiB R ξ :=
          mul_nonneg (by positivity) hc
        have h3 : 2 * π * ‖ξ‖ * C * t ≤ 2 * π * R * C * t := by
          have h2 : 2 * π * ‖ξ‖ ≤ 2 * π * R := mul_le_mul_of_nonneg_left hξ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hC0) ht.1
        calc ‖∫ s in (0 : ℝ)..t, g s ξ‖ * ‖mtf G ξ‖
            ≤ (2 * π * ‖ξ‖ * C * t) * (8 * π * R * (MG * 1) * chiB R ξ) :=
              mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
          _ ≤ (2 * π * R * C * t) * (8 * π * R * (MG * 1) * chiB R ξ) :=
              mul_le_mul_of_nonneg_right h3 hK
          _ = t * (2 * π * R * C) * (8 * π * R * (MG * 1) * chiB R ξ) := by ring
      · have h0 : mtf G ξ = 0 := by
          rw [mtf, hR ξ (lt_of_not_ge hξ)]
          have hz : cr (cpx ξ) 0 = 0 := by
            ext k; fin_cases k <;> simp [cr_apply0, cr_apply1, cr_apply2]
          rw [hz, smul_zero]
        rw [h0, norm_zero, mul_zero]
        exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hc)
  -- conclusão
  have e : ∀ ξ, ⟪bt ν U u₀S t ξ, mtf G ξ⟫_ℂ =
      ⟪heat ν t ξ • ahat u₀S ξ, mtf G ξ⟫_ℂ - ⟪∫ s in (0 : ℝ)..t, g s ξ, mtf G ξ⟫_ℂ := by
    intro ξ; rw [bt, inner_sub_left]
  simp_rw [e]
  refine ⟨i1.sub i2, ?_⟩
  rw [hD, integral_sub i1 i2, hA0, hnp]

end Pair

/-! ### A identificação `b(t) = bt(t)` q.t.p. -/

theorem inner_cr_e0 (a : E3) (v : C3) :
    ⟪v, cr (cpx a) (EuclideanSpace.single 0 (1 : ℂ))⟫_ℂ =
      (a 2 : ℂ) * conj (v 1) - (a 1 : ℂ) * conj (v 2) := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, cr_apply0, cr_apply1, cr_apply2, cpx_apply] <;>
    ring

theorem inner_cr_e1 (a : E3) (v : C3) :
    ⟪v, cr (cpx a) (EuclideanSpace.single 1 (1 : ℂ))⟫_ℂ =
      (a 0 : ℂ) * conj (v 2) - (a 2 : ℂ) * conj (v 0) := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, cr_apply0, cr_apply1, cr_apply2, cpx_apply] <;>
    ring

theorem inner_cr_e2 (a : E3) (v : C3) :
    ⟪v, cr (cpx a) (EuclideanSpace.single 2 (1 : ℂ))⟫_ℂ =
      (a 1 : ℂ) * conj (v 0) - (a 0 : ℂ) * conj (v 1) := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, cr_apply0, cr_apply1, cr_apply2, cpx_apply] <;>
    ring

/-- Álgebra: `⟪ξ, v⟫ = 0` e `v ⊥ ξ × eₖ` para todo `k`, com `ξ ≠ 0`, implicam `v = 0`. -/
theorem eq_zero_of_perp {a : E3} (ha : a ≠ 0) {v : C3} (hdiv : ⟪cpx a, v⟫_ℂ = 0)
    (hk : ∀ k : Fin 3, ⟪v, cr (cpx a) (EuclideanSpace.single k (1 : ℂ))⟫_ℂ = 0) : v = 0 := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  rw [inner_cr_e0] at h0
  rw [inner_cr_e1] at h1
  rw [inner_cr_e2] at h2
  rw [inner_cpx, Fin.sum_univ_three] at hdiv
  have hd : (a 0 : ℂ) * conj (v 0) + (a 1 : ℂ) * conj (v 1) + (a 2 : ℂ) * conj (v 2) = 0 := by
    have := congrArg conj hdiv
    simp only [map_add, map_mul, Complex.conj_ofReal, map_zero] at this
    exact this
  have hn : ((a 0 : ℂ) ^ 2 + (a 1 : ℂ) ^ 2 + (a 2 : ℂ) ^ 2) ≠ 0 := by
    have : (a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 ≠ 0 := by
      rw [← Fin.sum_univ_three (fun i => a i ^ 2), ← EuclideanSpace.real_norm_sq_eq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
    have h' : (((a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr this
    push_cast at h'
    exact h'
  have c0 : ((a 0 : ℂ) ^ 2 + (a 1 : ℂ) ^ 2 + (a 2 : ℂ) ^ 2) * conj (v 0) = 0 := by
    linear_combination (a 0 : ℂ) * hd + (a 1 : ℂ) * h2 - (a 2 : ℂ) * h1
  have c1 : ((a 0 : ℂ) ^ 2 + (a 1 : ℂ) ^ 2 + (a 2 : ℂ) ^ 2) * conj (v 1) = 0 := by
    linear_combination (a 1 : ℂ) * hd - (a 0 : ℂ) * h2 + (a 2 : ℂ) * h0
  have c2 : ((a 0 : ℂ) ^ 2 + (a 1 : ℂ) ^ 2 + (a 2 : ℂ) ^ 2) * conj (v 2) = 0 := by
    linear_combination (a 2 : ℂ) * hd + (a 0 : ℂ) * h1 - (a 1 : ℂ) * h0
  ext k
  fin_cases k
  · have := (mul_eq_zero.mp c0).resolve_left hn; simpa using this
  · have := (mul_eq_zero.mp c1).resolve_left hn; simpa using this
  · have := (mul_eq_zero.mp c2).resolve_left hn; simpa using this

theorem locInt_inner_cont {g : E3 → C3} (hg : LocallyIntegrable g volume) {w : E3 → C3}
    (hw : Continuous w) : LocallyIntegrable (fun ξ => ⟪g ξ, w ξ⟫_ℂ) volume := by
  refine (locallyIntegrable_iff).mpr fun K hK => ?_
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hw.continuousOn
  have hgK := hg.integrableOn_isCompact hK
  refine (hgK.norm.const_mul M).mono'
    (hgK.aestronglyMeasurable.inner hw.aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall fun ξ hξ => ?_)
  calc ‖⟪g ξ, w ξ⟫_ℂ‖ ≤ ‖g ξ‖ * ‖w ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖g ξ‖ * M := mul_le_mul_of_nonneg_left (hM ξ hξ) (norm_nonneg _)
    _ = M * ‖g ξ‖ := mul_comm _ _

theorem hasCompactSupport_mtf {G : E3 → C3} (hGs : HasCompactSupport G) :
    HasCompactSupport (mtf G) := by
  refine HasCompactSupport.intro hGs.isCompact fun ξ hξ => ?_
  rw [mtf, image_eq_zero_of_notMem_tsupport hξ]
  have hz : cr (cpx ξ) 0 = 0 := by
    ext k; fin_cases k <;> simp [cr_apply0, cr_apply1, cr_apply2]
  rw [hz, smul_zero]

section Ident

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

/-- A parte de Duhamel de `bt` é mensurável em `ξ` e limitada por `2π‖ξ‖Ct`. -/
theorem duh_part (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ico 0 T) :
    StronglyMeasurable (fun ξ => ∫ s in (0 : ℝ)..t,
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)) ∧
    ∃ C, 0 ≤ C ∧ ∀ ξ, ‖∫ s in (0 : ℝ)..t,
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)‖ ≤ 2 * π * ‖ξ‖ * C * t := by
  obtain ⟨C, hC0, hC⟩ := exists_energy h ht.2
  have hgm : StronglyMeasurable fun ξ => ∫ s in Ioc 0 t,
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U (max 0 (min s t)) ξ) :=
    MeasureTheory.StronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) t))
      (stronglyMeasurable_gc h ht.1 ht.2)
  have hgeq : (fun ξ => ∫ s in (0 : ℝ)..t,
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)) = fun ξ => ∫ s in Ioc 0 t,
      heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U (max 0 (min s t)) ξ) := by
    funext ξ
    rw [intervalIntegral.integral_of_le ht.1]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    simp only [min_eq_left hs.2, max_eq_right hs.1.le]
  refine ⟨by rw [hgeq]; exact hgm, C, hC0, fun ξ => ?_⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ))
    (C := 2 * π * ‖ξ‖ * C) (fun s hs => by
      rw [uIoc_of_le ht.1] at hs
      exact norm_g_le h hν (Ioc_subset_Icc_self hs) ht.2 (hC s (Ioc_subset_Icc_self hs)) ξ)
  rwa [sub_zero, abs_of_nonneg ht.1] at hb

theorem locInt_bt (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3) {t : ℝ}
    (ht : t ∈ Ico 0 T) : LocallyIntegrable (bt ν U u₀S t) volume := by
  obtain ⟨hm, C, hC0, hC⟩ := duh_part h hν ht
  obtain ⟨Ca, hCa0, hCa⟩ := ahat_bound u₀S 0
  have hc1 : Continuous fun ξ => heat ν t ξ • ahat u₀S ξ :=
    ((continuous_heat ν).comp (continuous_const.prodMk continuous_id)).smul (ahat_cont u₀S)
  have hbm : StronglyMeasurable (bt ν U u₀S t) := by
    have e : bt ν U u₀S t = fun ξ => heat ν t ξ • ahat u₀S ξ - ∫ s in (0 : ℝ)..t,
        heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ) := rfl
    rw [e]; exact hc1.stronglyMeasurable.sub hm
  refine (locallyIntegrable_iff).mpr fun K hK => ?_
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  refine Measure.integrableOn_of_bounded (M := Ca + 2 * π * |r| * C * t)
    hK.measure_lt_top.ne hbm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall fun ξ hξ => ?_)
  have hξr : ‖ξ‖ ≤ |r| := by
    have := hr hξ; rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_abs_self r)
  have h1 : ‖heat ν t ξ • ahat u₀S ξ‖ ≤ Ca := by
    rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
    have h2 := hCa ξ
    simp only [w, pow_zero, inv_one, mul_one] at h2
    calc heat ν t ξ * ‖ahat u₀S ξ‖ ≤ 1 * Ca :=
          mul_le_mul (heat_le_one hν ht.1 ξ) h2 (norm_nonneg _) zero_le_one
      _ = Ca := one_mul _
  have h3 : 2 * π * ‖ξ‖ * C * t ≤ 2 * π * |r| * C * t := by
    have h4 : 2 * π * ‖ξ‖ ≤ 2 * π * |r| := mul_le_mul_of_nonneg_left hξr (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hC0) ht.1
  calc ‖bt ν U u₀S t ξ‖ ≤ ‖heat ν t ξ • ahat u₀S ξ‖ + ‖∫ s in (0 : ℝ)..t,
        heat ν (t - s) ξ • ATK.NSFourierBase.lp ξ (NU U s ξ)‖ := norm_sub_le _ _
    _ ≤ Ca + 2 * π * |r| * C * t := add_le_add h1 ((hC ξ).trans h3)

/-- `⟪ξ, bt(t, ξ)⟫ = 0`. -/
theorem div_bt (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0) {t : ℝ} (ht : t ∈ Ico 0 T) (ξ : E3) :
    ⟪cpx ξ, bt ν U u₀S t ξ⟫_ℂ = 0 := by
  rw [bt, inner_sub_right, ← Complex.coe_smul, inner_smul_right, hdiv₀, mul_zero, zero_sub,
    neg_eq_zero, intervalIntegral.integral_of_le ht.1,
    ← integral_inner (integrableOn_g h hν ht.1 ht.2 ξ)]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
  simp only [Pi.zero_apply]
  rw [← Complex.coe_smul, inner_smul_right, inner_lp, mul_zero]

/-- **Identificação**: `b(t) = bt(t)` q.t.p. -/
theorem bF_ae_eq_bt (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) (hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) : bF U t =ᵐ[volume] bt ν U u₀S t := by
  set D : E3 → C3 := fun ξ => bF U t ξ - bt ν U u₀S t ξ with hD_def
  have hD : LocallyIntegrable D volume := (locallyIntegrable_FL _).sub (locInt_bt h hν u₀S ht)
  have hk : ∀ k : Fin 3, ∀ᵐ ξ ∂volume,
      ⟪D ξ, cr (cpx ξ) (EuclideanSpace.single k (1 : ℂ))⟫_ℂ = 0 := by
    intro k
    have hw : Continuous fun ξ : E3 => cr (cpx ξ) (EuclideanSpace.single k (1 : ℂ)) :=
      continuous_cr.comp (continuous_cpx.prodMk continuous_const)
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (locInt_inner_cont hD hw)
      (fun φ hφ hφs => ?_)
    have hG := contDiff_tk hφ k
    have hGs := hasCompactSupport_tk hφs k
    obtain ⟨hib, heq⟩ := pair_bt h hν u₀S hu₀ hG hGs ht
    have hif : Integrable fun ξ => ⟪bF U t ξ, mtf (tk φ k) ξ⟫_ℂ :=
      integrable_inner_of_hasCompactSupport (locallyIntegrable_FL _)
        (continuous_mt hG.continuous) (hasCompactSupport_mtf hGs)
    have hzero : ∫ ξ, ⟪D ξ, mtf (tk φ k) ξ⟫_ℂ = 0 := by
      simp_rw [hD_def, inner_sub_left]
      rw [integral_sub hif hib, heq, sub_self]
    set c : ℂ := ((2 * π : ℝ) * Complex.I : ℂ) with hc
    have hc0 : c ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    have e : ∀ ξ, φ ξ • ⟪D ξ, cr (cpx ξ) (EuclideanSpace.single k (1 : ℂ))⟫_ℂ =
        c⁻¹ * ⟪D ξ, mtf (tk φ k) ξ⟫_ℂ := by
      intro ξ
      rw [mtf, tk, cr_smul_right, inner_smul_right, inner_smul_right, Complex.real_smul,
        ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    simp_rw [e]
    rw [integral_const_mul, hzero, mul_zero]
  have hne : ∀ᵐ ξ ∂(volume : Measure E3), ξ ≠ 0 := by
    rw [ae_iff]
    have : {a : E3 | ¬a ≠ 0} = {0} := by ext a; simp
    rw [this]; exact measure_singleton 0
  filter_upwards [hk 0, hk 1, hk 2, div_bF h ht, hne] with ξ h0 h1 h2 hdb hξ
  have hdD : ⟪cpx ξ, D ξ⟫_ℂ = 0 := by
    simp only [hD_def]
    rw [inner_sub_right, hdb, div_bt h hν u₀S hdiv₀ ht ξ, sub_zero]
  have := eq_zero_of_perp hξ hdD (fun k => by fin_cases k <;> assumption)
  exact sub_eq_zero.mp this

end Ident

/-! ### Propriedades de `bt` -/

theorem inner_cpx_cpx (a b : E3) : ⟪cpx a, cpx b⟫_ℂ = ((inner ℝ a b : ℝ) : ℂ) := by
  rw [inner_cpx, inner_E3]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cpx_apply]

theorem cj3_cpx (v : E3) : ATK.NSSimetria.cj3 (cpx v) = cpx v := by
  ext k; simp [cpx_apply, ATK.NSSimetria.cj3_apply]

/-- `N` é hermitiano: `N(s, −ξ) = conj N(s, ξ)`. -/
theorem NU_herm (U : E3 × ℝ → E3) (s : ℝ) (ξ : E3) :
    NU U s (-ξ) = ATK.NSSimetria.cj3 (NU U s ξ) := by
  rw [NU, NU, Real.fourier_eq', Real.fourier_eq', ATK.NSSimetria.cj3_smul,
    ← ATK.NSSimetria.integral_cj3]
  set c : ℂ := ((2 * π : ℝ) * Complex.I : ℂ) with hc
  have hcc : conj c = -c := by rw [hc, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hf : ∀ x, Complex.exp (↑(-2 * π * ⟪x, -ξ⟫_ℝ) * Complex.I) •
      (⟪cpx (-ξ), cpx (U (x, s))⟫_ℂ • cpx (U (x, s))) =
      -ATK.NSSimetria.cj3 (Complex.exp (↑(-2 * π * ⟪x, ξ⟫_ℝ) * Complex.I) •
        (⟪cpx ξ, cpx (U (x, s))⟫_ℂ • cpx (U (x, s)))) := by
    intro x
    rw [ATK.NSSimetria.cj3_smul, ATK.NSSimetria.cj3_smul, cj3_cpx, ATK.NSSimetria.cpx_neg, inner_neg_left,
      inner_cpx_cpx, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, inner_neg_right, neg_smul, smul_neg]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hf), integral_neg, hcc, smul_neg, neg_smul]

section Props

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

/-- `bt(t)` é hermitiana. -/
theorem bt_herm (u₀S : SchwartzMap E3 E3) (t : ℝ) :
    ATK.NSSimetria.Herm (bt ν U u₀S t) := by
  intro ξ
  rw [bt, bt, heat_neg, ATK.NSDado.ahat_herm u₀S ξ, ATK.NSSimetria.cj3_sub,
    ATK.NSSimetria.cj3_real_smul, ← ATK.NSSimetria.intervalIntegral_cj3]
  congr 1
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  try dsimp only
  rw [heat_neg, NU_herm, ATK.NSSimetria.lp_herm, ATK.NSSimetria.cj3_real_smul]

theorem bt_zero (u₀S : SchwartzMap E3 E3) (ξ : E3) : bt ν U u₀S 0 ξ = ahat u₀S ξ := by
  rw [bt, heat_zero, one_smul, intervalIntegral.integral_same, sub_zero]

theorem integral_norm_sq_bt (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) (hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) : ∫ ξ, ‖bt ν U u₀S t ξ‖ ^ 2 = ∫ x, ‖U (x, t)‖ ^ 2 := by
  rw [← integral_norm_sq_bF h ht]
  refine integral_congr_ae ?_
  filter_upwards [bF_ae_eq_bt h hν u₀S hu₀ hdiv₀ ht] with ξ hξ
  rw [hξ]

theorem memLp_bt (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) (hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) : MemLp (bt ν U u₀S t) 2 :=
  (memLp_bF U t).ae_eq (bF_ae_eq_bt h hν u₀S hu₀ hdiv₀ ht)

theorem enstrofia_bt (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) (hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    Integrable (fun ξ => ‖ξ‖ ^ 2 * ‖bt ν U u₀S t ξ‖ ^ 2) ∧
      4 * π ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖bt ν U u₀S t ξ‖ ^ 2 = ∫ x, gradSq (fatia U t) x := by
  obtain ⟨h1, h2⟩ := enstrofia_bF h ht
  have hae : (fun ξ => ‖ξ‖ ^ 2 * ‖bF U t ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => ‖ξ‖ ^ 2 * ‖bt ν U u₀S t ξ‖ ^ 2 := by
    filter_upwards [bF_ae_eq_bt h hν u₀S hu₀ hdiv₀ ht] with ξ hξ
    rw [hξ]
  exact ⟨h1.congr hae, by rw [← integral_congr_ae hae, h2]⟩

/-- **`N(s) = N(bt(s), bt(s))`** (teorema da convolução em `L²`). -/
theorem NU_eq_Nl (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) (hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0) {s : ℝ}
    (hs : s ∈ Ico 0 T) (ξ : E3) :
    NU U s ξ = Nl (bt ν U u₀S s) (bt ν U u₀S s) ξ := by
  set B : C3 →L[ℂ] C3 →L[ℂ] C3 :=
    (innerSL ℂ (cpx ξ)).smulRight (ContinuousLinearMap.id ℂ C3) with hB
  have hBapp : ∀ v w, B v w = ⟪cpx ξ, v⟫_ℂ • w := fun v w => by
    simp [hB, innerSL_apply_apply]
  have hc := conv_FL B (memLp_cU h hs) (memLp_cU h hs) ξ
  have hae : FL (fun x => cpx (U (x, s))) =ᵐ[volume] bt ν U u₀S s :=
    bF_ae_eq_bt h hν u₀S hu₀ hdiv₀ hs
  rw [cvB_congr B hae hae ξ] at hc
  simp only [hBapp] at hc
  rw [NU, Nl, ← hc]

/-- **A equação branda para `bt`**, na forma da classe de Fourier. -/
theorem bt_mild (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) (hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0) {t : ℝ}
    (ht : t ∈ Ico 0 T) (ξ : E3) :
    bt ν U u₀S t ξ = heat ν t ξ • bt ν U u₀S 0 ξ -
      ∫ s in (0 : ℝ)..t, duhI ν (bt ν U u₀S) (bt ν U u₀S) t s ξ := by
  rw [bt_zero]
  conv_lhs => rw [bt]
  congr 1
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [uIcc_of_le ht.1] at hs
  simp only [duhI]
  rw [NU_eq_Nl h hν u₀S hu₀ hdiv₀ ⟨hs.1, hs.2.trans_lt ht.2⟩ ξ]

end Props

end ATK.NSIdent

#print axioms ATK.NSIdent.fourierInv_tkS
#print axioms ATK.NSIdent.integrable_FL_coord
#print axioms ATK.NSIdent.inner_cpx_FL_eq_zero
#print axioms ATK.NSIdent.norm_cj
#print axioms ATK.NSIdent.enstrofia_FL
#print axioms ATK.NSIdent.inner_cpx_mtf
#print axioms ATK.NSIdent.inner_lp_mtf
#print axioms ATK.NSIdent.contDiff_cU
#print axioms ATK.NSIdent.dX_cU
#print axioms ATK.NSIdent.exists_grad
#print axioms ATK.NSIdent.exists_enstrophy
#print axioms ATK.NSIdent.memLp_dX_cU
#print axioms ATK.NSIdent.div_bF
#print axioms ATK.NSIdent.enstrofia_bF
#print axioms ATK.NSIdent.measurable_lp
#print axioms ATK.NSIdent.norm_np_integrand_le
#print axioms ATK.NSIdent.integral_inner_left
#print axioms ATK.NSIdent.inner_real_smul_left
#print axioms ATK.NSIdent.mtf_tst_hk
#print axioms ATK.NSIdent.np_integrand_eq
#print axioms ATK.NSIdent.stronglyMeasurable_gc
#print axioms ATK.NSIdent.norm_g_le
#print axioms ATK.NSIdent.integrableOn_g
#print axioms ATK.NSIdent.pair_bt
#print axioms ATK.NSIdent.inner_cr_e0
#print axioms ATK.NSIdent.inner_cr_e1
#print axioms ATK.NSIdent.inner_cr_e2
#print axioms ATK.NSIdent.eq_zero_of_perp
#print axioms ATK.NSIdent.locInt_inner_cont
#print axioms ATK.NSIdent.hasCompactSupport_mtf
#print axioms ATK.NSIdent.duh_part
#print axioms ATK.NSIdent.locInt_bt
#print axioms ATK.NSIdent.div_bt
#print axioms ATK.NSIdent.bF_ae_eq_bt
#print axioms ATK.NSIdent.inner_cpx_cpx
#print axioms ATK.NSIdent.cj3_cpx
#print axioms ATK.NSIdent.NU_herm
#print axioms ATK.NSIdent.bt_herm
#print axioms ATK.NSIdent.bt_zero
#print axioms ATK.NSIdent.integral_norm_sq_bt
#print axioms ATK.NSIdent.memLp_bt
#print axioms ATK.NSIdent.enstrofia_bt
#print axioms ATK.NSIdent.NU_eq_Nl
#print axioms ATK.NSIdent.bt_mild
