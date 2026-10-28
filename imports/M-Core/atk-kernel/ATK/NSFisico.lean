import ATK.NSRegular
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# ATK — Navier–Stokes, marco NS4a: integrais de Fourier com parâmetros são `C^∞`

Ponte B3, marco NS4a. Para `V` na classe `Suave T k` para todo `k` (NS3) e um símbolo `L(ξ)`
mensurável com `‖L(ξ)‖ |ξ| ≤ K (1+|ξ|)^p` (permite a singularidade `1/|ξ|` do símbolo da pressão),
a função

  `Φ L V (x, t) = ∫ L(ξ) (e^{2πi⟨ξ,x⟩} V(ξ, t)) dξ`

é **`C^∞` em `ℝ³ × [0, T]`** (`contDiffOn_Φ`), com derivada explícita (`hasFDerivWithinAt_Φ`):
em `x` multiplica o símbolo por `2πi⟨ξ, h⟩`, em `t` troca `V` por `∂ₜV`.

Ferramentas: derivação sob a integral dentro de um convexo, em dimensão finita
(`hasFDerivWithinAt_integral`); a integrabilidade de `|ξ|^{−1}(1+|ξ|)^{−4}` em `ℝ³`.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Filter Topology Set
open scoped ContDiff
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular

namespace ATK.NSFisico

/-! ### Derivação sob a integral em dimensão finita -/

/-- **Derivação (de Fréchet) sob o sinal de integral, dentro de um convexo.** -/
theorem hasFDerivWithinAt_integral {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : Z → E3 → W} {F' : Z → E3 → (Z →L[ℝ] W)} {s : Set Z} (hs : Convex ℝ s) {z₀ : Z}
    (hz₀ : z₀ ∈ s) (hmeas : ∀ z ∈ s, AEStronglyMeasurable (F z)) (hint : Integrable (F z₀))
    (hmeas' : AEStronglyMeasurable (F' z₀)) {b : E3 → ℝ} (hb : Integrable b)
    (hderiv : ∀ᵐ ξ, ∀ z ∈ s, HasFDerivWithinAt (fun z => F z ξ) (F' z ξ) s z)
    (hbound : ∀ᵐ ξ, ∀ z ∈ s, ‖F' z ξ‖ ≤ b ξ) :
    HasFDerivWithinAt (fun z => ∫ ξ, F z ξ) (∫ ξ, F' z₀ ξ) s z₀ := by
  have hmvt : ∀ᵐ ξ, ∀ z ∈ s, ‖F z ξ - F z₀ ξ‖ ≤ b ξ * ‖z - z₀‖ := by
    filter_upwards [hderiv, hbound] with ξ hd hbd z hz
    exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbd hz₀ hz
  have hint' : Integrable (F' z₀) :=
    hb.mono' hmeas' (by filter_upwards [hbound] with ξ h; exact h z₀ hz₀)
  have hintz : ∀ z ∈ s, Integrable (F z) := by
    intro z hz
    have h1 : Integrable (fun ξ => F z ξ - F z₀ ξ) :=
      (hb.mul_const ‖z - z₀‖).mono' ((hmeas z hz).sub hint.aestronglyMeasurable)
        (by filter_upwards [hmvt] with ξ h; exact h z hz)
    exact (h1.add hint).congr (Eventually.of_forall fun ξ => by simp)
  rw [hasFDerivWithinAt_iff_tendsto]
  have hev : ∀ᶠ z in 𝓝[s] z₀, z ∈ s := self_mem_nhdsWithin
  have hlim : Tendsto (fun z => ∫ ξ, ‖z - z₀‖⁻¹ * ‖F z ξ - F z₀ ξ - F' z₀ ξ (z - z₀)‖)
      (𝓝[s] z₀) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure E3))
      (l := 𝓝[s] z₀) (F := fun z ξ => ‖z - z₀‖⁻¹ * ‖F z ξ - F z₀ ξ - F' z₀ ξ (z - z₀)‖)
      (f := fun _ => (0 : ℝ)) (fun ξ => 2 * b ξ) ?_ ?_ (hb.const_mul 2) ?_
    · simpa using h
    · filter_upwards [hev] with z hz
      exact (((hmeas z hz).sub hint.aestronglyMeasurable).sub
        (hint'.apply_continuousLinearMap (z - z₀)).aestronglyMeasurable).norm.const_mul _
    · filter_upwards [hev] with z hz
      filter_upwards [hmvt, hbound] with ξ h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      by_cases hzz : z = z₀
      · subst hzz
        simp only [sub_self, norm_zero, inv_zero, zero_mul]
        have := le_trans (norm_nonneg _) (h2 z hz)
        linarith
      have hn : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
      have e1 := h1 z hz
      have e2 : ‖F' z₀ ξ (z - z₀)‖ ≤ b ξ * ‖z - z₀‖ :=
        ((F' z₀ ξ).le_opNorm _).trans (mul_le_mul_of_nonneg_right (h2 z₀ hz₀) (norm_nonneg _))
      have e3 := norm_sub_le (F z ξ - F z₀ ξ) (F' z₀ ξ (z - z₀))
      rw [inv_mul_le_iff₀ hn]
      nlinarith
    · filter_upwards [hderiv] with ξ hd
      exact hasFDerivWithinAt_iff_tendsto.mp (hd z₀ hz₀)
  refine squeeze_zero' (Eventually.of_forall fun z => by positivity) ?_ hlim
  filter_upwards [hev] with z hz
  have hI1 := hintz z hz
  have hI3 := hint'.apply_continuousLinearMap (z - z₀)
  have heq : (∫ ξ, F z ξ) - (∫ ξ, F z₀ ξ) - (∫ ξ, F' z₀ ξ) (z - z₀) =
      ∫ ξ, (F z ξ - F z₀ ξ - F' z₀ ξ (z - z₀)) := by
    have hI2 : Integrable (fun ξ => F z ξ - F z₀ ξ) := hI1.sub hint
    rw [ContinuousLinearMap.integral_apply hint', ← integral_sub hI1 hint, ← integral_sub hI2 hI3]
  rw [heq, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

/-! ### A singularidade `1/|ξ|` -/

/-- `|ξ|^{−1} (1+|ξ|)^{−4}` é integrável em `ℝ³`. -/
theorem integrable_inv_norm_mul :
    Integrable (fun ξ : E3 => ‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) := by
  have hmeas : AEStronglyMeasurable (fun ξ : E3 => ‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) := by
    refine (Measurable.aestronglyMeasurable ?_)
    fun_prop
  have hball : IntegrableOn (fun ξ : E3 => ‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) (Metric.ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1) (by rw [finrank_E3]; norm_num)
      (by rw [finrank_E3]; norm_num) (Eventually.of_forall fun ξ => ?_) hmeas
    rw [Real.rpow_neg_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)), abs_of_nonneg (by positivity), one_mul]
    have h1 : ((1 + ‖ξ‖) ^ 4)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg ξ]))
    calc ‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹ ≤ ‖ξ‖⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (norm_nonneg ξ))
      _ = ‖ξ‖⁻¹ := mul_one _
  have hcompl : IntegrableOn (fun ξ : E3 => ‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) (Metric.ball 0 1)ᶜ := by
    refine ((integrable_inv_pow (m := 4) le_rfl).integrableOn).mono' hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball.compl).mpr (Eventually.of_forall fun ξ hξ => ?_)
    have h1 : 1 ≤ ‖ξ‖ := by simpa using hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹ ≤ 1 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
          gcongr
          exact inv_le_one_of_one_le₀ h1
      _ = ((1 + ‖ξ‖) ^ 4)⁻¹ := one_mul _
  have := hball.union hcompl
  rwa [union_compl_self, integrableOn_univ] at this

/-! ### O caractere `e^{2πi⟨ξ,x⟩}` -/

/-- `e_ξ(x) = exp(2πi⟨ξ, x⟩)`. -/
noncomputable def ex (ξ x : E3) : ℂ := Complex.exp (2 * π * Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))

theorem norm_ex (ξ x : E3) : ‖ex ξ x‖ = 1 := by
  unfold ex
  rw [show 2 * (π : ℂ) * Complex.I * ((inner ℝ ξ x : ℝ) : ℂ) =
    ((2 * π * inner ℝ ξ x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- A derivada de `x ↦ 2πi⟨ξ, x⟩`. -/
noncomputable def dex (ξ : E3) : E3 →L[ℝ] ℂ :=
  (2 * (π : ℂ) * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))

theorem dex_apply (ξ h : E3) : dex ξ h = 2 * π * Complex.I * ((inner ℝ ξ h : ℝ) : ℂ) := by
  simp [dex]

theorem hasFDerivAt_ex (ξ x : E3) : HasFDerivAt (ex ξ) (ex ξ x • dex ξ) x := by
  have h1 : HasFDerivAt (fun x : E3 => 2 * (π : ℂ) * Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))
      (dex ξ) x := by
    have : (fun x : E3 => 2 * (π : ℂ) * Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) = ⇑(dex ξ) := by
      funext y
      rw [dex_apply]
    rw [this]
    exact (dex ξ).hasFDerivAt
  exact h1.cexp

theorem continuous_ex : Continuous fun q : E3 × E3 => ex q.1 q.2 := by
  unfold ex
  fun_prop

/-! ### Medibilidade -/

theorem aesm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : E3 → (E →L[ℝ] F)} {g : E3 → E} (hL : AEStronglyMeasurable L)
    (hg : AEStronglyMeasurable g) : AEStronglyMeasurable (fun ξ => L ξ (g ξ)) :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.comp_aestronglyMeasurable
    (hL.prodMk hg)

/-! ### O integrando e os símbolos derivados -/

/-- Multiplicação por `i`, como aplicação `ℝ`-linear. -/
noncomputable def iC : C3 →L[ℝ] C3 :=
  (Complex.I • ContinuousLinearMap.id ℂ C3).restrictScalars ℝ

theorem iC_apply (a : C3) : iC a = Complex.I • a := rfl

theorem norm_iC_le : ‖iC‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [iC_apply, norm_smul, Complex.norm_I]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **`Φ L V (x, t) = ∫ L(ξ)(e^{2πi⟨ξ,x⟩} V(ξ, t)) dξ`.** -/
noncomputable def Φ (L : E3 → (C3 →L[ℝ] W)) (V : E3 × ℝ → C3) (z : E3 × ℝ) : W :=
  ∫ ξ, L ξ (ex ξ z.1 • V (ξ, z.2))

/-- O símbolo da derivada em `x` (como função de `(ξ, L(ξ))`). -/
noncomputable def LAf (ξ : E3) (M : C3 →L[ℝ] W) : C3 →L[ℝ] (E3 →L[ℝ] W) :=
  (ContinuousLinearMap.smulRightL ℝ E3 W ((2 * π) • innerSL ℝ ξ)).comp (M.comp iC)

/-- O símbolo da derivada em `x`: `a ↦ (h ↦ 2π⟨ξ, h⟩ L(ξ)(i a))`. -/
noncomputable def LA (L : E3 → (C3 →L[ℝ] W)) (ξ : E3) : C3 →L[ℝ] (E3 →L[ℝ] W) := LAf ξ (L ξ)

theorem LA_apply (L : E3 → (C3 →L[ℝ] W)) (ξ : E3) (a : C3) (h : E3) :
    LA L ξ a h = (2 * π * inner ℝ ξ h) • L ξ (Complex.I • a) := by
  simp [LA, LAf, iC_apply, innerSL_apply_apply, mul_comm, smul_smul]

/-- O símbolo da derivada em `t`: `a ↦ (r ↦ r L(ξ) a)`. -/
noncomputable def LB (L : E3 → (C3 →L[ℝ] W)) (ξ : E3) : C3 →L[ℝ] (ℝ →L[ℝ] W) :=
  (ContinuousLinearMap.smulRightL ℝ ℝ W (ContinuousLinearMap.id ℝ ℝ)).comp (L ξ)

theorem LB_apply (L : E3 → (C3 →L[ℝ] W)) (ξ : E3) (a : C3) (r : ℝ) :
    LB L ξ a r = r • L ξ a := by
  simp [LB]

theorem norm_LA_le (L : E3 → (C3 →L[ℝ] W)) (ξ : E3) : ‖LA L ξ‖ ≤ 2 * π * ‖ξ‖ * ‖L ξ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [LA_apply, norm_smul, Real.norm_eq_abs]
  have e1 : |2 * π * inner ℝ ξ h| ≤ 2 * π * (‖ξ‖ * ‖h‖) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    gcongr
    exact abs_real_inner_le_norm ξ h
  have e2 : ‖L ξ (Complex.I • a)‖ ≤ ‖L ξ‖ * ‖a‖ := by
    have := (L ξ).le_opNorm (Complex.I • a)
    rwa [norm_smul, Complex.norm_I, one_mul] at this
  calc |2 * π * inner ℝ ξ h| * ‖L ξ (Complex.I • a)‖
      ≤ (2 * π * (‖ξ‖ * ‖h‖)) * (‖L ξ‖ * ‖a‖) := by gcongr
    _ = 2 * π * ‖ξ‖ * ‖L ξ‖ * ‖a‖ * ‖h‖ := by ring

theorem norm_LB_le (L : E3 → (C3 →L[ℝ] W)) (ξ : E3) : ‖LB L ξ‖ ≤ ‖L ξ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun r => ?_
  rw [LB_apply, norm_smul, Real.norm_eq_abs, mul_comm]
  gcongr
  exact (L ξ).le_opNorm a

theorem continuous_LAf : Continuous fun q : E3 × (C3 →L[ℝ] W) => LAf q.1 q.2 := by
  unfold LAf
  have h1 : Continuous fun q : E3 × (C3 →L[ℝ] W) =>
      ContinuousLinearMap.smulRightL ℝ E3 W ((2 * π) • innerSL ℝ q.1) :=
    (ContinuousLinearMap.smulRightL ℝ E3 W).continuous.comp
      ((continuous_const_smul _).comp ((innerSL ℝ (E := E3)).continuous.comp continuous_fst))
  have h2 : Continuous fun q : E3 × (C3 →L[ℝ] W) => q.2.comp iC :=
    continuous_snd.clm_comp continuous_const
  exact h1.clm_comp h2

theorem aesm_LA {L : E3 → (C3 →L[ℝ] W)} (hL : AEStronglyMeasurable L) :
    AEStronglyMeasurable (LA L) := by
  have h1 : AEStronglyMeasurable (fun ξ : E3 => ((ξ, L ξ) : E3 × (C3 →L[ℝ] W))) :=
    (aestronglyMeasurable_id (μ := (volume : Measure E3))).prodMk hL
  have h2 := (continuous_LAf (W := W)).comp_aestronglyMeasurable h1
  exact h2

theorem aesm_LB {L : E3 → (C3 →L[ℝ] W)} (hL : AEStronglyMeasurable L) :
    AEStronglyMeasurable (LB L) := by
  have : Continuous fun M : C3 →L[ℝ] W =>
      (ContinuousLinearMap.smulRightL ℝ ℝ W (ContinuousLinearMap.id ℝ ℝ)).comp M :=
    continuous_const.clm_comp continuous_id
  exact this.comp_aestronglyMeasurable hL

/-! ### A derivada temporal canônica -/

/-- `∂ₜV` dentro de `[0, T]`. -/
noncomputable def dt (T : ℝ) (V : E3 × ℝ → C3) (q : E3 × ℝ) : C3 :=
  derivWithin (fun s => V (q.1, s)) (Icc 0 T) q.2

theorem Reg0.congr {T : ℝ} {g h : E3 × ℝ → C3} (hg : Reg0 T g)
    (he : ∀ ξ, ∀ t ∈ Icc 0 T, g (ξ, t) = h (ξ, t)) : Reg0 T h := by
  refine ⟨fun t ht => ?_, fun m => ?_⟩
  · have : (fun ξ => h (ξ, t)) = fun ξ => g (ξ, t) := funext fun ξ => (he ξ t ht).symm
    rw [this]
    exact hg.1 t ht
  · obtain ⟨C, hC⟩ := hg.2 m
    refine ⟨C, fun t ht ζ => ?_⟩
    have := hC t ht ζ
    simp only at this ⊢
    rwa [← he ζ t ht]

theorem Suave.congr {T : ℝ} : ∀ {k : ℕ} {g h : E3 × ℝ → C3}, Suave T k g →
    (∀ ξ, ∀ t ∈ Icc 0 T, g (ξ, t) = h (ξ, t)) → Suave T k h
  | 0, _, _, hg, he => Reg0.congr hg he
  | _ + 1, _, _, hg, he => by
    obtain ⟨hg0, g', hg', hd⟩ := hg
    refine ⟨Reg0.congr hg0 he, g', hg', fun ξ t ht => ?_⟩
    exact (hd ξ t ht).congr (fun s hs => (he ξ s hs).symm) (he ξ t ht).symm

/-- `∂ₜV` está na classe e é a derivada. -/
theorem suave_dt {T : ℝ} (hT : 0 < T) {V : E3 × ℝ → C3} (hV : ∀ k, Suave T k V) :
    (∀ k, Suave T k (dt T V)) ∧
      ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (dt T V (ξ, t)) (Icc 0 T) t := by
  have key : ∀ k, ∃ g', Suave T k g' ∧ ∀ ξ, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => V (ξ, s)) (g' (ξ, t)) (Icc 0 T) t := fun k =>
    (hV (k + 1)).2
  have heq : ∀ {g' : E3 × ℝ → C3}, (∀ ξ, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => V (ξ, s)) (g' (ξ, t)) (Icc 0 T) t) →
      ∀ ξ, ∀ t ∈ Icc 0 T, g' (ξ, t) = dt T V (ξ, t) := by
    intro g' hd ξ t ht
    exact ((hd ξ t ht).derivWithin (uniqueDiffOn_Icc hT t ht)).symm
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨g', hg', hd⟩ := key k
    exact Suave.congr hg' (heq hd)
  · obtain ⟨g', -, hd⟩ := key 0
    intro ξ t ht
    rw [← heq hd ξ t ht]
    exact hd ξ t ht

/-! ### A derivada do integrando -/

/-- O domínio `ℝ³ × [0, T]`. -/
abbrev Dom (T : ℝ) : Set (E3 × ℝ) := (univ : Set E3) ×ˢ Icc 0 T

theorem convex_Dom (T : ℝ) : Convex ℝ (Dom T) := convex_univ.prod (convex_Icc 0 T)

theorem hasFDerivWithinAt_integrand {T : ℝ} (L : E3 → (C3 →L[ℝ] W)) {V V' : E3 × ℝ → C3}
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    (ξ : E3) {z : E3 × ℝ} (hz : z ∈ Dom T) :
    HasFDerivWithinAt (fun z : E3 × ℝ => L ξ (ex ξ z.1 • V (ξ, z.2)))
      ((LA L ξ (ex ξ z.1 • V (ξ, z.2))).comp (ContinuousLinearMap.fst ℝ E3 ℝ) +
        (LB L ξ (ex ξ z.1 • V' (ξ, z.2))).comp (ContinuousLinearMap.snd ℝ E3 ℝ)) (Dom T) z := by
  have hc : HasFDerivWithinAt (fun z : E3 × ℝ => ex ξ z.1)
      ((ex ξ z.1 • dex ξ).comp (ContinuousLinearMap.fst ℝ E3 ℝ)) (Dom T) z :=
    ((hasFDerivAt_ex ξ z.1).comp z hasFDerivAt_fst).hasFDerivWithinAt
  have hf : HasFDerivWithinAt (fun z : E3 × ℝ => V (ξ, z.2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (V' (ξ, z.2))).comp
        (ContinuousLinearMap.snd ℝ E3 ℝ)) (Dom T) z := by
    have := (hdV ξ z.2 hz.2).hasFDerivWithinAt
    exact this.comp z hasFDerivWithinAt_snd (fun w hw => hw.2)
  have hp := HasFDerivWithinAt.smul (𝕜' := ℂ) hc hf
  have hL := (L ξ).hasFDerivAt.comp_hasFDerivWithinAt z hp
  have hL' : HasFDerivWithinAt (fun z : E3 × ℝ => L ξ (ex ξ z.1 • V (ξ, z.2))) _ (Dom T) z := hL
  refine hL'.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [add_apply, ContinuousLinearMap.comp_apply, LA_apply, LB_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply, map_add,
    dex_apply]
  have e1 : ex ξ z.1 • (w.2 • V' (ξ, z.2)) = w.2 • (ex ξ z.1 • V' (ξ, z.2)) := smul_comm _ _ _
  have e2 : (ex ξ z.1 • (2 * π * Complex.I * ((inner ℝ ξ w.1 : ℝ) : ℂ))) • V (ξ, z.2) =
      (2 * π * inner ℝ ξ w.1) • (Complex.I • (ex ξ z.1 • V (ξ, z.2))) := by
    rw [← Complex.coe_smul, smul_smul, smul_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  rw [e1, e2, (L ξ).map_smul, (L ξ).map_smul, add_comm]

/-! ### A derivada de `Φ` -/

theorem integrable_sing {K C : ℝ} : Integrable fun ξ : E3 => K * C * (‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) :=
  integrable_inv_norm_mul.const_mul _

theorem weight_cancel (ξ : E3) (p : ℕ) :
    (1 + ‖ξ‖) ^ p * ((1 + ‖ξ‖) ^ (p + 4))⁻¹ = ((1 + ‖ξ‖) ^ 4)⁻¹ := by
  have : (0 : ℝ) < 1 + ‖ξ‖ := by positivity
  rw [pow_add]
  field_simp

/-- Cotas do símbolo: `‖L(ξ)‖ ‖v‖ ≤ K C |ξ|^{−1} (1+|ξ|)^{−4}` se `‖v‖ ≤ C (1+|ξ|)^{−(p+4)}`. -/
theorem norm_L_mul_le {L : E3 → (C3 →L[ℝ] W)} {K : ℝ} {p : ℕ}
    (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) {ξ : E3} (hξ : ξ ≠ 0) {a : ℝ} (ha : 0 ≤ a)
    {C : ℝ} (hC : a ≤ C * ((1 + ‖ξ‖) ^ (p + 4))⁻¹) :
    ‖L ξ‖ * a ≤ K * C * (‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have h1 : ‖L ξ‖ ≤ K * (1 + ‖ξ‖) ^ p * ‖ξ‖⁻¹ := by
    rw [le_mul_inv_iff₀ hn]
    exact hLb ξ
  have hC0 : 0 ≤ C * ((1 + ‖ξ‖) ^ (p + 4))⁻¹ := ha.trans hC
  calc ‖L ξ‖ * a ≤ (K * (1 + ‖ξ‖) ^ p * ‖ξ‖⁻¹) * (C * ((1 + ‖ξ‖) ^ (p + 4))⁻¹) :=
        mul_le_mul h1 hC ha (le_trans (norm_nonneg _) h1)
    _ = K * C * (‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ p * ((1 + ‖ξ‖) ^ (p + 4))⁻¹)) := by ring
    _ = K * C * (‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) := by rw [weight_cancel]

theorem norm_LA_mul_le {L : E3 → (C3 →L[ℝ] W)} {K : ℝ} {p : ℕ} (hK : 0 ≤ K)
    (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) (ξ : E3) {a : ℝ} (ha : 0 ≤ a)
    {C : ℝ} (hC : a ≤ C * ((1 + ‖ξ‖) ^ (p + 4))⁻¹) :
    ‖LA L ξ‖ * a ≤ 2 * π * K * C * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
  have h1 : ‖LA L ξ‖ ≤ 2 * π * (K * (1 + ‖ξ‖) ^ p) := by
    calc ‖LA L ξ‖ ≤ 2 * π * ‖ξ‖ * ‖L ξ‖ := norm_LA_le L ξ
      _ = 2 * π * (‖L ξ‖ * ‖ξ‖) := by ring
      _ ≤ 2 * π * (K * (1 + ‖ξ‖) ^ p) := mul_le_mul_of_nonneg_left (hLb ξ) (by positivity)
  calc ‖LA L ξ‖ * a ≤ (2 * π * (K * (1 + ‖ξ‖) ^ p)) * (C * ((1 + ‖ξ‖) ^ (p + 4))⁻¹) :=
        mul_le_mul h1 hC ha (by positivity)
    _ = 2 * π * K * C * ((1 + ‖ξ‖) ^ p * ((1 + ‖ξ‖) ^ (p + 4))⁻¹) := by ring
    _ = 2 * π * K * C * ((1 + ‖ξ‖) ^ 4)⁻¹ := by rw [weight_cancel]

theorem continuous_exV {T : ℝ} {V : E3 × ℝ → C3} (hV : Reg0 T V) (x : E3) {t : ℝ}
    (ht : t ∈ Icc 0 T) : Continuous fun ξ => ex ξ x • V (ξ, t) :=
  (continuous_ex.comp (continuous_id.prodMk continuous_const)).smul (hV.1 t ht)

/-- **A derivada de `Φ L V`** dentro de `ℝ³ × [0, T]`. -/
theorem hasFDerivWithinAt_Φ [CompleteSpace W] {T : ℝ} {L : E3 → (C3 →L[ℝ] W)}
    (hL : AEStronglyMeasurable L) {K : ℝ} {p : ℕ} (hK : 0 ≤ K)
    (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) {V V' : E3 × ℝ → C3} (hV : Reg0 T V)
    (hV' : Reg0 T V')
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    {z : E3 × ℝ} (hz : z ∈ Dom T) :
    HasFDerivWithinAt (Φ L V) ((Φ (LA L) V z).comp (ContinuousLinearMap.fst ℝ E3 ℝ) +
      (Φ (LB L) V' z).comp (ContinuousLinearMap.snd ℝ E3 ℝ)) (Dom T) z := by
  obtain ⟨C₁, hC₁⟩ := hV.2 (p + 4)
  obtain ⟨C₂, hC₂⟩ := hV'.2 (p + 4)
  have hC₁0 : 0 ≤ C₁ := (hC₁ z.2 hz.2).nonneg
  have hC₂0 : 0 ≤ C₂ := (hC₂ z.2 hz.2).nonneg
  set F : E3 × ℝ → E3 → W := fun z ξ => L ξ (ex ξ z.1 • V (ξ, z.2))
  set A : E3 × ℝ → E3 → (E3 →L[ℝ] W) := fun z ξ => LA L ξ (ex ξ z.1 • V (ξ, z.2))
  set B : E3 × ℝ → E3 → (ℝ →L[ℝ] W) := fun z ξ => LB L ξ (ex ξ z.1 • V' (ξ, z.2))
  set F' : E3 × ℝ → E3 → (E3 × ℝ →L[ℝ] W) := fun z ξ =>
    (A z ξ).comp (ContinuousLinearMap.fst ℝ E3 ℝ) + (B z ξ).comp (ContinuousLinearMap.snd ℝ E3 ℝ)
  set b : E3 → ℝ := fun ξ => 2 * π * K * C₁ * ((1 + ‖ξ‖) ^ 4)⁻¹ +
    K * C₂ * (‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹)
  have hb : Integrable b :=
    ((integrable_inv_pow (m := 4) le_rfl).const_mul _).add integrable_sing
  have hAb : ∀ ξ, ∀ w ∈ Dom T, ‖A w ξ‖ ≤ 2 * π * K * C₁ * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
    intro ξ w hw
    have h1 := (LA L ξ).le_opNorm (ex ξ w.1 • V (ξ, w.2))
    rw [norm_smul, norm_ex, one_mul] at h1
    exact h1.trans (norm_LA_mul_le hK hLb ξ (norm_nonneg _) ((hC₁ w.2 hw.2).le_inv ξ))
  have hBb : ∀ ξ, ξ ≠ 0 → ∀ w ∈ Dom T, ‖B w ξ‖ ≤ K * C₂ * (‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) := by
    intro ξ hξ w hw
    have h1 := (LB L ξ).le_opNorm (ex ξ w.1 • V' (ξ, w.2))
    rw [norm_smul, norm_ex, one_mul] at h1
    refine h1.trans ((mul_le_mul_of_nonneg_right (norm_LB_le L ξ) (norm_nonneg _)).trans ?_)
    exact norm_L_mul_le hLb hξ (norm_nonneg _) ((hC₂ w.2 hw.2).le_inv ξ)
  have hFb : ∀ ξ, ξ ≠ 0 → ∀ w ∈ Dom T, ‖F w ξ‖ ≤ K * C₁ * (‖ξ‖⁻¹ * ((1 + ‖ξ‖) ^ 4)⁻¹) := by
    intro ξ hξ w hw
    have h1 := (L ξ).le_opNorm (ex ξ w.1 • V (ξ, w.2))
    rw [norm_smul, norm_ex, one_mul] at h1
    exact h1.trans (norm_L_mul_le hLb hξ (norm_nonneg _) ((hC₁ w.2 hw.2).le_inv ξ))
  have hmeasF : ∀ w ∈ Dom T, AEStronglyMeasurable (F w) := fun w hw =>
    aesm_apply hL (continuous_exV hV w.1 hw.2).aestronglyMeasurable
  have hmeasA : ∀ w ∈ Dom T, AEStronglyMeasurable (A w) := fun w hw =>
    aesm_apply (aesm_LA hL) (continuous_exV hV w.1 hw.2).aestronglyMeasurable
  have hmeasB : ∀ w ∈ Dom T, AEStronglyMeasurable (B w) := fun w hw =>
    aesm_apply (aesm_LB hL) (continuous_exV hV' w.1 hw.2).aestronglyMeasurable
  have hintA : Integrable (A z) :=
    ((integrable_inv_pow (m := 4) le_rfl).const_mul _).mono' (hmeasA z hz)
      (Eventually.of_forall fun ξ => hAb ξ z hz)
  have hintB : Integrable (B z) :=
    integrable_sing.mono' (hmeasB z hz)
      (by filter_upwards [Measure.ae_ne volume 0] with ξ hξ using hBb ξ hξ z hz)
  have hintF : Integrable (F z) :=
    integrable_sing.mono' (hmeasF z hz)
      (by filter_upwards [Measure.ae_ne volume 0] with ξ hξ using hFb ξ hξ z hz)
  have hmeasF' : AEStronglyMeasurable (F' z) := by
    have h1 := (ContinuousLinearMap.precomp W (ContinuousLinearMap.fst ℝ E3 ℝ)).continuous.comp_aestronglyMeasurable (hmeasA z hz)
    have h2 := (ContinuousLinearMap.precomp W (ContinuousLinearMap.snd ℝ E3 ℝ)).continuous.comp_aestronglyMeasurable (hmeasB z hz)
    exact h1.add h2
  have hderiv : ∀ᵐ ξ, ∀ w ∈ Dom T, HasFDerivWithinAt (fun w => F w ξ) (F' w ξ) (Dom T) w :=
    Eventually.of_forall fun ξ w hw => hasFDerivWithinAt_integrand L hdV ξ hw
  have hbound : ∀ᵐ ξ, ∀ w ∈ Dom T, ‖F' w ξ‖ ≤ b ξ := by
    filter_upwards [Measure.ae_ne volume 0] with ξ hξ w hw
    have e1 : ‖(A w ξ).comp (ContinuousLinearMap.fst ℝ E3 ℝ)‖ ≤ ‖A w ξ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ E3 ℝ))
    have e2 : ‖(B w ξ).comp (ContinuousLinearMap.snd ℝ E3 ℝ)‖ ≤ ‖B w ξ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E3 ℝ))
    exact (norm_add_le _ _).trans (add_le_add (e1.trans (hAb ξ w hw)) (e2.trans (hBb ξ hξ w hw)))
  have h := hasFDerivWithinAt_integral (convex_Dom T) hz hmeasF hintF hmeasF' hb hderiv hbound
  have hI : ∫ ξ, F' z ξ = (Φ (LA L) V z).comp (ContinuousLinearMap.fst ℝ E3 ℝ) +
      (Φ (LB L) V' z).comp (ContinuousLinearMap.snd ℝ E3 ℝ) := by
    have i1 : Integrable fun ξ => (A z ξ).comp (ContinuousLinearMap.fst ℝ E3 ℝ) :=
      (ContinuousLinearMap.precomp W (ContinuousLinearMap.fst ℝ E3 ℝ)).integrable_comp hintA
    have i2 : Integrable fun ξ => (B z ξ).comp (ContinuousLinearMap.snd ℝ E3 ℝ) :=
      (ContinuousLinearMap.precomp W (ContinuousLinearMap.snd ℝ E3 ℝ)).integrable_comp hintB
    simp only [F']
    rw [integral_add i1 i2]
    have c1 := (ContinuousLinearMap.precomp W (ContinuousLinearMap.fst ℝ E3 ℝ)).integral_comp_comm
      hintA
    have c2 := (ContinuousLinearMap.precomp W (ContinuousLinearMap.snd ℝ E3 ℝ)).integral_comp_comm
      hintB
    simp only [ContinuousLinearMap.precomp_apply] at c1 c2
    rw [c1, c2]
    rfl
  rw [hI] at h
  exact h

/-! ### `Φ L V` é `C^∞` -/

theorem LA_bound {L : E3 → (C3 →L[ℝ] W)} {K : ℝ} {p : ℕ}
    (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) (ξ : E3) :
    ‖LA L ξ‖ * ‖ξ‖ ≤ 2 * π * K * (1 + ‖ξ‖) ^ (p + 1) := by
  have h1 := norm_LA_le L ξ
  have h2 := hLb ξ
  have h3 : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith
  calc ‖LA L ξ‖ * ‖ξ‖ ≤ (2 * π * ‖ξ‖ * ‖L ξ‖) * ‖ξ‖ := by gcongr
    _ = 2 * π * ‖ξ‖ * (‖L ξ‖ * ‖ξ‖) := by ring
    _ ≤ 2 * π * (1 + ‖ξ‖) * (K * (1 + ‖ξ‖) ^ p) := by gcongr
    _ = 2 * π * K * (1 + ‖ξ‖) ^ (p + 1) := by ring

theorem LB_bound {L : E3 → (C3 →L[ℝ] W)} {K : ℝ} {p : ℕ}
    (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) (ξ : E3) :
    ‖LB L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p :=
  (mul_le_mul_of_nonneg_right (norm_LB_le L ξ) (norm_nonneg _)).trans (hLb ξ)

theorem uniqueDiffOn_Dom {T : ℝ} (hT : 0 < T) : UniqueDiffOn ℝ (Dom T) :=
  uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hT)

/-- **`Φ L V` é `C^n` em `ℝ³ × [0, T]`** para todo `n`. -/
theorem contDiffOn_Φ {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {L : E3 → (C3 →L[ℝ] W)} {V : E3 × ℝ → C3} {K : ℝ} {p : ℕ},
      AEStronglyMeasurable L → 0 ≤ K → (∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) →
      (∀ k, Suave T k V) → ContDiffOn ℝ n (Φ L V) (Dom T) := by
  induction n with
  | zero =>
    intro W _ _ _ L V K p hL hK hLb hV
    obtain ⟨hdt, hd⟩ := suave_dt hT hV
    have h0 : ((0 : ℕ) : WithTop ℕ∞) = 0 := rfl
    rw [h0, contDiffOn_zero]
    intro z hz
    exact (hasFDerivWithinAt_Φ hL hK hLb (hV 0) (hdt 0) hd hz).continuousWithinAt
  | succ n ih =>
    intro W _ _ _ L V K p hL hK hLb hV
    obtain ⟨hdt, hd⟩ := suave_dt hT hV
    have huniq := uniqueDiffOn_Dom hT
    have hder : ∀ z ∈ Dom T, HasFDerivWithinAt (Φ L V)
        ((Φ (LA L) V z).comp (ContinuousLinearMap.fst ℝ E3 ℝ) +
          (Φ (LB L) (dt T V) z).comp (ContinuousLinearMap.snd ℝ E3 ℝ)) (Dom T) z :=
      fun z hz => hasFDerivWithinAt_Φ hL hK hLb (hV 0) (hdt 0) hd hz
    have hA : ContDiffOn ℝ n (Φ (LA L) V) (Dom T) :=
      ih (aesm_LA hL) (by positivity) (LA_bound hLb) hV
    have hB : ContDiffOn ℝ n (Φ (LB L) (dt T V)) (Dom T) :=
      ih (aesm_LB hL) hK (LB_bound hLb) hdt
    have hD : ContDiffOn ℝ n (fun z => (Φ (LA L) V z).comp (ContinuousLinearMap.fst ℝ E3 ℝ) +
        (Φ (LB L) (dt T V) z).comp (ContinuousLinearMap.snd ℝ E3 ℝ)) (Dom T) :=
      ((ContinuousLinearMap.precomp W (ContinuousLinearMap.fst ℝ E3 ℝ)).contDiff.comp_contDiffOn
        hA).add
      ((ContinuousLinearMap.precomp W (ContinuousLinearMap.snd ℝ E3 ℝ)).contDiff.comp_contDiffOn
        hB)
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderivWithin huniq]
    refine ⟨fun z hz => (hder z hz).differentiableWithinAt, by simp, ?_⟩
    exact hD.congr fun z hz => (hder z hz).fderivWithin (huniq z hz)

/-- **`Φ L V` é `C^∞` em `ℝ³ × [0, T]`.** -/
theorem contDiffOn_Φ_top {T : ℝ} (hT : 0 < T) {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] {L : E3 → (C3 →L[ℝ] W)} {V : E3 × ℝ → C3} {K : ℝ}
    {p : ℕ} (hL : AEStronglyMeasurable L) (hK : 0 ≤ K) (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p)
    (hV : ∀ k, Suave T k V) : ContDiffOn ℝ ∞ (Φ L V) (Dom T) :=
  contDiffOn_infty.mpr fun n => contDiffOn_Φ hT n hL hK hLb hV

end ATK.NSFisico

#print axioms ATK.NSFisico.hasFDerivWithinAt_integral
#print axioms ATK.NSFisico.integrable_inv_norm_mul
#print axioms ATK.NSFisico.ex
#print axioms ATK.NSFisico.norm_ex
#print axioms ATK.NSFisico.dex
#print axioms ATK.NSFisico.dex_apply
#print axioms ATK.NSFisico.hasFDerivAt_ex
#print axioms ATK.NSFisico.continuous_ex
#print axioms ATK.NSFisico.aesm_apply
#print axioms ATK.NSFisico.iC
#print axioms ATK.NSFisico.iC_apply
#print axioms ATK.NSFisico.norm_iC_le
#print axioms ATK.NSFisico.Φ
#print axioms ATK.NSFisico.LAf
#print axioms ATK.NSFisico.LA
#print axioms ATK.NSFisico.LA_apply
#print axioms ATK.NSFisico.LB
#print axioms ATK.NSFisico.LB_apply
#print axioms ATK.NSFisico.norm_LA_le
#print axioms ATK.NSFisico.norm_LB_le
#print axioms ATK.NSFisico.continuous_LAf
#print axioms ATK.NSFisico.aesm_LA
#print axioms ATK.NSFisico.aesm_LB
#print axioms ATK.NSFisico.dt
#print axioms ATK.NSFisico.Reg0.congr
#print axioms ATK.NSFisico.Suave.congr
#print axioms ATK.NSFisico.suave_dt
#print axioms ATK.NSFisico.Dom
#print axioms ATK.NSFisico.convex_Dom
#print axioms ATK.NSFisico.hasFDerivWithinAt_integrand
#print axioms ATK.NSFisico.integrable_sing
#print axioms ATK.NSFisico.weight_cancel
#print axioms ATK.NSFisico.norm_L_mul_le
#print axioms ATK.NSFisico.norm_LA_mul_le
#print axioms ATK.NSFisico.continuous_exV
#print axioms ATK.NSFisico.hasFDerivWithinAt_Φ
#print axioms ATK.NSFisico.LA_bound
#print axioms ATK.NSFisico.LB_bound
#print axioms ATK.NSFisico.uniqueDiffOn_Dom
#print axioms ATK.NSFisico.contDiffOn_Φ
#print axioms ATK.NSFisico.contDiffOn_Φ_top
