import ATK.NSDual

/-!
# ATK — Navier–Stokes, marco NS8e: a fórmula de Duhamel testada para a diferença de duas soluções

Ponte B3, marco NS8 (quinta parte). Para duas soluções `U₁, U₂` da classe `SolucaoLocal` com o
mesmo dado (pressões **arbitrárias**), `W = U₁ − U₂` e um dado teste `h`:

`∫ W(t) · Re F0 h = ∫₀ᵗ Σ_j ∫ (U₁ⱼU₁ − U₂ⱼU₂)(σ) · ∂_j Re F0 (e^{−c|η|²(t−σ)} h) dσ`

(**`duhamel_testado`**, `c = 4π²ν`): a parte linear (viscosa) é absorvida pela família do calor.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology Asymptotics
open scoped ContDiff Interval
open ATK.LigacaoNS (E3 dX e div lap conv grad gradSq fatia NSEq SolucaoLocal EnergiaAte)
open ATK.NSFourierBase ATK.NSPicard ATK.NSFisico ATK.NSCampos ATK.NSFraca ATK.NSTeste
  ATK.NSFracaF ATK.NSDual

namespace ATK.NSMild

/-! ### Objetos congelados no tempo -/

/-- A diferença `U₁ − U₂`, congelada fora de `[0, τ]`. -/
noncomputable def Wc (τ : ℝ) (U₁ U₂ : E3 × ℝ → E3) (σ : ℝ) (x : E3) : E3 :=
  U₁ (x, clamp τ σ) - U₂ (x, clamp τ σ)

/-- `U_j U`, congelado fora de `[0, τ]`. -/
noncomputable def Nc (τ : ℝ) (U : E3 × ℝ → E3) (j : Fin 3) (σ : ℝ) (x : E3) : E3 :=
  U (x, clamp τ σ) j • U (x, clamp τ σ)

/-- `2πiη_j g`. -/
noncomputable def mjg (j : Fin 3) (g : E3 → C3) : E3 → C3 := fun η => mj j η • g η

/-- O pareamento linear `∫ W(σ) · Re F0 g`. -/
noncomputable def wP (τ : ℝ) (U₁ U₂ : E3 × ℝ → E3) (g : E3 → C3) (σ : ℝ) : ℝ :=
  pr (Wc τ U₁ U₂ σ) g

/-- O pareamento não linear `Σ_j ∫ (U₁ⱼU₁ − U₂ⱼU₂)(σ) · ∂_j Re F0 g`. -/
noncomputable def nP (τ : ℝ) (U₁ U₂ : E3 × ℝ → E3) (g : E3 → C3) (σ : ℝ) : ℝ :=
  ∑ j, (pr (Nc τ U₁ j σ) (mjg j g) - pr (Nc τ U₂ j σ) (mjg j g))

theorem clamp_mem {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) : clamp τ σ ∈ Icc 0 τ :=
  ⟨clamp_nonneg _ _, clamp_le hτ _⟩

theorem Bola.mul_mj {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) (j : Fin 3) :
    Bola ρ (2 * π * (1 + max ρ 0) * M) (mjg j g) := by
  refine ⟨(continuous_mj j).smul hg.1, fun η hη => by simp [mjg, hg.2.1 η hη], fun η => ?_⟩
  unfold mjg
  rw [norm_smul]
  by_cases h0 : g η = 0
  · rw [h0, norm_zero, mul_zero]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
    positivity
  have hη : ‖η‖ ≤ ρ := by
    by_contra h
    exact h0 (hg.2.1 η (not_le.mp h))
  have h1 := norm_mj_le j η
  rw [pow_one] at h1
  calc ‖mj j η‖ * ‖g η‖ ≤ 2 * π * (1 + ‖η‖) * M := by
        gcongr
        exact hg.2.2 η
    _ ≤ 2 * π * (1 + max ρ 0) * M := by
        have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
        gcongr
        exact hη.trans (le_max_left _ _)

theorem Hk_mjg (c : ℝ) (g : E3 → C3) (j : Fin 3) (k : ℕ) (s : ℝ) :
    Hk c (mjg j g) k s = mjg j (Hk c g k s) := by
  funext η
  simp only [Hk, mjg]
  rw [smul_comm]

theorem Teste.pesos_mjg {h : E3 → C3} (hh : Teste h) (j : Fin 3) : Pesos (mjg j h) :=
  pesos_mj hh.pesos j

/-! ### Troca de ordem no triângulo -/

theorem triangle {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) {t K : ℝ} (ht : 0 ≤ t)
    (hK : ∀ σ ∈ Icc 0 t, ∀ r ∈ Icc 0 t, |F σ r| ≤ K) :
    ∫ σ in (0 : ℝ)..t, (∫ r in σ..t, F σ r) = ∫ r in (0 : ℝ)..t, (∫ σ in (0 : ℝ)..r, F σ r) := by
  set μ : Measure ℝ := volume.restrict (Ioc 0 t) with hμ
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  set G : ℝ → ℝ → ℝ := fun σ r => if σ < r then F σ r else 0 with hG
  have hGm : Measurable (Function.uncurry G) := by
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : Function.uncurry G = {p : ℝ × ℝ | p.1 < p.2}.indicator (Function.uncurry F) := by
      funext p
      simp only [Function.uncurry, hG, indicator, Set.mem_ofPred_eq]
    rw [this]
    exact hF.indicator hs
  have hGi : Integrable (Function.uncurry G) (μ.prod μ) := by
    refine Integrable.of_bound hGm.aestronglyMeasurable K ?_
    rw [hμ, Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
      (Eventually.of_forall fun p hp => ?_)
    simp only [Function.uncurry, hG, Real.norm_eq_abs]
    split_ifs
    · exact hK p.1 (Ioc_subset_Icc_self hp.1) p.2 (Ioc_subset_Icc_self hp.2)
    · simpa using (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩ 0 ⟨le_rfl, ht⟩)
  -- lado esquerdo
  have hL : ∫ σ in (0 : ℝ)..t, (∫ r in σ..t, F σ r) = ∫ σ, (∫ r, G σ r ∂μ) ∂μ := by
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    rw [intervalIntegral.integral_of_le hσ.2, hμ]
    have e : (fun r => G σ r) = (Ioi σ).indicator (F σ) := by
      funext r
      simp only [hG, indicator, mem_Ioi]
    have hset : Ioc 0 t ∩ Ioi σ = Ioc σ t := by
      ext r
      simp only [mem_Ioc, mem_inter_iff, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hσ.1.trans h1, h2⟩, h1⟩
    rw [e, setIntegral_indicator measurableSet_Ioi, hset]
  -- lado direito
  have hR : ∫ r in (0 : ℝ)..t, (∫ σ in (0 : ℝ)..r, F σ r) = ∫ r, (∫ σ, G σ r ∂μ) ∂μ := by
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [intervalIntegral.integral_of_le hr.1.le, hμ]
    have e1 : ∫ σ in Ioc 0 t, G σ r = ∫ σ in Ioc 0 t, (Iic r).indicator (fun σ => F σ r) σ := by
      refine integral_congr_ae ?_
      have hne : ∀ᵐ σ ∂(volume.restrict (Ioc 0 t)), σ ≠ r := by
        refine ae_restrict_of_ae ?_
        rw [ae_iff]
        simp
      filter_upwards [hne] with σ hσr
      simp only [hG, indicator, mem_Iic]
      by_cases h : σ < r
      · simp [h, h.le]
      · have h2 : ¬ σ ≤ r := fun h' => h (lt_of_le_of_ne h' hσr)
        simp [h, h2]
    have hset : Ioc 0 t ∩ Iic r = Ioc 0 r := by
      ext σ
      simp only [mem_Ioc, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans hr.2⟩, h2⟩
    rw [e1, setIntegral_indicator measurableSet_Iic, hset]
  rw [hL, hR]
  exact integral_integral_swap hGi

theorem ii_of_bound {f : ℝ → ℝ} (hm : Measurable f) {t K : ℝ} (ht : 0 ≤ t)
    (hb : ∀ σ ∈ Icc 0 t, |f σ| ≤ K) : IntervalIntegrable f volume 0 t := by
  rw [intervalIntegrable_iff, uIoc_of_le ht]
  have hc : IntegrableOn (fun _ : ℝ => K) (Ioc 0 t) volume :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  refine hc.mono' hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun σ hσ => ?_)
  rw [Real.norm_eq_abs]
  exact hb σ (Ioc_subset_Icc_self hσ)

/-! ### As cotas uniformes -/

section Dois

variable {ν T₁ T₂ τ : ℝ} {u₀ : E3 → E3} {U₁ U₂ : E3 × ℝ → E3} {P₁ P₂ : E3 × ℝ → ℝ}

theorem continuous_clamped {T : ℝ} {U : E3 × ℝ → E3} (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T))
    (hτ0 : 0 ≤ τ) (hτ : τ < T) : Continuous fun p : ℝ × E3 => U (p.2, clamp τ p.1) := by
  have hc : ContinuousOn U (univ ×ˢ Icc 0 τ) :=
    hU.continuousOn.mono fun z hz => ⟨mem_univ _, hz.2.1, hz.2.2.trans_lt hτ⟩
  exact hc.comp_continuous (continuous_snd.prodMk ((continuous_clamp τ).comp continuous_fst))
    fun p => ⟨mem_univ _, clamp_mem hτ0 p.1⟩

theorem bounds_clamped {T : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (hS : SolucaoLocal ν u₀ T U P) (hτ0 : 0 ≤ τ) (hτ : τ < T) :
    ∃ C, 0 ≤ C ∧ ∀ σ, (Integrable fun x => ‖U (x, clamp τ σ)‖ ^ 2) ∧
      ∫ x, ‖U (x, clamp τ σ)‖ ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := sol_bounds hS hτ
  have hC0 : 0 ≤ C := (integral_nonneg fun x => sq_nonneg ‖U (x, 0)‖).trans
    (hC 0 ⟨le_rfl, hτ0⟩).1.2
  exact ⟨C, hC0, fun σ => (hC _ (clamp_mem hτ0 σ)).1⟩

theorem Wc_props (hS₁ : SolucaoLocal ν u₀ T₁ U₁ P₁) (hS₂ : SolucaoLocal ν u₀ T₂ U₂ P₂)
    (hτ0 : 0 ≤ τ) (hτ₁ : τ < T₁) (hτ₂ : τ < T₂) :
    ∃ C, 0 ≤ C ∧ ∀ σ, Continuous (Wc τ U₁ U₂ σ) ∧
      (Integrable fun x => ‖Wc τ U₁ U₂ σ x‖ ^ 2) ∧ ∫ x, ‖Wc τ U₁ U₂ σ x‖ ^ 2 ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := bounds_clamped hS₁ hτ0 hτ₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := bounds_clamped hS₂ hτ0 hτ₂
  have hc₁ := continuous_clamped hS₁.1 hτ0 hτ₁
  have hc₂ := continuous_clamped hS₂.1 hτ0 hτ₂
  refine ⟨2 * C₁ + 2 * C₂, by positivity, fun σ => ?_⟩
  have hcW : Continuous (Wc τ U₁ U₂ σ) :=
    (hc₁.comp (continuous_const.prodMk continuous_id)).sub
      (hc₂.comp (continuous_const.prodMk continuous_id))
  have hle : ∀ x, ‖Wc τ U₁ U₂ σ x‖ ^ 2 ≤
      2 * ‖U₁ (x, clamp τ σ)‖ ^ 2 + 2 * ‖U₂ (x, clamp τ σ)‖ ^ 2 := by
    intro x
    have h1 := norm_sub_le (U₁ (x, clamp τ σ)) (U₂ (x, clamp τ σ))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    unfold Wc
    nlinarith [sq_nonneg (‖U₁ (x, clamp τ σ)‖ - ‖U₂ (x, clamp τ σ)‖)]
  have hi : Integrable fun x => 2 * ‖U₁ (x, clamp τ σ)‖ ^ 2 + 2 * ‖U₂ (x, clamp τ σ)‖ ^ 2 :=
    ((hC₁ σ).1.const_mul 2).add ((hC₂ σ).1.const_mul 2)
  have hiW : Integrable fun x => ‖Wc τ U₁ U₂ σ x‖ ^ 2 :=
    hi.mono' (hcW.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle x)
  refine ⟨hcW, hiW, (integral_mono hiW hi hle).trans ?_⟩
  rw [integral_add ((hC₁ σ).1.const_mul 2) ((hC₂ σ).1.const_mul 2), integral_const_mul,
    integral_const_mul]
  linarith [(hC₁ σ).2, (hC₂ σ).2]

theorem Nc_props {T : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ} (hS : SolucaoLocal ν u₀ T U P)
    (hτ0 : 0 ≤ τ) (hτ : τ < T) :
    ∃ C, 0 ≤ C ∧ ∀ σ j, Continuous (Nc τ U j σ) ∧
      (Integrable fun x => ‖Nc τ U j σ x‖) ∧ ∫ x, ‖Nc τ U j σ x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := bounds_clamped hS hτ0 hτ
  have hc := continuous_clamped hS.1 hτ0 hτ
  refine ⟨C, hC0, fun σ j => ?_⟩
  have hcU : Continuous fun x => U (x, clamp τ σ) := hc.comp (continuous_const.prodMk continuous_id)
  have hcN : Continuous (Nc τ U j σ) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hcU).smul hcU
  have hle : ∀ x, ‖Nc τ U j σ x‖ ≤ ‖U (x, clamp τ σ)‖ ^ 2 := by
    intro x
    unfold Nc
    rw [norm_smul, Real.norm_eq_abs, sq]
    exact mul_le_mul_of_nonneg_right (NSFracaF.abs_coord_le _ j) (norm_nonneg _)
  have hi : Integrable fun x => ‖Nc τ U j σ x‖ :=
    (hC σ).1.mono' hcN.norm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [norm_norm]; exact hle x)
  exact ⟨hcN, hi, (integral_mono hi (hC σ).1 hle).trans (hC σ).2⟩

theorem pr_smul (F : E3 → E3) (G : E3 → C3) (a : ℝ) :
    pr F (fun η => a • G η) = a * pr F G := by
  have e : ∀ x, R0 (fun η => a • G η) x = a • R0 G x := by
    intro x
    unfold R0 F0
    have : (fun ξ => ex ξ x • a • G ξ) = fun ξ => a • (ex ξ x • G ξ) := by
      funext ξ
      rw [smul_comm]
    rw [this, integral_smul, map_smul]
  unfold pr
  simp_rw [e, real_inner_smul_right]
  exact integral_const_mul _ _

theorem sum_mj_sq_smul (g : E3 → C3) (η : E3) :
    ∑ j, mj j η • mj j η • g η = (-(4 * π ^ 2) * ‖η‖ ^ 2) • g η := by
  rw [real_smul_C3]
  simp_rw [smul_smul, ← Finset.sum_smul]
  congr 1
  have e : ∀ j, mj j η * mj j η = -(4 * π ^ 2 : ℂ) * ((η j : ℝ) : ℂ) ^ 2 := by
    intro j
    unfold mj
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [e, ← Finset.mul_sum]
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs]
  norm_cast
  rw [sq_abs]

/-! ### O integrando fraco é limitado -/

theorem Fw_bounded {T : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ} (hS : SolucaoLocal ν u₀ T U P)
    (hτ : τ < T) {g : E3 → C3} (hg : Pesos g) :
    ∃ K, ∀ σ ∈ Icc 0 τ, |Fw ν U (R0 g) σ| ≤ K := by
  obtain ⟨C, hC⟩ := sol_bounds hS hτ
  have hL : ∀ j, L2B fun x => ‖R0 (mjg j g) x‖ := fun j => L2B_R0 (pesos_mj hg j)
  choose B hB using fun j => (hL j).2.1
  set I : Fin 3 → ℝ := fun j => ∫ x, ‖R0 (mjg j g) x‖ ^ 2
  refine ⟨|ν| * ∑ j, (C + I j) / 2 + ∑ j, C * B j, fun σ hσ => ?_⟩
  have hd : ∀ j x, dX j (R0 g) x = R0 (mjg j g) x := fun j x => dX_R0 hg j x
  have t1 : ∀ j, |∫ x, inner ℝ (dX j (fatia U σ) x) (dX j (R0 g) x)| ≤ (C + I j) / 2 := by
    intro j
    simp_rw [hd]
    have hi : Integrable fun x => (‖dX j (fatia U σ) x‖ ^ 2 + ‖R0 (mjg j g) x‖ ^ 2) / 2 :=
      (((hC σ hσ).2 j).1.add (hL j).2.2).div_const 2
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hi
      (Eventually.of_forall fun x => ?_)).trans ?_
    · refine (abs_real_inner_le_norm _ _).trans ?_
      nlinarith [sq_nonneg (‖dX j (fatia U σ) x‖ - ‖R0 (mjg j g) x‖)]
    · rw [integral_div, integral_add ((hC σ hσ).2 j).1 (hL j).2.2]
      have := ((hC σ hσ).2 j).2
      linarith
  have t2 : ∀ j, |∫ x, fatia U σ x j * inner ℝ (fatia U σ x) (dX j (R0 g) x)| ≤ C * B j := by
    intro j
    simp_rw [hd]
    have hi : Integrable fun x => ‖U (x, σ)‖ ^ 2 * B j := (hC σ hσ).1.1.mul_const _
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hi
      (Eventually.of_forall fun x => ?_)).trans ?_
    · have h1 := abs_real_inner_le_norm (fatia U σ x) (R0 (mjg j g) x)
      have h2 : ‖R0 (mjg j g) x‖ ≤ B j := (le_abs_self _).trans (hB j x)
      have h3 := NSFracaF.abs_coord_le (fatia U σ x) j
      show |fatia U σ x j * inner ℝ (fatia U σ x) (R0 (mjg j g) x)| ≤ ‖U (x, σ)‖ ^ 2 * B j
      rw [abs_mul]
      calc |fatia U σ x j| * |inner ℝ (fatia U σ x) (R0 (mjg j g) x)|
          ≤ ‖fatia U σ x‖ * (‖fatia U σ x‖ * ‖R0 (mjg j g) x‖) := by gcongr
        _ ≤ ‖fatia U σ x‖ * (‖fatia U σ x‖ * B j) := by gcongr
        _ = ‖U (x, σ)‖ ^ 2 * B j := by simp only [fatia]; ring
    · rw [integral_mul_const]
      have hB0 : 0 ≤ B j := (abs_nonneg _).trans (hB j 0)
      have := (hC σ hσ).1.2
      nlinarith
  unfold Fw
  calc |-ν * (∑ j, ∫ x, inner ℝ (dX j (fatia U σ) x) (dX j (R0 g) x)) +
        ∑ j, ∫ x, fatia U σ x j * inner ℝ (fatia U σ x) (dX j (R0 g) x)|
      ≤ |ν| * ∑ j, |∫ x, inner ℝ (dX j (fatia U σ) x) (dX j (R0 g) x)| +
        ∑ j, |∫ x, fatia U σ x j * inner ℝ (fatia U σ x) (dX j (R0 g) x)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ (Finset.abs_sum_le_sum_abs _ _))
        rw [abs_mul, abs_neg]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |ν| * ∑ j, (C + I j) / 2 + ∑ j, C * B j :=
        add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => t1 j) (abs_nonneg _))
          (Finset.sum_le_sum fun j _ => t2 j)

theorem intervalIntegrable_Fw {T : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (hS : SolucaoLocal ν u₀ T U P) (hτ : τ < T) {g : E3 → C3} (hg : Pesos g) {s : ℝ}
    (hs : s ∈ Icc 0 τ) : IntervalIntegrable (Fw ν U (R0 g)) volume 0 s := by
  obtain ⟨K, hK⟩ := Fw_bounded hS hτ hg
  have hdφ : ∀ j, Continuous (dX j (R0 g)) := fun j =>
    continuous_dX_gen ((contDiff_R0 hg).of_le (by simp)) j
  have hm := aesm_Fw hS hτ hs hdφ
  rw [intervalIntegrable_iff]
  have hc : IntegrableOn (fun _ : ℝ => K) (Ι 0 s) volume := by
    rw [uIoc_of_le hs.1]
    exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  refine hc.mono' hm ?_
  rw [uIoc_of_le hs.1]
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun σ hσ => ?_)
  rw [Real.norm_eq_abs]
  exact hK σ ⟨hσ.1.le, hσ.2.trans hs.2⟩

theorem Hk_one_zero (c : ℝ) (g : E3 → C3) :
    Hk c g 1 0 = fun η => c • ((‖η‖ ^ 2 : ℝ) • g η) := by
  funext η
  simp only [Hk, pow_one, mul_zero, neg_zero, exp_zero, mul_one, smul_smul]

section Hip

variable (hS₁ : SolucaoLocal ν u₀ T₁ U₁ P₁) (hS₂ : SolucaoLocal ν u₀ T₂ U₂ P₂)
  (hτ0 : 0 ≤ τ) (hτ₁ : τ < T₁) (hτ₂ : τ < T₂)
include hS₁ hS₂ hτ0 hτ₁ hτ₂

theorem wP_bound : ∃ K, 0 ≤ K ∧ ∀ {ρ M : ℝ} {g : E3 → C3}, Bola ρ M g → ∀ σ,
    |wP τ U₁ U₂ g σ| ≤ M * (K + Vb ρ) / 2 := by
  obtain ⟨C, hC0, hC⟩ := Wc_props hS₁ hS₂ hτ0 hτ₁ hτ₂
  refine ⟨C, hC0, fun {ρ M g} hg σ => ?_⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
  have hb := pr_bound_L2 (hC σ).1.aestronglyMeasurable (hC σ).2.1 hg
  unfold wP
  refine hb.trans ?_
  have := (hC σ).2.2
  have := Vb_nonneg ρ
  gcongr

theorem nP_bound : ∃ K, 0 ≤ K ∧ ∀ {ρ M : ℝ} {g : E3 → C3}, Bola ρ M g → ∀ σ,
    |nP τ U₁ U₂ g σ| ≤ K * (2 * π * (1 + max ρ 0) * M) * Vb ρ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Nc_props hS₁ hτ0 hτ₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := Nc_props hS₂ hτ0 hτ₂
  refine ⟨3 * (C₁ + C₂), by positivity, fun {ρ M g} hg σ => ?_⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
  have hV := Vb_nonneg ρ
  set M' := 2 * π * (1 + max ρ 0) * M
  have hM' : 0 ≤ M' := by positivity
  have hj : ∀ j, |pr (Nc τ U₁ j σ) (mjg j g) - pr (Nc τ U₂ j σ) (mjg j g)| ≤
      (C₁ + C₂) * (M' * Vb ρ) := by
    intro j
    have h1 := pr_bound_L1 (hC₁ σ j).1.aestronglyMeasurable (hC₁ σ j).2.1 (Bola.mul_mj hg j)
    have h2 := pr_bound_L1 (hC₂ σ j).1.aestronglyMeasurable (hC₂ σ j).2.1 (Bola.mul_mj hg j)
    have e1 : (∫ x, ‖Nc τ U₁ j σ x‖) * (M' * Vb ρ) ≤ C₁ * (M' * Vb ρ) := by
      gcongr; exact (hC₁ σ j).2.2
    have e2 : (∫ x, ‖Nc τ U₂ j σ x‖) * (M' * Vb ρ) ≤ C₂ * (M' * Vb ρ) := by
      gcongr; exact (hC₂ σ j).2.2
    calc |pr (Nc τ U₁ j σ) (mjg j g) - pr (Nc τ U₂ j σ) (mjg j g)|
        ≤ |pr (Nc τ U₁ j σ) (mjg j g)| + |pr (Nc τ U₂ j σ) (mjg j g)| := abs_sub _ _
      _ ≤ C₁ * (M' * Vb ρ) + C₂ * (M' * Vb ρ) := by linarith
      _ = (C₁ + C₂) * (M' * Vb ρ) := by ring
  unfold nP
  calc |∑ j, (pr (Nc τ U₁ j σ) (mjg j g) - pr (Nc τ U₂ j σ) (mjg j g))|
      ≤ ∑ j, |pr (Nc τ U₁ j σ) (mjg j g) - pr (Nc τ U₂ j σ) (mjg j g)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, (C₁ + C₂) * (M' * Vb ρ) := Finset.sum_le_sum fun j _ => hj j
    _ = 3 * (C₁ + C₂) * M' * Vb ρ := by simp; ring

theorem hasDerivAt_wP {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) {c : ℝ} (hc : 0 ≤ c) (k : ℕ)
    (t σ r : ℝ) :
    HasDerivAt (fun r => wP τ U₁ U₂ (Hk c g k (t - r)) σ)
      (wP τ U₁ U₂ (Hk c g (k + 1) (t - r)) σ) r := by
  obtain ⟨C, hC0, hC⟩ := Wc_props hS₁ hS₂ hτ0 hτ₁ hτ₂
  set F := Wc τ U₁ U₂ σ
  have hint : ∀ {g : E3 → C3}, Pesos g → Integrable fun x => inner ℝ (F x) (R0 g x) :=
    fun hg' => integrable_pr_L2 (hC σ).1.aestronglyMeasurable (hC σ).2.1 hg'
  have hK : 0 ≤ ((∫ x, ‖F x‖ ^ 2) + Vb ρ) / 2 := by
    have : 0 ≤ ∫ x, ‖F x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
    have := Vb_nonneg ρ
    positivity
  have hbd : ∀ {M' : ℝ} {g' : E3 → C3}, Bola ρ M' g' →
      |pr F g'| ≤ ((∫ x, ‖F x‖ ^ 2) + Vb ρ) / 2 * M' := fun hg' => by
    have := pr_bound_L2 (hC σ).1.aestronglyMeasurable (hC σ).2.1 hg'
    linarith
  have h1 := hasDerivAt_pr_Hk hint hK hbd hc hg k (t - r)
  have h2 : HasDerivAt (fun r : ℝ => t - r) (-1) r := by
    exact (hasDerivAt_id r).const_sub t
  have h3 := h1.comp r h2
  unfold wP
  refine h3.congr_deriv ?_
  ring

theorem hasDerivAt_nP {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) {c : ℝ} (hc : 0 ≤ c) (k : ℕ)
    (t σ r : ℝ) :
    HasDerivAt (fun r => nP τ U₁ U₂ (Hk c g k (t - r)) σ)
      (nP τ U₁ U₂ (Hk c g (k + 1) (t - r)) σ) r := by
  have hderL1 : ∀ {T : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}, SolucaoLocal ν u₀ T U P → τ < T →
      ∀ j, HasDerivAt (fun r => pr (Nc τ U j σ) (Hk c (mjg j g) k (t - r)))
        (pr (Nc τ U j σ) (Hk c (mjg j g) (k + 1) (t - r))) r := by
    intro T U P hS hτ j
    obtain ⟨C, hC0, hC⟩ := Nc_props hS hτ0 hτ
    set F := Nc τ U j σ
    have hint : ∀ {g : E3 → C3}, Pesos g → Integrable fun x => inner ℝ (F x) (R0 g x) :=
      fun hg' => integrable_pr_L1 (hC σ j).1.aestronglyMeasurable (hC σ j).2.1 hg'
    have hK : 0 ≤ (∫ x, ‖F x‖) * Vb ρ := by
      have : 0 ≤ ∫ x, ‖F x‖ := integral_nonneg fun x => norm_nonneg _
      have := Vb_nonneg ρ
      positivity
    have hbd : ∀ {M' : ℝ} {g' : E3 → C3}, Bola ρ M' g' →
        |pr F g'| ≤ (∫ x, ‖F x‖) * Vb ρ * M' := fun hg' => by
      have := pr_bound_L1 (hC σ j).1.aestronglyMeasurable (hC σ j).2.1 hg'
      linarith
    have h1 := hasDerivAt_pr_Hk hint hK hbd hc (Bola.mul_mj hg j) k (t - r)
    have h2 : HasDerivAt (fun r : ℝ => t - r) (-1) r := by
      exact (hasDerivAt_id r).const_sub t
    have h3 := h1.comp r h2
    refine h3.congr_deriv ?_
    ring
  unfold nP
  simp_rw [← Hk_mjg]
  exact HasDerivAt.fun_sum fun j _ => (hderL1 hS₁ hτ₁ j).sub (hderL1 hS₂ hτ₂ j)


/-- **A diferença dos integrandos fracos**: a parte viscosa vira `−wP (c|η|² g)`. -/
theorem Fw_diff {g : E3 → C3} (hg : Pesos g) {σ : ℝ} (hσ : σ ∈ Icc 0 τ) :
    Fw ν U₁ (R0 g) σ - Fw ν U₂ (R0 g) σ =
      -wP τ U₁ U₂ (Hk (4 * π ^ 2 * ν) g 1 0) σ + nP τ U₁ U₂ g σ := by
  have hcl : clamp τ σ = σ := clamp_of_mem hσ
  obtain ⟨C₁, hC₁⟩ := sol_bounds hS₁ hτ₁
  obtain ⟨C₂, hC₂⟩ := sol_bounds hS₂ hτ₂
  obtain ⟨CW, -, hCW⟩ := Wc_props hS₁ hS₂ hτ0 hτ₁ hτ₂
  have hσ₁ : σ ∈ Ico 0 T₁ := ⟨hσ.1, hσ.2.trans_lt hτ₁⟩
  have hσ₂ : σ ∈ Ico 0 T₂ := ⟨hσ.1, hσ.2.trans_lt hτ₂⟩
  have hU₁ : ContDiff ℝ 1 (fatia U₁ σ) := (slice_contDiff hS₁.1 hσ₁).of_le (by simp)
  have hU₂ : ContDiff ℝ 1 (fatia U₂ σ) := (slice_contDiff hS₂.1 hσ₂).of_le (by simp)
  have hWeq : Wc τ U₁ U₂ σ = fun x => fatia U₁ σ x - fatia U₂ σ x := by
    funext x
    simp only [Wc, hcl, fatia]
  have hW1 : ContDiff ℝ 1 (Wc τ U₁ U₂ σ) := by rw [hWeq]; exact hU₁.sub hU₂
  have hdφ : ∀ j x, dX j (R0 g) x = R0 (mjg j g) x := fun j x => dX_R0 hg j x
  have hL : ∀ j, L2B fun x => ‖R0 (mjg j g) x‖ := fun j => L2B_R0 (pesos_mj hg j)
  have hprod : ∀ {a b : E3 → E3}, Continuous a → Continuous b →
      Integrable (fun x => ‖a x‖ ^ 2) → Integrable (fun x => ‖b x‖ ^ 2) →
      Integrable fun x => inner ℝ (a x) (b x) := by
    intro a b ha hb ha2 hb2
    refine ((ha2.add hb2).div_const 2).mono' (ha.inner hb).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    show ‖a x‖ * ‖b x‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have hdW : ∀ j x, dX j (Wc τ U₁ U₂ σ) x = dX j (fatia U₁ σ) x - dX j (fatia U₂ σ) x := by
    intro j x
    rw [hWeq]
    unfold dX
    rw [fderiv_fun_sub (hU₁.differentiable one_ne_zero x) (hU₂.differentiable one_ne_zero x)]
    rfl
  have hdW2 : ∀ j, Integrable fun x => ‖dX j (Wc τ U₁ U₂ σ) x‖ ^ 2 := by
    intro j
    have hc : Continuous (dX j (Wc τ U₁ U₂ σ)) := continuous_dX_gen hW1 j
    refine ((((hC₁ σ hσ).2 j).1.const_mul 2).add (((hC₂ σ hσ).2 j).1.const_mul 2)).mono'
      (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hdW]
    have h1 := norm_sub_le (dX j (fatia U₁ σ) x) (dX j (fatia U₂ σ) x)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    show _ ≤ 2 * ‖dX j (fatia U₁ σ) x‖ ^ 2 + 2 * ‖dX j (fatia U₂ σ) x‖ ^ 2
    nlinarith [sq_nonneg (‖dX j (fatia U₁ σ) x‖ - ‖dX j (fatia U₂ σ) x‖)]
  -- a parte linear
  have hlin : (∑ j, ∫ x, inner ℝ (dX j (fatia U₁ σ) x) (dX j (R0 g) x)) -
      ∑ j, ∫ x, inner ℝ (dX j (fatia U₂ σ) x) (dX j (R0 g) x) =
      4 * π ^ 2 * pr (Wc τ U₁ U₂ σ) (fun η => (‖η‖ ^ 2 : ℝ) • g η) := by
    have i1 : ∀ j, Integrable fun x => inner ℝ (dX j (fatia U₁ σ) x) (dX j (R0 g) x) := by
      intro j
      simp_rw [hdφ]
      exact hprod (continuous_dX_gen hU₁ j) (contDiff_R0 (pesos_mj hg j)).continuous
        ((hC₁ σ hσ).2 j).1 (hL j).2.2
    have i2 : ∀ j, Integrable fun x => inner ℝ (dX j (fatia U₂ σ) x) (dX j (R0 g) x) := by
      intro j
      simp_rw [hdφ]
      exact hprod (continuous_dX_gen hU₂ j) (contDiff_R0 (pesos_mj hg j)).continuous
        ((hC₂ σ hσ).2 j).1 (hL j).2.2
    rw [← Finset.sum_sub_distrib]
    have step : ∀ j, (∫ x, inner ℝ (dX j (fatia U₁ σ) x) (dX j (R0 g) x)) -
        ∫ x, inner ℝ (dX j (fatia U₂ σ) x) (dX j (R0 g) x) =
        -∫ x, inner ℝ (Wc τ U₁ U₂ σ x) (dX j (dX j (R0 g)) x) := by
      intro j
      rw [← integral_sub (i1 j) (i2 j), ← ibp_L2 hW1 (hCW σ).2.1 j (hdW2 j) hg]
      congr 1
      funext x
      rw [hdW, inner_sub_left]
    simp_rw [step]
    rw [Finset.sum_neg_distrib]
    have hφ2 : ∀ j, Pesos fun η => mj j η • mj j η • g η := fun j =>
      pesos_mj (pesos_mj hg j) j
    have hdd : ∀ j x, dX j (dX j (R0 g)) x = R0 (fun η => mj j η • mj j η • g η) x := by
      intro j x
      have : dX j (R0 g) = R0 (mjg j g) := funext (hdφ j)
      rw [this]
      exact dX_R0 (pesos_mj hg j) j x
    have i3 : ∀ j, Integrable fun x => inner ℝ (Wc τ U₁ U₂ σ x) (dX j (dX j (R0 g)) x) := by
      intro j
      simp_rw [hdd]
      exact integrable_pr_L2 (hCW σ).1.aestronglyMeasurable (hCW σ).2.1 (hφ2 j)
    rw [← integral_finsetSum _ fun j _ => i3 j]
    have e1 : (fun x => ∑ j, inner ℝ (Wc τ U₁ U₂ σ x) (dX j (dX j (R0 g)) x)) =
        fun x => inner ℝ (Wc τ U₁ U₂ σ x)
          (R0 (fun η => (-(4 * π ^ 2)) • ((‖η‖ ^ 2 : ℝ) • g η)) x) := by
      funext x
      rw [← inner_sum]
      congr 1
      simp_rw [hdd]
      rw [← R0_sum fun j => integrable_pesos (hφ2 j)]
      congr 1
      funext η
      rw [sum_mj_sq_smul, smul_smul, mul_comm]
    rw [e1, show (∫ x, inner ℝ (Wc τ U₁ U₂ σ x)
        (R0 (fun η => (-(4 * π ^ 2)) • ((‖η‖ ^ 2 : ℝ) • g η)) x)) =
        pr (Wc τ U₁ U₂ σ) (fun η => (-(4 * π ^ 2)) • ((‖η‖ ^ 2 : ℝ) • g η)) from rfl, pr_smul]
    ring
  -- a parte não linear
  have hnl : ∀ {T : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}, SolucaoLocal ν u₀ T U P →
      (∑ j, ∫ x, fatia U σ x j * inner ℝ (fatia U σ x) (dX j (R0 g) x)) =
        ∑ j, pr (Nc τ U j σ) (mjg j g) := by
    intro T U P _
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold pr Nc
    congr 1
    funext x
    rw [hcl, real_inner_smul_left, hdφ]
    rfl
  unfold Fw nP wP
  rw [hnl hS₁, hnl hS₂, Hk_one_zero, pr_smul, Finset.sum_sub_distrib]
  have e2 : -ν * (∑ j, ∫ x, inner ℝ (dX j (fatia U₁ σ) x) (dX j (R0 g) x)) -
      -ν * (∑ j, ∫ x, inner ℝ (dX j (fatia U₂ σ) x) (dX j (R0 g) x)) =
      -ν * (4 * π ^ 2 * pr (Wc τ U₁ U₂ σ) (fun η => (‖η‖ ^ 2 : ℝ) • g η)) := by
    rw [← hlin]
    ring
  linear_combination e2

/-- **A formulação fraca para a diferença** (com a parte viscosa já integrada por partes). -/
theorem fraca_W {h : E3 → C3} (hh : Teste h) {s : ℝ} (hs : s ∈ Icc 0 τ) :
    wP τ U₁ U₂ h s = ∫ σ in (0 : ℝ)..s,
      (-wP τ U₁ U₂ (Hk (4 * π ^ 2 * ν) h 1 0) σ + nP τ U₁ U₂ h σ) := by
  have F1 := fraca_fourier hS₁ hτ₁ hh hs
  have F2 := fraca_fourier hS₂ hτ₂ hh hs
  have I1 := intervalIntegrable_Fw hS₁ hτ₁ hh.pesos hs
  have I2 := intervalIntegrable_Fw hS₂ hτ₂ hh.pesos hs
  obtain ⟨C₁, hC₁⟩ := sol_bounds hS₁ hτ₁
  obtain ⟨C₂, hC₂⟩ := sol_bounds hS₂ hτ₂
  have hcl : clamp τ s = s := clamp_of_mem hs
  have hc₁ : Continuous fun x => U₁ (x, s) :=
    (slice_contDiff hS₁.1 ⟨hs.1, hs.2.trans_lt hτ₁⟩).continuous
  have hc₂ : Continuous fun x => U₂ (x, s) :=
    (slice_contDiff hS₂.1 ⟨hs.1, hs.2.trans_lt hτ₂⟩).continuous
  have j1 : Integrable fun x => inner ℝ (U₁ (x, s)) (R0 h x) :=
    integrable_pr_L2 hc₁.aestronglyMeasurable (hC₁ s hs).1.1 hh.pesos
  have j2 : Integrable fun x => inner ℝ (U₂ (x, s)) (R0 h x) :=
    integrable_pr_L2 hc₂.aestronglyMeasurable (hC₂ s hs).1.1 hh.pesos
  have hw : wP τ U₁ U₂ h s =
      (∫ x, inner ℝ (U₁ (x, s)) (R0 h x)) - ∫ x, inner ℝ (U₂ (x, s)) (R0 h x) := by
    unfold wP pr Wc
    rw [hcl, ← integral_sub j1 j2]
    congr 1
    funext x
    rw [inner_sub_left]
  rw [hw]
  have e : (∫ x, inner ℝ (U₁ (x, s)) (R0 h x)) - ∫ x, inner ℝ (U₂ (x, s)) (R0 h x) =
      (∫ σ in (0 : ℝ)..s, Fw ν U₁ (R0 h) σ) - ∫ σ in (0 : ℝ)..s, Fw ν U₂ (R0 h) σ := by
    rw [← F1, ← F2]
    ring
  rw [e, ← intervalIntegral.integral_sub I1 I2]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [uIcc_of_le hs.1] at hσ
  exact Fw_diff hS₁ hS₂ hτ0 hτ₁ hτ₂ hh.pesos ⟨hσ.1, hσ.2.trans hs.2⟩

theorem measurable_wP {g : E3 → C3} (hg : Pesos g) : Measurable fun σ => wP τ U₁ U₂ g σ := by
  have hc₁ := continuous_clamped hS₁.1 hτ0 hτ₁
  have hc₂ := continuous_clamped hS₂.1 hτ0 hτ₂
  have hf : Continuous fun p : ℝ × E3 =>
      inner ℝ (U₁ (p.2, clamp τ p.1) - U₂ (p.2, clamp τ p.1)) (R0 g p.2) :=
    (hc₁.sub hc₂).inner ((contDiff_R0 hg).continuous.comp continuous_snd)
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem measurable_nP {g : E3 → C3} (hg : Pesos g) : Measurable fun σ => nP τ U₁ U₂ g σ := by
  have hm : ∀ {T : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}, SolucaoLocal ν u₀ T U P → τ < T →
      ∀ j, Measurable fun σ => pr (Nc τ U j σ) (mjg j g) := by
    intro T U P hS hτ j
    have hc := continuous_clamped hS.1 hτ0 hτ
    have hf : Continuous fun p : ℝ × E3 =>
        inner ℝ (U (p.2, clamp τ p.1) j • U (p.2, clamp τ p.1)) (R0 (mjg j g) p.2) :=
      ((((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hc).smul hc).inner
        ((contDiff_R0 (pesos_mj hg j)).continuous.comp continuous_snd))
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  unfold nP
  exact Finset.measurable_fun_sum _ fun j _ => (hm hS₁ hτ₁ j).sub (hm hS₂ hτ₂ j)

/-- **A fórmula de Duhamel testada**: a parte viscosa é absorvida pelo calor. -/
theorem duhamel_testado (hν : 0 ≤ ν) {h : E3 → C3} (hh : Teste h) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    wP τ U₁ U₂ h t = ∫ σ in (0 : ℝ)..t, nP τ U₁ U₂ (Hk (4 * π ^ 2 * ν) h 0 (t - σ)) σ := by
  set c : ℝ := 4 * π ^ 2 * ν with hc_def
  have hc : 0 ≤ c := by positivity
  have ht0 : 0 ≤ t := ht.1
  obtain ⟨ρ, M, hρ, hB⟩ := Teste.bola hh
  have hM : 0 ≤ M := (norm_nonneg _).trans (hB.2.2 0)
  set g : ℕ → ℝ → E3 → C3 := fun k r => Hk c h k (t - r) with hg_def
  have hgT : ∀ k r, Teste (g k r) := fun k r => Teste.heat hh k (t - r)
  have hsucc : ∀ k r, Hk c (g k r) 1 0 = g (k + 1) r := by
    intro k r
    rw [Hk_one_zero]
    funext η
    simp only [hg_def]
    rw [Hk_succ, smul_smul]
  have hg0 : g 0 t = h := by
    funext η
    simp [hg_def, Hk]
  have dW : ∀ k σ r, HasDerivAt (fun r => wP τ U₁ U₂ (g k r) σ) (wP τ U₁ U₂ (g (k + 1) r) σ) r :=
    fun k σ r => hasDerivAt_wP hS₁ hS₂ hτ0 hτ₁ hτ₂ hB hc k t σ r
  have dN : ∀ k σ r, HasDerivAt (fun r => nP τ U₁ U₂ (g k r) σ) (nP τ U₁ U₂ (g (k + 1) r) σ) r :=
    fun k σ r => hasDerivAt_nP hS₁ hS₂ hτ0 hτ₁ hτ₂ hB hc k t σ r
  -- cotas em `[0, t]`
  obtain ⟨KW, hKW0, hKW⟩ := wP_bound hS₁ hS₂ hτ0 hτ₁ hτ₂
  obtain ⟨KN, hKN0, hKN⟩ := nP_bound hS₁ hS₂ hτ0 hτ₁ hτ₂
  set Mk : ℕ → ℝ := fun k => (c * ρ ^ 2) ^ k * exp (c * ρ ^ 2 * t) * M with hMk
  have hMk0 : ∀ k, 0 ≤ Mk k := fun k => by positivity
  have hBg : ∀ k, ∀ r ∈ Icc 0 t, Bola ρ (Mk k) (g k r) := by
    intro k r hr
    have h1 := hB.heat hc k (t - r)
    refine ⟨h1.1, h1.2.1, fun η => (h1.2.2 η).trans ?_⟩
    have : |t - r| ≤ t := by rw [abs_of_nonneg (by linarith [hr.2])]; linarith [hr.1]
    simp only [hMk]
    gcongr
  have bW : ∀ k, ∀ r ∈ Icc 0 t, ∀ σ, |wP τ U₁ U₂ (g k r) σ| ≤ Mk k * (KW + Vb ρ) / 2 :=
    fun k r hr σ => hKW (hBg k r hr) σ
  have bN : ∀ k, ∀ r ∈ Icc 0 t, ∀ σ,
      |nP τ U₁ U₂ (g k r) σ| ≤ KN * (2 * π * (1 + max ρ 0) * Mk k) * Vb ρ :=
    fun k r hr σ => hKN (hBg k r hr) σ
  -- mensurabilidade conjunta
  have mW : ∀ k, Measurable (Function.uncurry fun σ r => wP τ U₁ U₂ (g k r) σ) := by
    intro k
    have h1 : Measurable (Function.uncurry fun r σ => wP τ U₁ U₂ (g k r) σ) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun σ => continuous_iff_continuousAt.mpr fun r => (dW k σ r).continuousAt)
        (fun r => measurable_wP hS₁ hS₂ hτ0 hτ₁ hτ₂ (hgT k r).pesos)
    have e : (Function.uncurry fun σ r => wP τ U₁ U₂ (g k r) σ) =
        (Function.uncurry fun r σ => wP τ U₁ U₂ (g k r) σ) ∘ Prod.swap := by
      funext p
      simp only [Function.comp_apply, Function.uncurry, Prod.fst_swap, Prod.snd_swap]
    rw [e]
    exact h1.comp measurable_swap
  have mN : ∀ k, Measurable (Function.uncurry fun σ r => nP τ U₁ U₂ (g k r) σ) := by
    intro k
    have h1 : Measurable (Function.uncurry fun r σ => nP τ U₁ U₂ (g k r) σ) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun σ => continuous_iff_continuousAt.mpr fun r => (dN k σ r).continuousAt)
        (fun r => measurable_nP hS₁ hS₂ hτ0 hτ₁ hτ₂ (hgT k r).pesos)
    have e : (Function.uncurry fun σ r => nP τ U₁ U₂ (g k r) σ) =
        (Function.uncurry fun r σ => nP τ U₁ U₂ (g k r) σ) ∘ Prod.swap := by
      funext p
      simp only [Function.comp_apply, Function.uncurry, Prod.fst_swap, Prod.snd_swap]
    rw [e]
    exact h1.comp measurable_swap
  have mdiag : ∀ {F : ℝ → ℝ → ℝ}, Measurable (Function.uncurry F) →
      Measurable fun σ => F σ σ := fun hF => hF.comp (measurable_id.prodMk measurable_id)
  -- passo 1
  have s1 : wP τ U₁ U₂ (g 0 t) t = ∫ σ in (0 : ℝ)..t,
      (-wP τ U₁ U₂ (g 1 t) σ + nP τ U₁ U₂ (g 0 t) σ) := by
    have := fraca_W hS₁ hS₂ hτ0 hτ₁ hτ₂ (hgT 0 t) ht
    rw [hsucc] at this
    exact this
  have e0 : wP τ U₁ U₂ h t = wP τ U₁ U₂ (g 0 t) t := by rw [hg0]
  -- passo 2: FTC em `r`
  set F : ℝ → ℝ → ℝ := fun σ r => -wP τ U₁ U₂ (g 2 r) σ + nP τ U₁ U₂ (g 1 r) σ with hF_def
  have hFm : Measurable (Function.uncurry F) := ((mW 2).neg).add (mN 1)
  have s2 : ∀ σ, (-wP τ U₁ U₂ (g 1 t) σ + nP τ U₁ U₂ (g 0 t) σ) =
      (-wP τ U₁ U₂ (g 1 σ) σ + nP τ U₁ U₂ (g 0 σ) σ) + ∫ r in σ..t, F σ r := by
    intro σ
    have hd : ∀ r ∈ uIcc σ t, HasDerivAt (fun r => -wP τ U₁ U₂ (g 1 r) σ + nP τ U₁ U₂ (g 0 r) σ)
        (F σ r) r := fun r _ => ((dW 1 σ r).neg).add (dN 0 σ r)
    have hcont : Continuous fun r => F σ r := by
      refine continuous_iff_continuousAt.mpr fun r => ?_
      exact ((dW 2 σ r).continuousAt.neg).add (dN 1 σ r).continuousAt
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
    linarith
  -- integrabilidades
  set A : ℝ → ℝ := fun σ => -wP τ U₁ U₂ (g 1 σ) σ + nP τ U₁ U₂ (g 0 σ) σ with hA_def
  have hAi : IntervalIntegrable A volume 0 t := by
    refine ii_of_bound ((mdiag (mW 1)).neg.add (mdiag (mN 0))) ht0 (K := Mk 1 * (KW + Vb ρ) / 2 +
      KN * (2 * π * (1 + max ρ 0) * Mk 0) * Vb ρ) fun σ hσ => ?_
    show |-wP τ U₁ U₂ (g 1 σ) σ + nP τ U₁ U₂ (g 0 σ) σ| ≤ _
    refine (abs_add_le _ _).trans (add_le_add ?_ (bN 0 σ hσ σ))
    rw [abs_neg]
    exact bW 1 σ hσ σ
  have hLi : IntervalIntegrable (fun σ => -wP τ U₁ U₂ (g 1 t) σ + nP τ U₁ U₂ (g 0 t) σ)
      volume 0 t := by
    refine ii_of_bound ((measurable_wP hS₁ hS₂ hτ0 hτ₁ hτ₂ (hgT 1 t).pesos).neg.add
      (measurable_nP hS₁ hS₂ hτ0 hτ₁ hτ₂ (hgT 0 t).pesos)) ht0 (K := Mk 1 * (KW + Vb ρ) / 2 +
      KN * (2 * π * (1 + max ρ 0) * Mk 0) * Vb ρ) fun σ _ => ?_
    have htt : t ∈ Icc 0 t := ⟨ht0, le_rfl⟩
    show |-wP τ U₁ U₂ (g 1 t) σ + nP τ U₁ U₂ (g 0 t) σ| ≤ _
    refine (abs_add_le _ _).trans (add_le_add ?_ (bN 0 t htt σ))
    rw [abs_neg]
    exact bW 1 t htt σ
  have hBi : IntervalIntegrable (fun σ => ∫ r in σ..t, F σ r) volume 0 t := by
    have : (fun σ => ∫ r in σ..t, F σ r) =
        fun σ => (-wP τ U₁ U₂ (g 1 t) σ + nP τ U₁ U₂ (g 0 t) σ) - A σ := by
      funext σ
      rw [s2 σ]
      ring
    rw [this]
    exact hLi.sub hAi
  have hDi : IntervalIntegrable (fun r => wP τ U₁ U₂ (g 1 r) r) volume 0 t :=
    ii_of_bound (mdiag (mW 1)) ht0 fun σ hσ => bW 1 σ hσ σ
  -- passo 3–5
  have s3 : ∫ σ in (0 : ℝ)..t, (-wP τ U₁ U₂ (g 1 t) σ + nP τ U₁ U₂ (g 0 t) σ) =
      (∫ σ in (0 : ℝ)..t, A σ) + ∫ σ in (0 : ℝ)..t, (∫ r in σ..t, F σ r) := by
    rw [← intervalIntegral.integral_add hAi hBi]
    exact intervalIntegral.integral_congr fun σ _ => s2 σ
  have s4 : ∫ σ in (0 : ℝ)..t, (∫ r in σ..t, F σ r) =
      ∫ r in (0 : ℝ)..t, (∫ σ in (0 : ℝ)..r, F σ r) := by
    refine triangle hFm ht0 (K := Mk 2 * (KW + Vb ρ) / 2 +
      KN * (2 * π * (1 + max ρ 0) * Mk 1) * Vb ρ) fun σ _ r hr => ?_
    refine (abs_add_le _ _).trans (add_le_add ?_ (bN 1 r hr σ))
    rw [abs_neg]
    exact bW 2 r hr σ
  have s5 : ∫ r in (0 : ℝ)..t, (∫ σ in (0 : ℝ)..r, F σ r) =
      ∫ r in (0 : ℝ)..t, wP τ U₁ U₂ (g 1 r) r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht0] at hr
    have := fraca_W hS₁ hS₂ hτ0 hτ₁ hτ₂ (hgT 1 r) ⟨hr.1, hr.2.trans ht.2⟩
    rw [hsucc] at this
    exact this.symm
  rw [e0, s1, s3, s4, s5, ← intervalIntegral.integral_add hAi hDi]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [hA_def]
  ring

end Hip

end Dois

end ATK.NSMild

#print axioms ATK.NSMild.Wc
#print axioms ATK.NSMild.Nc
#print axioms ATK.NSMild.mjg
#print axioms ATK.NSMild.wP
#print axioms ATK.NSMild.nP
#print axioms ATK.NSMild.clamp_mem
#print axioms ATK.NSMild.Bola.mul_mj
#print axioms ATK.NSMild.Hk_mjg
#print axioms ATK.NSMild.Teste.pesos_mjg
#print axioms ATK.NSMild.triangle
#print axioms ATK.NSMild.ii_of_bound
#print axioms ATK.NSMild.continuous_clamped
#print axioms ATK.NSMild.bounds_clamped
#print axioms ATK.NSMild.Wc_props
#print axioms ATK.NSMild.Nc_props
#print axioms ATK.NSMild.pr_smul
#print axioms ATK.NSMild.sum_mj_sq_smul
#print axioms ATK.NSMild.Fw_bounded
#print axioms ATK.NSMild.intervalIntegrable_Fw
#print axioms ATK.NSMild.Hk_one_zero
#print axioms ATK.NSMild.wP_bound
#print axioms ATK.NSMild.nP_bound
#print axioms ATK.NSMild.hasDerivAt_wP
#print axioms ATK.NSMild.hasDerivAt_nP
#print axioms ATK.NSMild.Fw_diff
#print axioms ATK.NSMild.fraca_W
#print axioms ATK.NSMild.measurable_wP
#print axioms ATK.NSMild.measurable_nP
#print axioms ATK.NSMild.duhamel_testado
