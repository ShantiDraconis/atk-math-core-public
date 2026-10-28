import ATK.NSTeste

/-!
# ATK — Navier–Stokes, marco NS8c: a formulação fraca contra os campos teste de Fourier

Ponte B3, marco NS8 (terceira parte). Passando ao limite no teste truncado
`φ_n = Σ_k ∂_k(κ_{n+1} G_k)` (convergência dominada, majorantes de quadrado integrável), a
identidade fraca de `fraca_compacta` vale para o campo teste de Fourier `θ = Re F0 h`
(**`fraca_fourier`**), para toda solução da classe `SolucaoLocal`.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open scoped ContDiff Interval
open ATK.LigacaoNS (E3 dX e div lap conv grad gradSq fatia NSEq SolucaoLocal EnergiaAte)
open ATK.NSFourierBase ATK.NSPicard ATK.NSFraca ATK.NSTeste

namespace ATK.NSFracaF

/-! ### Continuidade conjunta e mensurabilidade -/

theorem dX_fatia_eq {T : ℝ} {U : E3 × ℝ → E3} (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T))
    {x : E3} {s : ℝ} (hs : s ∈ Ico 0 T) (j : Fin 3) :
    dX j (fatia U s) x = fderivWithin ℝ U ((univ : Set E3) ×ˢ Ico 0 T) (x, s) (e j, 0) := by
  have hsS : (x, s) ∈ (univ : Set E3) ×ˢ Ico 0 T := ⟨mem_univ _, hs⟩
  have hd : HasFDerivWithinAt U (fderivWithin ℝ U (univ ×ˢ Ico 0 T) (x, s)) (univ ×ˢ Ico 0 T)
      (x, s) := ((hU.differentiableOn (by simp)) _ hsS).hasFDerivWithinAt
  have hι : HasFDerivAt (fun y : E3 => ((y, s) : E3 × ℝ)) (ContinuousLinearMap.inl ℝ E3 ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const s x)
  have h := hd.comp x (hι.hasFDerivWithinAt (s := univ)) (fun y _ =>
    show ((y, s) : E3 × ℝ) ∈ (univ : Set E3) ×ˢ Ico 0 T from ⟨mem_univ _, hs⟩)
  rw [hasFDerivWithinAt_univ] at h
  unfold dX
  rw [show fatia U s = U ∘ fun y => (y, s) from rfl, h.fderiv]
  rfl

theorem continuousOn_dX_fatia {T : ℝ} {U : E3 × ℝ → E3}
    (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) (j : Fin 3) :
    ContinuousOn (fun z : E3 × ℝ => dX j (fatia U z.2) z.1) (univ ×ˢ Ico 0 T) := by
  have h := (hU.continuousOn_fderivWithin uniqueDiffOn_S (by simp)).clm_apply
    (continuousOn_const (c := ((e j, 0) : E3 × ℝ)))
  refine h.congr fun z hz => ?_
  exact dX_fatia_eq hU hz.2 j

theorem aesm_slice_integral {τ t : ℝ} (ht0 : 0 ≤ t) (htτ : t ≤ τ) {F : E3 × ℝ → ℝ}
    (hF : ContinuousOn F (univ ×ˢ Icc 0 τ)) :
    AEStronglyMeasurable (fun s => ∫ x, F (x, s)) (volume.restrict (Ι 0 t)) := by
  rw [uIoc_of_le ht0]
  have hG : ContinuousOn (fun p : ℝ × E3 => F (p.2, p.1)) (Ioc 0 t ×ˢ univ) :=
    hF.comp (continuous_snd.prodMk continuous_fst).continuousOn
      fun p hp => ⟨mem_univ _, hp.1.1.le, hp.1.2.trans htτ⟩
  have e : (volume.restrict (Ioc 0 t)).prod (volume : Measure E3) =
      ((volume : Measure ℝ).prod (volume : Measure E3)).restrict (Ioc 0 t ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hm : AEStronglyMeasurable (fun p : ℝ × E3 => F (p.2, p.1))
      ((volume.restrict (Ioc 0 t)).prod volume) := by
    rw [e]
    exact hG.aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  exact hm.integral_prod_right'

/-! ### Convergência dominada para os pareamentos -/

theorem dc_L2 {a : E3 → E3} (ha : Continuous a) (ha2 : Integrable fun x => ‖a x‖ ^ 2)
    {f : ℕ → E3 → E3} {g : E3 → E3} (hf : ∀ n, Continuous (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {D : E3 → ℝ} (hD : L2B D)
    (hb : ∀ n x, ‖f n x‖ ≤ D x) :
    Tendsto (fun n => ∫ x, inner ℝ (a x) (f n x)) atTop (𝓝 (∫ x, inner ℝ (a x) (g x))) := by
  refine tendsto_integral_of_dominated_convergence (fun x => (‖a x‖ ^ 2 + D x ^ 2) / 2)
    (fun n => (ha.inner (hf n)).aestronglyMeasurable) ((ha2.add hD.2.2).div_const 2)
    (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ((continuous_inner.tendsto _).comp
      ((tendsto_const_nhds (x := a x)).prodMk_nhds (hlim x))))
  have h1 := norm_inner_le_norm (𝕜 := ℝ) (a x) (f n x)
  have h2 := hb n x
  have h3 : 0 ≤ ‖f n x‖ := norm_nonneg _
  rw [Real.norm_eq_abs] at h1 ⊢
  have : ‖a x‖ * D x ≤ (‖a x‖ ^ 2 + D x ^ 2) / 2 := by nlinarith [sq_nonneg (‖a x‖ - D x)]
  calc |inner ℝ (a x) (f n x)| ≤ ‖a x‖ * ‖f n x‖ := h1
    _ ≤ ‖a x‖ * D x := by gcongr
    _ ≤ _ := this

theorem dc_L1 {a : E3 → E3} (ha : Continuous a) (ha1 : Integrable fun x => ‖a x‖)
    {f : ℕ → E3 → E3} {g : E3 → E3} (hf : ∀ n, Continuous (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {B : ℝ}
    (hb : ∀ n x, ‖f n x‖ ≤ B) :
    Tendsto (fun n => ∫ x, inner ℝ (a x) (f n x)) atTop (𝓝 (∫ x, inner ℝ (a x) (g x))) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖a x‖ * B)
    (fun n => (ha.inner (hf n)).aestronglyMeasurable) (ha1.mul_const B)
    (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ((continuous_inner.tendsto _).comp
      ((tendsto_const_nhds (x := a x)).prodMk_nhds (hlim x))))
  exact (norm_inner_le_norm _ _).trans (by gcongr; exact hb n x)

/-! ### As cotas da classe `SolucaoLocal` -/

theorem sol_bounds {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (hS : SolucaoLocal ν u₀ T U P) {τ : ℝ} (hτ : τ < T) :
    ∃ C, ∀ s ∈ Icc 0 τ, ((Integrable fun x => ‖U (x, s)‖ ^ 2) ∧ ∫ x, ‖U (x, s)‖ ^ 2 ≤ C) ∧
      ∀ j, (Integrable fun x => ‖dX j (fatia U s) x‖ ^ 2) ∧
        ∫ x, ‖dX j (fatia U s) x‖ ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := hS.2.2.2.2.2 τ hτ
  refine ⟨C, fun s hs => ⟨(hC s hs).1, fun j => ?_⟩⟩
  obtain ⟨-, hgi, hgC⟩ := hC s hs
  have hsI : s ∈ Ico 0 T := ⟨hs.1, hs.2.trans_lt hτ⟩
  have hc : Continuous (dX j (fatia U s)) :=
    continuous_dX_gen ((slice_contDiff hS.1 hsI).of_le (by simp)) j
  have hle : ∀ x, ‖dX j (fatia U s) x‖ ^ 2 ≤ gradSq (fatia U s) x := fun x =>
    Finset.single_le_sum (f := fun i => ‖dX i (fatia U s) x‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hi : Integrable fun x => ‖dX j (fatia U s) x‖ ^ 2 :=
    hgi.mono' (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle x)
  exact ⟨hi, (integral_mono hi hgi hle).trans hgC⟩


theorem abs_coord_le (x : E3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  simpa using this

/-! ### O integrando fraco: mensurabilidade, cota e limite -/

section Fw

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem aesm_Fw (hS : SolucaoLocal ν u₀ T U P) {τ : ℝ} (hτ : τ < T) {t : ℝ} (ht : t ∈ Icc 0 τ)
    {φ : E3 → E3} (hdφ : ∀ j, Continuous (dX j φ)) :
    AEStronglyMeasurable (Fw ν U φ) (volume.restrict (Ι 0 t)) := by
  have hU := hS.1
  have hsub : (univ : Set E3) ×ˢ Icc 0 τ ⊆ univ ×ˢ Ico 0 T :=
    fun z hz => ⟨mem_univ _, hz.2.1, hz.2.2.trans_lt hτ⟩
  have hUc : ContinuousOn U (univ ×ˢ Icc 0 τ) := hU.continuousOn.mono hsub
  have h1 : ∀ j, AEStronglyMeasurable
      (fun s => ∫ x, inner ℝ (dX j (fatia U s) x) (dX j φ x)) (volume.restrict (Ι 0 t)) := by
    intro j
    refine aesm_slice_integral (F := fun z => inner ℝ (dX j (fatia U z.2) z.1) (dX j φ z.1))
      ht.1 ht.2 ?_
    exact ((continuousOn_dX_fatia hU j).mono hsub).inner
      ((hdφ j).comp continuous_fst).continuousOn
  have h2 : ∀ j, AEStronglyMeasurable
      (fun s => ∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j φ x))
      (volume.restrict (Ι 0 t)) := by
    intro j
    refine aesm_slice_integral (F := fun z => U z j * inner ℝ (U z) (dX j φ z.1)) ht.1 ht.2 ?_
    have hj : ContinuousOn (fun z => U z j) (univ ×ˢ Icc 0 τ) :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn hUc
    exact hj.mul (hUc.inner ((hdφ j).comp continuous_fst).continuousOn)
  unfold Fw
  exact ((Finset.aestronglyMeasurable_fun_sum _ fun j _ => h1 j).const_mul _).add
    (Finset.aestronglyMeasurable_fun_sum _ fun j _ => h2 j)

end Fw

/-! ### A formulação fraca para os campos teste de Fourier -/

/-- **A formulação fraca** contra `θ = Re F0 h` (`h` dado teste): a pressão, arbitrária, não
aparece. -/
theorem fraca_fourier {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (hS : SolucaoLocal ν u₀ T U P) {τ : ℝ} (hτ : τ < T) {h : E3 → C3} (hh : Teste h)
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    (∫ x, inner ℝ (U (x, t)) (R0 h x)) - ∫ x, inner ℝ (u₀ x) (R0 h x) =
      ∫ s in (0 : ℝ)..t, Fw ν U (R0 h) s := by
  obtain ⟨C1, -, hC1⟩ := exists_bound_dX_kap0
  obtain ⟨C2, -, hC2⟩ := exists_bound_dX_dX_kap0
  obtain ⟨C, hC⟩ := sol_bounds hS hτ
  have hU := hS.1
  have h0 := hS.2.2.1
  have hτ0 : 0 ≤ τ := ht.1.trans ht.2
  have hsI : ∀ {s : ℝ}, s ∈ Icc 0 τ → s ∈ Ico 0 T := fun hs => ⟨hs.1, hs.2.trans_lt hτ⟩
  have hcU : ∀ {s : ℝ}, s ∈ Icc 0 τ → Continuous (fatia U s) := fun hs =>
    (slice_contDiff hU (hsI hs)).continuous
  have hcdU : ∀ {s : ℝ}, s ∈ Icc 0 τ → ∀ j, Continuous (dX j (fatia U s)) := fun hs j =>
    continuous_dX_gen ((slice_contDiff hU (hsI hs)).of_le (by simp)) j
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hφc : ∀ n, Continuous (phiN h n) := fun n => (contDiff_phiN hh n).continuous
  have hdφc : ∀ n j, Continuous (dX j (phiN h n)) := fun n j =>
    continuous_dX_gen ((contDiff_phiN hh n).of_le (by simp)) j
  have hid : ∀ n, (∫ x, inner ℝ (U (x, t)) (phiN h n x)) - ∫ x, inner ℝ (u₀ x) (phiN h n x) =
      ∫ s in (0 : ℝ)..t, Fw ν U (phiN h n) s := fun n =>
    fraca_compacta hS hτ ((contDiff_phiN hh n).of_le (by simp)) (hasCompactSupport_phiN hh n)
      (div_phiN hh n) ht
  -- o lado esquerdo
  have hL : Tendsto (fun n => (∫ x, inner ℝ (U (x, t)) (phiN h n x)) -
      ∫ x, inner ℝ (u₀ x) (phiN h n x)) atTop
      (𝓝 ((∫ x, inner ℝ (U (x, t)) (R0 h x)) - ∫ x, inner ℝ (u₀ x) (R0 h x))) := by
    have hb : ∀ n x, ‖phiN h n x‖ ≤ Dphi h C1 x := fun n x => norm_phiN_le hh hC1 n x
    have l1 := dc_L2 (a := fatia U t) (hcU ht) (hC t ht).1.1 hφc (tendsto_phiN hh)
      (L2B_Dphi hh C1) hb
    have hu0 : u₀ = fatia U 0 := funext fun x => (h0 x).symm
    have l2 := dc_L2 (a := fatia U 0) (hcU ⟨le_rfl, hτ0⟩) (hC 0 ⟨le_rfl, hτ0⟩).1.1 hφc
      (tendsto_phiN hh) (L2B_Dphi hh C1) hb
    rw [← hu0] at l2
    exact l1.sub l2
  -- o lado direito
  have hDL : ∀ j, L2B (DdPhi h C1 C2 j) := fun j => L2B_DdPhi hh C1 C2 j
  choose B hB using fun j => (hDL j).2.1
  set I : Fin 3 → ℝ := fun j => ∫ x, DdPhi h C1 C2 j x ^ 2
  set K : ℝ := |ν| * ∑ j, (C + I j) / 2 + ∑ j, C * B j
  have hbound : ∀ {φ : E3 → E3}, (∀ j x, ‖dX j φ x‖ ≤ DdPhi h C1 C2 j x) →
      ∀ s ∈ Icc 0 τ, ‖Fw ν U φ s‖ ≤ K := by
    intro φ hφ s hs
    have t1 : ∀ j, ‖∫ x, inner ℝ (dX j (fatia U s) x) (dX j φ x)‖ ≤ (C + I j) / 2 := by
      intro j
      have hi : Integrable fun x => (‖dX j (fatia U s) x‖ ^ 2 + DdPhi h C1 C2 j x ^ 2) / 2 :=
        (((hC s hs).2 j).1.add (hDL j).2.2).div_const 2
      refine (norm_integral_le_of_norm_le hi (Eventually.of_forall fun x => ?_)).trans ?_
      · have h1 := norm_inner_le_norm (𝕜 := ℝ) (dX j (fatia U s) x) (dX j φ x)
        have h2 := hφ j x
        have h3 : 0 ≤ ‖dX j φ x‖ := norm_nonneg _
        calc ‖inner ℝ (dX j (fatia U s) x) (dX j φ x)‖ ≤ ‖dX j (fatia U s) x‖ * ‖dX j φ x‖ := h1
          _ ≤ ‖dX j (fatia U s) x‖ * DdPhi h C1 C2 j x := by gcongr
          _ ≤ _ := by nlinarith [sq_nonneg (‖dX j (fatia U s) x‖ - DdPhi h C1 C2 j x)]
      · rw [integral_div, integral_add ((hC s hs).2 j).1 (hDL j).2.2]
        have := ((hC s hs).2 j).2
        linarith
    have t2 : ∀ j, ‖∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j φ x)‖ ≤ C * B j := by
      intro j
      have hi : Integrable fun x => ‖U (x, s)‖ ^ 2 * B j := (hC s hs).1.1.mul_const _
      refine (norm_integral_le_of_norm_le hi (Eventually.of_forall fun x => ?_)).trans ?_
      · have h1 := norm_inner_le_norm (𝕜 := ℝ) (fatia U s x) (dX j φ x)
        have h2 : ‖dX j φ x‖ ≤ B j := (hφ j x).trans ((le_abs_self _).trans (hB j x))
        have h3 := abs_coord_le (fatia U s x) j
        rw [norm_mul, Real.norm_eq_abs]
        calc |fatia U s x j| * ‖inner ℝ (fatia U s x) (dX j φ x)‖
            ≤ ‖fatia U s x‖ * (‖fatia U s x‖ * ‖dX j φ x‖) := by gcongr
          _ ≤ ‖fatia U s x‖ * (‖fatia U s x‖ * B j) := by gcongr
          _ = ‖U (x, s)‖ ^ 2 * B j := by simp only [fatia]; ring
      · rw [integral_mul_const]
        have hB0 : 0 ≤ B j := (abs_nonneg _).trans (hB j 0)
        have := (hC s hs).1.2
        nlinarith
    unfold Fw
    calc ‖-ν * (∑ j, ∫ x, inner ℝ (dX j (fatia U s) x) (dX j φ x)) +
          ∑ j, ∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j φ x)‖
        ≤ |ν| * ∑ j, ‖∫ x, inner ℝ (dX j (fatia U s) x) (dX j φ x)‖ +
          ∑ j, ‖∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j φ x)‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
          rw [norm_mul, norm_neg, Real.norm_eq_abs]
          gcongr
          exact norm_sum_le _ _
      _ ≤ K := add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => t1 j)
          (abs_nonneg _)) (Finset.sum_le_sum fun j _ => t2 j)
  have hR : Tendsto (fun n => ∫ s in (0 : ℝ)..t, Fw ν U (phiN h n) s) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, Fw ν U (R0 h) s)) := by
    have hsub : ∀ {s : ℝ}, s ∈ Ι 0 t → s ∈ Icc 0 τ := fun hs => by
      rw [uIoc_of_le ht.1] at hs
      exact ⟨hs.1.le, hs.2.trans ht.2⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
      (Eventually.of_forall fun n => aesm_Fw hS hτ ht (hdφc n))
      (Eventually.of_forall fun n => Eventually.of_forall fun s hs =>
        hbound (fun j x => norm_dX_phiN_le hh hC1 hC2 n j x) s (hsub hs))
      intervalIntegrable_const (Eventually.of_forall fun s hs => ?_)
    have hs' := hsub hs
    have l1 : ∀ j, Tendsto (fun n => ∫ x, inner ℝ (dX j (fatia U s) x) (dX j (phiN h n) x))
        atTop (𝓝 (∫ x, inner ℝ (dX j (fatia U s) x) (dX j (R0 h) x))) := fun j =>
      dc_L2 (hcdU hs' j) ((hC s hs').2 j).1 (fun n => hdφc n j) (tendsto_dX_phiN hh j)
        (hDL j) (fun n x => norm_dX_phiN_le hh hC1 hC2 n j x)
    have l2 : ∀ j, Tendsto (fun n => ∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j (phiN h n) x))
        atTop (𝓝 (∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j (R0 h) x))) := by
      intro j
      have hac : Continuous fun x => fatia U s x j • fatia U s x :=
        ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (hcU hs')).smul (hcU hs')
      have ha1 : Integrable fun x => ‖fatia U s x j • fatia U s x‖ := by
        refine (hC s hs').1.1.mono' hac.norm.aestronglyMeasurable
          (Eventually.of_forall fun x => ?_)
        rw [norm_norm, norm_smul, Real.norm_eq_abs, sq]
        exact mul_le_mul_of_nonneg_right (abs_coord_le _ j) (norm_nonneg _)
      have := dc_L1 hac ha1 (fun n => hdφc n j) (tendsto_dX_phiN hh j)
        (B := B j) (fun n x => (norm_dX_phiN_le hh hC1 hC2 n j x).trans
          ((le_abs_self _).trans (hB j x)))
      simp_rw [real_inner_smul_left] at this
      exact this
    unfold Fw
    exact ((tendsto_finsetSum _ fun j _ => l1 j).const_mul (-ν)).add
      (tendsto_finsetSum _ fun j _ => l2 j)
  exact tendsto_nhds_unique (hL.congr hid) hR

end ATK.NSFracaF

#print axioms ATK.NSFracaF.dX_fatia_eq
#print axioms ATK.NSFracaF.continuousOn_dX_fatia
#print axioms ATK.NSFracaF.aesm_slice_integral
#print axioms ATK.NSFracaF.dc_L2
#print axioms ATK.NSFracaF.dc_L1
#print axioms ATK.NSFracaF.sol_bounds
#print axioms ATK.NSFracaF.abs_coord_le
#print axioms ATK.NSFracaF.aesm_Fw
#print axioms ATK.NSFracaF.fraca_fourier
