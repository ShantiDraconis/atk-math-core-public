import ATK.HurwitzJensen
import ATK.DeBruijnNewman

/-!
# ATK — `S = {t | zeros de H_t reais}` é fechado (Hurwitz), e a ponte `HR ⟺ Λ ≤ 0` com uma hipótese a menos

* `H_ne_zero_at_zero`: `H_t(0) = ∫₀^∞e^{tu²}Φ(u)du > 0` (pois `Φ > 0`), logo `H_t ≢ 0`.
* `tendstoUniformlyOn_H`: `t_n → t ⇒ H_{t_n} → H_t` uniformemente em discos (convergência dominada).
* **`isClosed_S`**: `S` é fechado — por Hurwitz (`ATK.Hurwitz.hurwitz_local`): um zero não real de `H_t` seria
  limite de zeros não reais de `H_{t_n}`.
* `rh_iff_Lambda_le_zero'`: **HR ⟺ `Λ ≤ 0`**, condicional agora só a de Bruijn (`S ≠ ∅`, `S` fechado para cima) e
  Newman (`S` limitado inferiormente) — o fechamento de `S` deixou de ser hipótese.
-/

open Complex Filter Topology Metric Set MeasureTheory

namespace ATK.DBNF

open ATK.DBN ATK.Hurwitz ATK.XiCresc
open ATK.XiPhi (Phi)

theorem peso_pos (t : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 < peso t u :=
  mul_pos (Real.exp_pos _) (ATK.XiMom.Phi_pos hu)

theorem aesm_peso (t : ℝ) : AEStronglyMeasurable (peso t) (volume.restrict (Ioi 0)) :=
  ((continuousOn_peso t).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi

theorem integrableOn_peso (t : ℝ) : IntegrableOn (peso t) (Ioi 0) := by
  refine Integrable.mono' (ATK.XiPhi.integrableOn_exp_neg_mul
    (160 * Real.exp (|t| + 0 + (|t| + 0) ^ 2))) (aesm_peso t) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have h := peso_cota (t := t) (y := 0) le_rfl (le_of_lt hu)
  rw [zero_mul, Real.exp_zero, mul_one] at h
  rw [Real.norm_eq_abs]
  exact h

/-- `H_t(0) ≠ 0`. -/
theorem H_ne_zero_at_zero (t : ℝ) : H t 0 ≠ 0 := by
  have h := H_ofReal t 0
  simp only [zero_mul, Real.cos_zero, mul_one, Complex.ofReal_zero] at h
  rw [h, Complex.ofReal_ne_zero]
  apply ne_of_gt
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (integrableOn_peso t)]
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support (peso t) ∩ Ioi 0 :=
      fun u hu => ⟨(peso_pos t (le_of_lt hu)).ne', hu⟩
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    simp
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => (peso_pos t (le_of_lt hu)).le

theorem peso_abs_le {s T u : ℝ} (hs : |s| ≤ T) : |peso s u| ≤ |peso T u| := by
  unfold peso
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self s).trans hs) (sq_nonneg u))

/-- `∫|e^{τₙu²} − e^{tu²}||Φ(u)|e^{Ru}du → 0` quando `τₙ → t`. -/
theorem tendsto_int_dif {t R : ℝ} (hR : 0 ≤ R) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun n => ∫ u in Ioi (0 : ℝ), |peso (τ n) u - peso t u| * Real.exp (R * u)) atTop (𝓝 0) := by
  set T := |t| + 1 with hT
  set K := 160 * Real.exp (|T| + R + (|T| + R) ^ 2) with hK
  have hev : ∀ᶠ n in atTop, |τ n| ≤ T := by
    filter_upwards [(Metric.tendsto_nhds.mp hτ) 1 one_pos] with n hn
    rw [Real.dist_eq] at hn
    have := abs_sub_abs_le_abs_sub (τ n) t
    linarith
  have h := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℕ))
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun n u => |peso (τ n) u - peso t u| * Real.exp (R * u)) (f := fun _ => (0 : ℝ))
    (fun u => 2 * K * Real.exp (-u)) (Eventually.of_forall fun n => ?_) ?_
    (ATK.XiPhi.integrableOn_exp_neg_mul (2 * K)) ?_
  · simpa using h
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((((continuousOn_peso (τ n)).sub (continuousOn_peso t)).abs).mono Ioi_subset_Ici_self).mul
      (by fun_prop : Continuous fun u : ℝ => Real.exp (R * u)).continuousOn
  · filter_upwards [hev] with n hn
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt hu
    have h1 := peso_abs_le (u := u) hn
    have h2 := peso_abs_le (s := t) (T := T) (u := u) (by rw [hT]; linarith)
    have h3 := peso_cota (t := T) (y := R) hR hu0
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    have h4 := abs_sub (peso (τ n) u) (peso t u)
    have he := Real.exp_pos (R * u)
    calc |peso (τ n) u - peso t u| * Real.exp (R * u)
        ≤ (|peso T u| + |peso T u|) * Real.exp (R * u) := by gcongr; linarith
      _ = 2 * (|peso T u| * Real.exp (R * u)) := by ring
      _ ≤ 2 * (K * Real.exp (-u)) := by gcongr
      _ = 2 * K * Real.exp (-u) := by ring
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
    have hc : Continuous fun s : ℝ => peso s u := by unfold peso; fun_prop
    have := ((hc.tendsto t).comp hτ).sub_const (peso t u)
    rw [sub_self] at this
    have h2 := (this.abs).mul_const (Real.exp (R * u))
    simpa using h2

/-- `H_{τₙ} → H_t` uniformemente em discos. -/
theorem tendstoUniformlyOn_H {t : ℝ} {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝 t)) (z0 : ℂ) (r : ℝ) :
    TendstoUniformlyOn (fun n => H (τ n)) (H t) atTop (closedBall z0 r) := by
  set R := ‖z0‖ + |r| with hRdef
  have hR : 0 ≤ R := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_int_dif hR hτ).eventually (gt_mem_nhds hε)] with n hn z hz
  have hzR : ‖z‖ ≤ R := by
    have h1 := mem_closedBall_iff_norm.mp hz
    have h2 := norm_le_insert' z z0
    have h3 : r ≤ |r| := le_abs_self r
    linarith
  have hb : ∀ u ∈ Ioi (0 : ℝ), ‖(peso t u : ℂ) * Complex.cos (z * u) - (peso (τ n) u : ℂ) * Complex.cos (z * u)‖
      ≤ |peso (τ n) u - peso t u| * Real.exp (R * u) := by
    intro u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (norm_cos_le _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    exact mul_le_mul_of_nonneg_right hzR hu0
  have hint : IntegrableOn (fun u => |peso (τ n) u - peso t u| * Real.exp (R * u)) (Ioi 0) := by
    refine Integrable.mono' ((ATK.XiPhi.integrableOn_exp_neg_mul
      (160 * Real.exp (|τ n| + R + (|τ n| + R) ^ 2))).add (ATK.XiPhi.integrableOn_exp_neg_mul
      (160 * Real.exp (|t| + R + (|t| + R) ^ 2)))) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ((((continuousOn_peso (τ n)).sub (continuousOn_peso t)).abs).mono Ioi_subset_Ici_self).mul
        (by fun_prop : Continuous fun u : ℝ => Real.exp (R * u)).continuousOn
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 ≤ u := le_of_lt hu
      have h1 := peso_cota (t := τ n) (y := R) hR hu0
      have h2 := peso_cota (t := t) (y := R) hR hu0
      have h4 := abs_sub (peso (τ n) u) (peso t u)
      have he := Real.exp_pos (R * u)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
      calc |peso (τ n) u - peso t u| * Real.exp (R * u)
          ≤ (|peso (τ n) u| + |peso t u|) * Real.exp (R * u) := by gcongr
        _ = |peso (τ n) u| * Real.exp (R * u) + |peso t u| * Real.exp (R * u) := by ring
        _ ≤ _ := add_le_add h1 h2
  rw [dist_eq_norm, H, H, ← integral_sub (integrable_G t z) (integrable_G (τ n) z)]
  calc ‖∫ u in Ioi (0 : ℝ), ((peso t u : ℂ) * Complex.cos (z * u) -
        (peso (τ n) u : ℂ) * Complex.cos (z * u))‖
      ≤ ∫ u in Ioi (0 : ℝ), ‖(peso t u : ℂ) * Complex.cos (z * u) -
        (peso (τ n) u : ℂ) * Complex.cos (z * u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), |peso (τ n) u - peso t u| * Real.exp (R * u) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
          (ae_restrict_of_forall_mem measurableSet_Ioi hb)
    _ < ε := hn

/-- **`S` é fechado** (Hurwitz). -/
theorem isClosed_S : IsClosed S := by
  refine isClosed_of_closure_subset fun t ht => ?_
  obtain ⟨τ, hτS, hτ⟩ := mem_closure_iff_seq_limit.mp ht
  intro z0 hz0
  by_contra him
  have han : AnalyticOnNhd ℂ (H t) univ := fun z _ => (H_differentiable t).analyticAt z
  rcases (han z0 (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z0) h
      (mem_univ 0)
    exact H_ne_zero_at_zero t this
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hne⟩ := h
    have him' : 0 < |z0.im| := abs_pos.mpr him
    set r := min (ε / 2) (|z0.im| / 2) with hr_def
    have hr : 0 < r := lt_min (by positivity) (by positivity)
    have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hrim : r ≤ |z0.im| / 2 := min_le_right _ _
    refine hurwitz_local hr (F := fun n => H (τ n)) (fun n => (H_differentiable _).differentiableOn)
      (H_differentiable t).continuous.continuousOn (tendstoUniformlyOn_H hτ z0 r)
      (fun n z hz hz0' => ?_) (fun z hz => hne ?_ ?_) hz0
    · have hzim := hτS n z hz0'
      have h1 := Complex.abs_im_le_norm (z - z0)
      have h2 := mem_closedBall_iff_norm.mp hz
      rw [Complex.sub_im, hzim, zero_sub, abs_neg] at h1
      linarith
    · rw [dist_eq_norm, mem_sphere_iff_norm.mp hz]
      exact hrε
    · intro h'
      rw [mem_singleton_iff] at h'
      rw [h', mem_sphere_iff_norm, sub_self, norm_zero] at hz
      exact hr.ne' hz.symm

/-- **HR ⟺ `Λ ≤ 0`**, condicional só a de Bruijn (`S ≠ ∅`, fechamento para cima) e Newman (limitação). -/
theorem rh_iff_Lambda_le_zero' (hne : S.Nonempty) (hb : BddBelow S)
    (hup : ∀ s ∈ S, ∀ t, s ≤ t → t ∈ S) : RiemannHypothesis ↔ Lambda ≤ 0 :=
  rh_iff_Lambda_le_zero hne hb isClosed_S hup

end ATK.DBNF

#print axioms ATK.DBNF.peso_pos
#print axioms ATK.DBNF.aesm_peso
#print axioms ATK.DBNF.integrableOn_peso
#print axioms ATK.DBNF.H_ne_zero_at_zero
#print axioms ATK.DBNF.peso_abs_le
#print axioms ATK.DBNF.tendsto_int_dif
#print axioms ATK.DBNF.tendstoUniformlyOn_H
#print axioms ATK.DBNF.isClosed_S
#print axioms ATK.DBNF.rh_iff_Lambda_le_zero'
