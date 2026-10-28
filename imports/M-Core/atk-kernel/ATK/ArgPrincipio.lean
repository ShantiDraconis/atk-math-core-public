import Mathlib

/-!
# ATK — o princípio do argumento em círculos (o que falta na Mathlib)

A Mathlib tem a integral de Cauchy em círculos, `∮ (z − w)⁻¹ = 2πi`, e a extração de zeros de funções
meromorfas (`MeromorphicOn.extract_zeros_poles`), mas **não** o princípio do argumento. Este arquivo o
prova para funções analíticas numa vizinhança de um disco fechado:

  `∮_{|z−c|=R} f′(z)/f(z) dz = 2πi · Σ_{zeros u em B(c,R)} ord_u f`,

se `f` não se anula no círculo (`principio_argumento`). Antes, as peças: o disco engrossa (`engrossa`), a ordem
é finita (`ordem_finita`), a igualdade codiscreta vira igualdade numa vizinhança dos pontos interiores
(`codiscreta_vizinhanca`), e `∮ (z − u)⁻¹ = 0` fora do disco (`integral_inv_fora`), `∮ g′/g = 0` sem zeros
(`integral_logDeriv_sem_zeros`).
-/

open Complex Metric Set Filter Topology
open scoped Real

namespace ATK.ArgPrincipio

/-- O conjunto onde `f` é analítica contém um disco fechado maior. -/
theorem engrossa {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    ∃ R' > R, AnalyticOnNhd ℂ f (closedBall c R') := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c R).exists_cthickening_subset_open
    (isOpen_analyticAt ℂ f) hf
  refine ⟨R + δ, by linarith, fun z hz => hsub ?_⟩
  rw [cthickening_closedBall hδ.le hR, add_comm]; exact hz

/-- Num conexo onde `f` não é identicamente nula, a ordem é finita em todo ponto. -/
theorem ordem_finita {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : f z₀ ≠ 0) {u : ℂ} (hu : u ∈ U) : analyticOrderAt f u ≠ ⊤ := by
  intro htop
  exact h0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hu (analyticOrderAt_eq_top.mp htop) hz₀)

/-- Igualdade codiscreta em `U` + continuidade num ponto interior ⟹ igualdade numa vizinhança. -/
theorem codiscreta_vizinhanca {F G : ℂ → ℂ} {U : Set ℂ} (h : F =ᶠ[codiscreteWithin U] G) {z : ℂ}
    (hz : U ∈ 𝓝 z) (hF : ContinuousAt F z) (hG : ContinuousAt G z) : F =ᶠ[𝓝 z] G := by
  have hzU : z ∈ U := mem_of_mem_nhds hz
  have hd := (mem_codiscreteWithin.mp h) z hzU
  have hpunct : ∀ᶠ y in 𝓝[≠] z, F y = G y := by
    have h1 : ∀ᶠ y in 𝓝[≠] z, y ∉ U \ {y | F y = G y} := by
      rw [Filter.disjoint_principal_right] at hd
      exact hd
    have h2 : ∀ᶠ y in 𝓝[≠] z, y ∈ U := nhdsWithin_le_nhds hz
    filter_upwards [h1, h2] with y hy1 hy2
    by_contra hne
    exact hy1 ⟨hy2, hne⟩
  have hval : F z = G z := by
    have t1 : Tendsto F (𝓝[≠] z) (𝓝 (F z)) := hF.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto G (𝓝[≠] z) (𝓝 (G z)) := hG.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (t1.congr' hpunct) t2
  rw [eventually_nhdsWithin_iff] at hpunct
  filter_upwards [hpunct] with y hy
  by_cases e : y = z
  · rw [e]; exact hval
  · exact hy e

/-- `∮ (z − u)⁻¹ = 0` quando `u` está fora do disco fechado. -/
theorem integral_inv_fora {c u : ℂ} {R : ℝ} (hR : 0 ≤ R) (hu : u ∉ closedBall c R) :
    (∮ z in C(c, R), (z - u)⁻¹) = 0 := by
  have hne : ∀ z ∈ closedBall c R, z - u ≠ 0 := fun z hz e => hu (sub_eq_zero.mp e ▸ hz)
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty ?_ ?_
  · exact fun z hz => ((continuousAt_id.sub continuousAt_const).inv₀ (hne z hz)).continuousWithinAt
  · intro z hz
    exact ((differentiableAt_id.sub (differentiableAt_const u)).inv (hne z (ball_subset_closedBall hz.1)))

/-- **Sem zeros, `∮ g′/g = 0`**: `g` analítica numa vizinhança do disco fechado e sem zeros nele. -/
theorem integral_logDeriv_sem_zeros {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hg0 : ∀ z ∈ closedBall c R, g z ≠ 0) :
    (∮ z in C(c, R), logDeriv g z) = 0 := by
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty ?_ ?_
  · intro z hz
    exact ((hg z hz).deriv.continuousAt.div (hg z hz).continuousAt (hg0 z hz)).continuousWithinAt
  · intro z hz
    have hz' := ball_subset_closedBall hz.1
    exact (hg z hz').deriv.differentiableAt.div (hg z hz').differentiableAt (hg0 z hz')

/-- `ord_u f` como inteiro, para `f` analítica de ordem finita. -/
theorem divisor_eq_ordem {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {u : ℂ} (hu : u ∈ U)
    (htop : analyticOrderAt f u ≠ ⊤) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn]
  simp [analyticOrderNatAt, ← hn]

/-- Ordem natural zero ⟺ não é zero (ordem finita). -/
theorem ordemNat_zero_iff {f : ℂ → ℂ} {u : ℂ} (hf : AnalyticAt ℂ f u) (htop : analyticOrderAt f u ≠ ⊤) :
    analyticOrderNatAt f u = 0 ↔ f u ≠ 0 := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have e : analyticOrderNatAt f u = n := by simp [analyticOrderNatAt, ← hn]
  rw [e]
  have key := analyticOrderAt_eq_zero (f := f) (z₀ := u)
  rw [← hn] at key
  constructor
  · intro h0
    subst h0
    rcases key.mp (by simp) with h | h
    · exact absurd hf h
    · exact h
  · intro hne
    exact_mod_cast key.mpr (Or.inr hne)

/-- **Princípio do argumento** (círculos): `∮ f′/f = 2πi · Σ_{zeros u ∈ B(c,R)} ord_u f`. -/
theorem principio_argumento {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hs : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ u ∈ ball c R ∧ f u = 0) ∧
      (∮ z in C(c, R), logDeriv f z) = 2 * π * I * ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) := by
  classical
  obtain ⟨R', hR', hf'⟩ := engrossa hR.le hf
  set U := closedBall c R' with hUdef
  have hUc : IsPreconnected U := (convex_closedBall c R').isPreconnected
  -- um ponto do círculo
  have hz₀ : c + (R : ℂ) ∈ sphere c R := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hz₀U : c + (R : ℂ) ∈ U := sphere_subset_closedBall.trans (closedBall_subset_closedBall hR'.le) hz₀
  have htop : ∀ u ∈ U, analyticOrderAt f u ≠ ⊤ := fun u hu =>
    ordem_finita hf' hUc hz₀U (hs _ hz₀) hu
  have hmero : MeromorphicOn f U := hf'.meromorphicOn
  have htop' : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    intro ⟨u, hu⟩
    rw [(hf' u hu).meromorphicOrderAt_eq]
    intro h
    apply htop u hu
    simpa using h
  set d := MeromorphicOn.divisor f U with hd
  have hfin : d.support.Finite := d.finiteSupport (isCompact_closedBall c R')
  obtain ⟨g, hg, hg0, heq⟩ := hmero.extract_zeros_poles htop' hfin
  set T := hfin.toFinset with hT
  -- caracterização do suporte
  have hsupp : ∀ u, u ∈ T ↔ u ∈ U ∧ f u = 0 := by
    intro u
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support]
    by_cases huU : u ∈ U
    · rw [divisor_eq_ordem hf' huU (htop u huU)]
      have := ordemNat_zero_iff (hf' u huU) (htop u huU)
      constructor
      · intro h
        refine ⟨huU, ?_⟩
        by_contra hne
        exact h (by exact_mod_cast this.mpr hne)
      · rintro ⟨-, h0⟩ h
        exact (this.mp (by exact_mod_cast h)) h0
    · constructor
      · intro h; exact absurd (d.supportWithinDomain (Function.mem_support.mpr h)) huU
      · rintro ⟨h, -⟩; exact absurd h huU
  -- os zeros não estão no círculo
  have hTs : ∀ u ∈ T, ∀ z ∈ sphere c R, z ≠ u := by
    intro u hu z hz e
    exact hs z hz (e ▸ ((hsupp u).mp hu).2)
  -- forma explícita de `φ`
  set φ : ℂ → ℂ := fun z => ∏ u ∈ T, (z - u) ^ d u with hφ
  have hφeq : (∏ᶠ u, (· - u) ^ d u) = φ := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
    · funext z; simp [hφ, Finset.prod_apply]
    · intro u hu
      rw [hT, Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      apply hu
      simp [h0]
  rw [hφeq] at heq
  -- no círculo: `logDeriv f = Σ d u /(z − u) + logDeriv g`
  have hlog : ∀ z ∈ sphere c R, logDeriv f z = ∑ u ∈ T, (d u : ℂ) * (z - u)⁻¹ + logDeriv g z := by
    intro z hz
    have hzU : U ∈ 𝓝 z := by
      refine mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
      rw [mem_sphere] at hz; rw [mem_ball]; linarith
    have hzU' : z ∈ U := mem_of_mem_nhds hzU
    have hfac : ∀ u ∈ T, z - u ≠ 0 := fun u hu => sub_ne_zero.mpr (hTs u hu z hz)
    have hφd : ∀ u ∈ T, DifferentiableAt ℂ (fun x => (x - u) ^ d u) z := fun u hu =>
      (differentiableAt_id.sub (differentiableAt_const u)).zpow (Or.inl (hfac u hu))
    have hφz : φ z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun u hu => zpow_ne_zero _ (hfac u hu)
    have hφdz : DifferentiableAt ℂ φ z := by
      have := DifferentiableAt.finsetProd (u := T) (f := fun u x => (x - u) ^ d u) hφd
      convert this using 1
      funext x; simp [hφ, Finset.prod_apply]
    have hgz : g z ≠ 0 := hg0 ⟨z, hzU'⟩
    have hgd : DifferentiableAt ℂ g z := (hg z hzU').differentiableAt
    have heq' : f =ᶠ[codiscreteWithin U] φ * g := by simpa using heq
    have hev : f =ᶠ[𝓝 z] φ * g :=
      codiscreta_vizinhanca heq' hzU (hf' z hzU').continuousAt (hφdz.continuousAt.mul hgd.continuousAt)
    have hfz : f z = φ z * g z := hev.self_of_nhds
    have e1 : logDeriv f z = logDeriv (φ * g) z := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hfz]; rfl
    rw [e1, logDeriv_mul z hφz hgz hφdz hgd]
    congr 1
    have e2 : logDeriv φ z = ∑ u ∈ T, logDeriv (fun x => (x - u) ^ d u) z := by
      have := logDeriv_fun_prod (s := T) (f := fun u x => (x - u) ^ d u) (x := z)
        (fun u hu => zpow_ne_zero _ (hfac u hu)) hφd
      simpa [hφ] using this
    rw [e2]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [logDeriv_fun_zpow (f := fun x => x - u) (by fun_prop) (d u)]
    have : logDeriv (fun x => x - u) z = (z - u)⁻¹ := by
      rw [logDeriv_apply]
      have hd1 : deriv (fun x => x - u) z = 1 := by
        simp
      rw [hd1, one_div]
    rw [this]
  -- integrais
  have hcont_inv : ∀ u ∈ T, ContinuousOn (fun z => (d u : ℂ) * (z - u)⁻¹) (sphere c R) :=
    fun u hu z hz => (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr (hTs u hu z hz)))).continuousWithinAt
  have hint_inv : ∀ u ∈ T, CircleIntegrable (fun z => (d u : ℂ) * (z - u)⁻¹) c R :=
    fun u hu => (hcont_inv u hu).circleIntegrable hR.le
  have hRsub : closedBall c R ⊆ U := closedBall_subset_closedBall hR'.le
  have hint_g : CircleIntegrable (logDeriv g) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hz' : z ∈ U := hRsub (sphere_subset_closedBall hz)
    exact ((hg z hz').deriv.continuousAt.div (hg z hz').continuousAt (hg0 ⟨z, hz'⟩)).continuousWithinAt
  have hsum_int : CircleIntegrable (fun z => ∑ u ∈ T, (d u : ℂ) * (z - u)⁻¹) c R :=
    (continuousOn_finsetSum T hcont_inv).circleIntegrable hR.le
  have hI : (∮ z in C(c, R), logDeriv f z) =
      ∑ u ∈ T, (d u : ℂ) * (∮ z in C(c, R), (z - u)⁻¹) + ∮ z in C(c, R), logDeriv g z := by
    rw [circleIntegral.integral_congr hR.le hlog, circleIntegral.integral_add hsum_int hint_g,
      circleIntegral.integral_fun_sum hint_inv]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    exact circleIntegral.integral_const_mul _ _ _ _
  have hg_int : (∮ z in C(c, R), logDeriv g z) = 0 :=
    integral_logDeriv_sem_zeros hR.le (fun z hz => hg z (hRsub hz)) (fun z hz => hg0 ⟨z, hRsub hz⟩)
  -- a soma: só os zeros dentro de `B(c,R)` contam
  refine ⟨T.filter (· ∈ ball c R), fun u => ?_, ?_⟩
  · rw [Finset.mem_filter, hsupp]
    constructor
    · rintro ⟨⟨_, h0⟩, hb⟩; exact ⟨hb, h0⟩
    · rintro ⟨hb, h0⟩; exact ⟨⟨hRsub (ball_subset_closedBall hb), h0⟩, hb⟩
  · rw [hI, hg_int, add_zero, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have huU : u ∈ U := ((hsupp u).mp hu).1
    rw [divisor_eq_ordem hf' huU (htop u huU)]
    push_cast
    by_cases hb : u ∈ ball c R
    · simp only [hb, ↓reduceIte]
      rw [circleIntegral.integral_sub_inv_of_mem_ball hb]; ring
    · simp only [hb, ↓reduceIte]
      have hnc : u ∉ closedBall c R := by
        intro hc
        rcases (mem_closedBall.mp hc).lt_or_eq with h | h
        · exact hb (mem_ball.mpr h)
        · exact hTs u hu u (mem_sphere.mpr h) rfl
      rw [integral_inv_fora hR.le hnc, mul_zero, mul_zero]

/-! ## Rouché -/

/-- **Rouché**: se `|g − f| < |f|` no círculo, `f` e `g` têm o mesmo número de zeros (com multiplicidade)
em `B(c,R)`. Prova simétrica: `g/f` cai no semiplano `Re > 0` no círculo, onde `log` é analítico, e
`∮ (g′/g − f′/f) = ∮ (log(g/f))′ = 0`. -/
theorem rouche {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hlt : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    ∃ Sf Sg : Finset ℂ, (∀ u, u ∈ Sf ↔ u ∈ ball c R ∧ f u = 0) ∧
      (∀ u, u ∈ Sg ↔ u ∈ ball c R ∧ g u = 0) ∧
      ∑ u ∈ Sf, analyticOrderNatAt f u = ∑ u ∈ Sg, analyticOrderNatAt g u := by
  have hf0 : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz h => by
    have := hlt z hz; rw [h, norm_zero] at this; exact (norm_nonneg _).not_gt this
  have hg0 : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz h => by
    have := hlt z hz; rw [h, zero_sub, norm_neg] at this; exact lt_irrefl _ this
  obtain ⟨Sf, hSf, hIf⟩ := principio_argumento hR hf hf0
  obtain ⟨Sg, hSg, hIg⟩ := principio_argumento hR hg hg0
  refine ⟨Sf, Sg, hSf, hSg, ?_⟩
  have hsph : ∀ z ∈ sphere c R, z ∈ closedBall c R := fun z hz => sphere_subset_closedBall hz
  have hderiv : ∀ z ∈ sphere c |R|, HasDerivWithinAt (fun w => log (g w / f w))
      (logDeriv g z - logDeriv f z) (sphere c |R|) z := by
    intro z hz
    rw [abs_of_pos hR] at hz
    have hfz := hf0 z hz
    have hgz := hg0 z hz
    have hfa := hf z (hsph z hz)
    have hga := hg z (hsph z hz)
    have hq : HasDerivAt (fun w => g w / f w)
        ((deriv g z * f z - g z * deriv f z) / f z ^ 2) z :=
      hga.differentiableAt.hasDerivAt.div hfa.differentiableAt.hasDerivAt hfz
    have hslit : g z / f z ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      have e : g z / f z = 1 + (g z - f z) / f z := by field_simp; ring
      have hn : ‖(g z - f z) / f z‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hfz)]; exact hlt z hz
      have := Complex.abs_re_le_norm ((g z - f z) / f z)
      rw [e, add_re, one_re]
      have := abs_le.mp (this.trans hn.le)
      rcases (abs_le.mp ((Complex.abs_re_le_norm ((g z - f z) / f z)))) with ⟨h1, -⟩
      linarith
    have hlog := hq.clog hslit
    have e : (deriv g z * f z - g z * deriv f z) / f z ^ 2 / (g z / f z) =
        logDeriv g z - logDeriv f z := by
      rw [logDeriv_apply, logDeriv_apply]; field_simp
    rw [e] at hlog
    exact hlog.hasDerivWithinAt
  have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt' hderiv
  have hcont : ∀ {F : ℂ → ℂ}, AnalyticOnNhd ℂ F (closedBall c R) → (∀ z ∈ sphere c R, F z ≠ 0) →
      CircleIntegrable (logDeriv F) c R := by
    intro F hF hF0
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have ha := hF z (hsph z hz)
    exact (ha.deriv.continuousAt.div ha.continuousAt (hF0 z hz)).continuousWithinAt
  rw [circleIntegral.integral_sub (hcont hg hg0) (hcont hf hf0), sub_eq_zero, hIf, hIg] at hzero
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have := mul_left_cancel₀ h2 hzero
  exact_mod_cast this.symm

/-! ## Taylor de ordem 2 e a forma afiada de `E1` -/

/-- **Taylor de ordem 2**: `|f(z) − f(c) − f′(c)(z − c)| ≤ (M/2)|z − c|²` se `|f″| ≤ M` no disco. -/
theorem taylor2 {f : ℂ → ℂ} {c z : ℂ} {r M : ℝ}
    (hd : ∀ w ∈ closedBall c r, DifferentiableAt ℂ f w)
    (hd2 : ∀ w ∈ closedBall c r, DifferentiableAt ℂ (deriv f) w)
    (hM : ∀ w ∈ closedBall c r, ‖deriv (deriv f) w‖ ≤ M) (hz : z ∈ closedBall c r) :
    ‖f z - f c - deriv f c * (z - c)‖ ≤ M / 2 * ‖z - c‖ ^ 2 := by
  set w := z - c with hw
  have hr : 0 ≤ r := le_trans dist_nonneg hz
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, c + (t : ℂ) * w ∈ closedBall c r := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [mem_closedBall, dist_eq_norm] at hz
    nlinarith [ht.2, norm_nonneg w]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM c hc)
  set φ : ℝ → ℂ := fun t => f (c + (t : ℂ) * w) - f c - (t : ℂ) * (deriv f c * w) with hφ
  have hφd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ ((deriv f (c + (t : ℂ) * w) - deriv f c) * w) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℂ => c + s * w) w (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const w).const_add c
    have h2 : HasDerivAt (fun s : ℂ => f (c + s * w)) (deriv f (c + (t : ℂ) * w) * w) (t : ℂ) :=
      (hd _ (hseg t ht)).hasDerivAt.comp (t : ℂ) h1
    have h3 : HasDerivAt (fun s : ℝ => f (c + (s : ℂ) * w)) (deriv f (c + (t : ℂ) * w) * w) t :=
      h2.comp_ofReal
    have h4 : HasDerivAt (fun s : ℝ => (s : ℂ) * (deriv f c * w)) (deriv f c * w) t := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const (deriv f c * w) |>.comp_ofReal
    have := (h3.sub_const (f c)).sub h4
    convert this using 1
    ring
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(deriv f (c + (t : ℂ) * w) - deriv f c) * w‖ ≤ M * ‖w‖ ^ 2 * t := by
    intro t ht
    have hmv := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le hd2 hM hc (hseg t ht)
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] at hmv
    rw [norm_mul]
    calc ‖deriv f (c + (t : ℂ) * w) - deriv f c‖ * ‖w‖ ≤ M * (t * ‖w‖) * ‖w‖ :=
          mul_le_mul_of_nonneg_right hmv (norm_nonneg _)
      _ = M * ‖w‖ ^ 2 * t := by ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := φ)
    (f' := fun t => (deriv f (c + (t : ℂ) * w) - deriv f c) * w)
    (B := fun t => M / 2 * ‖w‖ ^ 2 * t ^ 2) (B' := fun t => M * ‖w‖ ^ 2 * t)
    (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hφ])
    (fun t => by
      have := (hasDerivAt_pow 2 t).const_mul (M / 2 * ‖w‖ ^ 2)
      convert this using 1
      simp; ring)
    (fun t ht => hbound t (Ico_subset_Icc_self ht))
  have := key (right_mem_Icc.mpr zero_le_one)
  simp only [hφ, Complex.ofReal_one, one_mul, one_pow, mul_one] at this
  rw [hw] at this ⊢
  simpa [add_sub_cancel] using this

/-- Ordem 1 ⟹ derivada não nula. -/
theorem deriv_ne_zero_of_ordem_um {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (h1 : analyticOrderAt f ρ = 1) : deriv f ρ ≠ 0 := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp (show analyticOrderAt f ρ = (1 : ℕ) by
    simpa using h1)
  have hfg' : f =ᶠ[𝓝 ρ] fun z => (z - ρ) * g z := by
    filter_upwards [hfg] with z hz; simpa using hz
  rw [hfg'.deriv_eq]
  have hd : HasDerivAt (fun z => (z - ρ) * g z) (1 * g ρ + (ρ - ρ) * deriv g ρ) ρ :=
    ((hasDerivAt_id ρ).sub_const ρ).mul hg.differentiableAt.hasDerivAt
  rw [hd.deriv]; simpa using hg0

/-- **`E1` afiado** (Rouché): se `|f″| ≤ M` no disco e `|f(c)| + M r²/2 < r|f′(c)|`, então `f` tem
**exatamente um** zero em `B(c, r)`, e ele é simples. -/
theorem E1_afiado {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hM : ∀ w ∈ closedBall c r, ‖deriv (deriv f) w‖ ≤ M)
    (h : ‖f c‖ + M * r ^ 2 / 2 < r * ‖deriv f c‖) :
    ∃ ρ ∈ ball c r, f ρ = 0 ∧ deriv f ρ ≠ 0 ∧ ∀ w ∈ ball c r, f w = 0 → w = ρ := by
  classical
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM c (mem_closedBall_self hr.le))
  have hdc : deriv f c ≠ 0 := by
    intro h0; rw [h0, norm_zero, mul_zero] at h; nlinarith [norm_nonneg (f c)]
  set L : ℂ → ℂ := fun z => deriv f c * (z - c) with hL
  have hLa : AnalyticOnNhd ℂ L (closedBall c r) := fun z _ => by
    simp only [hL]; fun_prop
  have hlt : ∀ z ∈ sphere c r, ‖f z - L z‖ < ‖L z‖ := by
    intro z hz
    have hzr : ‖z - c‖ = r := by rwa [mem_sphere, dist_eq_norm] at hz
    have ht := taylor2 (fun w hw => (hf w hw).differentiableAt) (fun w hw => (hf w hw).deriv.differentiableAt)
      hM (sphere_subset_closedBall hz)
    rw [hzr] at ht
    have hLz : ‖L z‖ = r * ‖deriv f c‖ := by simp only [hL]; rw [norm_mul, hzr, mul_comm]
    rw [hLz]
    calc ‖f z - L z‖ = ‖f c + (f z - f c - deriv f c * (z - c))‖ := by simp only [hL]; ring_nf
      _ ≤ ‖f c‖ + ‖f z - f c - deriv f c * (z - c)‖ := norm_add_le _ _
      _ ≤ ‖f c‖ + M / 2 * r ^ 2 := by linarith
      _ < r * ‖deriv f c‖ := by linarith
  obtain ⟨SL, Sf, hSL, hSf, hsum⟩ := rouche hr hLa hf hlt
  -- os zeros de `L`: só `c`, de ordem 1
  have hSLc : SL = {c} := by
    ext u
    rw [hSL, Finset.mem_singleton]
    simp only [hL, mul_eq_zero, hdc, false_or, sub_eq_zero]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨mem_ball_self hr, rfl⟩
  have hordL : analyticOrderNatAt L c = 1 := by
    have : analyticOrderAt L c = (1 : ℕ) := by
      rw [(hLa c (mem_closedBall_self hr.le)).analyticOrderAt_eq_natCast]
      exact ⟨fun _ => deriv f c, analyticAt_const, hdc, Eventually.of_forall fun z => by
        simp [hL, mul_comm]⟩
    simp [analyticOrderNatAt, this]
  rw [hSLc, Finset.sum_singleton, hordL] at hsum
  -- cada zero de `f` tem ordem ≥ 1 e finita
  have hz0 : c + (r : ℂ) ∈ sphere c r := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hf0 : f (c + (r : ℂ)) ≠ 0 := by
    intro h0
    have := hlt _ hz0
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  have htop : ∀ u ∈ closedBall c r, analyticOrderAt f u ≠ ⊤ := fun u hu =>
    ordem_finita hf (convex_closedBall c r).isPreconnected (sphere_subset_closedBall hz0) hf0 hu
  have hpos : ∀ u ∈ Sf, 1 ≤ analyticOrderNatAt f u := by
    intro u hu
    obtain ⟨hb, h0⟩ := (hSf u).mp hu
    have hu' := ball_subset_closedBall hb
    by_contra hlt1
    have : analyticOrderNatAt f u = 0 := by omega
    exact (ordemNat_zero_iff (hf u hu') (htop u hu')).mp this h0
  -- soma 1 com parcelas ≥ 1: um único zero, de ordem 1
  have hcard : Sf.card ≤ 1 := by
    have := Finset.card_nsmul_le_sum Sf (fun u => analyticOrderNatAt f u) 1 hpos
    simp at this; omega
  have hne : Sf.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro he; rw [he, Finset.sum_empty] at hsum; omega
  obtain ⟨ρ, hρ⟩ := Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hne))
  rw [hρ, Finset.sum_singleton] at hsum
  have hρS : ρ ∈ Sf := by rw [hρ]; exact Finset.mem_singleton_self ρ
  obtain ⟨hρb, hρ0⟩ := (hSf ρ).mp hρS
  have hρ' := ball_subset_closedBall hρb
  refine ⟨ρ, hρb, hρ0, ?_, fun w hw hw0 => ?_⟩
  · apply deriv_ne_zero_of_ordem_um (hf ρ hρ')
    rw [← Nat.cast_analyticOrderNatAt (htop ρ hρ'), ← hsum]; rfl
  · have : w ∈ Sf := (hSf w).mpr ⟨hw, hw0⟩
    rw [hρ, Finset.mem_singleton] at this
    exact this

end ATK.ArgPrincipio

#print axioms ATK.ArgPrincipio.engrossa
#print axioms ATK.ArgPrincipio.ordem_finita
#print axioms ATK.ArgPrincipio.codiscreta_vizinhanca
#print axioms ATK.ArgPrincipio.integral_inv_fora
#print axioms ATK.ArgPrincipio.integral_logDeriv_sem_zeros
#print axioms ATK.ArgPrincipio.divisor_eq_ordem
#print axioms ATK.ArgPrincipio.ordemNat_zero_iff
#print axioms ATK.ArgPrincipio.principio_argumento
#print axioms ATK.ArgPrincipio.rouche
#print axioms ATK.ArgPrincipio.taylor2
#print axioms ATK.ArgPrincipio.deriv_ne_zero_of_ordem_um
#print axioms ATK.ArgPrincipio.E1_afiado
