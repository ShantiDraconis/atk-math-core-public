import ATK.JensenPolya

/-!
# ATK — Teorema de Hurwitz e o critério de Pólya–Jensen completo: **HR ⟺ todo `J^{d,n}` de `Ξ` hiperbólico**

* `hurwitz_local` (**Hurwitz**): se `F_n → g` uniformemente num disco fechado, cada `F_n` é holomorfa e sem zeros no
  disco e `g ≠ 0` na circunferência, então `g ≠ 0` no centro. Prova pelo módulo máximo aplicado a `1/F_n` (sem Rouché).
* `zeros_reais_de_jensen`: se `B(w) = Σaₖwᵏ` é inteira, `a₀ ≠ 0`, e todo polinômio de Jensen `J^{d,0}` de
  `γ(k) = k!aₖ` tem só raízes reais, então **todo zero de `B` é real**. Prova: `J^{d,0}(w/d) = Σ_j (d^{(j)}/dʲ)aⱼwʲ → B(w)`
  uniformemente em discos (Tannery), cada `J^{d,0}(·/d)` não se anula fora do eixo real (cota `|p(z)| ≥ |a||Im z|ⁿ`),
  e Hurwitz + princípio de identidade.
* **`rh_de_jensen`**: `∀ d, J^{d,0}(γ_Ξ)` hiperbólico ⇒ HR (`B(−z²) = ξ(1/2 + iz)` e `ξ > 0` no eixo real).
* **`rh_iff_jensen`, `rh_iff_jensen0`: HR ⟺ todo `J^{d,n}` de `Ξ` tem só raízes reais ⟺ todo `J^{d,0}` tem**
  (Pólya 1927 — as duas direções no kernel, com `ATK.JensenPolya.rh_jensen`).

Isto é uma **equivalência**: a hiperbolicidade de todos os `J^{d,n}` continua `OPEN_MATH` (é HR).
-/

open Complex Filter Topology Metric Set Polynomial
open scoped Nat

namespace ATK.Hurwitz

open ATK.Edrei ATK.InteiraAn ATK.Laguerre ATK.PolyaCalor ATK.JensenPolya ATK.XiTP

/-! ## 1. Hurwitz -/

/-- **Teorema de Hurwitz (forma local).** -/
theorem hurwitz_local {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {z0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (closedBall z0 r))
    (hg : ContinuousOn g (sphere z0 r))
    (hconv : TendstoUniformlyOn F g atTop (closedBall z0 r))
    (hnz : ∀ n, ∀ z ∈ closedBall z0 r, F n z ≠ 0)
    (hsph : ∀ z ∈ sphere z0 r, g z ≠ 0) : g z0 ≠ 0 := by
  intro h0
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere z0 r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) (continuous_norm.comp_continuousOn hg)
  have hδ : 0 < ‖g z1‖ := norm_pos_iff.mpr (hsph z1 hz1)
  have hδle : ∀ z ∈ sphere z0 r, ‖g z1‖ ≤ ‖g z‖ := fun z hz => hmin hz
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp hconv) (‖g z1‖ / 2) (by positivity)).exists
  have hsF : ∀ z ∈ sphere z0 r, ‖g z1‖ / 2 ≤ ‖F n z‖ := by
    intro z hz
    have h1 := hn z (sphere_subset_closedBall hz)
    have h2 := hδle z hz
    rw [dist_eq_norm] at h1
    have h3 := norm_sub_norm_le (g z) (F n z)
    linarith
  have hz0F : ‖F n z0‖ < ‖g z1‖ / 2 := by
    have h := hn z0 (mem_closedBall_self hr.le)
    rwa [dist_eq_norm, h0, zero_sub, norm_neg] at h
  have hd : DifferentiableOn ℂ (fun z => (F n z)⁻¹) (closedBall z0 r) := (hF n).inv (hnz n)
  have hdc : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball z0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z0 hr.ne']
    exact hd
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
    (C := (‖g z1‖ / 2)⁻¹) (fun z hz => by
      rw [frontier_ball z0 hr.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ (by positivity) (hsF z hz)) (subset_closure (mem_ball_self hr))
  rw [norm_inv] at hmax
  have hpos : 0 < ‖F n z0‖ := norm_pos_iff.mpr (hnz n z0 (mem_closedBall_self hr.le))
  rw [inv_le_inv₀ hpos (by positivity)] at hmax
  linarith

/-! ## 2. Os polinômios de Jensen reescalados `J^{d,0}(w/d) → B(w)` -/

/-- `φ_d(j) = d^{(j)}/dʲ`. -/
noncomputable def phiJ (d j : ℕ) : ℝ := (d.descFactorial j : ℝ) / (d : ℝ) ^ j

theorem phiJ_nonneg (d j : ℕ) : 0 ≤ phiJ d j := by unfold phiJ; positivity

theorem phiJ_le_one (d j : ℕ) : phiJ d j ≤ 1 := by
  unfold phiJ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · cases j with
    | zero => simp
    | succ j => simp [Nat.descFactorial_eq_zero_iff_lt]
  · rw [div_le_one (by positivity)]
    exact_mod_cast Nat.descFactorial_le_pow d j

theorem tendsto_phiJ (j : ℕ) : Tendsto (fun d => phiJ d j) atTop (𝓝 1) := by
  have h := (tendsto_choose_div_pow j).const_mul (j ! : ℝ)
  rw [show (j ! : ℝ) * (1 / j !) = 1 by field_simp] at h
  refine h.congr fun d => ?_
  unfold phiJ
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- `F_d(w) = Σⱼ φ_d(j)aⱼwʲ`. -/
noncomputable def Fj (a : ℕ → ℝ) (d : ℕ) (w : ℂ) : ℂ := ∑' j, ((phiJ d j * a j : ℝ) : ℂ) * w ^ j

theorem Fj_eq (a : ℕ → ℝ) (d : ℕ) (w : ℂ) :
    Fj a d w = ((jensen (fun k => (k ! : ℝ) * a k) d 0).map (algebraMap ℝ ℂ)).eval (w / d) := by
  unfold Fj
  rw [tsum_eq_sum (s := Finset.range (d + 1)) (fun j hj => by
    simp only [Finset.mem_range, not_lt] at hj
    simp [phiJ, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : d < j)])]
  unfold jensen
  rw [eval_map, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval₂_mul, eval₂_C, eval₂_X_pow, zero_add, div_pow]
  unfold phiJ
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp only [Complex.coe_algebraMap]
  push_cast
  ring

theorem tendstoUniformlyOn_Fj {a : ℕ → ℝ} (ha : Inteira a) (z0 : ℂ) (r : ℝ) :
    TendstoUniformlyOn (fun d w => Fj a d w) (ev a) atTop (closedBall z0 r) := by
  set R := ‖z0‖ + |r| with hRdef
  have hR : 0 ≤ R := by positivity
  have hsum := ha R hR
  have hE : Tendsto (fun d => ∑' j, (1 - phiJ d j) * (|a j| * R ^ j)) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (f := fun d j => (1 - phiJ d j) * (|a j| * R ^ j))
      (g := fun _ => 0) (bound := fun j => |a j| * R ^ j) hsum (fun j => by
        have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_phiJ j)).mul_const (|a j| * R ^ j)
        simpa using this) (Eventually.of_forall fun d j => by
        have h1 := phiJ_nonneg d j
        have h2 := phiJ_le_one d j
        have h3 : 0 ≤ |a j| * R ^ j := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) h3)]
        nlinarith)
    simpa using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hE.eventually (gt_mem_nhds hε)] with d hd w hw
  have hwR : ‖w‖ ≤ R := by
    have h1 := mem_closedBall_iff_norm.mp hw
    have h2 := norm_le_insert' w z0
    have h3 : r ≤ |r| := le_abs_self r
    linarith
  have hterm : ∀ j, ‖(a j : ℂ) * w ^ j - ((phiJ d j * a j : ℝ) : ℂ) * w ^ j‖ ≤
      (1 - phiJ d j) * (|a j| * R ^ j) := by
    intro j
    have e : (a j : ℂ) * w ^ j - ((phiJ d j * a j : ℝ) : ℂ) * w ^ j =
        (((1 - phiJ d j) * a j : ℝ) : ℂ) * w ^ j := by push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_pow,
      abs_of_nonneg (by linarith [phiJ_le_one d j] : (0 : ℝ) ≤ 1 - phiJ d j)]
    have := pow_le_pow_left₀ (norm_nonneg w) hwR j
    have h1 : 0 ≤ 1 - phiJ d j := by linarith [phiJ_le_one d j]
    have h2 := abs_nonneg (a j)
    calc (1 - phiJ d j) * |a j| * ‖w‖ ^ j ≤ (1 - phiJ d j) * |a j| * R ^ j := by gcongr
      _ = _ := by ring
  have hbs : Summable fun j => (1 - phiJ d j) * (|a j| * R ^ j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (by linarith [phiJ_le_one d j]) (by positivity))
      (fun j => by
        have h1 := phiJ_nonneg d j
        have h3 : 0 ≤ |a j| * R ^ j := by positivity
        nlinarith) hsum
  have hs1 : Summable fun j => (a j : ℂ) * w ^ j := (summable_norm_ev ha w).of_norm
  have hs2 : Summable fun j => ((phiJ d j * a j : ℝ) : ℂ) * w ^ j := by
    refine Summable.of_norm_bounded hsum fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_pow,
      abs_of_nonneg (phiJ_nonneg d j)]
    have := pow_le_pow_left₀ (norm_nonneg w) hwR j
    have h1 := phiJ_le_one d j
    have h0 := phiJ_nonneg d j
    calc phiJ d j * |a j| * ‖w‖ ^ j ≤ 1 * |a j| * R ^ j := by gcongr
      _ = _ := by ring
  rw [dist_eq_norm, ev, Fj, ← hs1.tsum_sub hs2]
  calc ‖∑' j, ((a j : ℂ) * w ^ j - ((phiJ d j * a j : ℝ) : ℂ) * w ^ j)‖
      ≤ ∑' j, ‖(a j : ℂ) * w ^ j - ((phiJ d j * a j : ℝ) : ℂ) * w ^ j‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hbs)
    _ ≤ ∑' j, (1 - phiJ d j) * (|a j| * R ^ j) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hbs) hbs
    _ < ε := hd

theorem Fj_ne_zero {a : ℕ → ℝ} (ha0 : a 0 ≠ 0) {d : ℕ}
    (hJ : RealRooted (jensen (fun k => (k ! : ℝ) * a k) d 0)) {w : ℂ} (hw : w.im ≠ 0) : Fj a d w ≠ 0 := by
  rw [Fj_eq]
  intro h
  set J := jensen (fun k => (k ! : ℝ) * a k) d 0 with hJdef
  have hJne : J ≠ 0 := by
    intro h0
    have := congrArg (fun p : ℝ[X] => p.coeff 0) h0
    simp only [hJdef, coeff_jensen, Nat.zero_le, if_true, Nat.choose_zero_right, Nat.cast_one, one_mul,
      add_zero, Nat.factorial_zero, coeff_zero] at this
    exact ha0 this
  have hlc : 0 < |J.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr hJne)
  have hb := norm_eval_ge hJ (w / d)
  rw [h, norm_zero] at hb
  have hp : |(w / (d : ℂ)).im| ^ J.natDegree = 0 := by
    have h1 := pow_nonneg (abs_nonneg (w / (d : ℂ)).im) J.natDegree
    nlinarith
  rcases Nat.eq_zero_or_pos J.natDegree with h0 | h0
  · rw [h0, pow_zero] at hp
    exact one_ne_zero hp
  · have h2 := pow_eq_zero_iff (n := J.natDegree) (by omega) |>.mp hp
    rw [abs_eq_zero] at h2
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have : J.natDegree = 0 := by
        rw [hJdef]
        refine natDegree_eq_zero_iff_degree_le_zero.mpr ?_
        rw [degree_le_iff_coeff_zero]
        intro m hm
        rw [coeff_jensen, if_neg]
        intro hm0
        have : (m : WithBot ℕ) ≤ 0 := by exact_mod_cast hm0
        exact absurd hm (not_lt.mpr this)
      omega
    · have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      rw [Complex.div_natCast_im] at h2
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · exact hw h2
      · exact hd'.ne' h2

/-! ## 3. A volta de Pólya–Jensen -/

/-- **Se todo `J^{d,0}` (de `γ(k) = k!aₖ`) tem só raízes reais, todo zero de `B = Σaₖwᵏ` é real.** -/
theorem zeros_reais_de_jensen {a : ℕ → ℝ} (ha : Inteira a) (ha0 : a 0 ≠ 0)
    (hJ : ∀ d, RealRooted (jensen (fun k => (k ! : ℝ) * a k) d 0)) :
    ∀ w : ℂ, ev a w = 0 → w.im = 0 := by
  intro w0 hw0
  by_contra him
  have han := ev_analyticOnNhd ha
  rcases (han w0 (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ w0) h
      (mem_univ 0)
    rw [ev_zero] at this
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact ha0 this
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hne⟩ := h
    have him' : 0 < |w0.im| := abs_pos.mpr him
    set r := min (ε / 2) (|w0.im| / 2) with hr_def
    have hr : 0 < r := lt_min (by positivity) (by positivity)
    have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hrim : r ≤ |w0.im| / 2 := min_le_right _ _
    refine hurwitz_local hr (F := fun d w => Fj a d w) (fun d => ?_)
      (ev_differentiable ha).continuous.continuousOn (tendstoUniformlyOn_Fj ha w0 r)
      (fun d z hz => Fj_ne_zero ha0 (hJ d) ?_) (fun z hz => hne ?_ ?_) hw0
    · have e : (fun w => Fj a d w) =
          fun w : ℂ => ((jensen (fun k => (k ! : ℝ) * a k) d 0).map (algebraMap ℝ ℂ)).eval (w / (d : ℂ)) :=
        funext (Fj_eq a d)
      rw [e]
      have hdiv : Differentiable ℂ (fun w : ℂ => w / (d : ℂ)) := differentiable_id.div_const _
      exact ((Polynomial.differentiable _).comp hdiv).differentiableOn
    · intro hz0
      have h1 := Complex.abs_im_le_norm (z - w0)
      have h2 := mem_closedBall_iff_norm.mp hz
      rw [Complex.sub_im, hz0, zero_sub, abs_neg] at h1
      linarith
    · rw [dist_eq_norm, mem_sphere_iff_norm.mp hz]
      exact hrε
    · intro h'
      rw [mem_singleton_iff] at h'
      rw [h', mem_sphere_iff_norm, sub_self, norm_zero] at hz
      exact hr.ne' hz.symm

/-- **Pólya (direção ⇐): se todo `J^{d,0}` de `Ξ` tem só raízes reais, vale HR.** -/
theorem rh_de_jensen (h : ∀ d, RealRooted (jensen γXi d 0)) : RiemannHypothesis := by
  have hz := zeros_reais_de_jensen inteira_aXi aXi_zero_pos.ne' h
  rw [ATK.BaseRiemannXi.riemannHypothesis_iff_Xi]
  intro z hz0
  have hw : ev aXi (-z ^ 2) = 0 := by
    rw [ev_aXi]
    exact hz0
  have him := hz _ hw
  have h2 : z.re * z.im = 0 := by
    simp only [Complex.neg_im, sq, Complex.mul_im] at him
    linarith
  rcases mul_eq_zero.mp h2 with hre | hi
  · exfalso
    have hz' : (1 / 2 : ℂ) + z * I = ((1 / 2 - z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre, sub_eq_add_neg]
    rw [hz'] at hz0
    obtain ⟨x, hx, he⟩ := ATK.BaseRiemannXiSinal.riemannXi_ofReal_pos (1 / 2 - z.im)
    rw [he] at hz0
    exact hx.ne' (by exact_mod_cast hz0)
  · exact hi

/-- **Critério de Pólya–Jensen: HR ⟺ todo polinômio de Jensen `J^{d,n}` de `Ξ` tem só raízes reais.** -/
theorem rh_iff_jensen : RiemannHypothesis ↔ ∀ d n, RealRooted (jensen γXi d n) :=
  ⟨rh_jensen, fun h => rh_de_jensen fun d => h d 0⟩

/-- **HR ⟺ todo `J^{d,0}` de `Ξ` tem só raízes reais.** -/
theorem rh_iff_jensen0 : RiemannHypothesis ↔ ∀ d, RealRooted (jensen γXi d 0) :=
  ⟨fun h d => rh_jensen h d 0, rh_de_jensen⟩

end ATK.Hurwitz

#print axioms ATK.Hurwitz.hurwitz_local
#print axioms ATK.Hurwitz.phiJ_nonneg
#print axioms ATK.Hurwitz.phiJ_le_one
#print axioms ATK.Hurwitz.tendsto_phiJ
#print axioms ATK.Hurwitz.Fj_eq
#print axioms ATK.Hurwitz.tendstoUniformlyOn_Fj
#print axioms ATK.Hurwitz.Fj_ne_zero
#print axioms ATK.Hurwitz.zeros_reais_de_jensen
#print axioms ATK.Hurwitz.rh_de_jensen
#print axioms ATK.Hurwitz.rh_iff_jensen
#print axioms ATK.Hurwitz.rh_iff_jensen0
