import ATK.ZeroClasses.ExplicitaPecas

/-!
# A fórmula explícita: os resíduos no retângulo largo (rodada 70)

Primeira metade da fórmula explícita de Riemann–von Mangoldt sem hipóteses (Davenport, cap. 17). No retângulo
`[−U, c] × [−T, T]`, `U = 2K + ½`, `c > 1`, sem zeros de `ζ` no bordo:

  **`∮ x^s(−ζ′/ζ)(s)/s ds = 2πi (x − Σ_ρ m_ρ x^ρ/ρ + Σ_{n<K} x^{−2(n+1)}/(2(n+1)) − log 2π)`**   (`bordo_largo`),

a soma em `ρ` sobre os zeros não triviais do retângulo. As peças:

* **o princípio do argumento ponderado com um polo** (`principio_polo`): para `φ` analítica e um polo simples
  `c/(s − p)` no interior com `f(p) ≠ 0`,
  `∮ (f′/f)(φ + c/(s − p)) = 2πi (Σ_u m_u (φ(u) + c/(u − p)) + c f′/f(p))`;
* `ζ₁(s) = (s − 1)ζ(s)` (`riemannZeta₁` da Mathlib, inteira): mesmos zeros e ordens que `ζ` fora de `1`
  (`ordem_zeta1`), `ζ₁′/ζ₁ = ζ′/ζ + 1/(s − 1)` (`logDeriv_zeta1`), `ζ₁′/ζ₁(0) = log 2π − 1`
  (`deriv_riemannZeta_zero` da Mathlib);
* **os zeros triviais são simples** (`ordem_trivial`): pela equação funcional
  `ζ(1 − s) = 2(2π)^{−s}Γ(s) cos(πs/2) ζ(s)` em `s = 2n + 3`, onde só o cosseno se anula, e com zero simples;
* **os zeros em `Re s ≤ 0` são triviais** (rodada 15).

Classificação (rodada 70): **ferramenta**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.FormulaExplicita

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_sum bordo_cauchy bordo_inv
  bordo_const_mul)
open ATK.ZeroClasses.PsiRH (Fx px px_diff px_one)
open ATK.ZeroClasses.Explicita (zeta_analytic)

/-! ## 1. O princípio do argumento ponderado com um polo -/

/-- **`∮ (f′/f)(φ + c/(s − p)) = 2πi (Σ_u m_u (φ(u) + c/(u − p)) + c f′/f(p))`**. -/
theorem principio_polo {f φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hφ : AnalyticOnNhd ℂ φ U) {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im) (hK : Ret z w ⊆ U)
    (htop : ∀ p ∈ Ret z w, analyticOrderAt f p ≠ ⊤) (hbd : ∀ p ∈ Bordo z w, f p ≠ 0)
    {p c : ℂ} (hp : z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im) (hfp : f p ≠ 0) :
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ u ∈ Ret z w ∧ f u = 0) ∧
      bordo (fun s => logDeriv f s * (φ s + c * (s - p)⁻¹)) z w =
        2 * π * I * (∑ u ∈ S, (analyticOrderNatAt f u : ℂ) * (φ u + c * (u - p)⁻¹) + c * logDeriv f p) := by
  classical
  have hKc : IsCompact (Ret z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  set Zs := {u | u ∈ Ret z w ∧ f u = 0} with hZs
  have hfin : Zs.Finite := by
    have hD := (MeromorphicOn.divisor f (Ret z w)).finiteSupport hKc
    refine hD.subset fun u ⟨hu, hfu⟩ => ?_
    rw [Function.mem_support, ATK.ArgPrincipio.divisor_eq_ordem (hf.mono hK) hu (htop u hu)]
    have h0 : analyticOrderNatAt f u ≠ 0 := fun h =>
      ((ATK.ArgPrincipio.ordemNat_zero_iff (hf u (hK hu)) (htop u hu)).mp h) hfu
    exact_mod_cast h0
  set S := hfin.toFinset with hS
  have hmemS : ∀ u, u ∈ S ↔ u ∈ Ret z w ∧ f u = 0 := fun u => by
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  refine ⟨S, hmemS, ?_⟩
  have hint : ∀ u ∈ S, z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im := by
    intro u hu
    obtain ⟨huK, hfu⟩ := (hmemS u).mp hu
    have hr := (mem_reProdIm.mp huK).1
    have hi := (mem_reProdIm.mp huK).2
    rw [uIcc_of_le hre.le] at hr
    rw [uIcc_of_le him.le] at hi
    refine ⟨lt_of_le_of_ne hr.1 fun h => hbd u ⟨huK, Or.inl h.symm⟩ hfu,
      lt_of_le_of_ne hr.2 fun h => hbd u ⟨huK, Or.inr (Or.inl h)⟩ hfu,
      lt_of_le_of_ne hi.1 fun h => hbd u ⟨huK, Or.inr (Or.inr (Or.inl h.symm))⟩ hfu,
      lt_of_le_of_ne hi.2 fun h => hbd u ⟨huK, Or.inr (Or.inr (Or.inr h))⟩ hfu⟩
  have hpR : p ∈ Ret z w := by
    refine mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [uIcc_of_le hre.le]; exact ⟨hp.1.le, hp.2.1.le⟩
    · rw [uIcc_of_le him.le]; exact ⟨hp.2.2.1.le, hp.2.2.2.le⟩
  have hpS : p ∉ S := fun h => hfp ((hmemS p).mp h).2
  have hpU : p ∈ U := hK hpR
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hm
  set Q : ℂ → ℂ := fun s => ∏ u ∈ S, (s - u) ^ m u with hQ
  have hQan : AnalyticOnNhd ℂ Q univ := fun s _ => by simp only [hQ]; fun_prop
  have hordQ : ∀ q, analyticOrderAt Q q = if q ∈ S then (m q : ℕ∞) else 0 := fun q =>
    ATK.ZeroClasses.Landau.ordem_poli S m q
  have hmw : ∀ q ∈ S, (m q : ℕ∞) = analyticOrderAt f q := by
    intro q hq
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (htop q ((hmemS q).mp hq).1)
    simp only [hm, analyticOrderNatAt, ← hk]
    simp
  have hle : ∀ q ∈ U, analyticOrderAt Q q ≤ analyticOrderAt f q := by
    intro q _
    rw [hordQ]
    split_ifs with h
    · rw [hmw q h]
    · simp
  have htopQ : ∀ q ∈ U, analyticOrderAt Q q ≠ ⊤ := by
    intro q _
    rw [hordQ]
    split_ifs <;> simp
  obtain ⟨G, hGan, hfQG, hG0⟩ := ATK.ZeroClasses.Landau.quociente_local hU hf
    (hQan.mono (subset_univ _)) hle htopQ
  have hGne : ∀ q ∈ Ret z w, G q ≠ 0 := by
    intro q hq
    apply hG0 q (hK hq)
    rw [hordQ]
    split_ifs with h
    · exact (hmw q h).symm
    · have hfq : f q ≠ 0 := fun h' => h ((hmemS q).mpr ⟨hq, h'⟩)
      exact analyticOrderAt_eq_zero.mpr (Or.inr hfq)
  -- `f′/f = Σ m_u/(s − u) + G′/G` fora de `S`
  have hlogQG : ∀ q ∈ Ret z w, q ∉ S → logDeriv f q = ∑ u ∈ S, (m u : ℂ) / (q - u) + logDeriv G q := by
    intro q hq hqS
    have hqU : q ∈ U := hK hq
    have hev : f =ᶠ[𝓝 q] fun s => Q s * G s := by
      filter_upwards [hU.mem_nhds hqU] with s hs
      exact hfQG s hs
    have hQq : Q q ≠ 0 := by
      simp only [hQ]
      rw [Finset.prod_ne_zero_iff]
      intro u hu
      exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hqS (h ▸ hu))
    rw [(logDeriv_congr_nhds hev).self_of_nhds]
    change logDeriv (Q * G) q = _
    rw [logDeriv_mul q hQq (hGne q hq) (hQan q (mem_univ _)).differentiableAt
      (hGan q hqU).differentiableAt, ATK.ZeroClasses.Landau.logDeriv_poli S m hqS]
  -- `G′/G` analítica perto do retângulo
  have hLGan : ∀ q ∈ Ret z w, AnalyticAt ℂ (logDeriv G) q := by
    intro q hq
    have hqU := hK hq
    have e : logDeriv G = fun s => deriv G s / G s := funext fun s => logDeriv_apply G s
    rw [e]
    exact (hGan q hqU).deriv.div (hGan q hqU) (hGne q hq)
  -- `dslope (G′/G) p` é holomorfa no retângulo
  set W : Set ℂ := {q | AnalyticAt ℂ (logDeriv G) q} with hW
  have hWo : IsOpen W := isOpen_analyticAt ℂ (logDeriv G)
  have hRW : Ret z w ⊆ W := fun q hq => hLGan q hq
  have hLGd : DifferentiableOn ℂ (logDeriv G) W := fun q hq => (hq : AnalyticAt ℂ _ q).differentiableAt.differentiableWithinAt
  have hDL : DifferentiableOn ℂ (dslope (logDeriv G) p) W :=
    (differentiableOn_dslope (hWo.mem_nhds (hRW hpR))).mpr hLGd
  -- a parte holomorfa
  set A : ℂ → ℂ := fun u => (m u : ℂ) * (φ u + c * (u - p)⁻¹) with hA
  set B : ℂ := c * logDeriv G p - ∑ u ∈ S, (m u : ℂ) * c * (u - p)⁻¹ with hB
  set H : ℂ → ℂ := fun s => ∑ u ∈ S, (m u : ℂ) * dslope φ u s + logDeriv G s * φ s +
    c * dslope (logDeriv G) p s with hH
  have hEq : EqOn (fun s => logDeriv f s * (φ s + c * (s - p)⁻¹))
      (fun s => H s + (∑ u ∈ S, A u * (s - u)⁻¹ + B * (s - p)⁻¹)) (Bordo z w) := by
    intro s hs
    have hsS : s ∉ S := fun h => hbd s hs ((hmemS s).mp h).2
    have hsp : s ≠ p := by
      rintro rfl
      obtain ⟨_, h⟩ := hs
      rcases h with h | h | h | h
      · linarith [hp.1]
      · linarith [hp.2.1]
      · linarith [hp.2.2.1]
      · linarith [hp.2.2.2]
    have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
    have hterm : ∀ u ∈ S, (m u : ℂ) / (s - u) * (φ s + c * (s - p)⁻¹) =
        (m u : ℂ) * dslope φ u s + A u * (s - u)⁻¹ - (m u : ℂ) * c * (u - p)⁻¹ * (s - p)⁻¹ := by
      intro u hu
      have hsu : s ≠ u := fun h => hsS (h ▸ hu)
      have hsu' : s - u ≠ 0 := sub_ne_zero.mpr hsu
      have hup : u - p ≠ 0 := sub_ne_zero.mpr fun h => hpS (h ▸ hu)
      simp only [hA]
      rw [dslope_of_ne _ hsu, slope_def_field]
      field_simp
      ring
    have hG : logDeriv G s * (φ s + c * (s - p)⁻¹) =
        logDeriv G s * φ s + c * dslope (logDeriv G) p s + c * logDeriv G p * (s - p)⁻¹ := by
      rw [dslope_of_ne _ hsp, slope_def_field]
      field_simp
      ring
    simp only [hH, hB]
    rw [hlogQG s hs.1 hsS, add_mul, Finset.sum_mul, Finset.sum_congr rfl hterm, hG,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, sub_mul, Finset.sum_mul]
    ring
  have hHd : DifferentiableOn ℂ H (Ret z w) := by
    intro q hq
    have hqU := hK hq
    have h1 : DifferentiableAt ℂ (fun s => ∑ u ∈ S, (m u : ℂ) * dslope φ u s) q := by
      have : (fun s => ∑ u ∈ S, (m u : ℂ) * dslope φ u s) =
          ∑ u ∈ S, (fun s => (m u : ℂ) * dslope φ u s) := by
        funext s
        rw [Finset.sum_apply]
      rw [this]
      refine DifferentiableAt.sum fun u hu => ?_
      have huU : u ∈ U := hK ((hmemS u).mp hu).1
      have hD : DifferentiableOn ℂ (dslope φ u) U :=
        (differentiableOn_dslope (hU.mem_nhds huU)).mpr fun r hr =>
          (hφ r hr).differentiableAt.differentiableWithinAt
      exact (differentiableAt_const _).mul (hD.differentiableAt (hU.mem_nhds hqU))
    have h2 : DifferentiableAt ℂ (logDeriv G) q := (hLGan q hq).differentiableAt
    have h3 : DifferentiableAt ℂ (dslope (logDeriv G) p) q :=
      hDL.differentiableAt (hWo.mem_nhds (hRW hq))
    exact ((h1.add (h2.mul (hφ q hqU).differentiableAt)).add
      ((differentiableAt_const c).mul h3)).differentiableWithinAt
  have hBR : Bordo z w ⊆ Ret z w := fun q hq => hq.1
  have hc1 : ∀ u ∈ S, ContinuousOn (fun s => A u * (s - u)⁻¹) (Bordo z w) := by
    intro u hu
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun q hq h => ?_)
    have hqu : q = u := sub_eq_zero.mp h
    exact hbd q hq (hqu ▸ ((hmemS u).mp hu).2)
  have hc2 : ContinuousOn (fun s => B * (s - p)⁻¹) (Bordo z w) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun q hq h => ?_)
    have hqp : q = p := sub_eq_zero.mp h
    obtain ⟨_, hside⟩ := hq
    rw [hqp] at hside
    rcases hside with h | h | h | h
    · linarith [hp.1]
    · linarith [hp.2.1]
    · linarith [hp.2.2.1]
    · linarith [hp.2.2.2]
  have hcsum : ContinuousOn (fun s => ∑ u ∈ S, A u * (s - u)⁻¹) (Bordo z w) :=
    continuousOn_finsetSum S hc1
  have hc12 : ContinuousOn (fun s => ∑ u ∈ S, A u * (s - u)⁻¹ + B * (s - p)⁻¹) (Bordo z w) :=
    hcsum.add hc2
  rw [bordo_congr hEq, bordo_add (hHd.mono hBR).continuousOn hc12, bordo_cauchy hHd, zero_add,
    bordo_add hcsum hc2, bordo_sum S (fun u s => A u * (s - u)⁻¹) hc1, bordo_const_mul,
    bordo_inv hp.1 hp.2.1 hp.2.2.1 hp.2.2.2]
  have hsum : ∑ u ∈ S, bordo (fun s => A u * (s - u)⁻¹) z w = ∑ u ∈ S, A u * (2 * π * I) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨a1, a2, a3, a4⟩ := hint u hu
    rw [bordo_const_mul, bordo_inv a1 a2 a3 a4]
  rw [hsum]
  -- `B = c·f′/f(p)`
  have hfp' := hlogQG p hpR hpS
  have hBv : B = c * logDeriv f p := by
    simp only [hB]
    rw [hfp', mul_add, Finset.mul_sum]
    have e : ∀ u ∈ S, c * ((m u : ℂ) / (p - u)) = -((m u : ℂ) * c * (u - p)⁻¹) := by
      intro u hu
      have hup : u - p ≠ 0 := sub_ne_zero.mpr fun h => hpS (h ▸ hu)
      have hpu : p - u ≠ 0 := sub_ne_zero.mpr fun h => hpS (h.symm ▸ hu)
      field_simp
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
    ring
  rw [hBv, ← Finset.sum_mul]
  ring

/-! ## 2. `ζ₁(s) = (s − 1)ζ(s)` -/

theorem zeta1_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

theorem zeta1_an : AnalyticOnNhd ℂ riemannZeta₁ univ := fun s _ =>
  differentiable_riemannZeta₁.analyticAt s

theorem zeta1_eq_zero_iff {s : ℂ} : riemannZeta₁ s = 0 ↔ s ≠ 1 ∧ riemannZeta s = 0 := by
  by_cases h1 : s = 1
  · subst h1
    simp
  · rw [zeta1_eq h1, mul_eq_zero]
    exact ⟨fun h => ⟨h1, h.resolve_left (sub_ne_zero.mpr h1)⟩, fun h => Or.inr h.2⟩

theorem zeta1_zero : riemannZeta₁ 0 = 1 / 2 := by
  rw [zeta1_eq zero_ne_one, riemannZeta_zero]
  ring

theorem ev_zeta1 {u : ℂ} (h1 : u ≠ 1) :
    riemannZeta₁ =ᶠ[𝓝 u] (fun s : ℂ => s - 1) * riemannZeta := by
  filter_upwards [isOpen_ne.mem_nhds h1] with s hs
  exact zeta1_eq hs

/-- `ord_u ζ₁ = ord_u ζ` fora de `1`. -/
theorem ordem_zeta1 {u : ℂ} (h1 : u ≠ 1) :
    analyticOrderAt riemannZeta₁ u = analyticOrderAt riemannZeta u := by
  rw [analyticOrderAt_congr (ev_zeta1 h1), analyticOrderAt_mul (by fun_prop) (zeta_analytic h1)]
  have : analyticOrderAt (fun s : ℂ => s - 1) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr h1))
  rw [this, zero_add]

theorem ordem_zeta1_ne_top (u : ℂ) : analyticOrderAt riemannZeta₁ u ≠ ⊤ := by
  have h0 : analyticOrderAt riemannZeta₁ 0 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (by rw [zeta1_zero]; norm_num))]
    simp
  exact zeta1_an.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0)
    (mem_univ u) h0

/-- `ζ₁′/ζ₁ = ζ′/ζ + 1/(s − 1)`. -/
theorem logDeriv_zeta1 {s : ℂ} (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = logDeriv riemannZeta s + (s - 1)⁻¹ := by
  rw [(logDeriv_congr_nhds (ev_zeta1 h1)).self_of_nhds,
    logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s (sub_ne_zero.mpr h1) hz
      (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta h1)]
  have : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  rw [this, add_comm]

/-- **`ζ₁′/ζ₁(0) = log 2π − 1`**. -/
theorem logDeriv_zeta1_zero : logDeriv riemannZeta₁ 0 = (Real.log (2 * π) : ℂ) - 1 := by
  have hz : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  rw [logDeriv_zeta1 zero_ne_one hz, logDeriv_apply, deriv_riemannZeta_zero, riemannZeta_zero,
    Complex.ofReal_log (by positivity)]
  push_cast
  field_simp
  ring

/-! ## 3. Os zeros triviais são simples -/

theorem triv_re (n : ℕ) : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp

theorem triv_im (n : ℕ) : (-2 * ((n : ℂ) + 1)).im = 0 := by simp

/-- `ζ′(−2(n + 1)) ≠ 0`, pela equação funcional. -/
theorem deriv_trivial (n : ℕ) : deriv riemannZeta (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  set s₀ : ℂ := -2 * ((n : ℂ) + 1) with hs₀
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hre : s₀.re < 0 := by rw [hs₀, triv_re]; linarith
  set h : ℂ → ℂ := fun s => 2 * (2 * (π : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) * riemannZeta (1 - s)
    with hh
  set g : ℂ → ℂ := fun s => cos (π * (1 - s) / 2) with hg
  have hV : IsOpen {s : ℂ | s.re < 0} := isOpen_lt continuous_re continuous_const
  have hev : riemannZeta =ᶠ[𝓝 s₀] fun s => h s * g s := by
    filter_upwards [hV.mem_nhds hre] with s hs
    have hs' : s.re < 0 := hs
    have h1 : ∀ m : ℕ, 1 - s ≠ -m := by
      intro m hm
      have := congrArg Complex.re hm
      simp only [sub_re, one_re, neg_re, natCast_re] at this
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith
    have h2 : 1 - s ≠ 1 := by
      intro hm
      have := congrArg Complex.re hm
      simp only [sub_re, one_re] at this
      linarith
    have e := riemannZeta_one_sub h1 h2
    rw [sub_sub_cancel] at e
    rw [e]
    simp only [hh, hg]
    ring
  -- `1 − s₀ = 2n + 3`
  have ht : (1 - s₀).re = 2 * n + 3 := by
    rw [sub_re, one_re, hs₀, triv_re]
    ring
  have hΓ : ∀ m : ℕ, 1 - s₀ ≠ -m := by
    intro m hm
    have := congrArg Complex.re hm
    rw [ht, neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have h1' : 1 - s₀ ≠ 1 := by
    intro hm
    have := congrArg Complex.re hm
    rw [ht, one_re] at this
    linarith
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hA : DifferentiableAt ℂ (fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-(1 - s))) s₀ :=
    (differentiableAt_const _).mul
      (((differentiableAt_const _).sub differentiableAt_id).neg.const_cpow (Or.inl h2pi))
  have hB : DifferentiableAt ℂ (fun s : ℂ => Gamma (1 - s)) s₀ :=
    (Complex.differentiableAt_Gamma (1 - s₀) hΓ).comp s₀
      ((differentiableAt_const _).sub differentiableAt_id)
  have hC : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (1 - s)) s₀ :=
    (differentiableAt_riemannZeta h1').comp s₀ ((differentiableAt_const _).sub differentiableAt_id)
  have hdh : DifferentiableAt ℂ h s₀ := (hA.mul hB).mul hC
  have hh0 : h s₀ ≠ 0 := by
    simp only [hh]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero hΓ))
      (riemannZeta_ne_zero_of_one_le_re (by rw [ht]; linarith))
    exact fun h0 => h2pi ((cpow_eq_zero_iff _ _).mp h0).1
  have hg0 : cos (π * (1 - s₀) / 2) = 0 := by
    refine Complex.cos_eq_zero_iff.mpr ⟨(n : ℤ) + 1, ?_⟩
    rw [hs₀]
    push_cast
    ring
  have hsin : sin (π * (1 - s₀) / 2) ≠ 0 := by
    intro h0
    have := Complex.sin_sq_add_cos_sq (π * (1 - s₀) / 2)
    rw [h0, hg0] at this
    norm_num at this
  have hin : HasDerivAt (fun s : ℂ => (π : ℂ) * (1 - s) / 2) ((π : ℂ) * (-1) / 2) s₀ :=
    (((hasDerivAt_id s₀).const_sub 1).const_mul (π : ℂ)).div_const 2
  have hgd : HasDerivAt g (-sin (π * (1 - s₀) / 2) * ((π : ℂ) * (-1) / 2)) s₀ := hin.ccos
  have hk : HasDerivAt (fun s => h s * g s) (deriv h s₀ * g s₀ +
      h s₀ * (-sin (π * (1 - s₀) / 2) * ((π : ℂ) * (-1) / 2))) s₀ := hdh.hasDerivAt.mul hgd
  rw [hev.deriv_eq, hk.deriv]
  have hgs : g s₀ = 0 := hg0
  rw [hgs, mul_zero, zero_add]
  refine mul_ne_zero hh0 (mul_ne_zero (neg_ne_zero.mpr hsin) ?_)
  exact div_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by norm_num)) two_ne_zero

/-- **Os zeros triviais são simples**: `ord_{−2(n+1)} ζ = 1`. -/
theorem ordem_trivial (n : ℕ) : analyticOrderAt riemannZeta (-2 * ((n : ℂ) + 1)) = 1 := by
  have h1 : (-2 * ((n : ℂ) + 1)) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [triv_re, one_re] at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  exact (zeta_analytic h1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (riemannZeta_neg_two_mul_nat_add_one n) (deriv_trivial n)

/-! ## 4. O retângulo largo -/

/-- `ψ₁(s) = (x^s − 1)/s`, inteira. -/
noncomputable def psi1 (x : ℝ) : ℂ → ℂ := dslope (fun s : ℂ => (x : ℂ) ^ s) 0

theorem cpow_diff {x : ℝ} (hx : 0 < x) : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) := fun _ =>
  differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))

theorem dslope_diff {x : ℝ} (hx : 0 < x) (a : ℂ) :
    Differentiable ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) a) := by
  rw [← differentiableOn_univ, differentiableOn_dslope univ_mem]
  exact (cpow_diff hx).differentiableOn

theorem psi1_add_inv {x : ℝ} {u : ℂ} (hu : u ≠ 0) : psi1 x u + 1 * (u - 0)⁻¹ = px x u := by
  unfold psi1 px
  rw [dslope_of_ne _ hu, slope_def_field, cpow_zero, sub_zero]
  field_simp
  ring

/-- **O retângulo largo**: em `[−(2K + ½), c] × [−T, T]`, `c > 1`, `T > 0`, sem zeros nas horizontais,
`∮ x^s(−ζ′/ζ)(s)/s ds = 2πi (x − Σ_ρ m_ρ x^ρ/ρ + Σ_{n<K} x^{−2(n+1)}/(2(n+1)) − log 2π)`,
`ρ` sobre os zeros de `ζ` no retângulo com `Re ρ > 0`. -/
theorem bordo_largo {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) (K : ℕ)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re < 1 → (s.im = -T ∨ s.im = T) → riemannZeta s ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ u, u ∈ S ↔ u ∈ Ret ⟨-(2 * K + 1 / 2), -T⟩ ⟨c, T⟩ ∧ riemannZeta u = 0 ∧ 0 < u.re) ∧
      bordo (Fx x) ⟨-(2 * K + 1 / 2), -T⟩ ⟨c, T⟩ =
        2 * π * I * (x - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px x u +
          ∑ n ∈ Finset.range K, (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) -
          (Real.log (2 * π) : ℂ)) := by
  classical
  set z : ℂ := ⟨-(2 * (K : ℝ) + 1 / 2), -T⟩ with hz
  set w : ℂ := ⟨c, T⟩ with hw
  have hzre : z.re = -(2 * (K : ℝ) + 1 / 2) := rfl
  have hzim : z.im = -T := rfl
  have hwre : w.re = c := rfl
  have hwim : w.im = T := rfl
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  have hzc : -(2 * (K : ℝ) + 1 / 2) ≤ c := by linarith
  have hTT : -T ≤ T := by linarith
  have hmemR : ∀ p : ℂ, p ∈ Ret z w ↔
      (-(2 * (K : ℝ) + 1 / 2) ≤ p.re ∧ p.re ≤ c) ∧ (-T ≤ p.im ∧ p.im ≤ T) := by
    intro p
    rw [Ret, mem_reProdIm, hzre, hwre, hzim, hwim, uIcc_of_le hzc, uIcc_of_le hTT]
    rfl
  -- nenhum zero de `ζ₁` no bordo
  have hbd1 : ∀ p ∈ Bordo z w, riemannZeta₁ p ≠ 0 := by
    rintro p ⟨_, hside⟩ hp0
    obtain ⟨_, hζ⟩ := zeta1_eq_zero_iff.mp hp0
    rw [hzre, hwre, hzim, hwim] at hside
    by_cases hre : 0 < p.re
    · have hre1 : p.re < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
      rcases hside with h | h | h | h
      · linarith
      · linarith
      · exact hbd p hre hre1 (Or.inl h) hζ
      · exact hbd p hre hre1 (Or.inr h) hζ
    · obtain ⟨n, hn⟩ := ATK.ZetaSimetria.zero_trivial_de_re_nao_pos hζ (not_lt.mp hre)
      have hr : p.re = -2 * ((n : ℝ) + 1) := by rw [hn, triv_re]
      have hi : p.im = 0 := by rw [hn, triv_im]
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      rcases hside with h | h | h | h
      · rw [hr] at h
        have h4 : ((4 * (n + 1) : ℕ) : ℝ) = ((4 * K + 1 : ℕ) : ℝ) := by push_cast; linarith
        have h5 : 4 * (n + 1) = 4 * K + 1 := by exact_mod_cast h4
        omega
      · rw [hr] at h; linarith
      · rw [hi] at h; linarith
      · rw [hi] at h; linarith
  have htop : ∀ p ∈ Ret z w, analyticOrderAt riemannZeta₁ p ≠ ⊤ := fun p _ => ordem_zeta1_ne_top p
  have hψan : AnalyticOnNhd ℂ (psi1 x) univ := fun s _ => (dslope_diff hx 0).analyticAt s
  have h0int : z.re < (0 : ℂ).re ∧ (0 : ℂ).re < w.re ∧ z.im < (0 : ℂ).im ∧ (0 : ℂ).im < w.im := by
    simp only [zero_re, zero_im, hzre, hwre, hzim, hwim]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hz10 : riemannZeta₁ 0 ≠ 0 := by rw [zeta1_zero]; norm_num
  obtain ⟨S₀, hS₀, hpol⟩ := principio_polo isOpen_univ zeta1_an hψan (z := z) (w := w)
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) (subset_univ _) htop hbd1
    (p := 0) (c := 1) h0int hz10
  -- a decomposição de `F` no bordo
  have hne0 : ∀ p ∈ Bordo z w, p ≠ 0 := by
    rintro p ⟨_, h⟩ rfl
    rw [hzre, hwre, hzim, hwim, zero_re, zero_im] at h
    rcases h with h | h | h | h <;> linarith
  have hne1 : ∀ p ∈ Bordo z w, p ≠ 1 := by
    rintro p ⟨_, h⟩ rfl
    rw [hzre, hwre, hzim, hwim, one_re, one_im] at h
    rcases h with h | h | h | h <;> linarith
  have hζbd : ∀ p ∈ Bordo z w, riemannZeta p ≠ 0 := fun p hp h =>
    hbd1 p hp (zeta1_eq_zero_iff.mpr ⟨hne1 p hp, h⟩)
  have heq : EqOn (Fx x) (fun s => (-1 : ℂ) * (logDeriv riemannZeta₁ s * (psi1 x s + 1 * (s - 0)⁻¹)) +
      ((dslope (fun s : ℂ => (x : ℂ) ^ s) 1 s - psi1 x s) +
        ((x : ℂ) * (s - 1)⁻¹ + (-1 : ℂ) * (s - 0)⁻¹))) (Bordo z w) := by
    intro s hs
    have hs0 := hne0 s hs
    have hs1 := hne1 s hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp only [Fx, psi1]
    rw [logDeriv_zeta1 hs1 (hζbd s hs), dslope_of_ne _ hs1, dslope_of_ne _ hs0, slope_def_field,
      slope_def_field]
    simp only [cpow_one, cpow_zero, sub_zero]
    field_simp
    ring
  have hψc : Continuous (psi1 x) := (dslope_diff hx 0).continuous
  have hd1c : Continuous (dslope (fun s : ℂ => (x : ℂ) ^ s) 1) := (dslope_diff hx 1).continuous
  have hinv0 : ContinuousOn (fun s : ℂ => (s - 0)⁻¹) (Bordo z w) := fun p hp =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hne0 p hp))).continuousWithinAt
  have hinv1 : ContinuousOn (fun s : ℂ => (s - 1)⁻¹) (Bordo z w) := fun p hp =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hne1 p hp))).continuousWithinAt
  have hlogc : ContinuousOn (logDeriv riemannZeta₁) (Bordo z w) := by
    intro p hp
    have e : logDeriv riemannZeta₁ = fun z => deriv riemannZeta₁ z / riemannZeta₁ z :=
      funext fun z => logDeriv_apply _ z
    rw [e]
    exact ((zeta1_an p (mem_univ _)).deriv.continuousAt.div (zeta1_an p (mem_univ _)).continuousAt
      (hbd1 p hp)).continuousWithinAt
  have hP : ContinuousOn (fun s => logDeriv riemannZeta₁ s * (psi1 x s + 1 * (s - 0)⁻¹))
      (Bordo z w) :=
    hlogc.mul (hψc.continuousOn.add (continuousOn_const.mul hinv0))
  have hc1 : ContinuousOn (fun s => (-1 : ℂ) * (logDeriv riemannZeta₁ s * (psi1 x s + 1 * (s - 0)⁻¹)))
      (Bordo z w) := continuousOn_const.mul hP
  have hQ1 : ContinuousOn (fun s => dslope (fun s : ℂ => (x : ℂ) ^ s) 1 s - psi1 x s) (Bordo z w) :=
    (hd1c.sub hψc).continuousOn
  have hQ2a : ContinuousOn (fun s : ℂ => (x : ℂ) * (s - 1)⁻¹) (Bordo z w) :=
    continuousOn_const.mul hinv1
  have hQ2b : ContinuousOn (fun s : ℂ => (-1 : ℂ) * (s - 0)⁻¹) (Bordo z w) :=
    continuousOn_const.mul hinv0
  have hQ2 : ContinuousOn (fun s : ℂ => (x : ℂ) * (s - 1)⁻¹ + (-1 : ℂ) * (s - 0)⁻¹) (Bordo z w) :=
    hQ2a.add hQ2b
  have hQ : ContinuousOn (fun s => (dslope (fun s : ℂ => (x : ℂ) ^ s) 1 s - psi1 x s) +
      ((x : ℂ) * (s - 1)⁻¹ + (-1 : ℂ) * (s - 0)⁻¹)) (Bordo z w) := hQ1.add hQ2
  have hQd : DifferentiableOn ℂ (fun s => dslope (fun s : ℂ => (x : ℂ) ^ s) 1 s - psi1 x s)
      (Ret z w) :=
    ((dslope_diff hx 1).sub (dslope_diff hx 0)).differentiableOn
  have hb1 : bordo (fun s => (s - 1)⁻¹) z w = 2 * π * I :=
    bordo_inv (by rw [hzre, one_re]; linarith) (by rw [hwre, one_re]; linarith)
      (by rw [hzim, one_im]; linarith) (by rw [hwim, one_im]; linarith)
  have hb0 : bordo (fun s => (s - 0)⁻¹) z w = 2 * π * I :=
    bordo_inv h0int.1 h0int.2.1 h0int.2.2.1 h0int.2.2.2
  -- a soma sobre os zeros: não triviais + triviais
  set S : Finset ℂ := S₀.filter (fun u => 0 < u.re) with hSdef
  have hsplit : ∑ u ∈ S₀, (analyticOrderNatAt riemannZeta₁ u : ℂ) * (psi1 x u + 1 * (u - 0)⁻¹) =
      ∑ u ∈ S, (analyticOrderNatAt riemannZeta₁ u : ℂ) * (psi1 x u + 1 * (u - 0)⁻¹) +
      ∑ u ∈ S₀.filter (fun u => ¬ 0 < u.re),
        (analyticOrderNatAt riemannZeta₁ u : ℂ) * (psi1 x u + 1 * (u - 0)⁻¹) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hT2 : S₀.filter (fun u => ¬ 0 < u.re) =
      (Finset.range K).image (fun n : ℕ => -2 * ((n : ℂ) + 1)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, hS₀, hmemR, zeta1_eq_zero_iff]
    constructor
    · rintro ⟨⟨⟨⟨hr1, _⟩, _⟩, _, hζ⟩, hre⟩
      obtain ⟨n, hn⟩ := ATK.ZetaSimetria.zero_trivial_de_re_nao_pos hζ (not_lt.mp hre)
      refine ⟨n, ?_, hn.symm⟩
      rw [hn, triv_re] at hr1
      have h4 : ((4 * (n + 1) : ℕ) : ℝ) ≤ ((4 * K + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h5 : 4 * (n + 1) ≤ 4 * K + 1 := by exact_mod_cast h4
      omega
    · rintro ⟨n, hn, rfl⟩
      have hn' : ((n : ℝ) + 1) ≤ K := by
        have : n + 1 ≤ K := hn
        exact_mod_cast this
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      simp only [triv_re, triv_im]
      refine ⟨⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_,
        riemannZeta_neg_two_mul_nat_add_one n⟩, by linarith⟩
      intro h
      have := congrArg Complex.re h
      rw [triv_re, one_re] at this
      linarith
  have hinj : ∀ a ∈ Finset.range K, ∀ b ∈ Finset.range K,
      -2 * ((a : ℂ) + 1) = -2 * ((b : ℂ) + 1) → a = b := by
    intro a _ b _ hab
    have h := congrArg Complex.re hab
    rw [triv_re, triv_re] at h
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  have hsum2 : ∑ u ∈ S₀.filter (fun u => ¬ 0 < u.re),
      (analyticOrderNatAt riemannZeta₁ u : ℂ) * (psi1 x u + 1 * (u - 0)⁻¹) =
      ∑ n ∈ Finset.range K, -((x : ℂ) ^ (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1))) := by
    rw [hT2, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hn1 : (-2 * ((n : ℂ) + 1)) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [triv_re, one_re] at this
      linarith
    have hn0' : (-2 * ((n : ℂ) + 1)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      rw [triv_re, zero_re] at this
      linarith
    rw [psi1_add_inv hn0']
    have hm : analyticOrderNatAt riemannZeta₁ (-2 * ((n : ℂ) + 1)) = 1 := by
      simp only [analyticOrderNatAt, ordem_zeta1 hn1, ordem_trivial n, ENat.toNat_one]
    rw [hm, Nat.cast_one, one_mul, px, neg_mul, div_neg]
  have hsum1 : ∑ u ∈ S, (analyticOrderNatAt riemannZeta₁ u : ℂ) * (psi1 x u + 1 * (u - 0)⁻¹) =
      ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px x u := by
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨hu0', hre⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, hz1⟩ := (hS₀ u).mp hu0'
    have hu1 := (zeta1_eq_zero_iff.mp hz1).1
    have hu0 : u ≠ 0 := fun h => by rw [h, zero_re] at hre; exact lt_irrefl 0 hre
    rw [psi1_add_inv hu0]
    simp only [analyticOrderNatAt, ordem_zeta1 hu1]
  refine ⟨S, fun u => ?_, ?_⟩
  · rw [hSdef, Finset.mem_filter, hS₀, zeta1_eq_zero_iff]
    constructor
    · rintro ⟨⟨hR, _, hζ⟩, hre⟩
      exact ⟨hR, hζ, hre⟩
    · rintro ⟨hR, hζ, hre⟩
      refine ⟨⟨hR, ?_, hζ⟩, hre⟩
      rintro rfl
      exact riemannZeta_one_ne_zero hζ
  · rw [bordo_congr heq, bordo_add hc1 hQ, bordo_const_mul, hpol, bordo_add hQ1 hQ2,
      bordo_cauchy hQd, bordo_add hQ2a hQ2b, bordo_const_mul, bordo_const_mul, hb1, hb0, hsplit,
      hsum1, hsum2, logDeriv_zeta1_zero, Finset.sum_neg_distrib]
    ring

/-- Alturas boas (rodada 66): `∀ T₀ ≥ 6, ∃ T ∈ [T₀, T₀ + 1]` sem zeros de `ζ` nas horizontais `Im s = ±T`. -/
theorem horizontais_boas (T₀ : ℝ) (hT₀ : 6 ≤ T₀) : ∃ T : ℝ, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧
    ∀ s : ℂ, 0 < s.re → s.re < 1 → (s.im = -T ∨ s.im = T) → riemannZeta s ≠ 0 := by
  obtain ⟨_, _, hC⟩ := ATK.ZeroClasses.Explicita.altura_boa
  obtain ⟨T, h1, h2, hT⟩ := hC T₀ hT₀
  refine ⟨T, h1, h2, fun s h0 hs1 him => ?_⟩
  have hτ : s.im = T ∨ s.im = -T := him.symm
  have := (hT s.re h0 (by linarith) s.im hτ).1
  rwa [Complex.re_add_im] at this

end ATK.ZeroClasses.FormulaExplicita

#print axioms ATK.ZeroClasses.FormulaExplicita.principio_polo
#print axioms ATK.ZeroClasses.FormulaExplicita.zeta1_eq
#print axioms ATK.ZeroClasses.FormulaExplicita.zeta1_an
#print axioms ATK.ZeroClasses.FormulaExplicita.zeta1_eq_zero_iff
#print axioms ATK.ZeroClasses.FormulaExplicita.zeta1_zero
#print axioms ATK.ZeroClasses.FormulaExplicita.ev_zeta1
#print axioms ATK.ZeroClasses.FormulaExplicita.ordem_zeta1
#print axioms ATK.ZeroClasses.FormulaExplicita.ordem_zeta1_ne_top
#print axioms ATK.ZeroClasses.FormulaExplicita.logDeriv_zeta1
#print axioms ATK.ZeroClasses.FormulaExplicita.logDeriv_zeta1_zero
#print axioms ATK.ZeroClasses.FormulaExplicita.triv_re
#print axioms ATK.ZeroClasses.FormulaExplicita.triv_im
#print axioms ATK.ZeroClasses.FormulaExplicita.deriv_trivial
#print axioms ATK.ZeroClasses.FormulaExplicita.ordem_trivial
#print axioms ATK.ZeroClasses.FormulaExplicita.cpow_diff
#print axioms ATK.ZeroClasses.FormulaExplicita.dslope_diff
#print axioms ATK.ZeroClasses.FormulaExplicita.psi1_add_inv
#print axioms ATK.ZeroClasses.FormulaExplicita.bordo_largo
#print axioms ATK.ZeroClasses.FormulaExplicita.horizontais_boas
