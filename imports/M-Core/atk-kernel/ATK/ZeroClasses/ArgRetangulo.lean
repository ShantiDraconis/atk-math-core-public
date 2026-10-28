import ATK.ZeroClasses.StirlingComplexo

/-!
# O princípio do argumento em retângulos (rodada 40)

**Teorema** (`principio_argumento`). Seja `f` analítica num aberto `U` que contém o retângulo fechado `R` de cantos
`z`, `w`, sem zeros de ordem infinita em `R` e sem zeros no bordo. Então os zeros de `f` em `R` formam um conjunto
finito `S`, todos no interior, e

  `∮_{∂R} f′/f = 2πi · Σ_{u ∈ S} m_u`,

com a integral de bordo na convenção de `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (`bordo`). A
Mathlib tem o teorema de Cauchy em retângulos, mas não o princípio do argumento. A prova:

1. `bordo_inv`: `∮_{∂R} ds/(s − u) = 2πi` para `u` interior. Cada lado é uma primitiva explícita: `log(s − u)` na
   base, no topo e no lado direito, e `log(u − s)` no lado esquerdo. A soma é `2πi` porque `log(−x) = log x ∓ πi`
   conforme `Im x ≷ 0` (`log_neg_im_pos`, `log_neg_im_neg`);
2. linearidade do bordo (`bordo_add`, `bordo_sum`, `bordo_const_mul`, `bordo_congr`) e Cauchy (`bordo_cauchy`);
3. o quociente local da rodada 36: `f = Q·G` com `Q = ∏_{u ∈ S}(s − u)^{m_u}` e `G` sem zeros em `R`, logo
   `f′/f = Σ m_u/(s − u) + G′/G` no bordo e `∮ G′/G = 0`.

Classificação (rodada 40): **ferramenta** — o segundo ingrediente de Riemann–von Mangoldt. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real Interval

namespace ATK.ZeroClasses.ArgRetangulo

/-- O retângulo fechado de cantos `z` e `w`. -/
def Ret (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- O bordo do retângulo. -/
def Bordo (z w : ℂ) : Set ℂ :=
  {p | p ∈ Ret z w ∧ (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im)}

/-- A integral no bordo (convenção de `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`). -/
noncomputable def bordo (g : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, g (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, g (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, g (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, g (z.re + y * I)

/-! ## 1. Os quatro lados -/

theorem lado_inf {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) : (x : ℂ) + z.im * I ∈ Bordo z w :=
  ⟨mem_reProdIm.mpr ⟨by simpa using hx, by simp⟩, Or.inr (Or.inr (Or.inl (by simp)))⟩

theorem lado_sup {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) : (x : ℂ) + w.im * I ∈ Bordo z w :=
  ⟨mem_reProdIm.mpr ⟨by simpa using hx, by simp⟩, Or.inr (Or.inr (Or.inr (by simp)))⟩

theorem lado_dir {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) : (w.re : ℂ) + y * I ∈ Bordo z w :=
  ⟨mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩, Or.inr (Or.inl (by simp))⟩

theorem lado_esq {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) : (z.re : ℂ) + y * I ∈ Bordo z w :=
  ⟨mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩, Or.inl (by simp)⟩

theorem int_inf {g : ℂ → ℂ} {z w : ℂ} (hg : ContinuousOn g (Bordo z w)) :
    IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) MeasureTheory.volume z.re w.re :=
  (hg.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + z.im * I).continuousOn
    fun _ hx => lado_inf hx).intervalIntegrable

theorem int_sup {g : ℂ → ℂ} {z w : ℂ} (hg : ContinuousOn g (Bordo z w)) :
    IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) MeasureTheory.volume z.re w.re :=
  (hg.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + w.im * I).continuousOn
    fun _ hx => lado_sup hx).intervalIntegrable

theorem int_dir {g : ℂ → ℂ} {z w : ℂ} (hg : ContinuousOn g (Bordo z w)) :
    IntervalIntegrable (fun y : ℝ => g (w.re + y * I)) MeasureTheory.volume z.im w.im :=
  (hg.comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + y * I).continuousOn
    fun _ hy => lado_dir hy).intervalIntegrable

theorem int_esq {g : ℂ → ℂ} {z w : ℂ} (hg : ContinuousOn g (Bordo z w)) :
    IntervalIntegrable (fun y : ℝ => g (z.re + y * I)) MeasureTheory.volume z.im w.im :=
  (hg.comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + y * I).continuousOn
    fun _ hy => lado_esq hy).intervalIntegrable

/-! ## 2. Linearidade e Cauchy -/

theorem bordo_congr {g₁ g₂ : ℂ → ℂ} {z w : ℂ} (h : EqOn g₁ g₂ (Bordo z w)) :
    bordo g₁ z w = bordo g₂ z w := by
  unfold bordo
  rw [intervalIntegral.integral_congr (fun x hx => h (lado_inf hx)),
    intervalIntegral.integral_congr (fun x hx => h (lado_sup hx)),
    intervalIntegral.integral_congr (fun y hy => h (lado_dir hy)),
    intervalIntegral.integral_congr (fun y hy => h (lado_esq hy))]

theorem bordo_add {g₁ g₂ : ℂ → ℂ} {z w : ℂ} (h₁ : ContinuousOn g₁ (Bordo z w))
    (h₂ : ContinuousOn g₂ (Bordo z w)) :
    bordo (fun s => g₁ s + g₂ s) z w = bordo g₁ z w + bordo g₂ z w := by
  unfold bordo
  rw [intervalIntegral.integral_add (int_inf h₁) (int_inf h₂),
    intervalIntegral.integral_add (int_sup h₁) (int_sup h₂),
    intervalIntegral.integral_add (int_dir h₁) (int_dir h₂),
    intervalIntegral.integral_add (int_esq h₁) (int_esq h₂)]
  simp only [smul_eq_mul]
  ring

theorem bordo_sum {ι : Type*} (S : Finset ι) (g : ι → ℂ → ℂ) {z w : ℂ}
    (hg : ∀ i ∈ S, ContinuousOn (g i) (Bordo z w)) :
    bordo (fun s => ∑ i ∈ S, g i s) z w = ∑ i ∈ S, bordo (g i) z w := by
  unfold bordo
  rw [intervalIntegral.integral_finsetSum (fun i hi => int_inf (hg i hi)),
    intervalIntegral.integral_finsetSum (fun i hi => int_sup (hg i hi)),
    intervalIntegral.integral_finsetSum (fun i hi => int_dir (hg i hi)),
    intervalIntegral.integral_finsetSum (fun i hi => int_esq (hg i hi))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.smul_sum]

theorem bordo_const_mul (c : ℂ) (g : ℂ → ℂ) (z w : ℂ) :
    bordo (fun s => c * g s) z w = c * bordo g z w := by
  unfold bordo
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- **Cauchy em retângulos** (Mathlib). -/
theorem bordo_cauchy {g : ℂ → ℂ} {z w : ℂ} (hg : DifferentiableOn ℂ g (Ret z w)) : bordo g z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn g z w hg

/-! ## 3. O núcleo: `∮ ds/(s − u) = 2πi` -/

theorem log_neg_im_pos {x : ℂ} (h : 0 < x.im) : log (-x) = log x - π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos h]

theorem log_neg_im_neg {x : ℂ} (h : x.im < 0) : log (-x) = log x + π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_add_pi_of_im_neg h]

theorem bordo_inv {z w u : ℂ} (h1 : z.re < u.re) (h2 : u.re < w.re) (h3 : z.im < u.im) (h4 : u.im < w.im) :
    bordo (fun s => (s - u)⁻¹) z w = 2 * π * I := by
  have hb : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - u)⁻¹ =
      log (w.re + z.im * I - u) - log (z.re + z.im * I - u) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => log ((x : ℂ) + z.im * I - u))
      (f' := fun x : ℝ => ((x : ℂ) + z.im * I - u)⁻¹)
    · intro x _
      have hs : (x : ℂ) + z.im * I - u ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inr (by simp; linarith))
      have hd : HasDerivAt (fun x : ℝ => (x : ℂ) + z.im * I - u) 1 x := by
        simpa using ((hasDerivAt_id x).ofReal_comp.add_const ((z.im : ℂ) * I)).sub_const u
      simpa using hd.clog_real hs
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.inv₀ (by fun_prop) fun x _ h => ?_
      have := congrArg Complex.im h
      simp at this
      linarith
  have ht : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - u)⁻¹ =
      log (w.re + w.im * I - u) - log (z.re + w.im * I - u) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => log ((x : ℂ) + w.im * I - u))
      (f' := fun x : ℝ => ((x : ℂ) + w.im * I - u)⁻¹)
    · intro x _
      have hs : (x : ℂ) + w.im * I - u ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inr (by simp; linarith))
      have hd : HasDerivAt (fun x : ℝ => (x : ℂ) + w.im * I - u) 1 x := by
        simpa using ((hasDerivAt_id x).ofReal_comp.add_const ((w.im : ℂ) * I)).sub_const u
      simpa using hd.clog_real hs
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.inv₀ (by fun_prop) fun x _ h => ?_
      have := congrArg Complex.im h
      simp at this
      linarith
  have hr : ∫ y : ℝ in z.im..w.im, I * ((w.re : ℂ) + y * I - u)⁻¹ =
      log (w.re + w.im * I - u) - log (w.re + z.im * I - u) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => log ((w.re : ℂ) + y * I - u))
      (f' := fun y : ℝ => I * ((w.re : ℂ) + y * I - u)⁻¹)
    · intro y _
      have hs : (w.re : ℂ) + y * I - u ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
      have hd : HasDerivAt (fun y : ℝ => (w.re : ℂ) + y * I - u) I y := by
        simpa using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (w.re : ℂ)).sub_const u
      have := hd.clog_real hs
      simpa [div_eq_mul_inv] using this
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun y _ h => ?_)
      have := congrArg Complex.re h
      simp at this
      linarith
  have hl : ∫ y : ℝ in z.im..w.im, I * ((z.re : ℂ) + y * I - u)⁻¹ =
      log (u - (z.re + w.im * I)) - log (u - (z.re + z.im * I)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => log (u - ((z.re : ℂ) + y * I)))
      (f' := fun y : ℝ => I * ((z.re : ℂ) + y * I - u)⁻¹)
    · intro y _
      have hs : u - ((z.re : ℂ) + y * I) ∈ slitPlane :=
        mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
      have hd : HasDerivAt (fun y : ℝ => u - ((z.re : ℂ) + y * I)) (-I) y := by
        simpa using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (z.re : ℂ)).const_sub u
      have hne : (z.re : ℂ) + y * I - u ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hne' : u - ((z.re : ℂ) + y * I) ≠ 0 := by
        intro h
        exact hne (by rw [← neg_sub, h, neg_zero])
      have e : -I / (u - ((z.re : ℂ) + y * I)) = I * ((z.re : ℂ) + y * I - u)⁻¹ := by
        rw [show (z.re : ℂ) + y * I - u = -(u - ((z.re : ℂ) + y * I)) by ring, inv_neg, div_eq_mul_inv]
        ring
      have := hd.clog_real hs
      rw [e] at this
      exact this
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun y _ h => ?_)
      have := congrArg Complex.re h
      simp at this
      linarith
  unfold bordo
  simp only [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  rw [hb, ht, hr, hl]
  have e1 : log (u - ((z.re : ℂ) + w.im * I)) = log ((z.re : ℂ) + w.im * I - u) - π * I := by
    rw [show u - ((z.re : ℂ) + w.im * I) = -((z.re : ℂ) + w.im * I - u) by ring]
    exact log_neg_im_pos (by simp; linarith)
  have e2 : log (u - ((z.re : ℂ) + z.im * I)) = log ((z.re : ℂ) + z.im * I - u) + π * I := by
    rw [show u - ((z.re : ℂ) + z.im * I) = -((z.re : ℂ) + z.im * I - u) by ring]
    exact log_neg_im_neg (by simp; linarith)
  rw [e1, e2]
  ring

/-! ## 4. O princípio do argumento -/

/-- **O princípio do argumento em retângulos**: `∮_{∂R} f′/f = 2πi Σ_{u ∈ S} m_u`, `S` = os zeros de `f` em `R`
(todos interiores). -/
theorem principio_argumento {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im) (hK : Ret z w ⊆ U)
    (htop : ∀ p ∈ Ret z w, analyticOrderAt f p ≠ ⊤) (hbd : ∀ p ∈ Bordo z w, f p ≠ 0) :
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ u ∈ Ret z w ∧ f u = 0) ∧
      bordo (logDeriv f) z w = 2 * π * I * ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) := by
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
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hm
  set Q : ℂ → ℂ := fun s => ∏ u ∈ S, (s - u) ^ m u with hQ
  have hQan : AnalyticOnNhd ℂ Q univ := fun s _ => by simp only [hQ]; fun_prop
  have hordQ : ∀ p, analyticOrderAt Q p = if p ∈ S then (m p : ℕ∞) else 0 := fun p =>
    ATK.ZeroClasses.Landau.ordem_poli S m p
  have hmw : ∀ p ∈ S, (m p : ℕ∞) = analyticOrderAt f p := by
    intro p hp
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (htop p ((hmemS p).mp hp).1)
    simp only [hm, analyticOrderNatAt, ← hk]
    simp
  have hle : ∀ p ∈ U, analyticOrderAt Q p ≤ analyticOrderAt f p := by
    intro p _
    rw [hordQ]
    split_ifs with h
    · rw [hmw p h]
    · simp
  have htopQ : ∀ p ∈ U, analyticOrderAt Q p ≠ ⊤ := by
    intro p _
    rw [hordQ]
    split_ifs <;> simp
  obtain ⟨G, hGan, hfQG, hG0⟩ := ATK.ZeroClasses.Landau.quociente_local hU hf
    (hQan.mono (subset_univ _)) hle htopQ
  have hGne : ∀ p ∈ Ret z w, G p ≠ 0 := by
    intro p hp
    apply hG0 p (hK hp)
    rw [hordQ]
    split_ifs with h
    · exact (hmw p h).symm
    · have hfp : f p ≠ 0 := fun h' => h ((hmemS p).mpr ⟨hp, h'⟩)
      exact analyticOrderAt_eq_zero.mpr (Or.inr hfp)
  have hlogf : EqOn (logDeriv f) (fun s => ∑ u ∈ S, (m u : ℂ) * (s - u)⁻¹ + logDeriv G s)
      (Bordo z w) := by
    intro p hp
    have hpS : p ∉ S := fun h => hbd p hp ((hmemS p).mp h).2
    have hpU : p ∈ U := hK hp.1
    have hev : f =ᶠ[𝓝 p] fun s => Q s * G s := by
      filter_upwards [hU.mem_nhds hpU] with s hs
      exact hfQG s hs
    have hQp : Q p ≠ 0 := by
      simp only [hQ]
      rw [Finset.prod_ne_zero_iff]
      intro u hu
      exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hpS (h ▸ hu))
    rw [(logDeriv_congr_nhds hev).self_of_nhds]
    change logDeriv (Q * G) p = _
    rw [logDeriv_mul p hQp (hGne p hp.1) (hQan p (mem_univ _)).differentiableAt
      (hGan p hpU).differentiableAt, ATK.ZeroClasses.Landau.logDeriv_poli S m hpS]
    simp only [div_eq_mul_inv]
  have hcont1 : ∀ u ∈ S, ContinuousOn (fun s => (m u : ℂ) * (s - u)⁻¹) (Bordo z w) := by
    intro u hu
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun p hp h => ?_)
    have hpu : p = u := sub_eq_zero.mp h
    exact hbd p hp (hpu ▸ ((hmemS u).mp hu).2)
  have hcontG : ContinuousOn (logDeriv G) (Bordo z w) := by
    intro p hp
    have hpU := hK hp.1
    exact ((hGan p hpU).deriv.continuousAt.div (hGan p hpU).continuousAt (hGne p hp.1)).continuousWithinAt
  rw [bordo_congr hlogf,
    bordo_add (g₁ := fun s => ∑ u ∈ S, (m u : ℂ) * (s - u)⁻¹) (continuousOn_finsetSum S hcont1) hcontG,
    bordo_sum S (fun u s => (m u : ℂ) * (s - u)⁻¹) hcont1]
  have hGz : bordo (logDeriv G) z w = 0 := bordo_cauchy fun p hp => by
    have hpU := hK hp
    exact ((hGan p hpU).deriv.differentiableAt.div (hGan p hpU).differentiableAt
      (hGne p hp)).differentiableWithinAt
  rw [hGz, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨a1, a2, a3, a4⟩ := hint u hu
  rw [bordo_const_mul, bordo_inv a1 a2 a3 a4]
  ring

end ATK.ZeroClasses.ArgRetangulo

#print axioms ATK.ZeroClasses.ArgRetangulo.lado_inf
#print axioms ATK.ZeroClasses.ArgRetangulo.lado_sup
#print axioms ATK.ZeroClasses.ArgRetangulo.lado_dir
#print axioms ATK.ZeroClasses.ArgRetangulo.lado_esq
#print axioms ATK.ZeroClasses.ArgRetangulo.int_inf
#print axioms ATK.ZeroClasses.ArgRetangulo.int_sup
#print axioms ATK.ZeroClasses.ArgRetangulo.int_dir
#print axioms ATK.ZeroClasses.ArgRetangulo.int_esq
#print axioms ATK.ZeroClasses.ArgRetangulo.bordo_congr
#print axioms ATK.ZeroClasses.ArgRetangulo.bordo_add
#print axioms ATK.ZeroClasses.ArgRetangulo.bordo_sum
#print axioms ATK.ZeroClasses.ArgRetangulo.bordo_const_mul
#print axioms ATK.ZeroClasses.ArgRetangulo.bordo_cauchy
#print axioms ATK.ZeroClasses.ArgRetangulo.log_neg_im_pos
#print axioms ATK.ZeroClasses.ArgRetangulo.log_neg_im_neg
#print axioms ATK.ZeroClasses.ArgRetangulo.bordo_inv
#print axioms ATK.ZeroClasses.ArgRetangulo.principio_argumento
