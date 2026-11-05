import ATK.ZeroClasses.LogDerivZeta
import ATK.ZeroClasses.LittlewoodMu
import ATK.PerronSuave

/-!
# A soma de Chebyshev suavizada: `Σ_{n ≤ x} Λ(n)(1 − n/x) = x/2 + O(x log x · e^{−c√log x})` (rodada 53)

Segunda peça do teorema dos números primos com o erro de de la Vallée Poussin.

1. **Perron suavizado em `Re s = c`** (`perron_kk_c`): `(1/2π)∫ u^{−(c+iy)} K(c+iy) dy = (1 − u)₊` para `c > 0`,
   com `K(s) = 1/(s(s+1))` (inversão de Mellin da Mathlib), e daí, para `c > 1`,
   `Σ_{n ≤ x} Λ(n)(1 − n/x) = (1/2π) ∫ x^{c+iy} (−ζ′/ζ)(c + iy) K(c + iy) dy`   (`Ssm_eq_integral`);
2. **o resíduo** (`bordo_f`): no retângulo `[σ₁, c] × [−T, T]` sem zeros de `ζ`, `∮ x^s(−ζ′/ζ)(s)K(s) ds = πi x`
   (o polo de `−ζ′/ζ` em `s = 1` tem resíduo 1 e `K(1) = 1/2`), pela decomposição
   `ζ′/ζ = G′/G − 1/(s − 1)` com `G(s) = (s − 1)ζ(s)` (`logDeriv_eq_Gp`);
3. **as cotas** dos três lados e da cauda `|y| > T` com `|ζ′/ζ| = O(log² T)` (rodada 52) e a escolha
   `c = 1 + 1/log x`, `T = e^{√log x}` (`chebyshev_suave`).

Classificação (rodada 53): **ferramenta** (a forma suavizada do TNP com erro; a passagem a `ψ(x)` vem a seguir).
RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.PNT

open ATK.PerronSuave (kk KK continuous_kk kk_of_le_one kk_of_one_le kk_nonneg kk_le_one mellin_kk
  mellinConvergent_kk norm_KK norm_KK_le continuous_KK_line integrable_KK_line cpow_quociente)

/-! ## 1. Perron suavizado para `Λ` -/

/-- **Perron (inversão de Mellin) na reta `Re s = c`**: `(1/2π)∫ u^{−(c+iy)} K(c+iy) dy = k(u)`. -/
theorem perron_kk_c {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) * KK (c + y * I) = kk x := by
  have hm : 0 < min c 1 := lt_min hc one_pos
  have hint : Integrable (fun y : ℝ => KK (c + y * I)) :=
    integrable_KK_line (σ := c) (m := min c 1) hm (min_le_right _ _)
      (by rw [abs_of_pos hc]; exact min_le_left _ _) (by rw [abs_of_pos (by linarith)]; linarith)
  have hcre : 0 < ((c : ℂ)).re := by simpa using hc
  have hinv := mellinInv_mellin_eq (σ := c) (f := fun u => ((kk u : ℝ) : ℂ)) hx
    (mellinConvergent_kk hcre) ?_ (continuous_ofReal.comp continuous_kk).continuousAt
  · unfold mellinInv at hinv
    rw [Complex.real_smul] at hinv
    rw [← hinv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [mellin_kk (by simpa using hc)]
  · show Integrable (fun y : ℝ => mellin (fun u => ((kk u : ℝ) : ℂ)) ((c : ℂ) + y * I))
    refine hint.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [mellin_kk (by simpa using hc)]

theorem integrable_KK_c {c : ℝ} (hc : 0 < c) : Integrable (fun y : ℝ => KK (c + y * I)) :=
  integrable_KK_line (σ := c) (m := min c 1) (lt_min hc one_pos) (min_le_right _ _)
    (by rw [abs_of_pos hc]; exact min_le_left _ _) (by rw [abs_of_pos (by linarith)]; linarith)

theorem continuous_KK_c {c : ℝ} (hc : 0 < c) : Continuous (fun y : ℝ => KK (c + y * I)) :=
  continuous_KK_line hc.ne' (by linarith)

/-- `Λ` como coeficiente complexo. -/
noncomputable def vM (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

/-- A soma de Chebyshev suavizada `Σ_{n ≤ x} Λ(n)(1 − n/x)`. -/
noncomputable def Ssm (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n * kk (n / x)

theorem LSeries_vM {s : ℂ} (hs : 1 < s.re) : LSeries vM s = -logDeriv riemannZeta s := by
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  unfold vM
  rw [h, logDeriv_apply]
  ring

/-- O termo `n` como integral na reta `Re = c`. -/
theorem integral_termo {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    ∫ y : ℝ, (x : ℂ) ^ ((c : ℂ) + y * I) * LSeries.term vM ((c : ℂ) + y * I) n * KK (c + y * I) =
      ((2 * π : ℝ) : ℂ) * (vM n * (kk (n / x) : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vM]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hu : (0 : ℝ) < (n : ℝ) / x := by positivity
  have hP := perron_kk_c hc hu
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hpt : ∀ y : ℝ, (x : ℂ) ^ ((c : ℂ) + y * I) * LSeries.term vM ((c : ℂ) + y * I) n * KK (c + y * I) =
      vM n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) * KK (c + y * I)) := by
    intro y
    rw [LSeries.term_of_ne_zero hn.ne', cpow_quociente hnr hx]
    have e1 : ((n : ℝ) : ℂ) = (n : ℂ) := by norm_cast
    rw [e1, Complex.cpow_neg, Complex.cpow_neg, inv_inv]
    have h1 : (n : ℂ) ^ ((c : ℂ) + y * I) ≠ 0 := fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    field_simp
  rw [integral_congr_ae (Eventually.of_forall hpt), MeasureTheory.integral_const_mul]
  have h2pi : ((2 * π : ℝ) : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul]; field_simp; simp
  have hI : ∫ y : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) * KK (c + y * I) =
      ((2 * π : ℝ) : ℂ) * (kk ((n : ℝ) / x) : ℂ) := by
    rw [← hP, ← mul_assoc, h2pi, one_mul]
  rw [hI]
  ring

/-- **Perron suavizado para `Λ`**: para `x ≥ 1` e `c > 1`,
`Σ_{n ≤ x} Λ(n)(1 − n/x) = (1/2π) ∫ x^{c+iy} L(Λ, c + iy) K(c + iy) dy`. -/
theorem Ssm_eq_integral {x c : ℝ} (hx : 1 ≤ x) (hc : 1 < c) :
    ((Ssm x : ℝ) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) *
      ∫ y : ℝ, (x : ℂ) ^ ((c : ℂ) + y * I) * LSeries vM ((c : ℂ) + y * I) * KK (c + y * I) := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by linarith
  set g : ℕ → ℝ → ℂ := fun n y =>
    (x : ℂ) ^ ((c : ℂ) + y * I) * LSeries.term vM ((c : ℂ) + y * I) n * KK (c + y * I) with hgdef
  have hK := integrable_KK_c hc0
  have hcre : 1 < ((c : ℂ)).re := by simpa using hc
  have hLs : LSeriesSummable vM (c : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hcre
  have hnorm : ∀ n y, ‖g n y‖ = x ^ c * ‖LSeries.term vM (c : ℂ) n‖ * ‖KK (c + y * I)‖ := by
    intro n y
    simp only [hgdef, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hint : ∀ n, Integrable (g n) := by
    intro n
    have hc' : Continuous (fun y : ℝ => g n y) := by
      simp only [hgdef]
      refine ((Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx0.ne'))).mul ?_).mul
        (continuous_KK_c hc0)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [LSeries.term_zero]; exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn.ne']
        refine continuous_const.div (Continuous.const_cpow (by fun_prop)
          (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))) (fun y => ?_)
        exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
          intro h; have := congrArg Complex.re h; simp at this; linarith)).mpr
          (Nat.cast_ne_zero.mpr hn.ne')
    refine (hK.norm.const_mul (x ^ c * ‖LSeries.term vM (c : ℂ) n‖)).mono' hc'.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [hnorm n y]
  have hsum : Summable (fun n => ∫ y, ‖g n y‖) := by
    have hs := (hLs.norm.mul_left (x ^ c * ∫ y : ℝ, ‖KK (c + y * I)‖))
    refine hs.congr fun n => ?_
    simp_rw [hnorm n]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hpt : ∀ y : ℝ, ∑' n, g n y =
      (x : ℂ) ^ ((c : ℂ) + y * I) * LSeries vM ((c : ℂ) + y * I) * KK (c + y * I) := by
    intro y
    simp only [hgdef]
    rw [tsum_mul_right, tsum_mul_left, LSeries]
  have hfin : ∑' n, ∫ y, g n y = ((2 * π : ℝ) : ℂ) * ((Ssm x : ℝ) : ℂ) := by
    simp only [hgdef]
    simp_rw [integral_termo hx0 hc0]
    rw [tsum_mul_left, Ssm]
    congr 1
    rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊ + 1)) (fun n hn => ?_)]
    · push_cast
      rfl
    · rw [Finset.mem_range, not_lt] at hn
      have h1 : 1 ≤ (n : ℝ) / x := by
        rw [le_div_iff₀ hx0, one_mul]
        have := Nat.lt_floor_add_one x
        have hn' : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
        push_cast at hn'
        linarith
      rw [kk_of_one_le h1]
      simp
  rw [← funext hpt, ← hswap, hfin, ← mul_assoc, ← ofReal_mul]
  have : 1 / (2 * π) * (2 * π) = 1 := by field_simp
  rw [this, ofReal_one, one_mul]


/-! ## 2. A derivada logarítmica e a região do contorno -/

open ATK.ZeroClasses.RegiaoLivre (Gp Gp_diff Gp_eq Gp_ne_zero polo re_lt_um)
open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_cauchy bordo_inv
  bordo_const_mul)

/-- `ζ′/ζ = G′/G − 1/(s − 1)` onde `ζ ≠ 0`, `G(s) = (s − 1)ζ(s)`. -/
theorem logDeriv_eq_Gp {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv Gp s - 1 / (s - 1) := by
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ne
  have hev : Gp =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [hU.mem_nhds ⟨hs, hs1⟩] with z hz
    exact Gp_eq hz.1 hz.2
  rw [(logDeriv_congr_nhds hev).self_of_nhds]
  change logDeriv riemannZeta s = logDeriv ((fun z : ℂ => z - 1) * riemannZeta) s - 1 / (s - 1)
  rw [logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s (sub_ne_zero.mpr hs1) hz
      (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)]
  have : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  rw [this]
  ring

/-- Os zeros com `|Im s| ≤ A` e `Re s > 0` ficam em `Re s ≤ 1 − η`. -/
theorem zeros_compacto (A : ℝ) : ∃ η > 0, η ≤ 1 ∧ ∀ s : ℂ, riemannZeta s = 0 → |s.im| ≤ A → 0 < s.re →
    s.re ≤ 1 - η := by
  set F : Set ℂ := closedBall (0 : ℂ) (|A| + 1) ∩ riemannZetaZeros ∩ {s | 0 < s.re} with hF
  have hfin : F.Finite :=
    ((isCompact_closedBall (0 : ℂ) (|A| + 1)).inter_riemannZetaZeros_finite).subset inter_subset_left
  have hmem : ∀ s : ℂ, riemannZeta s = 0 → |s.im| ≤ A → 0 < s.re → s ∈ F := by
    intro s hs hA h0
    refine ⟨⟨?_, hs⟩, h0⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 := re_lt_um hs
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos h0] at h
    have : A ≤ |A| := le_abs_self A
    linarith
  rcases F.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, le_rfl, fun s hs hA h0 => ?_⟩
    have := hmem s hs hA h0
    rw [he] at this
    exact absurd this (Set.notMem_empty s)
  · obtain ⟨ρ₀, hρ₀, hmax⟩ := Set.exists_max_image F (fun ρ => ρ.re) hfin hne
    have hρ1 : ρ₀.re < 1 := re_lt_um hρ₀.1.2
    have hρ0 : 0 < ρ₀.re := hρ₀.2
    refine ⟨1 - ρ₀.re, by linarith, by linarith, fun s hs hA h0 => ?_⟩
    have := hmax s (hmem s hs hA h0)
    linarith

/-- **A região do contorno**: existem `c₁ > 0`, `T₀ ≥ 3` e `C ≥ 0` tais que, para `T ≥ T₀` e `s ≠ 1` com
`1 − c₁/log T ≤ Re s ≤ 2` e `|Im s| ≤ T`: `ζ(s) ≠ 0` e `|ζ′/ζ(s) + 1/(s − 1)| ≤ C log² T`. -/
theorem regiao_contorno : ∃ c₁ > 0, ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ s : ℂ,
    1 - c₁ / Real.log T ≤ s.re → s.re ≤ 2 → |s.im| ≤ T → s ≠ 1 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s + 1 / (s - 1)‖ ≤ C * Real.log T ^ 2 := by
  obtain ⟨c, hc, T₁, hT₁, CL, hCL, hL⟩ := ATK.ZeroClasses.LogDerivZeta.logDeriv_zeta_le
  obtain ⟨η, hη, hη1, hzc⟩ := zeros_compacto T₁
  -- o compacto `K = [1 − η/2, 2] × [−T₁, T₁]`
  set K : Set ℂ := Icc (1 - η / 2) 2 ×ℂ Icc (-T₁) T₁ with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKre : ∀ s ∈ K, 1 - η / 2 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ T₁ := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    exact ⟨h1.1, h1.2, abs_le.mpr ⟨h2.1, h2.2⟩⟩
  have hzK : ∀ s : ℂ, 1 - η / 2 ≤ s.re → |s.im| ≤ T₁ → riemannZeta s ≠ 0 := by
    intro s h1 h2 hz
    have := hzc s hz h2 (by linarith)
    linarith
  have hGK : ∀ s ∈ K, Gp s ≠ 0 := by
    intro s hs
    obtain ⟨h1, -, h2⟩ := hKre s hs
    by_cases hs1 : s = 1
    · rw [hs1]
      have := Gp_ne_zero (σ := 1) le_rfl
      simpa using this
    · rw [Gp_eq (by linarith) hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (hzK s h1 h2)
  have hV : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hGd : DifferentiableOn ℂ Gp {z : ℂ | z ≠ 0} := fun z hz => (Gp_diff hz).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv Gp) {z : ℂ | z ≠ 0} := hGd.deriv hV
  have hK0 : K ⊆ {z : ℂ | z ≠ 0} := by
    intro s hs h0
    have := (hKre s hs).1
    rw [h0, zero_re] at this
    linarith
  have hcont : ContinuousOn (logDeriv Gp) K := by
    have e : logDeriv Gp = fun z => deriv Gp z / Gp z := funext fun z => logDeriv_apply Gp z
    rw [e]
    exact (hdd.continuousOn.mono hK0).div (hGd.continuousOn.mono hK0) hGK
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨min c (η / 2), lt_min hc (by positivity), max T₁ 3, le_max_right _ _, CL + 1 + max C₁ 0,
    by positivity, fun T hT s hlo hhi him hs1 => ?_⟩
  have hT3 : 3 ≤ T := (le_max_right _ _).trans hT
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogT0 : 0 < Real.log T := by linarith
  have hsq : 1 ≤ Real.log T ^ 2 := one_le_pow₀ hlogT
  have hmin : min c (η / 2) / Real.log T ≤ η / 2 := by
    calc min c (η / 2) / Real.log T ≤ min c (η / 2) := div_le_self (le_min hc.le (by positivity)) hlogT
      _ ≤ η / 2 := min_le_right _ _
  rcases le_or_gt T₁ |s.im| with hbig | hsmall
  · -- `|Im s| ≥ T₁`
    have hlogs : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hlogsT : Real.log |s.im| ≤ Real.log T := Real.log_le_log (by linarith) him
    have hre : 1 - c / Real.log |s.im| ≤ s.re := by
      have h1 : min c (η / 2) / Real.log T ≤ c / Real.log T :=
        div_le_div_of_nonneg_right (min_le_left _ _) hlogT0.le
      have h2 : c / Real.log T ≤ c / Real.log |s.im| := div_le_div_of_nonneg_left hc.le hlogs hlogsT
      linarith
    obtain ⟨hz, hb⟩ := hL s hbig hre hhi
    refine ⟨hz, ?_⟩
    have hs1n : 1 ≤ ‖s - 1‖ := by
      have h := Complex.abs_im_le_norm (s - 1)
      rw [sub_im, one_im, sub_zero] at h
      linarith
    have hinv : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact div_le_one_of_le₀ hs1n (norm_nonneg _)
    have hb2 : CL * Real.log |s.im| ^ 2 ≤ CL * Real.log T ^ 2 := by
      gcongr
    calc ‖logDeriv riemannZeta s + 1 / (s - 1)‖ ≤ ‖logDeriv riemannZeta s‖ + ‖1 / (s - 1)‖ :=
          norm_add_le _ _
      _ ≤ CL * Real.log T ^ 2 + 1 := by linarith
      _ ≤ (CL + 1 + max C₁ 0) * Real.log T ^ 2 := by
          have := le_max_right C₁ 0
          nlinarith
  · -- `|Im s| < T₁`: o compacto
    have hsK : s ∈ K := by
      refine ⟨⟨by linarith, hhi⟩, ?_⟩
      exact ⟨by linarith [(abs_lt.mp hsmall).1], by linarith [(abs_lt.mp hsmall).2]⟩
    have hz : riemannZeta s ≠ 0 := hzK s (by linarith) hsmall.le
    refine ⟨hz, ?_⟩
    rw [logDeriv_eq_Gp (by linarith) hs1 hz, sub_add_cancel]
    have := hC₁ s hsK
    have hm := le_max_left C₁ 0
    have hm0 := le_max_right C₁ 0
    nlinarith

/-! ## 3. O resíduo no retângulo -/

/-- O integrando `f(s) = x^s (−ζ′/ζ)(s) K(s)`. -/
noncomputable def fx (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s * (-logDeriv riemannZeta s) * KK s

/-- `φ(s) = x^s K(s)`. -/
noncomputable def phx (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s * KK s

theorem phx_diff {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (phx x) s := by
  have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have h1 : s + 1 ≠ 0 := fun h => by
    have := congrArg re h; rw [add_re, one_re, zero_re] at this; linarith
  unfold phx KK
  exact (differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))).mul
    ((differentiableAt_const _).div (differentiableAt_id.mul (differentiableAt_id.add_const 1))
      (mul_ne_zero h0 h1))

theorem phx_one {x : ℝ} : phx x 1 = x / 2 := by
  unfold phx KK
  rw [cpow_one]
  norm_num
  ring

/-- **O resíduo**: `∮ x^s(−ζ′/ζ)(s)K(s) ds = πi x` no retângulo `[σ₁, c] × [−T, T]` onde `G ≠ 0`. -/
theorem bordo_fx {x σ₁ c T : ℝ} (hx : 0 < x) (hσ₁ : 0 < σ₁) (h1 : σ₁ < 1) (hc : 1 < c) (hT : 0 < T)
    (hG : ∀ s ∈ Ret ⟨σ₁, -T⟩ ⟨c, T⟩, Gp s ≠ 0) :
    bordo (fx x) ⟨σ₁, -T⟩ ⟨c, T⟩ = π * I * x := by
  set z : ℂ := ⟨σ₁, -T⟩ with hz
  set w : ℂ := ⟨c, T⟩ with hw
  have hRre : ∀ p ∈ Ret z w, σ₁ ≤ p.re := by
    intro p hp
    have h := (mem_reProdIm.mp hp).1
    change p.re ∈ [[σ₁, c]] at h
    rw [uIcc_of_le (by linarith)] at h
    exact h.1
  -- `φ` e `h = φ · G′/G` são holomorfas perto do retângulo
  have hU : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const continuous_re
  have h1U : (1 : ℂ) ∈ {p : ℂ | 0 < p.re} := by show (0 : ℝ) < (1 : ℂ).re; simp
  have hφd : DifferentiableOn ℂ (phx x) {p : ℂ | 0 < p.re} := fun p hp =>
    (phx_diff hx hp).differentiableWithinAt
  have hD : DifferentiableOn ℂ (dslope (phx x) 1) {p : ℂ | 0 < p.re} :=
    (differentiableOn_dslope (hU.mem_nhds h1U)).mpr hφd
  have hV : IsOpen {p : ℂ | p ≠ 0} := isOpen_ne
  have hGd : DifferentiableOn ℂ Gp {p : ℂ | p ≠ 0} := fun p hp => (Gp_diff hp).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv Gp) {p : ℂ | p ≠ 0} := hGd.deriv hV
  have hne0 : ∀ p ∈ Ret z w, p ≠ 0 := fun p hp h0 => by
    have := hRre p hp; rw [h0, zero_re] at this; linarith
  have hhd : DifferentiableOn ℂ (fun p => dslope (phx x) 1 p - phx x p * logDeriv Gp p) (Ret z w) := by
    intro p hp
    have hp0 : 0 < p.re := lt_of_lt_of_le hσ₁ (hRre p hp)
    have hpn := hne0 p hp
    have hl : DifferentiableAt ℂ (logDeriv Gp) p := by
      have e : logDeriv Gp = fun z => deriv Gp z / Gp z := funext fun z => logDeriv_apply Gp z
      rw [e]
      exact (hdd.differentiableAt (hV.mem_nhds hpn)).div (Gp_diff hpn) (hG p hp)
    exact ((hD.differentiableAt (hU.mem_nhds hp0)).sub ((phx_diff hx hp0).mul hl)).differentiableWithinAt
  have hne1 : ∀ p ∈ Bordo z w, p ≠ 1 := by
    rintro p ⟨_, h⟩ hp
    change p.re = σ₁ ∨ p.re = c ∨ p.im = -T ∨ p.im = T at h
    have hr : p.re = 1 := by rw [hp, one_re]
    have hi : p.im = 0 := by rw [hp, one_im]
    rcases h with h | h | h | h <;> linarith
  have heq : EqOn (fx x) (fun p => (dslope (phx x) 1 p - phx x p * logDeriv Gp p) +
      phx x 1 * (p - 1)⁻¹) (Bordo z w) := by
    intro p hp
    have hp1 := hne1 p hp
    have hpR : p ∈ Ret z w := hp.1
    have hp0 : 0 < p.re := lt_of_lt_of_le hσ₁ (hRre p hpR)
    have hzp : riemannZeta p ≠ 0 := by
      intro h0
      apply hG p hpR
      rw [Gp_eq hp0 hp1, h0, mul_zero]
    simp only [fx]
    rw [logDeriv_eq_Gp hp0 hp1 hzp, dslope_of_ne _ hp1, slope_def_field]
    have hs1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
    unfold phx
    field_simp
    ring
  have hBR : Bordo z w ⊆ Ret z w := fun p hp => hp.1
  have hc1 : ContinuousOn (fun p => dslope (phx x) 1 p - phx x p * logDeriv Gp p) (Bordo z w) :=
    (hhd.mono hBR).continuousOn
  have hc2 : ContinuousOn (fun p : ℂ => phx x 1 * (p - 1)⁻¹) (Bordo z w) := fun p hp =>
    (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr (hne1 p hp)))).continuousWithinAt
  rw [bordo_congr heq, bordo_add hc1 hc2, bordo_cauchy hhd, bordo_const_mul,
    bordo_inv (z := z) (w := w) (u := 1) (by simp [hz]; linarith) (by simp [hw]; linarith)
      (by simp [hz]; linarith) (by simp [hw]; linarith), phx_one]
  ring


/-! ## 4. As cotas -/

/-- A cauda `|y| > T`: `‖∫_ℝ f − ∫_{−T}^{T} f‖ ≤ 2B/T` se `‖f(y)‖ ≤ B/(1 + y²)`. -/
theorem cauda {f : ℝ → ℂ} {B T : ℝ} (hf : Integrable f) (hb : ∀ y, ‖f y‖ ≤ B * (1 + y ^ 2)⁻¹)
    (hT : 0 < T) : ‖(∫ y, f y) - ∫ y in (-T)..T, f y‖ ≤ 2 * B / T := by
  have hB : 0 ≤ B := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  have hs : MeasurableSet (Ioc (-T) T) := measurableSet_Ioc
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_add_compl hs hf, add_sub_cancel_left]
  have hg : Integrable (fun y : ℝ => B * (1 + y ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul B
  have h1 : ‖∫ y in (Ioc (-T) T)ᶜ, f y‖ ≤ ∫ y in (Ioc (-T) T)ᶜ, B * (1 + y ^ 2)⁻¹ :=
    norm_integral_le_of_norm_le hg.integrableOn (Eventually.of_forall hb)
  have h2 : ∫ y in (Ioc (-T) T)ᶜ, B * (1 + y ^ 2)⁻¹ = B * (π - 2 * Real.arctan T) := by
    have hc := integral_add_compl hs hg
    have htot : ∫ y, B * (1 + y ^ 2)⁻¹ = B * π := by
      rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
    rw [htot] at hc
    have hI : ∫ y in Ioc (-T) T, B * (1 + y ^ 2)⁻¹ = B * (2 * Real.arctan T) := by
      rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
        integral_inv_one_add_sq, Real.arctan_neg]
      ring
    rw [hI] at hc
    linarith
  have h3 : π - 2 * Real.arctan T ≤ 2 / T := by
    have e := Real.arctan_inv_of_pos hT
    have h := Real.arctan_le_self (inv_nonneg.mpr hT.le)
    rw [e] at h
    rw [div_eq_mul_inv]
    linarith
  calc ‖∫ y in (Ioc (-T) T)ᶜ, f y‖ ≤ B * (π - 2 * Real.arctan T) := h2 ▸ h1
    _ ≤ B * (2 / T) := by gcongr
    _ = 2 * B / T := by ring

theorem norm_KK_um {c y : ℝ} (hc : 1 ≤ c) : ‖KK (c + y * I)‖ ≤ (1 + y ^ 2)⁻¹ := by
  rw [norm_KK]
  have h1 : √(1 + y ^ 2) ≤ ‖((c : ℂ) + y * I)‖ := by
    refine ATK.PerronSuave.le_of_sq_le (by positivity) (norm_nonneg _) ?_
    rw [Real.sq_sqrt (by positivity), ATK.PerronSuave.sq_norm_line]
    nlinarith
  have h2 : √(1 + y ^ 2) ≤ ‖((c : ℂ) + y * I) + 1‖ := by
    have e : ((c : ℂ) + y * I) + 1 = ((c + 1 : ℝ) : ℂ) + y * I := by push_cast; ring
    rw [e]
    refine ATK.PerronSuave.le_of_sq_le (by positivity) (norm_nonneg _) ?_
    rw [Real.sq_sqrt (by positivity), ATK.PerronSuave.sq_norm_line]
    nlinarith
  have hs : 0 < √(1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hprod : 1 + y ^ 2 ≤ ‖((c : ℂ) + y * I)‖ * ‖((c : ℂ) + y * I) + 1‖ := by
    calc 1 + y ^ 2 = √(1 + y ^ 2) * √(1 + y ^ 2) := (Real.mul_self_sqrt (by positivity)).symm
      _ ≤ _ := mul_le_mul h1 h2 hs.le (norm_nonneg _)
  rw [one_div]
  exact inv_anti₀ (by positivity) hprod

/-- A série de von Mangoldt na reta `Re = c`: `‖ζ′/ζ(c + iy)‖ ≤ 1/(c − 1) + C_p`. -/
theorem norm_logDeriv_c {Cp : ℝ}
    (hpolo : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → (-(logDeriv riemannZeta σ)).re ≤ 1 / (σ - 1) + Cp)
    {c : ℝ} (hc : 1 < c) (hc2 : c ≤ 2) (y : ℝ) :
    ‖logDeriv riemannZeta (c + y * I)‖ ≤ 1 / (c - 1) + Cp :=
  (ATK.ZeroClasses.LogDerivZeta.norm_logDeriv_le hc y).trans (hpolo c hc hc2)

theorem continuous_logDeriv_c {c : ℝ} (hc : 1 < c) :
    Continuous (fun y : ℝ => logDeriv riemannZeta (c + y * I)) := by
  have hV : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hzd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv riemannZeta) {s : ℂ | s ≠ 1} := hzd.deriv hV
  have hne1 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg re h; simp at this; linarith
  have hz0 : ∀ y : ℝ, riemannZeta ((c : ℂ) + y * I) ≠ 0 := fun y =>
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hl : Continuous (fun y : ℝ => (c : ℂ) + y * I) := by fun_prop
  simp only [logDeriv_apply]
  refine Continuous.div ?_ ?_ hz0
  · refine continuous_iff_continuousAt.mpr fun y => ?_
    have h1 := (hdd.differentiableAt (hV.mem_nhds (hne1 y))).continuousAt
    exact h1.comp (f := fun y : ℝ => (c : ℂ) + y * I) hl.continuousAt
  · refine continuous_iff_continuousAt.mpr fun y => ?_
    have h1 := (differentiableAt_riemannZeta (hne1 y)).continuousAt
    exact h1.comp (f := fun y : ℝ => (c : ℂ) + y * I) hl.continuousAt

/-- **O erro explícito**: com `σ₁ = 1 − c₁/log T`,
`|Σ Λ(n)(1 − n/x) − x/2| ≤ (2B/T + ‖A‖ + ‖B'‖ + ‖D‖)/(2π)` com as cotas dos três lados. -/
theorem erro_explicito : ∃ c₁ > 0, ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ Cp : ℝ, 0 ≤ Cp ∧
    ∀ x c T : ℝ, 1 ≤ x → 1 < c → c ≤ 2 → T₀ ≤ T → c₁ / Real.log T ≤ 1 / 2 →
      |Ssm x - x / 2| ≤ (2 * (x ^ c * (1 / (c - 1) + Cp)) / T +
        2 * (x ^ c * (C * Real.log T ^ 2 + 1) * (4 * (1 + T ^ 2)⁻¹) * 2) +
        x ^ (1 - c₁ / Real.log T) * (C * Real.log T ^ 2 + Real.log T / c₁) * 4 * π) / (2 * π) := by
  obtain ⟨c₁, hc₁, T₀, hT₀, C, hC, hreg⟩ := regiao_contorno
  obtain ⟨Cp, hCp, hpolo⟩ := polo
  refine ⟨c₁, hc₁, T₀, hT₀, C, hC, Cp, hCp, fun x c T hx hc hc2 hT hσ => ?_⟩
  have hx0 : 0 < x := by linarith
  have hT3 : 3 ≤ T := hT₀.trans hT
  have hT0 : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogT0 : 0 < Real.log T := by linarith
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ℝ, σ₁ = 1 - c₁ / Real.log T := ⟨_, rfl⟩
  rw [← hσ₁]
  have hσ₁h : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσ₁1 : σ₁ < 1 := by rw [hσ₁]; have : 0 < c₁ / Real.log T := by positivity
                           linarith
  have hσ₁0 : 0 < σ₁ := by linarith
  have h1σ : 1 - σ₁ = c₁ / Real.log T := by rw [hσ₁]; ring
  -- a região: `G ≠ 0` no retângulo
  have hreg' : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 → |s.im| ≤ T → s ≠ 1 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s + 1 / (s - 1)‖ ≤ C * Real.log T ^ 2 :=
    fun s h1 h2 h3 h4 => hreg T hT s (by rw [← hσ₁]; exact h1) h2 h3 h4
  have hG : ∀ s ∈ Ret ⟨σ₁, -T⟩ ⟨c, T⟩, Gp s ≠ 0 := by
    intro s hs
    have h := mem_reProdIm.mp hs
    have hre := h.1
    have him := h.2
    change s.re ∈ [[σ₁, c]] at hre
    change s.im ∈ [[-T, T]] at him
    rw [uIcc_of_le (by linarith)] at hre
    rw [uIcc_of_le (by linarith)] at him
    by_cases hs1 : s = 1
    · rw [hs1]
      have := Gp_ne_zero (σ := 1) le_rfl
      simpa using this
    · rw [Gp_eq (by linarith [hre.1]) hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) (hreg' s hre.1 (by linarith [hre.2]) ?_ hs1).1
      exact abs_le.mpr ⟨him.1, him.2⟩
  -- a cota de `ζ′/ζ` num ponto da região
  have hld : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 → |s.im| ≤ T → s ≠ 1 →
      ‖logDeriv riemannZeta s‖ ≤ C * Real.log T ^ 2 + ‖1 / (s - 1)‖ := by
    intro s h1 h2 h3 h4
    have h := (hreg' s h1 h2 h3 h4).2
    have e : logDeriv riemannZeta s = (logDeriv riemannZeta s + 1 / (s - 1)) - 1 / (s - 1) := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith)
  -- Perron e o resíduo
  have hP := Ssm_eq_integral hx hc
  have hfx : ∀ y : ℝ, (x : ℂ) ^ ((c : ℂ) + y * I) * LSeries vM ((c : ℂ) + y * I) * KK (c + y * I) =
      fx x (c + y * I) := by
    intro y
    have hre : 1 < ((c : ℂ) + y * I).re := by simp; linarith
    rw [LSeries_vM hre, fx]
  simp_rw [hfx] at hP
  have hB := bordo_fx hx0 hσ₁0 hσ₁1 hc hT0 hG
  simp only [bordo, smul_eq_mul] at hB
  have hB' : (∫ u in σ₁..c, fx x (u + ((-T : ℝ) : ℂ) * I)) - (∫ u in σ₁..c, fx x (u + (T : ℂ) * I)) +
      I * (∫ y in (-T)..T, fx x ((c : ℂ) + y * I)) - I * (∫ y in (-T)..T, fx x ((σ₁ : ℂ) + y * I)) =
      2 * π * I * ((x / 2 : ℝ) : ℂ) := by
    rw [hB]; push_cast; ring
  have hres := ATK.ZeroClasses.LittlewoodMu.alg_res hB'
  -- integrabilidade na reta `Re = c`
  have hlc := continuous_logDeriv_c hc
  have hbc : ∀ y : ℝ, ‖fx x (c + y * I)‖ ≤ x ^ c * (1 / (c - 1) + Cp) * (1 + y ^ 2)⁻¹ := by
    intro y
    simp only [fx, norm_mul, norm_neg]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have e : ((c : ℂ) + y * I).re = c := by simp
    rw [e]
    have h1 := norm_logDeriv_c hpolo hc hc2 y
    have h2 := norm_KK_um (c := c) (y := y) hc.le
    have h3 : 0 ≤ x ^ c := Real.rpow_nonneg hx0.le c
    gcongr
  have hint : Integrable (fun y : ℝ => fx x (c + y * I)) := by
    refine ((integrable_inv_one_add_sq).const_mul (x ^ c * (1 / (c - 1) + Cp))).mono' ?_
      (Eventually.of_forall hbc)
    have hc0 : 0 < c := by linarith
    refine (Continuous.mul (Continuous.mul ?_ hlc.neg) (continuous_KK_c hc0)).aestronglyMeasurable
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx0.ne'))
  have htail := cauda hint hbc hT0
  -- as cotas dos lados
  have hKs : ∀ σ y : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → ‖KK (σ + y * I)‖ ≤ 4 * (1 + y ^ 2)⁻¹ := by
    intro σ y h1 h2
    have := norm_KK_le (σ := σ) (m := 1 / 2) (by norm_num) (by norm_num)
      (by rw [abs_of_pos (by linarith)]; exact h1) (by rw [abs_of_pos (by linarith)]; linarith) y
    rw [div_eq_mul_inv] at this
    calc ‖KK (σ + y * I)‖ ≤ 2 / (1 / 2) * (1 + y ^ 2)⁻¹ := this
      _ = 4 * (1 + y ^ 2)⁻¹ := by norm_num
  have hD : ‖∫ y in (-T)..T, fx x ((σ₁ : ℂ) + y * I)‖ ≤
      x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) * 4 * π := by
    have hb : ∀ y ∈ Ioc (-T) T, ‖fx x ((σ₁ : ℂ) + y * I)‖ ≤
        x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) * (4 * (1 + y ^ 2)⁻¹) := by
      intro y hy
      have hs1 : (σ₁ : ℂ) + y * I ≠ 1 := fun h => by
        have := congrArg re h; simp at this; linarith
      have hre : ((σ₁ : ℂ) + y * I).re = σ₁ := by simp
      have him : |((σ₁ : ℂ) + y * I).im| ≤ T := by
        rw [show ((σ₁ : ℂ) + y * I).im = y by simp]
        exact abs_le.mpr ⟨hy.1.le, hy.2⟩
      have hl := hld _ (by rw [hre]) (by rw [hre]; linarith) him hs1
      have hinv : ‖1 / ((σ₁ : ℂ) + y * I - 1)‖ ≤ Real.log T / c₁ := by
        rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))]
        have h := Complex.abs_re_le_norm ((σ₁ : ℂ) + y * I - 1)
        rw [show ((σ₁ : ℂ) + y * I - 1).re = σ₁ - 1 by simp] at h
        rw [abs_of_neg (by linarith), neg_sub, h1σ] at h
        calc (1 : ℝ) = Real.log T / c₁ * (c₁ / Real.log T) := by field_simp
          _ ≤ Real.log T / c₁ * ‖(σ₁ : ℂ) + y * I - 1‖ := by gcongr
      simp only [fx, norm_mul, norm_neg]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
      have hk := hKs σ₁ y hσ₁h (by linarith)
      have h3 : 0 ≤ x ^ σ₁ := Real.rpow_nonneg hx0.le σ₁
      gcongr
      linarith
    have hgi : IntervalIntegrable (fun y : ℝ => x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) *
        (4 * (1 + y ^ 2)⁻¹)) volume (-T) T :=
      ((integrable_inv_one_add_sq.const_mul 4).const_mul _).intervalIntegrable
    refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun y hy => hb y hy) hgi).trans ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_one_add_sq, Real.arctan_neg]
    have ha := Real.arctan_lt_pi_div_two T
    have hpos : 0 ≤ x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) := by positivity
    have : 4 * (Real.arctan T - -Real.arctan T) ≤ 4 * π := by linarith
    calc x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) * (4 * (Real.arctan T - -Real.arctan T))
        ≤ x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) * (4 * π) := by gcongr
      _ = x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) * 4 * π := by ring
  have hhor : ∀ τ : ℝ, |τ| = T → ‖∫ u in σ₁..c, fx x (u + (τ : ℂ) * I)‖ ≤
      x ^ c * (C * Real.log T ^ 2 + 1) * (4 * (1 + T ^ 2)⁻¹) * 2 := by
    intro τ hτ
    have hb : ∀ u ∈ Ι σ₁ c, ‖fx x (u + (τ : ℂ) * I)‖ ≤ x ^ c * (C * Real.log T ^ 2 + 1) * (4 * (1 + T ^ 2)⁻¹) := by
      intro u hu
      rw [uIoc_of_le (by linarith)] at hu
      have hre : ((u : ℂ) + τ * I).re = u := by simp
      have him : ((u : ℂ) + τ * I).im = τ := by simp
      have hs1 : (u : ℂ) + τ * I ≠ 1 := fun h => by
        have := congrArg im h; rw [him, one_im] at this; rw [this, abs_zero] at hτ; linarith
      have hl := hld _ (by rw [hre]; linarith [hu.1]) (by rw [hre]; linarith [hu.2])
        (by rw [him, hτ]) hs1
      have hinv : ‖1 / ((u : ℂ) + τ * I - 1)‖ ≤ 1 := by
        rw [norm_div, norm_one]
        refine div_le_one_of_le₀ ?_ (norm_nonneg _)
        have h := Complex.abs_im_le_norm ((u : ℂ) + τ * I - 1)
        rw [sub_im, him, one_im, sub_zero, hτ] at h
        linarith
      simp only [fx, norm_mul, norm_neg]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
      have hk := hKs u τ (by linarith [hu.1]) (by linarith [hu.2])
      have hτ2 : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ]
      rw [hτ2] at hk
      have hxu : x ^ u ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx hu.2
      have h3 : 0 ≤ x ^ u := Real.rpow_nonneg hx0.le u
      have h4 : 0 ≤ ‖logDeriv riemannZeta ((u : ℂ) + τ * I)‖ := norm_nonneg _
      gcongr
      linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    have hcσ : |c - σ₁| ≤ 2 := by rw [abs_of_pos (by linarith)]; linarith
    have hpos : 0 ≤ x ^ c * (C * Real.log T ^ 2 + 1) * (4 * (1 + T ^ 2)⁻¹) := by positivity
    gcongr
  have hA := hhor (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hB2 := hhor T (abs_of_pos hT0)
  -- montagem
  have hSc : ((Ssm x : ℝ) : ℂ) - ((x / 2 : ℝ) : ℂ) =
      (2 * π : ℂ)⁻¹ * ((∫ y : ℝ, fx x (c + y * I)) - ∫ y in (-T)..T, fx x ((c : ℂ) + y * I)) +
        ((2 * π : ℂ)⁻¹ * (∫ y in (-T)..T, fx x ((c : ℂ) + y * I)) - ((x / 2 : ℝ) : ℂ)) := by
    rw [hP]
    push_cast
    ring
  have hnorm : |Ssm x - x / 2| = ‖((Ssm x : ℝ) : ℂ) - ((x / 2 : ℝ) : ℂ)‖ := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hSc]
  have h2π : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv]
    congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hpi : 0 < 2 * π := by positivity
  calc ‖(2 * π : ℂ)⁻¹ * ((∫ y : ℝ, fx x (c + y * I)) - ∫ y in (-T)..T, fx x ((c : ℂ) + y * I)) +
        ((2 * π : ℂ)⁻¹ * (∫ y in (-T)..T, fx x ((c : ℂ) + y * I)) - ((x / 2 : ℝ) : ℂ))‖
      ≤ ‖(2 * π : ℂ)⁻¹ * ((∫ y : ℝ, fx x (c + y * I)) - ∫ y in (-T)..T, fx x ((c : ℂ) + y * I))‖ +
        ‖(2 * π : ℂ)⁻¹ * (∫ y in (-T)..T, fx x ((c : ℂ) + y * I)) - ((x / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ (2 * (x ^ c * (1 / (c - 1) + Cp)) / T) / (2 * π) +
        (‖∫ u in σ₁..c, fx x (u + ((-T : ℝ) : ℂ) * I)‖ + ‖∫ u in σ₁..c, fx x (u + (T : ℂ) * I)‖ +
          ‖∫ y in (-T)..T, fx x ((σ₁ : ℂ) + y * I)‖) / (2 * π) := by
        refine add_le_add ?_ hres
        rw [norm_mul, h2π, div_eq_inv_mul (2 * (x ^ c * (1 / (c - 1) + Cp)) / T)]
        exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ (2 * (x ^ c * (1 / (c - 1) + Cp)) / T +
        2 * (x ^ c * (C * Real.log T ^ 2 + 1) * (4 * (1 + T ^ 2)⁻¹) * 2) +
        x ^ σ₁ * (C * Real.log T ^ 2 + Real.log T / c₁) * 4 * π) / (2 * π) := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hpi.le
        have hA' : ‖∫ u in σ₁..c, fx x (u + ((-T : ℝ) : ℂ) * I)‖ ≤
            x ^ c * (C * Real.log T ^ 2 + 1) * (4 * (1 + T ^ 2)⁻¹) * 2 := hA
        linarith


/-! ## 5. A escolha `c = 1 + 1/log x`, `T = e^{√log x}` -/

/-- **A soma de Chebyshev suavizada com o erro de de la Vallée Poussin**:
`|Σ_{n ≤ x} Λ(n)(1 − n/x) − x/2| ≤ K x log x · e^{−a√log x}`. -/
theorem chebyshev_suave : ∃ a > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    |Ssm x - x / 2| ≤ K * x * Real.log x * Real.exp (-(a * Real.sqrt (Real.log x))) := by
  obtain ⟨c₁, hc₁, T₀, hT₀, C, hC, Cp, hCp, hE⟩ := erro_explicito
  have hπ := Real.pi_pos
  refine ⟨min c₁ 1, lt_min hc₁ one_pos, (6 * (1 + Cp) + 48 * (C + 1) + 4 * π * (C + 1 / c₁)) / (2 * π),
    by positivity, Real.exp (max 1 (max (Real.log T₀ ^ 2) (4 * c₁ ^ 2))),
    Real.one_le_exp (by positivity), fun x hx => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min c₁ 1 := ⟨_, rfl⟩
  rw [← ha]
  have ha0 : 0 < a := by rw [ha]; exact lt_min hc₁ one_pos
  have ha1 : a ≤ 1 := by rw [ha]; exact min_le_right _ _
  have hac : a ≤ c₁ := by rw [ha]; exact min_le_left _ _
  have hx1 : 1 ≤ x := (Real.one_le_exp (by positivity)).trans hx
  have hx0 : 0 < x := by linarith
  -- `ℓ = log x`, `r = √ℓ`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log x := ⟨_, rfl⟩
  rw [← hℓ]
  have hℓM : max 1 (max (Real.log T₀ ^ 2) (4 * c₁ ^ 2)) ≤ ℓ := by
    rw [hℓ, ← Real.log_exp (max 1 (max (Real.log T₀ ^ 2) (4 * c₁ ^ 2)))]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hℓ1 : 1 ≤ ℓ := (le_max_left _ _).trans hℓM
  have hℓT : Real.log T₀ ^ 2 ≤ ℓ := ((le_max_left _ _).trans (le_max_right _ _)).trans hℓM
  have hℓc : 4 * c₁ ^ 2 ≤ ℓ := ((le_max_right _ _).trans (le_max_right _ _)).trans hℓM
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt ℓ := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = ℓ := by rw [hr]; exact Real.sq_sqrt hℓ0.le
  have hr1 : 1 ≤ r := by
    rw [hr]; exact Real.one_le_sqrt.mpr hℓ1
  have hrℓ : r ≤ ℓ := by
    have h := le_mul_of_one_le_left hr0 hr1
    rw [← sq, hr2] at h
    exact h
  have hrT : Real.log T₀ ≤ r := by
    rw [hr]
    exact Real.le_sqrt_of_sq_le hℓT
  have hrc : 2 * c₁ ≤ r := by
    rw [hr]
    refine Real.le_sqrt_of_sq_le ?_
    have e : (2 * c₁) ^ 2 = 4 * c₁ ^ 2 := by ring
    linarith
  -- `c` e `T`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 + 1 / ℓ := ⟨_, rfl⟩
  have hc1 : 1 < c := by rw [hc]; have : 0 < 1 / ℓ := by positivity
                         linarith
  have hc2 : c ≤ 2 := by
    rw [hc]; have : 1 / ℓ ≤ 1 := by rw [div_le_one hℓ0]; exact hℓ1
    linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.exp r := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have hTT₀ : T₀ ≤ T := by
    rw [hT, ← Real.exp_log (show 0 < T₀ by linarith)]
    exact Real.exp_le_exp.mpr hrT
  have hlogT : Real.log T = r := by rw [hT, Real.log_exp]
  have hσ : c₁ / Real.log T ≤ 1 / 2 := by
    rw [hlogT, div_le_iff₀ (by linarith)]
    linarith
  have h := hE x c T hx1 hc1 hc2 hTT₀ hσ
  rw [hlogT] at h
  -- as potências de `x`
  have hxc : x ^ c = x * Real.exp 1 := by
    rw [hc, Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0, ← hℓ]
    congr 1
    congr 1
    field_simp
  have hxs : x ^ (1 - c₁ / r) = x * Real.exp (-(c₁ * r)) := by
    rw [Real.rpow_def_of_pos hx0, ← hℓ]
    have e : ℓ * (1 - c₁ / r) = ℓ + -(c₁ * r) := by
      rw [← hr2]
      field_simp
      ring
    rw [e, Real.exp_add, hℓ, Real.exp_log hx0]
  have hc1' : 1 / (c - 1) = ℓ := by rw [hc, add_sub_cancel_left, one_div_one_div]
  rw [hxc, hxs, hc1', hr2] at h
  -- as exponenciais
  set E := Real.exp (-(a * r)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have har : a * r ≤ r := mul_le_of_le_one_left hr0 ha1
  have hTinv : 1 / T ≤ E := by
    rw [hT, one_div, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hT2 : (1 + T ^ 2)⁻¹ ≤ E := by
    have h1 : (1 + T ^ 2)⁻¹ ≤ 1 / T := by
      rw [one_div]
      apply inv_anti₀ hT0
      have h1T : 1 ≤ T := by rw [hT]; exact Real.one_le_exp hr0
      have hTT : T ≤ T ^ 2 := by
        have h := le_mul_of_one_le_left hT0.le h1T
        rwa [← sq] at h
      linarith
    linarith
  have hEc : Real.exp (-(c₁ * r)) ≤ E := by
    have h := mul_le_mul_of_nonneg_right hac hr0
    exact Real.exp_le_exp.mpr (by linarith)
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  -- os três termos
  have hT1 : 2 * (x * Real.exp 1 * (ℓ + Cp)) / T ≤ 6 * (1 + Cp) * (x * ℓ * E) := by
    have e : 2 * (x * Real.exp 1 * (ℓ + Cp)) / T = 2 * (x * Real.exp 1 * (ℓ + Cp)) * (1 / T) := by ring
    rw [e]
    have h1 : ℓ + Cp ≤ (1 + Cp) * ℓ := by
      have h := le_mul_of_one_le_right hCp hℓ1
      have e : (1 + Cp) * ℓ = ℓ + Cp * ℓ := by ring
      linarith
    have h2 : 0 ≤ x * Real.exp 1 * (ℓ + Cp) := by positivity
    calc 2 * (x * Real.exp 1 * (ℓ + Cp)) * (1 / T) ≤ 2 * (x * Real.exp 1 * (ℓ + Cp)) * E := by gcongr
      _ ≤ 2 * (x * 3 * ((1 + Cp) * ℓ)) * E := by gcongr
      _ = 6 * (1 + Cp) * (x * ℓ * E) := by ring
  have hT2' : 2 * (x * Real.exp 1 * (C * ℓ + 1) * (4 * (1 + T ^ 2)⁻¹) * 2) ≤
      48 * (C + 1) * (x * ℓ * E) := by
    have h1 : C * ℓ + 1 ≤ (C + 1) * ℓ := by
      have e : (C + 1) * ℓ = C * ℓ + ℓ := by ring
      linarith
    have h2 : 0 ≤ C * ℓ + 1 := by positivity
    calc 2 * (x * Real.exp 1 * (C * ℓ + 1) * (4 * (1 + T ^ 2)⁻¹) * 2)
        ≤ 2 * (x * 3 * ((C + 1) * ℓ) * (4 * E) * 2) := by gcongr
      _ = 48 * (C + 1) * (x * ℓ * E) := by ring
  have hT3 : x * Real.exp (-(c₁ * r)) * (C * ℓ + r / c₁) * 4 * π ≤
      4 * π * (C + 1 / c₁) * (x * ℓ * E) := by
    have h1 : C * ℓ + r / c₁ ≤ (C + 1 / c₁) * ℓ := by
      have : r / c₁ ≤ ℓ / c₁ := div_le_div_of_nonneg_right hrℓ hc₁.le
      have e : (C + 1 / c₁) * ℓ = C * ℓ + ℓ / c₁ := by ring
      linarith
    have h2 : 0 ≤ C * ℓ + r / c₁ := by positivity
    calc x * Real.exp (-(c₁ * r)) * (C * ℓ + r / c₁) * 4 * π
        ≤ x * E * ((C + 1 / c₁) * ℓ) * 4 * π := by gcongr
      _ = 4 * π * (C + 1 / c₁) * (x * ℓ * E) := by ring
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have e : (6 * (1 + Cp) + 48 * (C + 1) + 4 * π * (C + 1 / c₁)) / (2 * π) * x * ℓ * E * (2 * π) =
      6 * (1 + Cp) * (x * ℓ * E) + 48 * (C + 1) * (x * ℓ * E) + 4 * π * (C + 1 / c₁) * (x * ℓ * E) := by
    field_simp
  rw [e]
  linarith

end ATK.ZeroClasses.PNT

#print axioms ATK.ZeroClasses.PNT.perron_kk_c
#print axioms ATK.ZeroClasses.PNT.integrable_KK_c
#print axioms ATK.ZeroClasses.PNT.continuous_KK_c
#print axioms ATK.ZeroClasses.PNT.LSeries_vM
#print axioms ATK.ZeroClasses.PNT.integral_termo
#print axioms ATK.ZeroClasses.PNT.Ssm_eq_integral
#print axioms ATK.ZeroClasses.PNT.logDeriv_eq_Gp
#print axioms ATK.ZeroClasses.PNT.zeros_compacto
#print axioms ATK.ZeroClasses.PNT.regiao_contorno
#print axioms ATK.ZeroClasses.PNT.phx_diff
#print axioms ATK.ZeroClasses.PNT.phx_one
#print axioms ATK.ZeroClasses.PNT.bordo_fx
#print axioms ATK.ZeroClasses.PNT.cauda
#print axioms ATK.ZeroClasses.PNT.norm_KK_um
#print axioms ATK.ZeroClasses.PNT.norm_logDeriv_c
#print axioms ATK.ZeroClasses.PNT.continuous_logDeriv_c
#print axioms ATK.ZeroClasses.PNT.erro_explicito
#print axioms ATK.ZeroClasses.PNT.chebyshev_suave
