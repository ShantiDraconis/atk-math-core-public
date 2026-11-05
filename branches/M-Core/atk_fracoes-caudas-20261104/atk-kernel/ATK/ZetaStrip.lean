import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.Convex

/-!
# ATK — ζ na faixa crítica pela integral de `{t}` (passo 1 da ponte de Báez-Duarte)

Prova **incondicional**, no kernel, da representação clássica

  `∫_1^∞ {t} t^{-s-1} dt = 1/(s-1) − ζ(s)/s`   para `Re s > 0`, `s ≠ 1`,

onde `ζ` é a função zeta **da Mathlib** (já continuada analiticamente). Roteiro:

1. `H_eq_of_one_lt`: para `Re s > 1`, por somação de Abel (`LSeries_eq_mul_integral'` da Mathlib
   aplicada à sequência constante 1) e `{t} = t − ⌊t⌋`.
2. `H_differentiableAt`: `H(s)` é a transformada de Mellin de `{t}·𝟙_{t>1}` em `−s`, holomorfa em
   `Re s > 0` (`mellin_differentiableAt_of_isBigO_rpow`).
3. `H_eq`: princípio da identidade no semiplano `Re s > 0` (convexo) contra a função inteira
   `(1 − ζ₀(s))/s`, onde `ζ = 1/(s−1) + ζ₀` (`riemannZeta_eq_inv_sub_add`).
-/

open Complex Set MeasureTheory Filter Topology Asymptotics

namespace ATK.ZetaStrip

/-- `{t}` restrito a `(1, ∞)`, como função complexa. -/
noncomputable def fracTail (t : ℝ) : ℂ :=
  Set.indicator (Ioi (1 : ℝ)) (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) t

/-- `H(s) = ∫_1^∞ {t} t^{-s-1} dt`, como transformada de Mellin de `fracTail` em `-s`. -/
noncomputable def H (s : ℂ) : ℂ := mellin fracTail (-s)

theorem fracTail_norm_le (t : ℝ) : ‖fracTail t‖ ≤ 1 := by
  unfold fracTail
  rw [Set.indicator_apply]
  split_ifs with ht
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  · simp

theorem fracTail_of_lt_one {t : ℝ} (ht : t < 1) : fracTail t = 0 := by
  have hn : t ∉ Ioi (1 : ℝ) := fun h => absurd (lt_trans h ht) (lt_irrefl 1)
  unfold fracTail
  simp [hn]

theorem measurable_fracTail : Measurable fracTail := by
  unfold fracTail
  exact (Complex.measurable_ofReal.comp (measurable_fract : Measurable (Int.fract : ℝ → ℝ))).indicator
    measurableSet_Ioi

theorem locInt_fracTail : LocallyIntegrableOn fracTail (Ioi 0) := by
  refine LocallyIntegrable.locallyIntegrableOn ?_ _
  rw [locallyIntegrable_iff]
  intro K hK
  exact IntegrableOn.of_bound hK.measure_lt_top measurable_fracTail.aestronglyMeasurable 1
    (Eventually.of_forall fracTail_norm_le)

theorem fracTail_isBigO_top : fracTail =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact fracTail_norm_le t

theorem fracTail_isBigO_bot (b : ℝ) : fracTail =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [h1] with t ht
  rw [fracTail_of_lt_one ht, norm_zero]
  positivity

theorem mellinConvergent_fracTail {w : ℂ} (hw : w.re < 0) : MellinConvergent fracTail w :=
  mellinConvergent_of_isBigO_rpow (a := 0) (b := w.re - 1) locInt_fracTail fracTail_isBigO_top hw
    (fracTail_isBigO_bot _) (by linarith)

/-- **`H` é holomorfa em `Re s > 0`.** -/
theorem H_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ H s := by
  have hd : DifferentiableAt ℂ (mellin fracTail) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) locInt_fracTail
      fracTail_isBigO_top (by rw [neg_re]; linarith) (fracTail_isBigO_bot _)
      (by rw [neg_re]; linarith)
  exact hd.comp s differentiableAt_id.neg

/-- `H(s)` como integral sobre `(1, ∞)`. -/
theorem H_eq_integral (s : ℂ) :
    H s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • fracTail t =
      Set.indicator (Ioi (1 : ℝ)) (fun u : ℝ => (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ)) t := by
    intro t
    unfold fracTail
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> simp
  unfold H mellin
  simp_rw [hpt]
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

/-- `t^{-s-1} {t}` é integrável em `(1, ∞)` para `Re s > 0`. -/
theorem integrableOn_cpow_mul_fract {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_Ioi_norm_cpow_of_lt (a := -s - 1)
    (by simp only [sub_re, neg_re, one_re]; linarith) zero_lt_one) ?_ ?_
  · exact ((Complex.measurable_ofReal.pow_const _).mul
      (Complex.measurable_ofReal.comp (measurable_fract : Measurable (Int.fract : ℝ → ℝ)))).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [norm_mul]
    have h1 : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
    calc ‖(t : ℂ) ^ (-s - 1)‖ * ‖((Int.fract t : ℝ) : ℂ)‖ ≤ ‖(t : ℂ) ^ (-s - 1)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖(t : ℂ) ^ (-s - 1)‖ := mul_one _

/-- `ζ(s) = s ∫_1^∞ ⌊t⌋ t^{-s-1} dt` para `Re s > 1` (somação de Abel, Mathlib). -/
theorem zeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← LSeries_one_eq_riemannZeta hs,
    LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one (by simpa using hs) ?_]
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp
  · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp

/-- **Passo de Abel**: `H(s) = 1/(s−1) − ζ(s)/s` para `Re s > 1`. -/
theorem H_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) : H s = 1 / (s - 1) - riemannZeta s / s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this, one_re] at hs; linarith
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by rw [neg_re]; linarith) zero_lt_one
  have hint2 := integrableOn_cpow_mul_fract (s := s) (by linarith)
  have hpt : ∀ t ∈ Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) =
      (t : ℂ) ^ (-s) - ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hfr : (Int.fract t : ℝ) = t - (⌊t⌋₊ : ℝ) := by
      rw [Int.fract, ← Int.natCast_floor_eq_floor ht0.le]
      push_cast
      ring
    have hcp : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s - 1) * (t : ℂ) := by
      rw [show -s = (-s - 1) + 1 by ring, cpow_add _ _ htc, cpow_one]
      ring_nf
    rw [hfr, hcp, show -(s + 1) = -s - 1 by ring]
    push_cast
    ring
  have hint3 : IntegrableOn (fun t : ℝ => ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    refine IntegrableOn.congr_fun (Integrable.sub hint1 hint2) (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [hpt t ht]
    ring
  rw [H_eq_integral, setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hint1 hint3,
    integral_Ioi_cpow_of_lt (by rw [neg_re]; linarith) zero_lt_one]
  have hz := zeta_eq_mul_integral_floor hs
  have hI : ∫ t in Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) = riemannZeta s / s := by
    rw [hz]; field_simp
  rw [hI]
  have hs1' : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

/-- **Representação na faixa**: `H(s) = (1 − ζ₀(s))/s` para todo `Re s > 0`. -/
theorem H_eq {s : ℂ} (hs : 0 < s.re) : H s = (1 - riemannZeta₀ s) / s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hH : AnalyticOnNhd ℂ H U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (H_differentiableAt hz).differentiableWithinAt) hUo
  have hG : AnalyticOnNhd ℂ (fun z => (1 - riemannZeta₀ z) / z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hz0 : z ≠ 0 := by
      intro h; have hz' : (0 : ℝ) < z.re := hz; rw [h, zero_re] at hz'; exact lt_irrefl 0 hz'
    exact (((differentiable_riemannZeta₀ z).const_sub 1).div differentiableAt_id hz0).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : H =ᶠ[𝓝 (2 : ℂ)] fun z => (1 - riemannZeta₀ z) / z := by
    have hO : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hO] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, zero_re] at hz'; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h, one_re] at hz'; linarith
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    rw [H_eq_of_one_lt hz', riemannZeta_eq_inv_sub_add hz1]
    field_simp
    ring
  exact hH.eqOn_of_preconnected_of_eventuallyEq hG hUc h2 hev hs

/-- **`∫_1^∞ {t} t^{-s-1} dt = 1/(s−1) − ζ(s)/s`** para `Re s > 0`, `s ≠ 1`. -/
theorem H_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : H s = 1 / (s - 1) - riemannZeta s / s := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [H_eq hs, riemannZeta_eq_inv_sub_add hs1]
  field_simp
  ring

end ATK.ZetaStrip

#print axioms ATK.ZetaStrip.fracTail_norm_le
#print axioms ATK.ZetaStrip.fracTail_of_lt_one
#print axioms ATK.ZetaStrip.measurable_fracTail
#print axioms ATK.ZetaStrip.locInt_fracTail
#print axioms ATK.ZetaStrip.fracTail_isBigO_top
#print axioms ATK.ZetaStrip.fracTail_isBigO_bot
#print axioms ATK.ZetaStrip.mellinConvergent_fracTail
#print axioms ATK.ZetaStrip.H_differentiableAt
#print axioms ATK.ZetaStrip.H_eq_integral
#print axioms ATK.ZetaStrip.integrableOn_cpow_mul_fract
#print axioms ATK.ZetaStrip.zeta_eq_mul_integral_floor
#print axioms ATK.ZetaStrip.H_eq_of_one_lt
#print axioms ATK.ZetaStrip.H_eq
#print axioms ATK.ZetaStrip.H_eq_zeta
