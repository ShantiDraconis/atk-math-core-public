import ATK.ZeroClasses.HardyCuspide
import ATK.BaseRiemannTeta
import ATK.GammaVertical
import ATK.ZeroClasses.VariacaoArg

/-!
# ATK — Hardy (parte 2): a representação de Fourier de `Ξ` e o decaimento exponencial

Rodada 48 do projeto Hardy (R4: infinitos zeros na reta crítica). Sobre a cúspide (R47):

* `th_ofReal`: `θ(ix) = 1 + 2ψ(x)` (a teta da Mathlib e a cauda `ψ` de `ATK.BaseRiemannTeta`);
* `psi_inv`: a equação funcional real `1 + 2ψ(1/x) = √x (1 + 2ψ(x))`;
* `Hr u = e^{−u/2} − 2 e^{u/2} ψ(e^{2u})`, com `Hr = 2 cosh(u/2) − Θ(u)` (`Hr_eq`), **par**
  (`Hr_neg`), contínua e com `|Hr u| ≤ 5 e^{−|u|/2}` (`abs_Hr_le`);
* **`Fx_eq`** — a representação de Fourier em cossenos
  `Ξ(t)/(t² + 1/4) = ∫₀^∞ Hr(u) cos(tu) du`
  (Titchmarsh (2.16.1)), via a fórmula de Riemann `Xi_riemann`, a troca `x = e^{2u}` e
  `∫₀^∞ e^{−u/2} cos(tu) du = (1/2)/(t² + 1/4)`;
* **`abs_Xi_le`** — o decaimento `|Ξ(t)| ≤ 24 CΓ (1 + |t|)⁴ e^{−π|t|/4}`, por Stirling vertical
  (`ATK.GammaVertical.norm_Gamma_le_vertical`) e `|ζ(s)| ≤ ½ + 1/|s−1| + 6|s|`.

Nada aqui toca a Hipótese de Riemann; é ferramenta para o teorema de Hardy (1914).
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.Hardy

open ATK.BaseRiemannTeta (psi hasSum_psi psi_pos Xi_riemann)
open ATK.BaseRiemannXi (Xi riemannXi riemannXi_eq_zeta)
open ATK.GammaVertical (CΓ CΓ_pos norm_Gamma_le_vertical)
open HurwitzZeta

/-! ## 1. A teta real e a equação funcional -/

theorem evenKernel_zero (x : ℝ) : evenKernel 0 x = 1 + 2 * psi x := by
  unfold psi; ring

/-- `θ(ix) = 1 + 2ψ(x)`. -/
theorem th_ofReal (x : ℝ) : th x = ((1 + 2 * psi x : ℝ) : ℂ) := by
  have h := evenKernel_def 0 x
  simp only [QuotientAddGroup.mk_zero, ofReal_zero, zero_mul, mul_zero, zero_pow two_ne_zero,
    Complex.exp_zero, one_mul] at h
  rw [← evenKernel_zero]
  unfold th
  rw [h]

theorem psi_eq_th (x : ℝ) : psi x = ((th x).re - 1) / 2 := by
  rw [th_ofReal, ofReal_re]; ring

theorem continuousAt_psi {x : ℝ} (hx : 0 < x) : ContinuousAt psi x := by
  have e : psi = fun y : ℝ => ((th y).re - 1) / 2 := funext psi_eq_th
  rw [e]
  have h : ContinuousAt (fun y : ℝ => th y) x :=
    (th_diff (by simpa using hx)).continuousAt.comp continuous_ofReal.continuousAt
  exact ((continuous_re.continuousAt.comp h).sub continuousAt_const).div_const 2

theorem psi_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ psi x := (psi_pos hx).le

/-- **Equação funcional real**: `1 + 2ψ(1/x) = x^{1/2} (1 + 2ψ(x))`. -/
theorem psi_inv {x : ℝ} (hx : 0 < x) : 1 + 2 * psi (1 / x) = x ^ (1 / 2 : ℝ) * (1 + 2 * psi x) := by
  have h := evenKernel_functional_equation 0 x
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  have hp : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  rw [← evenKernel_zero, ← evenKernel_zero, h]
  field_simp

/-- `ψ(y) ≤ 2 e^{−πy}` para `y ≥ 1`. -/
theorem psi_le {y : ℝ} (hy : 1 ≤ y) : psi y ≤ 2 * Real.exp (-π * y) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨q, hq⟩ : ∃ q, q = Real.exp (-π * y) := ⟨_, rfl⟩
  have hπ := Real.pi_gt_three
  have hq0 : 0 ≤ q := hq ▸ (Real.exp_pos _).le
  have hq1 : q ≤ 1 / 4 := by
    have h4 : 4 ≤ Real.exp π := by linarith [Real.add_one_le_exp π]
    have h1 : q ≤ Real.exp (-π) := hq ▸ Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.exp_neg] at h1
    have h2 : (Real.exp π)⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) h4
    linarith
  have hgeo := (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left q
  have hle := hasSum_le (fun n : ℕ => ?_) (hasSum_psi hy0) hgeo
  · rw [← hq]
    calc psi y ≤ q * (1 - q)⁻¹ := hle
      _ ≤ 2 * q := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
        nlinarith
  · rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : π * y * ((n : ℝ) + 1) ≤ π * y * ((n : ℝ) + 1) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith

/-! ## 2. O núcleo `Hr` -/

/-- `Hr(u) = e^{−u/2} − 2 e^{u/2} ψ(e^{2u})`. -/
noncomputable def Hr (u : ℝ) : ℝ := Real.exp (-u / 2) - 2 * Real.exp (u / 2) * psi (Real.exp (2 * u))

/-- `Hr = 2 cosh(u/2) − Θ(u)`. -/
theorem Hr_eq (u : ℝ) : (Hr u : ℂ) = 2 * Complex.cosh (u / 2) - Th u := by
  unfold Hr Th
  rw [Complex.two_cosh, show (2 : ℂ) * (u : ℂ) = ((2 * u : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp,
    th_ofReal]
  have e : cexp (-((u : ℂ) / 2)) = cexp (-(u : ℂ) / 2) := by rw [neg_div]
  push_cast
  rw [e]
  ring

/-- **`Hr` é par** (equação funcional de `θ`). -/
theorem Hr_neg (u : ℝ) : Hr (-u) = Hr u := by
  have h := psi_inv (Real.exp_pos (2 * u))
  have e1 : 1 / Real.exp (2 * u) = Real.exp (2 * -u) := by rw [mul_neg, Real.exp_neg, one_div]
  have e2 : Real.exp (2 * u) ^ (1 / 2 : ℝ) = Real.exp u := by rw [← Real.exp_mul]; ring_nf
  rw [e1, e2] at h
  have e3 : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by rw [← Real.exp_add]; ring_nf
  unfold Hr
  simp only [neg_neg]
  linear_combination (-Real.exp (-u / 2)) * h - (1 + 2 * psi (Real.exp (2 * u))) * e3

theorem continuous_Hr : Continuous Hr := by
  have e : Hr = fun u : ℝ => (2 * Complex.cosh (u / 2) - Th u).re := by
    funext u; rw [← Hr_eq, ofReal_re]
  rw [e]
  refine continuous_re.comp (continuous_iff_continuousAt.mpr fun u => ?_)
  have hT : ContinuousAt (fun v : ℝ => Th v) u :=
    (Th_diff (by simp [Real.pi_pos])).continuousAt.comp continuous_ofReal.continuousAt
  exact ((continuous_const.mul ((Complex.continuous_cosh.comp
    (continuous_ofReal.div_const 2)))).continuousAt).sub hT

theorem abs_Hr_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) : |Hr u| ≤ 5 * Real.exp (-u / 2) := by
  have hπ := Real.pi_gt_three
  have hE : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hψ0 := psi_nonneg (Real.exp_pos (2 * u))
  have hψ := psi_le (show 1 ≤ Real.exp (2 * u) by linarith)
  have hk : Real.exp (u / 2) * Real.exp (-π * Real.exp (2 * u)) ≤ Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have ha := Real.exp_pos (u / 2)
  have hb := Real.exp_pos (-u / 2)
  unfold Hr
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- `|Hr(u)| ≤ 5 e^{−|u|/2}`. -/
theorem abs_Hr_le (u : ℝ) : |Hr u| ≤ 5 * Real.exp (-|u| / 2) := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact abs_Hr_le_of_nonneg hu
  · rw [abs_of_nonpos hu, ← Hr_neg]; exact abs_Hr_le_of_nonneg (by linarith)

theorem integrableOn_exp_Ioi : IntegrableOn (fun u : ℝ => Real.exp (-u / 2)) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < 1 / 2 by norm_num)).congr_fun
    (fun u _ => by ring_nf) measurableSet_Ioi

theorem integrableOn_Hr_cos (t : ℝ) : IntegrableOn (fun u => Hr u * Real.cos (t * u)) (Ioi 0) := by
  refine (integrableOn_exp_Ioi.const_mul 5).mono' ?_ ?_
  · exact (continuous_Hr.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_Hr_le_of_nonneg (le_of_lt hu)
    have h2 := Real.abs_cos_le_one (t * u)
    have h3 := abs_nonneg (Hr u)
    nlinarith

theorem integrableOn_exp_cos (t : ℝ) :
    IntegrableOn (fun u => Real.exp (-u / 2) * Real.cos (t * u)) (Ioi 0) := by
  refine integrableOn_exp_Ioi.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_neg.div_const 2)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-! ## 3. A representação de Fourier -/

/-- `∫₀^∞ e^{−u/2} cos(tu) du = (1/2)/(t² + 1/4)`. -/
theorem integral_exp_cos (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-u / 2) * Real.cos (t * u) = (1 / 2) / (t ^ 2 + 1 / 4) := by
  obtain ⟨a, haa⟩ : ∃ a : ℂ, a = ((-1 / 2 : ℝ) : ℂ) + t * I := ⟨_, rfl⟩
  have hare : a.re = -1 / 2 := by rw [haa]; simp
  have haim : a.im = t := by rw [haa]; simp
  have ha : a.re < 0 := by rw [hare]; norm_num
  have hi := integrableOn_exp_mul_complex_Ioi ha 0
  have h := integral_exp_mul_complex_Ioi ha 0
  have hre : ∀ u : ℝ, Real.exp (-u / 2) * Real.cos (t * u) = (cexp (a * u)).re := by
    intro u
    rw [Complex.exp_re]
    congr 2
    · simp [hare, haim]; ring
    · simp [hare, haim]
  simp_rw [hre]
  have hr := integral_re hi
  simp only [RCLike.re_to_complex] at hr
  rw [hr, h, ofReal_zero, mul_zero, Complex.exp_zero]
  have hpos : 0 < t ^ 2 + 1 / 4 := by positivity
  have hn : normSq a = t ^ 2 + 1 / 4 := by rw [normSq_apply, hare, haim]; ring
  rw [div_re, neg_re, neg_im, one_re, one_im, hare, haim, hn]
  field_simp
  ring

/-- Troca `x = e^{2u}` na fórmula de Riemann. -/
theorem integral_psi_exp (t : ℝ) :
    ∫ x in Ioi (1 : ℝ), psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x) =
      2 * ∫ u in Ioi (0 : ℝ), Real.exp (u / 2) * psi (Real.exp (2 * u)) * Real.cos (t * u) := by
  have h1 := integral_comp_exp_Ioi
    (fun x : ℝ => psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x)) 0
  rw [Real.exp_zero] at h1
  rw [← h1]
  have h2 := integral_comp_mul_left_Ioi (fun v : ℝ => Real.exp v •
    (psi (Real.exp v) * Real.exp v ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log (Real.exp v)))) 0
    (two_pos : (0 : ℝ) < 2)
  rw [mul_zero] at h2
  have h3 : ∫ v in Ioi (0 : ℝ), Real.exp v •
      (psi (Real.exp v) * Real.exp v ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log (Real.exp v))) =
      2 * ∫ u in Ioi (0 : ℝ), Real.exp (2 * u) •
      (psi (Real.exp (2 * u)) * Real.exp (2 * u) ^ (-(3 / 4 : ℝ)) *
        Real.cos (t / 2 * Real.log (Real.exp (2 * u)))) := by
    rw [h2, smul_eq_mul]; ring
  rw [h3]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [smul_eq_mul, Real.log_exp]
  rw [← Real.exp_mul]
  have e : Real.exp (2 * u) * Real.exp (2 * u * -(3 / 4)) = Real.exp (u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : t / 2 * (2 * u) = t * u := by ring
  rw [e2]
  linear_combination (psi (Real.exp (2 * u)) * Real.cos (t * u)) * e

/-- `Fx(t) = Ξ(t)/(t² + 1/4)`. -/
noncomputable def Fx (t : ℝ) : ℝ := Xi t / (t ^ 2 + 1 / 4)

/-- **Representação de Fourier** (Titchmarsh (2.16.1)): `Ξ(t)/(t² + 1/4) = ∫₀^∞ Hr(u) cos(tu) du`. -/
theorem Fx_eq (t : ℝ) : Fx t = ∫ u in Ioi (0 : ℝ), Hr u * Real.cos (t * u) := by
  have hpos : 0 < t ^ 2 + 1 / 4 := by positivity
  have hI1 := integrableOn_exp_cos t
  have hI2 := integrableOn_Hr_cos t
  have hI3 : IntegrableOn (fun u => 2 * (Real.exp (u / 2) * psi (Real.exp (2 * u)) * Real.cos (t * u)))
      (Ioi 0) := by
    refine (hI1.sub hI2).congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    unfold Hr; ring
  have hsplit : ∫ u in Ioi (0 : ℝ), Hr u * Real.cos (t * u) =
      (∫ u in Ioi (0 : ℝ), Real.exp (-u / 2) * Real.cos (t * u)) -
        2 * ∫ u in Ioi (0 : ℝ), Real.exp (u / 2) * psi (Real.exp (2 * u)) * Real.cos (t * u) := by
    rw [← integral_const_mul, ← integral_sub hI1 hI3]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold Hr; ring
  rw [hsplit, integral_exp_cos, ← integral_psi_exp]
  unfold Fx
  rw [Xi_riemann]
  field_simp

/-! ## 4. O decaimento exponencial de `Ξ` -/

/-- `‖Γ(1/4 + iτ)‖ ≤ 8 CΓ (1 + 2|τ|) e^{−π|τ|/2}`. -/
theorem norm_Gamma_quarto (τ : ℝ) :
    ‖Complex.Gamma (1 / 4 + τ * I)‖ ≤ 8 * CΓ * (1 + 2 * |τ|) * Real.exp (-(π * |τ|) / 2) := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = 1 / 4 + τ * I := ⟨_, rfl⟩
  rw [← hw]
  have hwre : w.re = 1 / 4 := by rw [hw]; simp
  have hwim : w.im = τ := by rw [hw]; simp
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre
  have hwn : 1 / 4 ≤ ‖w‖ := by
    have := abs_re_le_norm w; rw [hwre] at this; linarith [abs_of_pos (show (0:ℝ) < 1/4 by norm_num)]
  have h1re : (w + 1).re = 5 / 4 := by simp [hwre]; norm_num
  have h1im : (w + 1).im = τ := by simp [hwim]
  have hG := norm_Gamma_le_vertical (w := w + 1) (by rw [h1re]; norm_num) (by rw [h1re]; norm_num)
  rw [Complex.Gamma_add_one w hw0, norm_mul, h1re, h1im] at hG
  have hn1 : 1 ≤ ‖w + 1‖ := by
    have := abs_re_le_norm (w + 1); rw [h1re] at this; norm_num at this; linarith
  have hn2 : ‖w + 1‖ ≤ 5 / 4 + |τ| := by
    have e : w + 1 = ((5 / 4 : ℝ) : ℂ) + τ * I := by
      apply Complex.ext <;> simp [h1re, h1im]
    rw [e]
    refine (norm_add_le _ _).trans ?_
    simp
  have hp : ‖w + 1‖ ^ (5 / 4 - 1 / 2 : ℝ) ≤ ‖w + 1‖ := by
    calc ‖w + 1‖ ^ (5 / 4 - 1 / 2 : ℝ) ≤ ‖w + 1‖ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = ‖w + 1‖ := Real.rpow_one _
  have hE := Real.exp_pos (-(π * |τ|) / 2)
  have hC := CΓ_pos
  have hwpos : 0 < ‖w‖ := by linarith
  have hGw : ‖w‖ * ‖Complex.Gamma w‖ ≤ CΓ * ‖w + 1‖ * Real.exp (-(π * |τ|) / 2) := by
    refine hG.trans ?_
    gcongr
  have hτ := abs_nonneg τ
  have key : ‖Complex.Gamma w‖ ≤ 4 * (CΓ * ‖w + 1‖ * Real.exp (-(π * |τ|) / 2)) := by
    have hg0 := norm_nonneg (Complex.Gamma w)
    nlinarith
  calc ‖Complex.Gamma w‖ ≤ 4 * (CΓ * ‖w + 1‖ * Real.exp (-(π * |τ|) / 2)) := key
    _ ≤ 4 * (CΓ * (2 * (1 + 2 * |τ|)) * Real.exp (-(π * |τ|) / 2)) := by
        gcongr; linarith
    _ = 8 * CΓ * (1 + 2 * |τ|) * Real.exp (-(π * |τ|) / 2) := by ring

/-- **Decaimento de `Ξ`**: `|Ξ(t)| ≤ 24 CΓ (1 + |t|)⁴ e^{−π|t|/4}`. -/
theorem abs_Xi_le (t : ℝ) : |Xi t| ≤ 24 * CΓ * (1 + |t|) ^ 4 * Real.exp (-(π / 4) * |t|) := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = 1 / 2 + t * I := ⟨_, rfl⟩
  have hsre : s.re = 1 / 2 := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsre; simp at hsre
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre
  have hG0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hX : |Xi t| ≤ ‖riemannXi s‖ := by unfold Xi; rw [← hs]; exact abs_re_le_norm _
  rw [riemannXi_eq_zeta hs0 hs1 hG0, norm_mul, norm_mul, norm_div, norm_mul] at hX
  have ht := abs_nonneg t
  -- `‖s‖`, `‖s − 1‖`
  have hsn : ‖s‖ ≤ 1 / 2 + |t| := by
    rw [hs]; refine (norm_add_le _ _).trans ?_; simp
  have hs1n : ‖s - 1‖ ≤ 1 / 2 + |t| := by
    have e : s - 1 = -(1 / 2 : ℂ) + t * I := by rw [hs]; ring
    rw [e]; refine (norm_add_le _ _).trans ?_; simp
  have hs1n' : 1 / 2 ≤ ‖s - 1‖ := by
    have := abs_re_le_norm (s - 1)
    rw [sub_re, hsre, one_re] at this; norm_num at this; linarith
  -- `ζ`
  have hz := ATK.ZeroClasses.VariacaoArg.cota_zeta_quarto (s := s) (by rw [hsre]; norm_num) hs1
  have hz' : ‖riemannZeta s‖ ≤ 6 * (1 + |t|) := by
    have : 1 / ‖s - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  -- `Γℝ`
  have hGr : ‖Gammaℝ s‖ ≤ 8 * CΓ * (1 + |t|) * Real.exp (-(π / 4) * |t|) := by
    rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hpre : (-s / 2).re = -(1 / 4) := by simp [hsre]; norm_num
    have hπ1 : π ^ (-s / 2).re ≤ 1 := by
      rw [hpre]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
    have e : s / 2 = 1 / 4 + ((t / 2 : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
    have hg := norm_Gamma_quarto (t / 2)
    rw [← e] at hg
    have hab : |t / 2| = |t| / 2 := by rw [abs_div, abs_two]
    rw [hab] at hg
    have eE : -(π * (|t| / 2)) / 2 = -(π / 4) * |t| := by ring
    rw [eE] at hg
    have hg0 := norm_nonneg (Complex.Gamma (s / 2))
    have hp0 : 0 ≤ π ^ (-s / 2).re := Real.rpow_nonneg Real.pi_pos.le _
    calc π ^ (-s / 2).re * ‖Complex.Gamma (s / 2)‖ ≤ 1 * ‖Complex.Gamma (s / 2)‖ := by gcongr
      _ ≤ 8 * CΓ * (1 + 2 * (|t| / 2)) * Real.exp (-(π / 4) * |t|) := by rw [one_mul]; exact hg
      _ = 8 * CΓ * (1 + |t|) * Real.exp (-(π / 4) * |t|) := by ring
  -- `s(s−1)/2`
  have hss : ‖s‖ * ‖s - 1‖ / ‖(2 : ℂ)‖ ≤ (1 + |t|) ^ 2 / 2 := by
    rw [Complex.norm_two]
    have := mul_le_mul hsn hs1n (norm_nonneg _) (by linarith)
    have h2 : (1 / 2 + |t|) * (1 / 2 + |t|) ≤ (1 + |t|) ^ 2 := by nlinarith
    linarith
  have hE := Real.exp_pos (-(π / 4) * |t|)
  have hC := CΓ_pos
  have hA0 : 0 ≤ ‖s‖ * ‖s - 1‖ / ‖(2 : ℂ)‖ := by positivity
  calc |Xi t| ≤ ‖s‖ * ‖s - 1‖ / ‖(2 : ℂ)‖ * ‖Gammaℝ s‖ * ‖riemannZeta s‖ := hX
    _ ≤ (1 + |t|) ^ 2 / 2 * (8 * CΓ * (1 + |t|) * Real.exp (-(π / 4) * |t|)) * (6 * (1 + |t|)) := by
        gcongr
    _ = 24 * CΓ * (1 + |t|) ^ 4 * Real.exp (-(π / 4) * |t|) := by ring

/-- `|Fx(t)| ≤ 96 CΓ (1 + |t|)⁴ e^{−π|t|/4}`. -/
theorem abs_Fx_le (t : ℝ) : |Fx t| ≤ 96 * CΓ * (1 + |t|) ^ 4 * Real.exp (-(π / 4) * |t|) := by
  have hpos : (1 : ℝ) / 4 ≤ t ^ 2 + 1 / 4 := by nlinarith [sq_nonneg t]
  unfold Fx
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < t ^ 2 + 1 / 4), div_le_iff₀ (by linarith)]
  have h := abs_Xi_le t
  have h0 : 0 ≤ 24 * CΓ * (1 + |t|) ^ 4 * Real.exp (-(π / 4) * |t|) := by
    have := CΓ_pos; positivity
  nlinarith

theorem Fx_neg (t : ℝ) : Fx (-t) = Fx t := by
  unfold Fx; rw [ATK.BaseRiemannXi.Xi_neg, neg_sq]

end ATK.ZeroClasses.Hardy

#print axioms ATK.ZeroClasses.Hardy.evenKernel_zero
#print axioms ATK.ZeroClasses.Hardy.th_ofReal
#print axioms ATK.ZeroClasses.Hardy.psi_eq_th
#print axioms ATK.ZeroClasses.Hardy.continuousAt_psi
#print axioms ATK.ZeroClasses.Hardy.psi_nonneg
#print axioms ATK.ZeroClasses.Hardy.psi_inv
#print axioms ATK.ZeroClasses.Hardy.psi_le
#print axioms ATK.ZeroClasses.Hardy.Hr_eq
#print axioms ATK.ZeroClasses.Hardy.Hr_neg
#print axioms ATK.ZeroClasses.Hardy.continuous_Hr
#print axioms ATK.ZeroClasses.Hardy.abs_Hr_le_of_nonneg
#print axioms ATK.ZeroClasses.Hardy.abs_Hr_le
#print axioms ATK.ZeroClasses.Hardy.integrableOn_exp_Ioi
#print axioms ATK.ZeroClasses.Hardy.integrableOn_Hr_cos
#print axioms ATK.ZeroClasses.Hardy.integrableOn_exp_cos
#print axioms ATK.ZeroClasses.Hardy.integral_exp_cos
#print axioms ATK.ZeroClasses.Hardy.integral_psi_exp
#print axioms ATK.ZeroClasses.Hardy.Fx_eq
#print axioms ATK.ZeroClasses.Hardy.norm_Gamma_quarto
#print axioms ATK.ZeroClasses.Hardy.abs_Xi_le
#print axioms ATK.ZeroClasses.Hardy.abs_Fx_le
#print axioms ATK.ZeroClasses.Hardy.Fx_neg
