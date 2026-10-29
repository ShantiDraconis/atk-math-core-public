import ATK.NSTrilinear
import ATK.NSClasse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# ATK — Navier–Stokes: unicidade fraca–forte

Camada 22 do ataque a B3 (passos U-7, U-8). A solução `U₁` da classe de Fourier
(`ATK.NSClasse.ClasseF`, amplitude `a` com todas as cotas `w_m⁻¹`) e uma solução suave qualquer
`U₂` (amplitude `bt`, só `L²` com `‖ξ‖ bt ∈ L²`, `ATK.NSIdent`) resolvem a mesma equação branda
com o mesmo dado. Para `d = a − bt`:

* identidade de energia pontual em `ξ` (`energia_edo`, sem derivar: funções lipschitzianas com
  derivada nula q.t.p. são constantes);
* `∫ ⟪d, N(bt, d)⟫ = 0` (cancelamento; integrabilidade por Cauchy–Schwarz com pesos — não há
  imersão de Sobolev na Mathlib, e ela não é necessária);
* `|∫ ⟪d, N(d, a)⟫| ≤ 2π ‖ξ a‖₁ ‖d‖₂²`;
* Gronwall: `‖d(t)‖₂ = 0`, logo `U₂ = U₁`.

**CLOSED_MATH continua false.**
-/

open MeasureTheory FourierTransform SchwartzMap Filter Set ComplexConjugate Topology
open scoped ContDiff InnerProductSpace Real Nat

namespace ATK.NSUnicidade

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSFisico ATK.NSL2 ATK.NSDado ATK.NSPicard
  ATK.NSFracaFourier ATK.NSDuhamel ATK.NSIdent

/-! ### Gronwall na forma integral -/

theorem gronwall_int {E : ℝ → ℝ} {t K M : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hE0 : ∀ s ∈ Icc 0 t, 0 ≤ E s) (hEM : ∀ s ∈ Icc 0 t, E s ≤ M)
    (hint : IntervalIntegrable E volume 0 t)
    (h : ∀ s ∈ Icc 0 t, E s ≤ K * ∫ r in (0 : ℝ)..s, E r) : ∀ s ∈ Icc 0 t, E s = 0 := by
  have hM : 0 ≤ M := (hE0 0 ⟨le_rfl, ht⟩).trans (hEM 0 ⟨le_rfl, ht⟩)
  have hind : ∀ n : ℕ, ∀ s ∈ Icc 0 t, E s ≤ M * (K * s) ^ n / n ! := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hEM s hs
    | succ n ih =>
      intro s hs
      have hsub : uIcc 0 s ⊆ uIcc 0 t := by
        rw [uIcc_of_le hs.1, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hs.2
      have hint_s : IntervalIntegrable E volume 0 s := hint.mono_set hsub
      have hmono : ∫ r in (0 : ℝ)..s, E r ≤ ∫ r in (0 : ℝ)..s, M * (K * r) ^ n / n ! := by
        refine intervalIntegral.integral_mono_on hs.1 hint_s ?_ (fun r hr => ?_)
        · exact (by fun_prop : Continuous fun r : ℝ => M * (K * r) ^ n / n !).intervalIntegrable _ _
        · exact ih r ⟨hr.1, hr.2.trans hs.2⟩
      have hcalc : ∫ r in (0 : ℝ)..s, M * (K * r) ^ n / n ! = M * K ^ n * s ^ (n + 1) / (n + 1) ! := by
        have e : (fun r : ℝ => M * (K * r) ^ n / n !) = fun r => (M * K ^ n / n !) * r ^ n := by
          funext r; rw [mul_pow]; ring
        rw [e, intervalIntegral.integral_const_mul, integral_pow]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
      calc E s ≤ K * ∫ r in (0 : ℝ)..s, E r := h s hs
        _ ≤ K * (M * K ^ n * s ^ (n + 1) / (n + 1) !) := by
            rw [← hcalc]; exact mul_le_mul_of_nonneg_left hmono hK
        _ = M * (K * s) ^ (n + 1) / (n + 1) ! := by rw [mul_pow, pow_succ K]; ring
  intro s hs
  refine le_antisymm ?_ (hE0 s hs)
  have hlim : Tendsto (fun n : ℕ => M * ((K * s) ^ n / n !)) atTop (𝓝 (M * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (K * s)).const_mul M
  rw [mul_zero] at hlim
  refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  have := hind n s hs
  rwa [mul_div_assoc] at this

/-! ### Identidade de energia de uma EDO linear com forçante limitado -/

/-- `f(s) = ∫₀ˢ e^{−l(s−r)} g(r) dr`. -/
noncomputable def fE (l : ℝ) (g : ℝ → C3) (s : ℝ) : C3 :=
  ∫ r in (0 : ℝ)..s, Real.exp (-(l * (s - r))) • g r

/-- `F(s) = ∫₀ˢ e^{l r} g(r) dr`. -/
noncomputable def FE (l : ℝ) (g : ℝ → C3) (s : ℝ) : C3 :=
  ∫ r in (0 : ℝ)..s, Real.exp (l * r) • g r

theorem fE_eq (l : ℝ) (g : ℝ → C3) (s : ℝ) : fE l g s = Real.exp (-(l * s)) • FE l g s := by
  unfold fE FE
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun r _ => ?_)
  try dsimp only
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring

theorem norm_sq_lip {B : ℝ} (hB : 0 ≤ B) :
    LipschitzOnWith (Real.toNNReal (2 * B)) (fun v : C3 => ‖v‖ ^ 2) (Metric.closedBall 0 B) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at ha hb
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have h1 : |‖a‖ ^ 2 - ‖b‖ ^ 2| = |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) := by
    rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring, abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
  rw [h1]
  calc |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) ≤ ‖a - b‖ * (2 * B) :=
        mul_le_mul (abs_norm_sub_norm_le a b) (by linarith) (by positivity) (norm_nonneg _)
    _ = 2 * B * ‖a - b‖ := by ring

theorem re_inner_self_C3 (v : C3) : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 :=
  (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm

theorem hasDerivAt_norm_sq_C3 {f : ℝ → C3} {f' : C3} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * (⟪f x, f'⟫_ℂ).re) x := by
  have h1 := HasDerivAt.inner ℂ hf hf
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h1
  have e : (fun r => ‖f r‖ ^ 2) = Complex.reCLM ∘ fun t => ⟪f t, f t⟫_ℂ := by
    funext r
    rw [Function.comp_apply, Complex.reCLM_apply]
    exact (re_inner_self_C3 _).symm
  rw [e]
  convert h2 using 1
  rw [Complex.reCLM_apply, Complex.add_re, ← inner_conj_symm f' (f x), Complex.conj_re]
  ring

/-- **Identidade de energia** (sem derivar a forçante): para `g` limitada e integrável,
`‖f(s)‖² = ∫₀ˢ (−2l ‖f‖² + 2 Re⟪f, g⟫)`. -/
theorem energia_edo {l t M : ℝ} {g : ℝ → C3} (hl : 0 ≤ l) (ht : 0 ≤ t)
    (hg : IntervalIntegrable g volume 0 t) (hM : ∀ r ∈ Icc 0 t, ‖g r‖ ≤ M) {s : ℝ}
    (hs : s ∈ Icc 0 t) :
    (‖fE l g s‖ ^ 2 =
      ∫ r in (0 : ℝ)..s, (-(2 * l) * ‖fE l g r‖ ^ 2 + 2 * (⟪fE l g r, g r⟫_ℂ).re)) ∧
      ‖fE l g s‖ ^ 2 ≤ ∫ r in (0 : ℝ)..s, 2 * (⟪fE l g r, g r⟫_ℂ).re := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  have hut : uIcc (0 : ℝ) t = Icc 0 t := uIcc_of_le ht
  -- a integral `F`
  have hgi : IntervalIntegrable (fun r => Real.exp (l * r) • g r) volume 0 t :=
    hg.continuousOn_smul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hFlip : LipschitzOnWith (Real.toNNReal (Real.exp (l * t) * M)) (FE l g) (uIcc 0 t) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [hut] at hx hy
    have hx' : uIcc 0 x ⊆ uIcc 0 t := by
      rw [uIcc_of_le hx.1, hut]; exact Icc_subset_Icc le_rfl hx.2
    have hy' : uIcc 0 y ⊆ uIcc 0 t := by
      rw [uIcc_of_le hy.1, hut]; exact Icc_subset_Icc le_rfl hy.2
    rw [dist_eq_norm, FE, FE, intervalIntegral.integral_interval_sub_left (hgi.mono_set hx')
      (hgi.mono_set hy'), Real.coe_toNNReal _ (by positivity), Real.dist_eq]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_).trans
      (le_of_eq (by rw [abs_sub_comm]))
    have hr' : r ∈ Icc 0 t := by
      rcases le_total y x with hyx | hxy
      · rw [uIoc_of_le hyx] at hr; exact ⟨hy.1.trans hr.1.le, hr.2.trans hx.2⟩
      · rw [uIoc_of_ge hxy] at hr; exact ⟨hx.1.trans hr.1.le, hr.2.trans hy.2⟩
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr'.2 hl)) (hM r hr')
      (norm_nonneg _) (Real.exp_pos _).le
  have hF_AC : AbsolutelyContinuousOnInterval (FE l g) 0 t :=
    hFlip.absolutelyContinuousOnInterval
  have he_AC : AbsolutelyContinuousOnInterval (fun r => Real.exp (-(l * r))) 0 t :=
    ContDiffOn.absolutelyContinuousOnInterval
      ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg).contDiffOn)
  have hf_AC : AbsolutelyContinuousOnInterval (fE l g) 0 t := by
    have h := he_AC.smul hF_AC
    have e : (fun r => Real.exp (-(l * r))) • FE l g = fE l g := by
      funext r; rw [Pi.smul_apply', fE_eq]
    rwa [e] at h
  -- cota de `f`
  have hfb : ∀ r ∈ Icc 0 t, ‖fE l g r‖ ≤ M * t := by
    intro r hr
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
      (f := fun q => Real.exp (-(l * (r - q))) • g q) (C := M) (fun q hq => by
        rw [uIoc_of_le hr.1] at hq
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        have h1 : Real.exp (-(l * (r - q))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hq.2])
        calc Real.exp (-(l * (r - q))) * ‖g q‖ ≤ 1 * M :=
              mul_le_mul h1 (hM q ⟨hq.1.le, hq.2.trans hr.2⟩) (norm_nonneg _) zero_le_one
          _ = M := one_mul _)
    rw [sub_zero, abs_of_nonneg hr.1] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hr.2 hM0)
  have hN_AC : AbsolutelyContinuousOnInterval (fun r => ‖fE l g r‖ ^ 2) 0 t := by
    have h := (norm_sq_lip (mul_nonneg hM0 ht)).comp_absolutelyContinuousOnInterval
      (fun r hr => by
        rw [hut] at hr
        rw [Metric.mem_closedBall, dist_zero_right]; exact hfb r hr) hf_AC
    exact h
  -- o integrando
  set h : ℝ → ℝ := fun r => -(2 * l) * ‖fE l g r‖ ^ 2 + 2 * (⟪fE l g r, g r⟫_ℂ).re with hh
  have hfc : ContinuousOn (fE l g) (uIcc 0 t) := hf_AC.continuousOn
  have h1i : IntervalIntegrable (fun r => -(2 * l) * ‖fE l g r‖ ^ 2) volume 0 t :=
    ((continuousOn_const.mul ((continuous_norm.comp_continuousOn hfc).pow 2))).intervalIntegrable
  have h2i : IntervalIntegrable (fun r => 2 * (⟪fE l g r, g r⟫_ℂ).re) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    have hgI : IntegrableOn g (Ioc 0 t) := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hg
    refine (hgI.norm.const_mul (2 * (M * t))).mono' ?_ ?_
    · have hfa : AEStronglyMeasurable (fE l g) (volume.restrict (Ioc 0 t)) :=
        (hfc.mono (by rw [hut]; exact Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
      exact (aestronglyMeasurable_const.mul
        (Complex.continuous_re.comp_aestronglyMeasurable (hfa.inner hgI.aestronglyMeasurable)))
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun r hr => ?_)
      have hr' : r ∈ Icc 0 t := Ioc_subset_Icc_self hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc |(⟪fE l g r, g r⟫_ℂ).re| ≤ ‖⟪fE l g r, g r⟫_ℂ‖ := Complex.abs_re_le_norm _
        _ ≤ ‖fE l g r‖ * ‖g r‖ := norm_inner_le_norm _ _
        _ ≤ M * t * ‖g r‖ := mul_le_mul_of_nonneg_right (hfb r hr') (norm_nonneg _)
  have hhi : IntervalIntegrable h volume 0 t := h1i.add h2i
  have hI_AC : AbsolutelyContinuousOnInterval (fun r => ∫ q in (0 : ℝ)..r, h q) 0 t :=
    hhi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hΦ_AC : AbsolutelyContinuousOnInterval
      (fun r => ‖fE l g r‖ ^ 2 - ∫ q in (0 : ℝ)..r, h q) 0 t := hN_AC.sub hI_AC
  -- derivada nula q.t.p.
  have hderiv : ∀ᵐ x, x ∈ uIcc 0 t →
      HasDerivAt (fun r => ‖fE l g r‖ ^ 2 - ∫ q in (0 : ℝ)..r, h q) 0 x := by
    filter_upwards [hgi.ae_hasDerivAt_integral, hhi.ae_hasDerivAt_integral] with x h1 h2 hx
    have hF' : HasDerivAt (FE l g) (Real.exp (l * x) • g x) x := h1 hx 0 left_mem_uIcc
    have hI' : HasDerivAt (fun r => ∫ q in (0 : ℝ)..r, h q) (h x) x := h2 hx 0 left_mem_uIcc
    have he' : HasDerivAt (fun r => Real.exp (-(l * r))) (-l * Real.exp (-(l * x))) x := by
      have h0 : HasDerivAt (fun r => -l * r) (-l * 1) x := (hasDerivAt_id' x).const_mul (-l)
      have h00 := h0.exp
      have e : (fun r => Real.exp (-(l * r))) = fun r => Real.exp (-l * r) :=
        funext fun r => by rw [neg_mul]
      rw [e]
      convert h00 using 1
      rw [neg_mul l x]
      ring
    have h3 : HasDerivAt (fun y => Real.exp (-(l * y)) • FE l g y)
        (Real.exp (-(l * x)) • (Real.exp (l * x) • g x) + (-l * Real.exp (-(l * x))) • FE l g x)
        x := he'.smul hF'
    have e3 : (fun y => Real.exp (-(l * y)) • FE l g y) = fE l g :=
      funext fun y => (fE_eq l g y).symm
    rw [e3] at h3
    have hf' : HasDerivAt (fE l g) (g x - ((l : ℂ) • fE l g x)) x := by
      convert h3 using 1
      have e1 : Real.exp (-(l * x)) * Real.exp (l * x) = 1 := by
        rw [← Real.exp_add, show -(l * x) + l * x = 0 by ring, Real.exp_zero]
      rw [fE_eq, Complex.coe_smul, smul_smul (Real.exp (-(l * x))), e1, one_smul, smul_smul,
        neg_mul, neg_smul, sub_eq_add_neg]
    have hN' := hasDerivAt_norm_sq_C3 hf'
    convert hN'.sub hI' using 1
    rw [hh, inner_sub_right, inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul,
      re_inner_self_C3]
    ring

  obtain ⟨C, hC⟩ := hΦ_AC.const_of_ae_hasDerivAt_zero hderiv
  have h0 : ‖fE l g 0‖ ^ 2 - ∫ q in (0 : ℝ)..0, h q = 0 := by
    simp [fE]
  have hs' : s ∈ uIcc 0 t := by rw [hut]; exact hs
  have := hC s hs'
  rw [← hC 0 left_mem_uIcc, h0] at this
  have heq : ‖fE l g s‖ ^ 2 = ∫ q in (0 : ℝ)..s, h q := by linarith
  refine ⟨heq, heq.trans_le ?_⟩
  have hsub : uIcc 0 s ⊆ uIcc 0 t := by
    rw [uIcc_of_le hs.1, hut]; exact Icc_subset_Icc le_rfl hs.2
  refine intervalIntegral.integral_mono_on hs.1 (hhi.mono_set hsub) (h2i.mono_set hsub)
    (fun r _ => ?_)
  show -(2 * l) * ‖fE l g r‖ ^ 2 + 2 * (⟪fE l g r, g r⟫_ℂ).re ≤ 2 * (⟪fE l g r, g r⟫_ℂ).re
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hl) (sq_nonneg ‖fE l g r‖)
  linarith

/-! ### A unicidade no lado de Fourier (forma abstrata) -/

section Abstrata

open ATK.NSTrilinear

theorem integral_sq_le_nH1 {f : E3 → C3} (hf2 : MemLp f 2) (hH : H1 f) :
    ∫ ξ, ‖f ξ‖ ^ 2 ≤ nH1 f := by
  refine integral_mono (integrable_sq_norm_of_memLp hf2) hH (fun ξ => ?_)
  have h1 := one_le_w 1 ξ
  have h0 := norm_nonneg (f ξ)
  show ‖f ξ‖ ^ 2 ≤ (w 1 ξ * ‖f ξ‖) ^ 2
  exact pow_le_pow_left₀ h0 (le_mul_of_one_le_left h0 h1) 2

/-- O forçante da diferença na frequência `ξ`. -/
noncomputable def gD (a G : ℝ → E3 → C3) (ξ : E3) (q : ℝ) : C3 :=
  -ATK.NSFourierBase.lp ξ (Nl (a q) (a q) ξ - G q ξ)

/-- **Unicidade fraca–forte no lado de Fourier.** Uma amplitude `a` da classe de Fourier e uma
amplitude `b` só em `H¹` (uniformemente em `[0, t]`), conjuntamente mensurável, hermitiana e de
divergência nula, que resolvem a mesma equação branda com o mesmo dado, coincidem q.t.p. -/
theorem unicidade_fourier {ν t : ℝ} {a b G : ℝ → E3 → C3} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (ha : ATK.NSTempo.BoaW a) (hah : ∀ r, ATK.NSSimetria.Herm (a r)) (had : ∀ r ξ, ⟪cpx ξ, a r ξ⟫_ℂ = 0)
    (ham : ∀ r ∈ Icc 0 t, ∀ ξ,
      a r ξ = heat ν r ξ • a 0 ξ - ∫ q in (0 : ℝ)..r, duhI ν a a r q ξ)
    (hbm : StronglyMeasurable fun p : ℝ × E3 => b p.1 p.2)
    (hbh : ∀ r ∈ Icc 0 t, ATK.NSSimetria.Herm (b r)) (hbd : ∀ r ∈ Icc 0 t, ∀ ξ, ⟪cpx ξ, b r ξ⟫_ℂ = 0)
    (hb2 : ∀ r ∈ Icc 0 t, MemLp (b r) 2) {Cb : ℝ}
    (hbH : ∀ r ∈ Icc 0 t, H1 (b r) ∧ nH1 (b r) ≤ Cb)
    (hGm : StronglyMeasurable fun p : ℝ × E3 => G p.1 p.2)
    (hG : ∀ r ∈ Icc 0 t, ∀ ξ, G r ξ = Nl (b r) (b r) ξ)
    (hbmild : ∀ r ∈ Icc 0 t, ∀ ξ, b r ξ = heat ν r ξ • a 0 ξ -
      ∫ q in (0 : ℝ)..r, heat ν (r - q) ξ • ATK.NSFourierBase.lp ξ (G q ξ)) :
    ∀ r ∈ Icc 0 t, ∀ᵐ ξ, a r ξ = b r ξ := by
  -- constantes
  obtain ⟨A, hA0, hA⟩ := ha.bound 5
  obtain ⟨A4, hA4⟩ := ha.boa4
  have hCb0 : 0 ≤ Cb := (nH1_nonneg _).trans (hbH 0 ⟨le_rfl, ht⟩).2
  have hI4 := I4_nonneg
  set Ca : ℝ := A ^ 2 * I4 with hCa
  have hCa0 : 0 ≤ Ca := by positivity
  -- propriedades de `a(r)` e `b(r)`
  have ham_r : ∀ r, Measurable (a r) := fun r => (ha.cont_s r).measurable
  have hbm_r : ∀ r, Measurable (b r) := fun r =>
    Measurable.comp (g := fun p : ℝ × E3 => b p.1 p.2) (f := fun ξ : E3 => (r, ξ)) hbm.measurable
      (measurable_const.prodMk measurable_id)
  have ha2 : ∀ r, MemLp (a r) 2 := fun r => ATK.NSPlancherel.memLp_two_of_bound
    (ham_r r).aestronglyMeasurable (fun ζ => (hA r ζ).trans
      (mul_le_mul_of_nonneg_left (w_inv_anti (by norm_num) ζ) hA0))
  have haH : ∀ r, H1 (a r) ∧ nH1 (a r) ≤ Ca := fun r => H1_of_bound (ham_r r) (hA r)
  have haL2 : ∀ r, ∫ ξ, ‖a r ξ‖ ^ 2 ≤ Ca := fun r =>
    (integral_sq_le_nH1 (ha2 r) (haH r).1).trans (haH r).2
  have hbL2 : ∀ r ∈ Icc 0 t, ∫ ξ, ‖b r ξ‖ ^ 2 ≤ Cb := fun r hr =>
    (integral_sq_le_nH1 (hb2 r hr) (hbH r hr).1).trans (hbH r hr).2
  -- o forçante
  have hNa : Continuous fun p : ℝ × E3 => Nl (a p.1) (a p.1) p.2 := continuous_Nl hA4 hA4
  have hgDm : Measurable fun p : ℝ × E3 => gD a G p.2 p.1 := by
    unfold gD
    exact (ATK.NSIdent.measurable_lp.comp (measurable_snd.prodMk
      (hNa.measurable.sub hGm.measurable))).neg
  have hgDb : ∀ q ∈ Icc 0 t, ∀ ξ, ‖gD a G ξ q‖ ≤ 2 * π * ‖ξ‖ * (Ca + Cb) := by
    intro q hq ξ
    unfold gD
    rw [norm_neg]
    refine (norm_lp_le _ _).trans ((norm_sub_le _ _).trans ?_)
    rw [hG q hq ξ, mul_add]
    exact add_le_add ((norm_Nl_le_L2 (ha2 q) ξ).trans
        (mul_le_mul_of_nonneg_left (haL2 q) (by positivity)))
      ((norm_Nl_le_L2 (hb2 q hq) ξ).trans
        (mul_le_mul_of_nonneg_left (hbL2 q hq) (by positivity)))
  have hgDi : ∀ ξ, IntervalIntegrable (gD a G ξ) volume 0 t := by
    intro ξ
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    have hm : Measurable (gD a G ξ) := by
      exact Measurable.comp (g := fun p : ℝ × E3 => gD a G p.2 p.1) (f := fun q : ℝ => (q, ξ))
        hgDm (measurable_id.prodMk measurable_const)
    refine Measure.integrableOn_of_bounded (M := 2 * π * ‖ξ‖ * (Ca + Cb)) (by simp)
      hm.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun q hq =>
      hgDb q (Ioc_subset_Icc_self hq) ξ)
  -- a representação de Duhamel da diferença
  set κ : E3 → ℝ := fun ξ => 4 * π ^ 2 * ν * ‖ξ‖ ^ 2 with hκ
  have hκ0 : ∀ ξ, 0 ≤ κ ξ := fun ξ => by
    show 0 ≤ 4 * π ^ 2 * ν * ‖ξ‖ ^ 2
    positivity
  have hrep : ∀ r ∈ Icc 0 t, ∀ ξ, a r ξ - b r ξ = fE (κ ξ) (gD a G ξ) r := by
    intro r hr ξ
    have i1 : IntervalIntegrable (fun q => duhI ν a a r q ξ) volume 0 r := by
      have hc : Continuous fun q : ℝ => duhI ν a a r q ξ :=
        Continuous.comp (g := fun p : (ℝ × ℝ) × E3 => duhI ν a a p.1.1 p.1.2 p.2)
          (f := fun q : ℝ => ((r, q), ξ)) (continuous_duhI hA4 hA4 ν) (by fun_prop)
      exact hc.intervalIntegrable _ _
    have i2 : IntervalIntegrable
        (fun q => heat ν (r - q) ξ • ATK.NSFourierBase.lp ξ (G q ξ)) volume 0 r := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1]
      have hGs : Measurable fun q => G q ξ :=
        Measurable.comp (g := fun p : ℝ × E3 => G p.1 p.2) (f := fun q : ℝ => (q, ξ))
          hGm.measurable (measurable_id.prodMk measurable_const)
      have hm : Measurable fun q => heat ν (r - q) ξ • ATK.NSFourierBase.lp ξ (G q ξ) :=
        ((continuous_heat ν).measurable.comp ((measurable_const.sub measurable_id).prodMk
          (measurable_const (a := ξ)))).smul
          (ATK.NSIdent.measurable_lp.comp ((measurable_const (a := ξ)).prodMk hGs))
      refine Measure.integrableOn_of_bounded (M := 2 * π * ‖ξ‖ * Cb) (by simp)
        hm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun q hq => ?_)
      have hq' : q ∈ Icc 0 t := ⟨hq.1.le, hq.2.trans hr.2⟩
      rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
      calc heat ν (r - q) ξ * ‖ATK.NSFourierBase.lp ξ (G q ξ)‖ ≤ 1 * ‖G q ξ‖ :=
            mul_le_mul (heat_le_one hν (by linarith [hq.2]) ξ) (norm_lp_le _ _) (norm_nonneg _)
              zero_le_one
        _ ≤ 2 * π * ‖ξ‖ * Cb := by
            rw [one_mul, hG q hq' ξ]
            exact (norm_Nl_le_L2 (hb2 q hq') ξ).trans
              (mul_le_mul_of_nonneg_left (hbL2 q hq') (by positivity))
    rw [ham r hr ξ, hbmild r hr ξ, sub_sub_sub_cancel_left,
      ← intervalIntegral.integral_sub i2 i1]
    unfold fE
    refine intervalIntegral.integral_congr (fun q _ => ?_)
    simp only [duhI, gD]
    rw [ATK.NSFourierBase.lp_sub, ← smul_sub, neg_sub]
    rfl
  -- o integrando de energia
  set ψ : E3 × ℝ → ℝ := fun p => 2 * (⟪a p.2 p.1 - b p.2 p.1, gD a G p.1 p.2⟫_ℂ).re with hψ
  have hψm : Measurable ψ := by
    have h1 : Measurable fun p : E3 × ℝ => a p.2 p.1 :=
      Measurable.comp (g := fun p : ℝ × E3 => a p.1 p.2) (f := Prod.swap) ha.cont.measurable
        measurable_swap
    have h2 : Measurable fun p : E3 × ℝ => b p.2 p.1 :=
      Measurable.comp (g := fun p : ℝ × E3 => b p.1 p.2) (f := Prod.swap) hbm.measurable
        measurable_swap
    have h3 : Measurable fun p : E3 × ℝ => gD a G p.1 p.2 :=
      Measurable.comp (g := fun p : ℝ × E3 => gD a G p.2 p.1) (f := Prod.swap) hgDm
        measurable_swap
    exact measurable_const.mul (Complex.measurable_re.comp
      (Measurable.inner (𝕜 := ℂ) (h1.sub h2) h3))
  have hψphi' : ∀ q ∈ Icc 0 t, ∀ ξ, ψ (ξ, q) = phiE (a q) (b q) ξ := by
    intro q hq ξ
    show 2 * (⟪a q ξ - b q ξ, gD a G ξ q⟫_ℂ).re = _
    unfold phiE gD
    rw [hG q hq ξ]
  have hpt : ∀ s ∈ Icc 0 t, ∀ ξ, ‖a s ξ - b s ξ‖ ^ 2 ≤ ∫ q in (0 : ℝ)..s, ψ (ξ, q) := by
    intro s hs ξ
    have h := (energia_edo (hκ0 ξ) ht (hgDi ξ) (fun r hr => hgDb r hr ξ) hs).2
    rw [← hrep s hs ξ] at h
    refine h.trans (le_of_eq (intervalIntegral.integral_congr (fun q hq => ?_)))
    rw [uIcc_of_le hs.1] at hq
    show 2 * (⟪fE (κ ξ) (gD a G ξ) q, gD a G ξ q⟫_ℂ).re =
      2 * (⟪a q ξ - b q ξ, gD a G ξ q⟫_ℂ).re
    rw [hrep q ⟨hq.1, hq.2.trans hs.2⟩ ξ]
  -- as propriedades estáticas, uniformes em `q`
  set B : ℝ := 2 * π * (2 * I4 * (2 * Ca + 2 * Cb) + Ca ^ 2 + Cb ^ 2) with hB
  set K : ℝ := 4 * π * (A * I4) with hK
  have hK0 : 0 ≤ K := by positivity
  have hstat : ∀ q ∈ Icc 0 t, Integrable (phiE (a q) (b q)) ∧
      ∫ ξ, ‖phiE (a q) (b q) ξ‖ ≤ B ∧
      ∫ ξ, phiE (a q) (b q) ξ ≤ K * ∫ ξ, ‖a q ξ - b q ξ‖ ^ 2 := by
    intro q hq
    obtain ⟨p1, p2, p3⟩ := phiE_props (ham_r q) (hbm_r q) hA0 (hA q) (had q) (hah q) (hb2 q hq)
      (hbH q hq).1 (hbd q hq) (hbh q hq)
    refine ⟨p1, p2.trans ?_, p3.trans (le_of_eq (by rw [hK]; ring))⟩
    have hd := (H1_sub (ham_r q) (hbm_r q) (haH q).1 (hbH q hq).1).2
    have e1 := nH1_nonneg (a q)
    have e2 := nH1_nonneg (b q)
    have e3 := nH1_nonneg (a q - b q)
    have f1 := (haH q).2
    have f2 := (hbH q hq).2
    rw [hB]
    have g1 : nH1 (a q) ^ 2 ≤ Ca ^ 2 := pow_le_pow_left₀ e1 f1 2
    have g2 : nH1 (b q) ^ 2 ≤ Cb ^ 2 := pow_le_pow_left₀ e2 f2 2
    have g3 : nH1 (a q - b q) ≤ 2 * Ca + 2 * Cb := by linarith
    have g4 : 2 * I4 * nH1 (a q - b q) ≤ 2 * I4 * (2 * Ca + 2 * Cb) :=
      mul_le_mul_of_nonneg_left g3 (by positivity)
    have hπ : 0 ≤ 2 * π := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hπ
  -- a energia da diferença
  set E : ℝ → ℝ := fun q => ∫ ξ, ‖a q ξ - b q ξ‖ ^ 2 with hE
  have hEm : Measurable E := by
    have h : StronglyMeasurable fun p : ℝ × E3 => ‖a p.1 p.2 - b p.1 p.2‖ ^ 2 :=
      ((ha.cont.measurable.sub hbm.measurable).norm.pow_const 2).stronglyMeasurable
    exact (h.integral_prod_right' (ν := (volume : Measure E3))).measurable
  have hE0 : ∀ q ∈ Icc 0 t, 0 ≤ E q := fun q _ => integral_nonneg fun _ => sq_nonneg _
  have hEint_q : ∀ q ∈ Icc 0 t, Integrable fun ξ => ‖a q ξ - b q ξ‖ ^ 2 := fun q hq =>
    integrable_sq_norm_of_memLp ((ha2 q).sub (hb2 q hq))
  have hEM : ∀ q ∈ Icc 0 t, E q ≤ 2 * Ca + 2 * Cb := by
    intro q hq
    have i1 := integrable_sq_norm_of_memLp (ha2 q)
    have i2 := integrable_sq_norm_of_memLp (hb2 q hq)
    calc E q ≤ ∫ ξ, (2 * ‖a q ξ‖ ^ 2 + 2 * ‖b q ξ‖ ^ 2) := by
          refine integral_mono (hEint_q q hq) ((i1.const_mul 2).add (i2.const_mul 2)) (fun ξ => ?_)
          have h1 := norm_sub_le (a q ξ) (b q ξ)
          have h0 := norm_nonneg (a q ξ - b q ξ)
          show ‖a q ξ - b q ξ‖ ^ 2 ≤ 2 * ‖a q ξ‖ ^ 2 + 2 * ‖b q ξ‖ ^ 2
          nlinarith [sq_nonneg (‖a q ξ‖ - ‖b q ξ‖), norm_nonneg (a q ξ), norm_nonneg (b q ξ)]
      _ = 2 * (∫ ξ, ‖a q ξ‖ ^ 2) + 2 * ∫ ξ, ‖b q ξ‖ ^ 2 := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * Ca + 2 * Cb := by linarith [haL2 q, hbL2 q hq]
  have hEi : IntervalIntegrable E volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    refine Measure.integrableOn_of_bounded (M := 2 * Ca + 2 * Cb) (by simp)
      hEm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun q hq => ?_)
    have hq' := Ioc_subset_Icc_self hq
    rw [Real.norm_of_nonneg (hE0 q hq')]
    exact hEM q hq'
  -- a desigualdade integral
  have hmain : ∀ s ∈ Icc 0 t, E s ≤ K * ∫ r in (0 : ℝ)..s, E r := by
    intro s hs
    have hsub : Ioc 0 s ⊆ Icc 0 t := fun q hq => ⟨hq.1.le, hq.2.trans hs.2⟩
    set μs : Measure ℝ := volume.restrict (Ioc 0 s) with hμs
    have hprod : Integrable ψ ((volume : Measure E3).prod μs) := by
      refine (integrable_prod_iff' hψm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
      · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun q hq => ?_)
        simp only [hψphi' q (hsub hq)]
        exact (hstat q (hsub hq)).1
      · have hm : StronglyMeasurable fun q => ∫ ξ, ‖ψ (ξ, q)‖ :=
          hψm.norm.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure E3))
        refine Measure.integrableOn_of_bounded (M := B) (by simp) hm.aestronglyMeasurable ?_
        refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun q hq => ?_)
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        simp only [hψphi' q (hsub hq)]
        exact (hstat q (hsub hq)).2.1
    have hEs : IntegrableOn E (Ioc 0 s) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).mp
        (hEi.mono_set (by rw [uIcc_of_le hs.1, uIcc_of_le ht]; exact Icc_subset_Icc le_rfl hs.2))
    have hR : Integrable (fun ξ => ∫ q in (0 : ℝ)..s, ψ (ξ, q)) :=
      hprod.integral_prod_left.congr (Eventually.of_forall fun ξ =>
        (intervalIntegral.integral_of_le hs.1).symm)
    calc E s ≤ ∫ ξ, ∫ q in (0 : ℝ)..s, ψ (ξ, q) := integral_mono (hEint_q s hs) hR (hpt s hs)
      _ = ∫ ξ, ∫ q, ψ (ξ, q) ∂μs := by
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          exact intervalIntegral.integral_of_le hs.1
      _ = ∫ q, ∫ ξ, ψ (ξ, q) ∂volume ∂μs :=
          integral_integral_swap (f := fun ξ q => ψ (ξ, q)) hprod
      _ ≤ ∫ q, K * E q ∂μs := by
          refine integral_mono_ae hprod.integral_prod_right (hEs.const_mul K) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun q hq => ?_)
          show ∫ ξ, ψ (ξ, q) ≤ K * E q
          simp only [hψphi' q (hsub hq)]
          exact (hstat q (hsub hq)).2.2
      _ = K * ∫ r in (0 : ℝ)..s, E r := by
          rw [integral_const_mul, intervalIntegral.integral_of_le hs.1]
  -- Gronwall
  have hzero := gronwall_int ht hK0 hE0 hEM hEi hmain
  intro r hr
  have h0 : E r = 0 := hzero r hr
  have hae := (integral_eq_zero_iff_of_nonneg (fun ξ => sq_nonneg ‖a r ξ - b r ξ‖)
    (hEint_q r hr)).mp h0
  filter_upwards [hae] with ξ hξ
  have h1 : ‖a r ξ - b r ξ‖ ^ 2 = 0 := hξ
  have h2 : ‖a r ξ - b r ξ‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

end Abstrata

/-! ### A solução suave: mensurabilidade conjunta e cotas `H¹` -/

section Aplicacao

open ATK.NSTrilinear

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

/-- `bt` truncada no tempo é conjuntamente mensurável. -/
theorem stronglyMeasurable_btc (h : SolucaoLocal ν u₀ T U P) (u₀S : SchwartzMap E3 E3) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < T) :
    StronglyMeasurable fun p : ℝ × E3 => bt ν U u₀S (max 0 (min p.1 t)) p.2 := by
  set c : ℝ → ℝ := fun s => max 0 (min s t) with hc
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hc0 : ∀ s, 0 ≤ c s := fun s => le_max_left _ _
  have hct : ∀ s, c s ≤ t := fun s => max_le ht0 (min_le_right _ _)
  have hcs : ∀ s, 0 ≤ s → s ≤ t → c s = s := fun s h0 h1 => by
    show max 0 (min s t) = s
    rw [min_eq_left h1, max_eq_right h0]
  set S : Set ((ℝ × E3) × ℝ) := {q | 0 < q.2} ∩ {q | q.2 ≤ c q.1.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hcc.measurable.comp (measurable_fst.comp measurable_fst)))
  set F : (ℝ × E3) × ℝ → C3 := fun q =>
    heat ν (c q.1.1 - q.2) q.1.2 • ATK.NSFourierBase.lp q.1.2 (NU U (c q.2) q.1.2) with hF
  have hFm : Measurable F := by
    have h1 : Measurable fun q : (ℝ × E3) × ℝ => heat ν (c q.1.1 - q.2) q.1.2 :=
      (continuous_heat ν).measurable.comp
        (((hcc.measurable.comp (measurable_fst.comp measurable_fst)).sub measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))
    have h2 : Measurable fun q : (ℝ × E3) × ℝ => NU U (c q.2) q.1.2 :=
      Measurable.comp (g := fun p : ℝ × E3 => NU U (max 0 (min p.1 t)) p.2)
        (f := fun q : (ℝ × E3) × ℝ => (q.2, q.1.2))
        (stronglyMeasurable_NUc h ht0 ht).measurable
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact h1.smul (ATK.NSIdent.measurable_lp.comp ((measurable_snd.comp measurable_fst).prodMk h2))
  have e : (fun p : ℝ × E3 => bt ν U u₀S (c p.1) p.2) =
      fun p => heat ν (c p.1) p.2 • ahat u₀S p.2 - ∫ s, S.indicator F (p, s) := by
    funext p
    rw [bt, intervalIntegral.integral_of_le (hc0 p.1), ← integral_indicator measurableSet_Ioc]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ Ioc 0 (c p.1)
    · have hS' : (p, s) ∈ S := hs
      rw [indicator_of_mem hs]
      show _ = S.indicator F (p, s)
      rw [indicator_of_mem hS']
      show _ = heat ν (c p.1 - s) p.2 • ATK.NSFourierBase.lp p.2 (NU U (c s) p.2)
      rw [hcs s hs.1.le (hs.2.trans (hct _))]
    · have hS' : (p, s) ∉ S := hs
      rw [indicator_of_notMem hs]
      show _ = S.indicator F (p, s)
      rw [indicator_of_notMem hS']
  have hahat : Continuous (ahat u₀S) := continuous_fourier_L1 (uc u₀S).integrable
  have h1 : StronglyMeasurable fun p : ℝ × E3 => heat ν (c p.1) p.2 • ahat u₀S p.2 :=
    (((continuous_heat ν).comp ((hcc.comp continuous_fst).prodMk continuous_snd)).smul
      (hahat.comp continuous_snd)).stronglyMeasurable
  have h2 : StronglyMeasurable fun p : ℝ × E3 => ∫ s, S.indicator F (p, s) :=
    (hFm.indicator hSm).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  exact e ▸ h1.sub h2

theorem H1_of_enstrofia {f : E3 → C3} (hf2 : MemLp f 2)
    (hf1 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2) :
    H1 f ∧ nH1 f ≤ 2 * (∫ ξ, ‖f ξ‖ ^ 2) + 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2 := by
  have i0 := integrable_sq_norm_of_memLp hf2
  have hpt : ∀ ξ, (w 1 ξ * ‖f ξ‖) ^ 2 ≤ 2 * ‖f ξ‖ ^ 2 + 2 * (‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2) := by
    intro ξ
    have e : (w 1 ξ * ‖f ξ‖) ^ 2 = (1 + ‖ξ‖) ^ 2 * ‖f ξ‖ ^ 2 := by
      unfold w; ring
    rw [e]
    nlinarith [sq_nonneg (1 - ‖ξ‖), sq_nonneg ‖f ξ‖, mul_nonneg (sq_nonneg (1 - ‖ξ‖))
      (sq_nonneg ‖f ξ‖)]
  have hi : Integrable fun ξ => 2 * ‖f ξ‖ ^ 2 + 2 * (‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2) :=
    (i0.const_mul 2).add (hf1.const_mul 2)
  have hm : AEStronglyMeasurable (fun ξ => (w 1 ξ * ‖f ξ‖) ^ 2) volume :=
    (((measurable_w 1).aestronglyMeasurable.mul hf2.aestronglyMeasurable.norm).pow 2)
  have hH : H1 f := hi.mono' hm (Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt ξ)
  refine ⟨hH, (integral_mono hH hi hpt).trans (le_of_eq ?_)⟩
  rw [integral_add (i0.const_mul 2) (hf1.const_mul 2), integral_const_mul, integral_const_mul]

end Aplicacao

/-! ### Unicidade fraca–forte na classe de Fourier -/

open ATK.NSTrilinear in
/-- **Unicidade fraca–forte**: uma solução da classe de Fourier coincide com qualquer solução
suave do modelo genuíno, no intervalo comum. -/
theorem unicidadeF : ATK.NSClasse.UnicidadeD fun d => ATK.NSClasse.ClasseF d.1 := by
  rintro ⟨ν, u₀⟩ ⟨hν, ⟨u₀S, hu₀S⟩, hdiv⟩ T₁ T₂ U₁ U₂ P₁ P₂ ⟨hsol₁, hR⟩ h₂ x t ht0 ht₁ ht₂
  simp only at hν hdiv hu₀S hsol₁ hR h₂ ⊢
  subst hu₀S
  obtain ⟨a, ha, hah, had, ham, hU⟩ := hR t ht0 ht₁
  have hu₀ : ∀ x, u₀S x = u₀S x := fun _ => rfl
  have hdiv₀ : ∀ ξ, ⟪cpx ξ, ahat u₀S ξ⟫_ℂ = 0 := ATK.NSDado.ahat_div u₀S hdiv
  have htT : t ∈ Ico 0 T₂ := ⟨ht0, ht₂⟩
  -- `a(0) = â₀`
  have hVf : ∀ y, ATK.NSSuave.Vf (a 0) y = ATK.NSSuave.Vf (ahat u₀S) y := by
    intro y
    have e1 : U₁ (y, 0) = re3 (ATK.NSSuave.Vf (a 0) y) := by
      rw [hU y 0 le_rfl ht0]
      simp [ATK.NSExistencia.Uf, ATK.NSSuave.V, ATK.NSTempo.ader_zero]
    have e2 : U₁ (y, 0) = u₀S y := hsol₁.2.2.1 y
    rw [ATK.NSDado.Vf_ahat, ← cpx_re3 (ATK.NSFisico.Vf_real (hah 0) y), ← e1, e2]
  obtain ⟨A4, hA40, hA4⟩ := ha.bound 4
  obtain ⟨B4, -, hB4⟩ := ATK.NSDado.ahat_bound u₀S 4
  have hahat : Continuous (ahat u₀S) := continuous_fourier_L1 (uc u₀S).integrable
  have ha0 : a 0 = ahat u₀S :=
    ATK.NSContinuacao.amp_inj (ha.cont_s 0) hahat (hA4 0) hB4 hVf
  -- a cota de energia e enstrofia da solução suave em `[0, t]`
  obtain ⟨C, hC⟩ := h₂.2.2.2.2.2 t ht₂
  set c : ℝ → ℝ := fun s => max 0 (min s t) with hc
  have hcs : ∀ s ∈ Icc 0 t, c s = s := fun s hs => by
    show max 0 (min s t) = s
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hIco : ∀ s ∈ Icc 0 t, s ∈ Ico 0 T₂ := fun s hs => ⟨hs.1, hs.2.trans_lt ht₂⟩
  have hπ : 0 < 4 * π ^ 2 := by positivity
  set Cb : ℝ := 2 * C + 2 * (C / (4 * π ^ 2)) with hCb
  have hbH : ∀ r ∈ Icc 0 t, H1 (bt ν U₂ u₀S (c r)) ∧ nH1 (bt ν U₂ u₀S (c r)) ≤ Cb := by
    intro r hr
    rw [hcs r hr]
    obtain ⟨hE1, hE2⟩ := enstrofia_bt h₂ hν.le u₀S hu₀ hdiv₀ (hIco r hr)
    obtain ⟨hH, hn⟩ := H1_of_enstrofia (memLp_bt h₂ hν.le u₀S hu₀ hdiv₀ (hIco r hr)) hE1
    refine ⟨hH, hn.trans ?_⟩
    have hL2 : ∫ ξ, ‖bt ν U₂ u₀S r ξ‖ ^ 2 ≤ C := by
      rw [integral_norm_sq_bt h₂ hν.le u₀S hu₀ hdiv₀ (hIco r hr)]
      exact (hC r hr).1.2
    have hens : ∫ ξ, ‖ξ‖ ^ 2 * ‖bt ν U₂ u₀S r ξ‖ ^ 2 ≤ C / (4 * π ^ 2) := by
      rw [le_div_iff₀ hπ, mul_comm, hE2]
      exact (hC r hr).2.2
    rw [hCb]
    linarith
  -- a unicidade no lado de Fourier
  have hae := unicidade_fourier (t := t) (a := a) (b := fun r => bt ν U₂ u₀S (c r))
    (G := fun r ξ => NU U₂ (c r) ξ) hν.le ht0 ha hah had ham
    (stronglyMeasurable_btc h₂ u₀S ht0 ht₂)
    (fun r hr => by
      show ATK.NSSimetria.Herm (bt ν U₂ u₀S (c r))
      rw [hcs r hr]; exact bt_herm u₀S r)
    (fun r hr ξ => by
      show ⟪cpx ξ, bt ν U₂ u₀S (c r) ξ⟫_ℂ = 0
      rw [hcs r hr]; exact div_bt h₂ hν.le u₀S hdiv₀ (hIco r hr) ξ)
    (fun r hr => by
      show MemLp (bt ν U₂ u₀S (c r)) 2
      rw [hcs r hr]; exact memLp_bt h₂ hν.le u₀S hu₀ hdiv₀ (hIco r hr))
    hbH (stronglyMeasurable_NUc h₂ ht0 ht₂)
    (fun r hr ξ => by
      show NU U₂ (c r) ξ = Nl (bt ν U₂ u₀S (c r)) (bt ν U₂ u₀S (c r)) ξ
      rw [hcs r hr]; exact NU_eq_Nl h₂ hν.le u₀S hu₀ hdiv₀ (hIco r hr) ξ)
    (fun r hr ξ => by
      show bt ν U₂ u₀S (c r) ξ = heat ν r ξ • a 0 ξ -
        ∫ q in (0 : ℝ)..r, heat ν (r - q) ξ • ATK.NSFourierBase.lp ξ (NU U₂ (c q) ξ)
      rw [hcs r hr, ha0, bt]
      congr 1
      refine intervalIntegral.integral_congr (fun q hq => ?_)
      rw [uIcc_of_le hr.1] at hq
      show _ = heat ν (r - q) ξ • ATK.NSFourierBase.lp ξ (NU U₂ (c q) ξ)
      rw [hcs q ⟨hq.1, hq.2.trans hr.2⟩])
    t ⟨ht0, le_rfl⟩
  -- identificação no espaço físico
  have hbt : (fun ξ => bt ν U₂ u₀S (c t) ξ) = bt ν U₂ u₀S t := by
    rw [hcs t ⟨ht0, le_rfl⟩]
  have hu2 := memLp_cU h₂ htT
  have hat : a t =ᵐ[volume] ⇑(𝓕 (hu2.toLp _) : Lp C3 2 (volume : Measure E3)) := by
    have h1 : a t =ᵐ[volume] bt ν U₂ u₀S t := by
      filter_upwards [hae] with ξ hξ
      rw [hξ, ← hbt]
    have h2 := bF_ae_eq_bt h₂ hν.le u₀S hu₀ hdiv₀ htT
    rw [bF, FL_eq hu2] at h2
    exact h1.trans h2.symm
  obtain ⟨A5, -, hA5⟩ := ha.bound 4
  have ha1 : Integrable (a t) :=
    ATK.NSPlancherel.integrable_of_bound (ha.cont_s t).aestronglyMeasurable (hA5 t)
  have ha2 : MemLp (a t) 2 :=
    ATK.NSPlancherel.memLp_two_of_bound (ha.cont_s t).aestronglyMeasurable (hA5 t)
  have hL : ha2.toLp (a t) = 𝓕 (hu2.toLp _) := Lp.ext (ha2.coeFn_toLp.trans hat)
  have hinv : (𝓕⁻ (ha2.toLp (a t)) : Lp C3 2 (volume : Measure E3)) = hu2.toLp _ := by
    rw [hL]; exact FourierTransform.fourierInv_fourier_eq _
  have e1 := ATK.NSPlancherel.fourierInv_toLp_ae_eq ha1 ha2
  rw [hinv] at e1
  have e2 : (fun y => cpx (U₂ (y, t))) =ᵐ[volume] 𝓕⁻ (a t) := hu2.coeFn_toLp.symm.trans e1
  have heq : (fun y => cpx (U₂ (y, t))) = 𝓕⁻ (a t) :=
    ((contDiff_cU h₂ htT).continuous.ae_eq_iff_eq volume
      (ATK.NSPlancherel.continuous_fourierInv ha1)).mp e2
  have eU1 : U₁ (x, t) = re3 (ATK.NSSuave.Vf (a t) x) := by
    rw [hU x t ht0 le_rfl]
    simp [ATK.NSExistencia.Uf, ATK.NSSuave.V, ATK.NSTempo.ader_zero]
  rw [eU1, ATK.NSPlancherel.Vf_eq_fourierInv, ← congrFun heq x, re3_cpx]

end ATK.NSUnicidade

#print axioms ATK.NSUnicidade.gronwall_int
#print axioms ATK.NSUnicidade.fE_eq
#print axioms ATK.NSUnicidade.norm_sq_lip
#print axioms ATK.NSUnicidade.re_inner_self_C3
#print axioms ATK.NSUnicidade.hasDerivAt_norm_sq_C3
#print axioms ATK.NSUnicidade.energia_edo
#print axioms ATK.NSUnicidade.integral_sq_le_nH1
#print axioms ATK.NSUnicidade.unicidade_fourier
#print axioms ATK.NSUnicidade.stronglyMeasurable_btc
#print axioms ATK.NSUnicidade.H1_of_enstrofia
#print axioms ATK.NSUnicidade.unicidadeF
