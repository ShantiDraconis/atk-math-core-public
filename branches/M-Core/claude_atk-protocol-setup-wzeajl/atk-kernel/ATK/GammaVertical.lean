import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# ATK — `Γ` em faixas verticais e o fator da equação funcional

Cota de Stirling (só a de cima, com o expoente exato) para a função `Γ` complexa da Mathlib na faixa
`1/2 ≤ Re w ≤ 3/2`:

  `‖Γ(w)‖ ≤ C · ‖w‖^(Re w − 1/2) · e^(−π|Im w|/2)`   (`norm_Gamma_le_vertical`),

provada pelo princípio de Phragmén–Lindelöf da Mathlib aplicado a `H(w) = Γ(w) w^(1/2 − w) eʷ`,
limitada nas retas `Re w = 1/2` e `Re w = 3/2` pela fórmula de reflexão
(`‖Γ(1/2 + iy)‖² = π/cosh(πy)`, `norm_sq_Gamma_half`).

Consequência para a equação funcional (`riemannZeta_one_sub`):

  `‖ζ(1 − w)‖ ≤ C · ‖w‖^(Re w − 1/2) · ‖ζ(w)‖`   (`norm_zeta_one_sub_le`).
-/

open Complex Real Set Filter Asymptotics

namespace ATK.GammaVertical

/-! ## Desigualdades elementares -/

theorem norm_Gamma_le_Gamma_re {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem Gamma_le_two {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) : Real.Gamma σ ≤ 2 := by
  have hc := Real.convexOn_Gamma
  have hle := hc.le_max_of_mem_Icc (x := 1 / 2) (y := 3 / 2) (z := σ)
    (by norm_num [mem_Ioi]) (by norm_num [mem_Ioi]) ⟨h1, h2⟩
  have hhalf : Real.Gamma (1 / 2) ≤ 2 := by
    rw [Real.Gamma_one_half_eq]
    have : √π ≤ √4 := Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
  have h32 : Real.Gamma (3 / 2) ≤ 2 := by linarith [Real.Gamma_three_div_two_lt_one]
  exact hle.trans (max_le hhalf h32)

theorem norm_cos_le_cosh (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos, Real.cosh_eq]
  rw [norm_div, Complex.norm_ofNat]
  gcongr
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_exp, Complex.norm_exp]
  simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub, neg_mul, neg_re]
  ring_nf

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [abs_of_nonpos hx]
    have : Real.exp x ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    linarith

theorem exp_abs_le_two_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]; linarith [Real.exp_pos x]

/-! ## `Γ` na reta `Re w = 1/2` -/

/-- **`‖Γ(1/2 + iy)‖² = π / cosh(πy)`** (fórmula de reflexão). -/
theorem norm_sq_Gamma_half (y : ℝ) :
    ‖Complex.Gamma (1 / 2 + y * I)‖ ^ 2 = π / Real.cosh (π * y) := by
  have href := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + y * I)
  have hconj : (1 : ℂ) - (1 / 2 + y * I) = (starRingEnd ℂ) (1 / 2 + y * I) := by
    apply Complex.ext <;> simp; norm_num
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at href
  have hsin : Complex.sin (π * (1 / 2 + y * I)) = Real.cosh (π * y) := by
    rw [show (π : ℂ) * (1 / 2 + y * I) = π / 2 + (π * y : ℝ) * I by push_cast; ring,
      Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
      Complex.sin_mul_I]
    simp [Complex.ofReal_cosh]
  rw [hsin, Complex.normSq_eq_norm_sq] at href
  have h := congrArg Complex.re href
  rw [Complex.ofReal_re, ← Complex.ofReal_div, Complex.ofReal_re] at h
  exact_mod_cast h

theorem norm_Gamma_half_le (y : ℝ) :
    ‖Complex.Gamma (1 / 2 + y * I)‖ ≤ √(2 * π) * Real.exp (-(π * |y|) / 2) := by
  have hsq := norm_sq_Gamma_half y
  have hc : 0 < Real.cosh (π * y) := Real.cosh_pos _
  have hb : Real.exp (π * |y|) ≤ 2 * Real.cosh (π * y) := by
    have := exp_abs_le_two_cosh (π * y)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  have hrhs : (√(2 * π) * Real.exp (-(π * |y|) / 2)) ^ 2 = 2 * π / Real.exp (π * |y|) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), sq, ← Real.exp_add,
      show -(π * |y|) / 2 + -(π * |y|) / 2 = -(π * |y|) by ring, Real.exp_neg, div_eq_mul_inv]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [hsq, hrhs]
  rw [div_le_div_iff₀ hc (Real.exp_pos _)]
  nlinarith [Real.pi_pos]

/-! ## A função `H(w) = Γ(w) w^(1/2 − w) eʷ` -/

/-- A normalização de Stirling. -/
noncomputable def Hst (w : ℂ) : ℂ := Complex.Gamma w * w ^ ((1 / 2 : ℂ) - w) * Complex.exp w

theorem arg_mul_im_bounds {w : ℂ} (hw : 0 < w.re) :
    0 ≤ w.im * arg w ∧ w.im * arg w ≤ π * |w.im| / 2 ∧
      π * |w.im| / 2 - π * w.re / 2 ≤ w.im * arg w := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by rw [h, zero_re] at hw; exact lt_irrefl 0 hw)
  rw [Complex.arg_of_re_nonneg hw.le]
  set y := w.im
  set r := ‖w‖
  have hyr : |y| ≤ r := Complex.abs_im_le_norm w
  have hσr : w.re ≤ r := Complex.re_le_norm w
  have hr2 : r ^ 2 = w.re ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  -- `y · arcsin(y/r) = |y| · arcsin(|y|/r)`
  have hsym : y * Real.arcsin (y / r) = |y| * Real.arcsin (|y| / r) := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_nonpos hy, neg_div, Real.arcsin_neg]; ring
  rw [hsym]
  set a := Real.arcsin (|y| / r)
  have hu0 : 0 ≤ |y| / r := div_nonneg (abs_nonneg _) hn.le
  have hu1 : |y| / r ≤ 1 := (div_le_one hn).mpr hyr
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hu0
  have ha1 : a ≤ π / 2 := Real.arcsin_le_pi_div_two _
  refine ⟨mul_nonneg (abs_nonneg _) ha0, ?_, ?_⟩
  · calc |y| * a ≤ |y| * (π / 2) := mul_le_mul_of_nonneg_left ha1 (abs_nonneg _)
      _ = π * |y| / 2 := by ring
  · -- `b = π/2 − a`, `sin b = cos a = σ/r`, Jordan: `b ≤ (π/2) σ/r`
    have hcos : Real.cos a = w.re / r := by
      rw [Real.cos_arcsin, div_pow, sq_abs]
      rw [show 1 - y ^ 2 / r ^ 2 = (w.re / r) ^ 2 by field_simp; rw [hr2]; ring]
      exact Real.sqrt_sq (div_nonneg hw.le hn.le)
    set b := π / 2 - a
    have hb0 : 0 ≤ b := by simp only [b]; linarith
    have hb1 : b ≤ π / 2 := by simp only [b]; linarith
    have hsinb : Real.sin b = w.re / r := by
      simp only [b]; rw [Real.sin_pi_div_two_sub, hcos]
    have hj := Real.mul_le_sin hb0 hb1
    rw [hsinb] at hj
    have hble : b ≤ π / 2 * (w.re / r) := by
      have hp : 0 < π := Real.pi_pos
      have := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ π / 2)
      calc b = π / 2 * (2 / π * b) := by field_simp
        _ ≤ π / 2 * (w.re / r) := this
    have hyb : |y| * b ≤ π * w.re / 2 := by
      calc |y| * b ≤ |y| * (π / 2 * (w.re / r)) := mul_le_mul_of_nonneg_left hble (abs_nonneg _)
        _ = π / 2 * w.re * (|y| / r) := by ring
        _ ≤ π / 2 * w.re * 1 := by
          gcongr
        _ = π * w.re / 2 := by ring
    have : a = π / 2 - b := by simp only [b]; ring
    rw [this]
    nlinarith

theorem norm_cpow_half_sub {w : ℂ} (hw : 0 < w.re) :
    ‖w ^ ((1 / 2 : ℂ) - w)‖ = ‖w‖ ^ (1 / 2 - w.re) * Real.exp (w.im * arg w) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl 0 hw
  rw [Complex.norm_cpow_of_ne_zero hw0]
  simp only [sub_re, sub_im, div_ofNat_re, one_re, div_ofNat_im, one_im, zero_div, zero_sub]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

theorem norm_Hst {w : ℂ} (hw : 0 < w.re) :
    ‖Hst w‖ = ‖Complex.Gamma w‖ * ‖w‖ ^ (1 / 2 - w.re) * Real.exp (w.im * arg w) *
      Real.exp w.re := by
  rw [Hst, norm_mul, norm_mul, norm_cpow_half_sub hw, Complex.norm_exp]
  ring

theorem differentiableAt_Hst {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Hst w := by
  have hΓ : DifferentiableAt ℂ Complex.Gamma w := by
    refine Complex.differentiableAt_Gamma w (fun m h => ?_)
    rw [h] at hw
    simp at hw
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hslit : w ∈ Complex.slitPlane := Or.inl hw
  have hpow : DifferentiableAt ℂ (fun z : ℂ => z ^ ((1 / 2 : ℂ) - z)) w :=
    differentiableAt_id.cpow (differentiableAt_const _ |>.sub differentiableAt_id) hslit
  exact (hΓ.mul hpow).mul Complex.differentiableAt_exp

/-- Nas retas da fronteira, `‖H‖ ≤ √(2π) e^(3/2)`. -/
theorem norm_Hst_borda_esq (y : ℝ) :
    ‖Hst (1 / 2 + y * I)‖ ≤ √(2 * π) * Real.exp (3 / 2) := by
  have hre : (1 / 2 + y * I : ℂ).re = 1 / 2 := by simp
  have him : (1 / 2 + y * I : ℂ).im = y := by simp
  rw [norm_Hst (by rw [hre]; norm_num), hre, him, sub_self, Real.rpow_zero, mul_one]
  have hb := (arg_mul_im_bounds (w := 1 / 2 + y * I) (by rw [hre]; norm_num)).2.1
  rw [him] at hb
  have hΓ := norm_Gamma_half_le y
  calc ‖Complex.Gamma (1 / 2 + y * I)‖ * Real.exp (y * arg (1 / 2 + y * I)) * Real.exp (1 / 2)
      ≤ (√(2 * π) * Real.exp (-(π * |y|) / 2)) * Real.exp (π * |y| / 2) * Real.exp (3 / 2) := by
        gcongr
        all_goals first | norm_num | exact Real.exp_le_exp.mpr hb
    _ = √(2 * π) * Real.exp (3 / 2) := by
        rw [mul_assoc (√(2 * π)), ← Real.exp_add]
        rw [show -(π * |y|) / 2 + π * |y| / 2 = 0 by ring, Real.exp_zero, mul_one]

theorem norm_Hst_borda_dir (y : ℝ) :
    ‖Hst (3 / 2 + y * I)‖ ≤ √(2 * π) * Real.exp (3 / 2) := by
  have hre : (3 / 2 + y * I : ℂ).re = 3 / 2 := by simp
  have him : (3 / 2 + y * I : ℂ).im = y := by simp
  rw [norm_Hst (by rw [hre]; norm_num), hre, him]
  have hb := (arg_mul_im_bounds (w := 3 / 2 + y * I) (by rw [hre]; norm_num)).2.1
  rw [him] at hb
  -- `Γ(3/2 + iy) = (1/2 + iy) Γ(1/2 + iy)`
  have hrec : Complex.Gamma (3 / 2 + y * I) = (1 / 2 + y * I) * Complex.Gamma (1 / 2 + y * I) := by
    rw [show (3 / 2 + y * I : ℂ) = (1 / 2 + y * I) + 1 by ring]
    exact Complex.Gamma_add_one _ (fun h => by
      have := congrArg Complex.re h
      simp at this)
  have hΓ := norm_Gamma_half_le y
  have hn1 : ‖(1 / 2 + y * I : ℂ)‖ ≤ ‖(3 / 2 + y * I : ℂ)‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    nlinarith
  have hn0 : 0 < ‖(3 / 2 + y * I : ℂ)‖ := by
    refine norm_pos_iff.mpr (fun h => ?_)
    have := congrArg Complex.re h
    simp at this
  have hpow : ‖(3 / 2 + y * I : ℂ)‖ ^ ((1 : ℝ) / 2 - 3 / 2) = ‖(3 / 2 + y * I : ℂ)‖⁻¹ := by
    rw [show (1 : ℝ) / 2 - 3 / 2 = -1 by norm_num, Real.rpow_neg_one]
  rw [hpow, hrec, norm_mul]
  calc ‖(1 / 2 + y * I : ℂ)‖ * ‖Complex.Gamma (1 / 2 + y * I)‖ * ‖(3 / 2 + y * I : ℂ)‖⁻¹ *
        Real.exp (y * arg (3 / 2 + y * I)) * Real.exp (3 / 2)
      ≤ ‖(3 / 2 + y * I : ℂ)‖ * (√(2 * π) * Real.exp (-(π * |y|) / 2)) *
          ‖(3 / 2 + y * I : ℂ)‖⁻¹ * Real.exp (π * |y| / 2) * Real.exp (3 / 2) := by
        gcongr
        all_goals first | exact Real.exp_le_exp.mpr hb | skip
    _ = √(2 * π) * Real.exp (3 / 2) := by
        have hx : ‖(3 / 2 + y * I : ℂ)‖ * ‖(3 / 2 + y * I : ℂ)‖⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
        have he : Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) = 1 := by
          rw [← Real.exp_add, show -(π * |y|) / 2 + π * |y| / 2 = 0 by ring, Real.exp_zero]
        calc ‖(3 / 2 + y * I : ℂ)‖ * (√(2 * π) * Real.exp (-(π * |y|) / 2)) *
              ‖(3 / 2 + y * I : ℂ)‖⁻¹ * Real.exp (π * |y| / 2) * Real.exp (3 / 2)
            = (‖(3 / 2 + y * I : ℂ)‖ * ‖(3 / 2 + y * I : ℂ)‖⁻¹) *
                (Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2)) *
                (√(2 * π) * Real.exp (3 / 2)) := by ring
          _ = √(2 * π) * Real.exp (3 / 2) := by rw [hx, he]; ring

/-- Crescimento a priori na faixa. -/
theorem norm_Hst_le_faixa {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖Hst w‖ ≤ 4 * Real.exp (3 / 2) * Real.exp (π * |w.im| / 2) := by
  have hw : 0 < w.re := by linarith
  rw [norm_Hst hw]
  have hΓ : ‖Complex.Gamma w‖ ≤ 2 :=
    (norm_Gamma_le_Gamma_re hw).trans (Gamma_le_two h1 h2)
  have hn : 1 / 2 ≤ ‖w‖ := h1.trans (Complex.re_le_norm w)
  have hpow : ‖w‖ ^ (1 / 2 - w.re) ≤ 2 := by
    have : ‖w‖ ^ (1 / 2 - w.re) ≤ (1 / 2 : ℝ) ^ (1 / 2 - w.re) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by linarith)
    refine this.trans ?_
    rw [show (1 / 2 : ℝ) ^ (1 / 2 - w.re) = 2 ^ (w.re - 1 / 2) by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg
        (by norm_num)]; ring_nf]
    calc (2 : ℝ) ^ (w.re - 1 / 2) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have harg := (arg_mul_im_bounds hw).2.1
  have hexp : Real.exp w.re ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr h2
  calc ‖Complex.Gamma w‖ * ‖w‖ ^ (1 / 2 - w.re) * Real.exp (w.im * arg w) * Real.exp w.re
      ≤ 2 * 2 * Real.exp (π * |w.im| / 2) * Real.exp (3 / 2) := by
        gcongr
    _ = 4 * Real.exp (3 / 2) * Real.exp (π * |w.im| / 2) := by ring

theorem re_add_im_I (z : ℂ) : z = (z.re : ℂ) + z.im * I := (Complex.re_add_im z).symm

/-- **Phragmén–Lindelöf**: `‖H(w)‖ ≤ √(2π) e^(3/2)` em toda a faixa `1/2 ≤ Re w ≤ 3/2`. -/
theorem norm_Hst_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖Hst w‖ ≤ √(2 * π) * Real.exp (3 / 2) := by
  have hsub : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) ⊆ {z : ℂ | 0 < z.re} := by
    refine (closure_minimal (t := re ⁻¹' Ici (1 / 2 : ℝ))
      (fun z (hz : z ∈ re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) =>
        show z.re ∈ Ici (1 / 2 : ℝ) from le_of_lt hz.1)
      (isClosed_Ici.preimage Complex.continuous_re)).trans ?_
    intro z hz
    simp only [mem_preimage, mem_Ici] at hz
    show 0 < z.re
    linarith
  refine PhragmenLindelof.vertical_strip (a := 1 / 2) (b := 3 / 2) ?_ ?_ ?_ ?_ h1 h2
  · refine ⟨fun z (hz : z ∈ re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) =>
      (differentiableAt_Hst (by have := hz.1; linarith)).differentiableWithinAt,
      fun z (hz : z ∈ closure (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2))) =>
        (differentiableAt_Hst (hsub hz)).continuousAt.continuousWithinAt⟩
  · refine ⟨1, by
      have := Real.pi_gt_three
      rw [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, div_one]; linarith, π / 2, ?_⟩
    refine Asymptotics.IsBigO.of_bound (4 * Real.exp (3 / 2)) ?_
    refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun z hz => ?_)
    have hz1 : 1 / 2 ≤ z.re := le_of_lt hz.1
    have hz2 : z.re ≤ 3 / 2 := le_of_lt hz.2
    refine (norm_Hst_le_faixa hz1 hz2).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
    have := Real.add_one_le_exp |z.im|
    rw [one_mul]
    nlinarith [Real.pi_pos, abs_nonneg z.im]
  · intro z hz
    rw [re_add_im_I z, hz]
    push_cast
    exact norm_Hst_borda_esq z.im
  · intro z hz
    rw [re_add_im_I z, hz]
    push_cast
    exact norm_Hst_borda_dir z.im

/-- A constante de Stirling usada. -/
noncomputable def CΓ : ℝ := √(2 * π) * Real.exp (3 / 2) * Real.exp (3 * π / 4)

theorem CΓ_pos : 0 < CΓ := by unfold CΓ; positivity

/-- **Cota de Stirling** em `1/2 ≤ Re w ≤ 3/2`:
`‖Γ(w)‖ ≤ CΓ · ‖w‖^(Re w − 1/2) · e^(−π|Im w|/2)`. -/
theorem norm_Gamma_le_vertical {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖Complex.Gamma w‖ ≤ CΓ * ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-(π * |w.im|) / 2) := by
  have hw : 0 < w.re := by linarith
  have hH := norm_Hst_le h1 h2
  rw [norm_Hst hw] at hH
  have hn : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  have hb := (arg_mul_im_bounds hw).2.2
  set A := ‖w‖ ^ (1 / 2 - w.re)
  have hA : 0 < A := Real.rpow_pos_of_pos hn _
  have hAinv : A⁻¹ = ‖w‖ ^ (w.re - 1 / 2) := by
    simp only [A]
    rw [← Real.rpow_neg hn.le]
    ring_nf
  have hE : 0 < Real.exp (w.im * arg w) * Real.exp w.re := by positivity
  have key : ‖Complex.Gamma w‖ ≤ √(2 * π) * Real.exp (3 / 2) /
      (A * (Real.exp (w.im * arg w) * Real.exp w.re)) := by
    rw [le_div_iff₀ (mul_pos hA hE)]
    calc ‖Complex.Gamma w‖ * (A * (Real.exp (w.im * arg w) * Real.exp w.re))
        = ‖Complex.Gamma w‖ * A * Real.exp (w.im * arg w) * Real.exp w.re := by ring
      _ ≤ √(2 * π) * Real.exp (3 / 2) := hH
  refine key.trans ?_
  rw [div_le_iff₀ (mul_pos hA hE)]
  -- `exp(−π|y|/2) · exp(y arg w) · exp(σ) ≥ exp(−πσ/2) ≥ exp(−3π/4)`
  have h3 : Real.exp (-(3 * π / 4)) ≤ Real.exp (-(π * |w.im|) / 2) *
      (Real.exp (w.im * arg w) * Real.exp w.re) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hCΓ : CΓ * ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-(π * |w.im|) / 2) *
      (A * (Real.exp (w.im * arg w) * Real.exp w.re)) =
      √(2 * π) * Real.exp (3 / 2) * Real.exp (3 * π / 4) *
        (Real.exp (-(π * |w.im|) / 2) * (Real.exp (w.im * arg w) * Real.exp w.re)) := by
    rw [← hAinv]
    unfold CΓ
    field_simp
  rw [hCΓ]
  calc √(2 * π) * Real.exp (3 / 2)
      = √(2 * π) * Real.exp (3 / 2) * Real.exp (3 * π / 4) * Real.exp (-(3 * π / 4)) := by
        rw [mul_assoc (√(2 * π) * Real.exp (3 / 2)), ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]
    _ ≤ _ := by gcongr

/-! ## O fator da equação funcional -/

/-- **`‖ζ(1 − w)‖ ≤ 2 CΓ · ‖w‖^(Re w − 1/2) · ‖ζ(w)‖`** para `1/2 ≤ Re w ≤ 3/2`, `w ≠ 1`. -/
theorem norm_zeta_one_sub_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) (hw1 : w ≠ 1) :
    ‖riemannZeta (1 - w)‖ ≤ 2 * CΓ * ‖w‖ ^ (w.re - 1 / 2) * ‖riemannZeta w‖ := by
  have hw : 0 < w.re := by linarith
  have hn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    rw [h] at hw
    simp at hw
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [riemannZeta_one_sub hn hw1]
  have h2pi : ‖(2 * (π : ℂ)) ^ (-w)‖ ≤ 1 := by
    have hb : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [hb, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three]) (by linarith)
  have hcos : ‖Complex.cos (π * w / 2)‖ ≤ Real.exp (π * |w.im| / 2) := by
    refine (norm_cos_le_cosh _).trans ((cosh_le_exp_abs _).trans (le_of_eq ?_))
    congr 1
    have : (π * w / 2 : ℂ).im = π * w.im / 2 := by simp [mul_comm]
    rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  have hΓ := norm_Gamma_le_vertical h1 h2
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  have hG0 : 0 ≤ CΓ * ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-(π * |w.im|) / 2) :=
    mul_nonneg (mul_nonneg CΓ_pos.le (Real.rpow_nonneg (norm_nonneg _) _)) (Real.exp_pos _).le
  calc 2 * ‖(2 * (π : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ *
        ‖riemannZeta w‖
      ≤ 2 * 1 * (CΓ * ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-(π * |w.im|) / 2)) *
          Real.exp (π * |w.im| / 2) * ‖riemannZeta w‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine mul_le_mul ?_ hcos (norm_nonneg _) (by positivity)
        exact mul_le_mul (by linarith) hΓ (norm_nonneg _) (by norm_num)
    _ = 2 * CΓ * ‖w‖ ^ (w.re - 1 / 2) * ‖riemannZeta w‖ := by
        rw [show 2 * 1 * (CΓ * ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-(π * |w.im|) / 2)) *
          Real.exp (π * |w.im| / 2) * ‖riemannZeta w‖ = 2 * CΓ * ‖w‖ ^ (w.re - 1 / 2) *
          (Real.exp (-(π * |w.im|) / 2) * Real.exp (π * |w.im| / 2)) * ‖riemannZeta w‖ by ring,
          ← Real.exp_add, show -(π * |w.im|) / 2 + π * |w.im| / 2 = 0 by ring, Real.exp_zero,
          mul_one]

end ATK.GammaVertical

#print axioms ATK.GammaVertical.norm_Gamma_le_Gamma_re
#print axioms ATK.GammaVertical.Gamma_le_two
#print axioms ATK.GammaVertical.norm_cos_le_cosh
#print axioms ATK.GammaVertical.cosh_le_exp_abs
#print axioms ATK.GammaVertical.exp_abs_le_two_cosh
#print axioms ATK.GammaVertical.norm_sq_Gamma_half
#print axioms ATK.GammaVertical.norm_Gamma_half_le
#print axioms ATK.GammaVertical.arg_mul_im_bounds
#print axioms ATK.GammaVertical.norm_cpow_half_sub
#print axioms ATK.GammaVertical.norm_Hst
#print axioms ATK.GammaVertical.differentiableAt_Hst
#print axioms ATK.GammaVertical.norm_Hst_borda_esq
#print axioms ATK.GammaVertical.norm_Hst_borda_dir
#print axioms ATK.GammaVertical.norm_Hst_le_faixa
#print axioms ATK.GammaVertical.re_add_im_I
#print axioms ATK.GammaVertical.norm_Hst_le
#print axioms ATK.GammaVertical.CΓ_pos
#print axioms ATK.GammaVertical.norm_Gamma_le_vertical
#print axioms ATK.GammaVertical.norm_zeta_one_sub_le
