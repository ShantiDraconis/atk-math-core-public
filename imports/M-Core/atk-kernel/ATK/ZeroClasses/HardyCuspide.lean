import ATK.AtaqueRH
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Hardy, parte 1: a teta na cúspide `y = i` (rodada 47)

O alvo R4 do programa (`ATK.AtaqueRH.Hardy`: infinitos zeros na reta crítica, Hardy 1914) passa pela
função `θ(y) = Σ_{n ∈ ℤ} e^{−πn²y}` (`th`), holomorfa em `Re y > 0`, perto do ponto `y = i` da fronteira. Aqui:

* **`th_cusp_eq`**: `θ(i + η) = θ₂(½, iη)` (sinais `(−1)^n`, porque `n(n + 1)` é par);
* **`norm_th_cusp`**: pela equação funcional da Mathlib, para `Re η > 0` e `Re(1/η) ≥ 1`,
  `|θ(i + η)| ≤ K₀ |η|^{−1/2} e^{−(π/4) Re(1/η)}`: a teta decai **mais rápido que qualquer potência** na cúspide;
* `Th(u) = e^{u/2} θ(e^{2u})` é holomorfa na faixa `|Im u| < π/4` (`Th_diff`);
* **`iteratedDeriv_Th_tendsto`**: para todo `k`, `Th^{(k)}(iα) → 0` quando `α → π/4⁻` (estimativa de Cauchy num
  círculo de raio `(π/4 − α)/2`, onde `Re(1/η) ≥ 1/(72πr)`).

É a peça analítica do argumento de Hardy: com `H(u) = 2 cosh(u/2) − Th(u)`, os momentos
`∫ Ξ(t)/(t² + ¼) t^{2n} cosh(αt) dt = (−1)^n (π/2) H^{(2n)}(iα)` tendem a `(−1)^n π cos(π/8)/4^n`, com sinal
alternado (rodadas seguintes).

Classificação (rodada 47): **ferramenta** (primeira peça do teorema de Hardy). Não é RH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.Hardy

/-- `θ(y) = Σ_{n ∈ ℤ} e^{−πn²y}`. -/
noncomputable def th (y : ℂ) : ℂ := jacobiTheta₂ 0 (I * y)

/-- **A cúspide**: `θ(i + η) = θ₂(½, iη)`. -/
theorem th_cusp_eq (η : ℂ) : th (I + η) = jacobiTheta₂ (1 / 2) (I * η) := by
  unfold th jacobiTheta₂
  congr 1
  funext n
  unfold jacobiTheta₂_term
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have hk' : (n : ℂ) * (n + 1) = (k : ℂ) + k := by exact_mod_cast hk
  have e : 2 * π * I * n * 0 + π * I * n ^ 2 * (I * (I + η)) =
      (2 * π * I * n * (1 / 2) + π * I * n ^ 2 * (I * η)) + ((-k : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    linear_combination (-(π : ℂ) * I) * hk' + (π * I * (n : ℂ) ^ 2) * I_mul_I
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A constante `K₀ = Σ_{n ∈ ℤ} e^{−π(n² − |n|)}`. -/
noncomputable def K0 : ℝ := ∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))

theorem hasSum_K0 : HasSum (fun n : ℤ => Real.exp (-π * ((n : ℝ) ^ 2 - 2 * (1 / 2) * ((|n| : ℤ) : ℝ)))) K0 := by
  have := summable_pow_mul_jacobiTheta₂_term_bound (1 / 2) one_pos 0
  simp only [pow_zero, one_mul] at this
  exact this.hasSum

theorem K0_nonneg : 0 ≤ K0 := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- `|θ₂(z, σ)| ≤ K₀` quando `Im σ = R ≥ 1` e `|Im z| ≤ R/2`. -/
theorem norm_theta2_le {z σ : ℂ} {R : ℝ} (hR : 1 ≤ R) (hσ : σ.im = R) (hz : |z.im| ≤ R / 2) :
    ‖jacobiTheta₂ z σ‖ ≤ K0 := by
  refine tsum_of_norm_bounded hasSum_K0 fun n => ?_
  have h := norm_jacobiTheta₂_term_le (S := R / 2) (T := R) (by linarith) hz hσ.ge n
  refine h.trans (Real.exp_le_exp.mpr ?_)
  simp only [Int.cast_abs]
  have hn : 0 ≤ (n : ℝ) ^ 2 - |(n : ℝ)| := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have : 1 ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn
      nlinarith [sq_abs (n : ℝ)]
  have : (n : ℝ) ^ 2 - |(n : ℝ)| ≤ R * ((n : ℝ) ^ 2 - |(n : ℝ)|) := le_mul_of_one_le_left hn hR
  nlinarith [mul_le_mul_of_nonneg_left this Real.pi_pos.le]

/-- **A teta na cúspide**: `|θ(i + η)| ≤ K₀ |η|^{−1/2} e^{−(π/4) Re(1/η)}` para `Re η > 0`, `Re(1/η) ≥ 1`. -/
theorem norm_th_cusp {η : ℂ} (hη : 0 < η.re) (hR : 1 ≤ (η⁻¹).re) :
    ‖th (I + η)‖ ≤ K0 * ‖η‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 4) * (η⁻¹).re) := by
  have hη0 : η ≠ 0 := fun h => by rw [h, zero_re] at hη; exact lt_irrefl 0 hη
  rw [th_cusp_eq, jacobiTheta₂_functional_equation]
  have e1 : -I * (I * η) = η := by
    have := I_mul_I
    linear_combination (-η) * this
  have e2 : -(π : ℂ) * I * (1 / 2 : ℂ) ^ 2 / (I * η) = ((-(π / 4) : ℝ) : ℂ) * η⁻¹ := by
    push_cast
    field_simp
    ring_nf
  have e3 : (1 / 2 : ℂ) / (I * η) = -(I / 2) * η⁻¹ := by
    rw [div_eq_iff (mul_ne_zero I_ne_zero hη0)]
    symm
    calc -(I / 2) * η⁻¹ * (I * η) = -(I * I) / 2 * (η⁻¹ * η) := by ring
      _ = 1 / 2 := by rw [I_mul_I, inv_mul_cancel₀ hη0]; ring
  have e4 : (-1 : ℂ) / (I * η) = I * η⁻¹ := by
    rw [div_eq_iff (mul_ne_zero I_ne_zero hη0)]
    symm
    calc I * η⁻¹ * (I * η) = (I * I) * (η⁻¹ * η) := by ring
      _ = -1 := by rw [I_mul_I, inv_mul_cancel₀ hη0]; ring
  rw [e1, e2, e3, e4, norm_mul, norm_mul, norm_div, norm_one, Complex.norm_exp]
  have hre : (((-(π / 4) : ℝ) : ℂ) * η⁻¹).re = -(π / 4) * (η⁻¹).re := by
    rw [re_ofReal_mul]
  rw [hre]
  have hcp : ‖η ^ (1 / 2 : ℂ)‖ = ‖η‖ ^ (1 / 2 : ℝ) := by
    have := norm_cpow_real η (1 / 2)
    push_cast at this
    exact this
  rw [hcp]
  have hth : ‖jacobiTheta₂ (-(I / 2) * η⁻¹) (I * η⁻¹)‖ ≤ K0 := by
    apply norm_theta2_le hR
    · simp
    · have : (-(I / 2) * η⁻¹).im = -((η⁻¹).re / 2) := by simp; ring
      rw [this, abs_neg, abs_of_nonneg (by linarith)]
  have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
  have hinv : 1 / ‖η‖ ^ (1 / 2 : ℝ) = ‖η‖ ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hpos.le, one_div]
  rw [hinv]
  calc ‖η‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 4) * (η⁻¹).re) * ‖jacobiTheta₂ (-(I / 2) * η⁻¹) (I * η⁻¹)‖
      ≤ ‖η‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 4) * (η⁻¹).re) * K0 :=
        mul_le_mul_of_nonneg_left hth (by positivity)
    _ = K0 * ‖η‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 4) * (η⁻¹).re) := by ring

/-! ## 2. `Θ(u) = e^{u/2} θ(e^{2u})` na faixa `|Im u| < π/4` -/

/-- `Θ(u) = e^{u/2} θ(e^{2u})`. -/
noncomputable def Th (u : ℂ) : ℂ := cexp (u / 2) * th (cexp (2 * u))

theorem re_exp_two_pos {u : ℂ} (hu : |u.im| < π / 4) : 0 < (cexp (2 * u)).re := by
  rw [Complex.exp_re]
  have him : (2 * u).im = 2 * u.im := by simp
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · rw [him]; linarith [(abs_lt.mp hu).1]
  · rw [him]; linarith [(abs_lt.mp hu).2]

theorem th_diff {y : ℂ} (hy : 0 < y.re) : DifferentiableAt ℂ th y := by
  have h : 0 < (I * y).im := by simpa using hy
  exact (differentiableAt_jacobiTheta₂_snd 0 h).comp y (differentiableAt_id.const_mul I)

theorem Th_diff {u : ℂ} (hu : |u.im| < π / 4) : DifferentiableAt ℂ Th u := by
  have h1 : DifferentiableAt ℂ (fun u : ℂ => cexp (u / 2)) u := by fun_prop
  have h2 : DifferentiableAt ℂ (th ∘ fun u : ℂ => cexp (2 * u)) u :=
    (th_diff (re_exp_two_pos hu)).comp (f := fun u : ℂ => cexp (2 * u)) u (by fun_prop)
  exact h1.mul h2

/-! ## 3. A estimativa na cúspide -/

/-- Geometria perto de `u = iπ/4`: com `α = π/4 − 2r` e `|u − iα| ≤ r`, `η = e^{2u} − i` tem
`Re η ≥ 2r/π` e `|η| ≤ 12r`. -/
theorem geometria {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 250) {u : ℂ}
    (hu : ‖u - I * ((π / 4 - 2 * r : ℝ) : ℂ)‖ ≤ r) :
    2 * r / π ≤ (cexp (2 * u) - I).re ∧ ‖cexp (2 * u) - I‖ ≤ 12 * r := by
  have hπ := Real.pi_gt_three
  have hx : |u.re| ≤ r := by
    have := Complex.abs_re_le_norm (u - I * ((π / 4 - 2 * r : ℝ) : ℂ))
    simp only [sub_re, mul_re, I_re, ofReal_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero] at this
    linarith
  have hy : |u.im - (π / 4 - 2 * r)| ≤ r := by
    have := Complex.abs_im_le_norm (u - I * ((π / 4 - 2 * r : ℝ) : ℂ))
    simp only [sub_im, mul_im, I_re, ofReal_re, I_im, ofReal_im, zero_mul, one_mul,
      zero_add] at this
    linarith
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  constructor
  · -- a parte real
    have hre : (cexp (2 * u) - I).re = Real.exp (2 * u.re) * Real.cos (2 * u.im) := by
      rw [sub_re, I_re, sub_zero, Complex.exp_re]
      simp
    rw [hre]
    have hcos : Real.sin (2 * r) ≤ Real.cos (2 * u.im) := by
      rw [← Real.cos_pi_div_two_sub]
      apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith
    have hsin : 2 / π * (2 * r) < Real.sin (2 * r) := Real.mul_lt_sin (by linarith) (by linarith)
    have hexp : 1 / 2 ≤ Real.exp (2 * u.re) := by
      have := Real.add_one_le_exp (2 * u.re)
      linarith
    have h4 : 2 * r / π = 1 / 2 * (2 / π * (2 * r)) := by field_simp
    rw [h4]
    exact mul_le_mul hexp (hsin.le.trans hcos) (by positivity) (Real.exp_pos _).le
  · -- a norma
    have hw : ‖2 * u - (π / 2 : ℂ) * I‖ ≤ 6 * r := by
      have e : 2 * u - (π / 2 : ℂ) * I = 2 * (u - I * ((π / 4 - 2 * r : ℝ) : ℂ)) + ((-4 * r : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith : -4 * r < 0)]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith
    have e2 : cexp (2 * u) - I = I * (cexp (2 * u - (π / 2 : ℂ) * I) - 1) := by
      rw [Complex.exp_sub, exp_pi_div_two_mul_I]
      field_simp
    rw [e2, norm_mul, norm_I, one_mul]
    calc ‖cexp (2 * u - (π / 2 : ℂ) * I) - 1‖ ≤ 2 * ‖2 * u - (π / 2 : ℂ) * I‖ :=
          Complex.norm_exp_sub_one_le (by linarith)
      _ ≤ 12 * r := by linarith

/-- **A estimativa na cúspide**: no círculo `|u − iα| = r`, `α = π/4 − 2r`,
`|Θ(u)| ≤ 2 K₀ (2r/π)^{−1/2} e^{−1/(288 r)}`. -/
theorem norm_Th_cusp {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 250) {u : ℂ}
    (hu : ‖u - I * ((π / 4 - 2 * r : ℝ) : ℂ)‖ ≤ r) :
    ‖Th u‖ ≤ 2 * K0 * (2 * r / π) ^ (-(1 / 2 : ℝ)) * Real.exp (-1 / (288 * r)) := by
  have hπ := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  obtain ⟨hre, hnorm⟩ := geometria hr hr1 hu
  set η := cexp (2 * u) - I with hηdef
  have hη : 0 < η.re := lt_of_lt_of_le (by positivity) hre
  have hηn : 2 * r / π ≤ ‖η‖ := hre.trans (re_le_norm η)
  have hR : 1 / (72 * π * r) ≤ (η⁻¹).re := by
    rw [inv_re, Complex.normSq_eq_norm_sq]
    have h1 : ‖η‖ ^ 2 ≤ (12 * r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have h2 : 0 < ‖η‖ ^ 2 := by have := lt_of_lt_of_le (by positivity) hηn; positivity
    calc 1 / (72 * π * r) = (2 * r / π) / (12 * r) ^ 2 := by field_simp; ring
      _ ≤ η.re / (12 * r) ^ 2 := div_le_div_of_nonneg_right hre (by positivity)
      _ ≤ η.re / ‖η‖ ^ 2 := div_le_div_of_nonneg_left hη.le h2 h1
  have hR1 : 1 ≤ (η⁻¹).re := by
    refine le_trans ?_ hR
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hth := norm_th_cusp hη hR1
  have e : cexp (2 * u) = I + η := by rw [hηdef]; ring
  unfold Th
  rw [norm_mul, e]
  have hexp : ‖cexp (u / 2)‖ ≤ 2 := by
    rw [Complex.norm_exp]
    have : (u / 2).re ≤ 1 / 2 := by
      have := Complex.abs_re_le_norm (u - I * ((π / 4 - 2 * r : ℝ) : ℂ))
      simp only [sub_re, mul_re, I_re, ofReal_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero] at this
      rw [div_ofNat_re]
      linarith [le_abs_self u.re]
    calc Real.exp (u / 2).re ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr this
      _ ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
  have hpow : ‖η‖ ^ (-(1 / 2 : ℝ)) ≤ (2 * r / π) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_neg (by positivity)]
    apply inv_anti₀ (by positivity)
    exact Real.rpow_le_rpow (by positivity) hηn (by norm_num)
  have hexp2 : Real.exp (-(π / 4) * (η⁻¹).re) ≤ Real.exp (-1 / (288 * r)) := by
    apply Real.exp_le_exp.mpr
    have : -(π / 4) * (η⁻¹).re ≤ -(π / 4) * (1 / (72 * π * r)) :=
      mul_le_mul_of_nonpos_left hR (by linarith)
    calc -(π / 4) * (η⁻¹).re ≤ -(π / 4) * (1 / (72 * π * r)) := this
      _ = -1 / (288 * r) := by field_simp; ring
  have hK := K0_nonneg
  calc ‖cexp (u / 2)‖ * ‖th (I + η)‖
      ≤ 2 * (K0 * ‖η‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 4) * (η⁻¹).re)) :=
        mul_le_mul hexp hth (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (K0 * (2 * r / π) ^ (-(1 / 2 : ℝ)) * Real.exp (-1 / (288 * r))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hK) hexp2 (by positivity) (by positivity)
    _ = 2 * K0 * (2 * r / π) ^ (-(1 / 2 : ℝ)) * Real.exp (-1 / (288 * r)) := by ring

/-- **Cauchy**: `|Θ^{(k)}(iα)| ≤ k! · 2K₀ (2r/π)^{−1/2} e^{−1/(288 r)} / r^k`, `α = π/4 − 2r`. -/
theorem norm_iteratedDeriv_Th_le (k : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 250) :
    ‖iteratedDeriv k Th (I * ((π / 4 - 2 * r : ℝ) : ℂ))‖ ≤
      k.factorial * (2 * K0 * (2 * r / π) ^ (-(1 / 2 : ℝ)) * Real.exp (-1 / (288 * r))) / r ^ k := by
  have hπ := Real.pi_gt_three
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro u hu
    apply (Th_diff _).differentiableWithinAt
    rw [mem_closedBall, dist_eq_norm] at hu
    have := Complex.abs_im_le_norm (u - I * ((π / 4 - 2 * r : ℝ) : ℂ))
    simp only [sub_im, mul_im, I_re, ofReal_re, I_im, ofReal_im, zero_mul, one_mul,
      zero_add] at this
    rw [abs_lt]
    constructor <;> linarith [abs_le.mp (this.trans hu)]
  · intro u hu
    rw [mem_sphere_iff_norm] at hu
    exact norm_Th_cusp hr hr1 hu.le

/-- **As derivadas de `Θ` se anulam na cúspide**: `Θ^{(k)}(i(π/4 − 2r)) → 0` quando `r → 0⁺`. -/
theorem iteratedDeriv_Th_tendsto (k : ℕ) :
    Tendsto (fun r : ℝ => iteratedDeriv k Th (I * ((π / 4 - 2 * r : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  have hπ := Real.pi_gt_three
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- `s = 1/(288 r) → ∞`
  have hs : Tendsto (fun r : ℝ => 1 / (288 * r)) (𝓝[>] 0) atTop := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop (show (0 : ℝ) < 1 / 288 by norm_num)
    refine this.congr fun r => ?_
    field_simp
  have hlim := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + 1)).comp hs).const_mul
    (k.factorial * (2 * K0 * (2 / π) ^ (-(1 / 2 : ℝ))) * 288 ^ (k + 1))
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 250 by norm_num)] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hK := K0_nonneg
  have h1 : r ^ (-(1 / 2 : ℝ)) ≤ r ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 (by linarith) (by norm_num)
  have h2 : r ^ (-1 : ℝ) / r ^ k = 288 ^ (k + 1) * (1 / (288 * r)) ^ (k + 1) := by
    have hr' : r ≠ 0 := hr0.ne'
    rw [Real.rpow_neg_one, ← mul_pow, show (288 : ℝ) * (1 / (288 * r)) = r⁻¹ by field_simp, inv_pow,
      pow_succ, mul_inv, div_eq_mul_inv, mul_comm]
  have hexp : Real.exp (-1 / (288 * r)) = Real.exp (-(1 / (288 * r))) := by ring_nf
  calc ‖iteratedDeriv k Th (I * ((π / 4 - 2 * r : ℝ) : ℂ))‖
      ≤ k.factorial * (2 * K0 * (2 * r / π) ^ (-(1 / 2 : ℝ)) * Real.exp (-1 / (288 * r))) / r ^ k :=
        norm_iteratedDeriv_Th_le k hr0 hr1.le
    _ = k.factorial * (2 * K0 * (2 / π) ^ (-(1 / 2 : ℝ))) * (r ^ (-(1 / 2 : ℝ)) / r ^ k) *
          Real.exp (-1 / (288 * r)) := by
        rw [show 2 * r / π = 2 / π * r by ring, Real.mul_rpow (by positivity) hr0.le]
        ring
    _ ≤ k.factorial * (2 * K0 * (2 / π) ^ (-(1 / 2 : ℝ))) * (r ^ (-1 : ℝ) / r ^ k) *
          Real.exp (-1 / (288 * r)) := by
        gcongr
    _ = k.factorial * (2 * K0 * (2 / π) ^ (-(1 / 2 : ℝ))) * 288 ^ (k + 1) *
          ((1 / (288 * r)) ^ (k + 1) * Real.exp (-(1 / (288 * r)))) := by
        rw [h2, hexp]; ring

end ATK.ZeroClasses.Hardy

#print axioms ATK.ZeroClasses.Hardy.th_cusp_eq
#print axioms ATK.ZeroClasses.Hardy.hasSum_K0
#print axioms ATK.ZeroClasses.Hardy.K0_nonneg
#print axioms ATK.ZeroClasses.Hardy.norm_theta2_le
#print axioms ATK.ZeroClasses.Hardy.norm_th_cusp
#print axioms ATK.ZeroClasses.Hardy.re_exp_two_pos
#print axioms ATK.ZeroClasses.Hardy.th_diff
#print axioms ATK.ZeroClasses.Hardy.Th_diff
#print axioms ATK.ZeroClasses.Hardy.geometria
#print axioms ATK.ZeroClasses.Hardy.norm_Th_cusp
#print axioms ATK.ZeroClasses.Hardy.norm_iteratedDeriv_Th_le
#print axioms ATK.ZeroClasses.Hardy.iteratedDeriv_Th_tendsto
