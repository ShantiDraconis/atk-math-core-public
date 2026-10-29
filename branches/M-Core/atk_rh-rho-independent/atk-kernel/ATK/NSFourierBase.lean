import ATK.LigacaoNS
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Group.Integral

/-!
# ATK — Navier–Stokes no lado de Fourier: pesos, convolução, calor e projetor de Leray

Base para a existência local (camada 2 do ataque a B3). No lado de Fourier, `ξ ∈ ℝ³` e as
amplitudes são campos `ℝ³ → ℂ³`. Aqui ficam as estimativas elementares:

* pesos `w m ξ = (1 + ‖ξ‖)^m`, `w m ξ ≤ 2^m (w m η + w m (ξ − η))`, e `I₄ = ∫ w₄⁻¹ < ∞`
  (`integrable_w_inv`, via `integrable_one_add_norm`);
* **convolução com pesos** (`conv_peso`): se `φ ≤ A w₄⁻¹`, `φ ≤ A' w_m⁻¹` e o mesmo para `ψ`, então
  `w_m(ξ) ∫ φ(η) ψ(ξ − η) dη ≤ 2^m I₄ (A' B + A B')` — a estimativa "mansa" que deixa o tempo
  de existência depender só da norma `m = 4`;
* **calor** (`calor_grad_le`): `2π‖ξ‖ e^{−4π²ν‖ξ‖²τ} ≤ (ντ)^{−1/2}`;
* **projetor de Leray** `lp ξ v = v − (⟪ξ, v⟫/‖ξ‖²) ξ` (`norm_lp_le`, `inner_lp`);
* o termo não linear `Nl f g ξ = 2πi Σ_j ξ_j ∫ f_j(η) g(ξ − η) dη` (a transformada de
  `div(u ⊗ v)`) e sua cota (`norm_Nl_le`).

Nada aqui é sobre soluções; **CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace ATK.NSFourierBase

open ATK.LigacaoNS

/-- Vetores complexos `ℂ³`. -/
abbrev C3 := EuclideanSpace ℂ (Fin 3)

/-! ### Pesos -/

/-- O peso `(1 + ‖ξ‖)^m`. -/
noncomputable def w (m : ℕ) (ξ : E3) : ℝ := (1 + ‖ξ‖) ^ m

theorem w_pos (m : ℕ) (ξ : E3) : 0 < w m ξ := by unfold w; positivity

theorem one_le_w (m : ℕ) (ξ : E3) : 1 ≤ w m ξ :=
  one_le_pow₀ (by linarith [norm_nonneg ξ])

theorem w_mono {m n : ℕ} (h : m ≤ n) (ξ : E3) : w m ξ ≤ w n ξ :=
  pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) h

theorem w_succ (m : ℕ) (ξ : E3) : w (m + 1) ξ = (1 + ‖ξ‖) * w m ξ := by
  unfold w; ring

theorem continuous_w (m : ℕ) : Continuous (w m) := by
  unfold w; fun_prop

/-- `w_m(ξ) ≤ 2^m (w_m(η) + w_m(ξ − η))`. -/
theorem w_le_add (m : ℕ) (ξ η : E3) : w m ξ ≤ 2 ^ m * (w m η + w m (ξ - η)) := by
  unfold w
  have h1 : 1 + ‖ξ‖ ≤ (1 + ‖η‖) + (1 + ‖ξ - η‖) := by
    have := norm_add_le η (ξ - η)
    rw [add_sub_cancel] at this
    linarith
  have hη : 0 ≤ 1 + ‖η‖ := by positivity
  have hξη : 0 ≤ 1 + ‖ξ - η‖ := by positivity
  rcases le_total (1 + ‖η‖) (1 + ‖ξ - η‖) with h | h
  · calc (1 + ‖ξ‖) ^ m ≤ (2 * (1 + ‖ξ - η‖)) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * (1 + ‖ξ - η‖) ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * ((1 + ‖η‖) ^ m + (1 + ‖ξ - η‖) ^ m) := by
          gcongr; exact le_add_of_nonneg_left (by positivity)
  · calc (1 + ‖ξ‖) ^ m ≤ (2 * (1 + ‖η‖)) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * (1 + ‖η‖) ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * ((1 + ‖η‖) ^ m + (1 + ‖ξ - η‖) ^ m) := by
          gcongr; exact le_add_of_nonneg_right (by positivity)

/-- `w₄⁻¹` é integrável em `ℝ³`. -/
theorem integrable_w_inv : Integrable (fun ξ : E3 => (w 4 ξ)⁻¹) := by
  have h := integrable_one_add_norm (E := E3) (μ := volume) (r := 4) (by simp; norm_num)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only [w]
  rw [Real.rpow_neg (by positivity)]
  congr 1
  exact_mod_cast Real.rpow_natCast (1 + ‖ξ‖) 4

/-- `I₄ = ∫ (1 + ‖ξ‖)^{−4} dξ`. -/
noncomputable def I4 : ℝ := ∫ ξ : E3, (w 4 ξ)⁻¹

theorem I4_nonneg : 0 ≤ I4 := integral_nonneg fun ξ => (inv_pos.mpr (w_pos 4 ξ)).le

/-- Se `0 ≤ φ ≤ A w₄⁻¹` então `∫ φ ≤ A I₄`. -/
theorem integral_le_I4 {φ : E3 → ℝ} (hφ0 : ∀ η, 0 ≤ φ η) {A : ℝ}
    (hφ : ∀ η, φ η ≤ A * (w 4 η)⁻¹) (hm : AEStronglyMeasurable φ volume) :
    ∫ η, φ η ≤ A * I4 := by
  have hint : Integrable (fun η => A * (w 4 η)⁻¹) := integrable_w_inv.const_mul A
  calc ∫ η, φ η ≤ ∫ η, A * (w 4 η)⁻¹ :=
        integral_mono_of_nonneg (Eventually.of_forall hφ0) hint (Eventually.of_forall hφ)
    _ = A * I4 := by rw [integral_const_mul]; rfl

theorem integrable_of_le_w4 {φ : E3 → ℝ} (hφ0 : ∀ η, 0 ≤ φ η) {A : ℝ}
    (hφ : ∀ η, φ η ≤ A * (w 4 η)⁻¹) (hm : AEStronglyMeasurable φ volume) :
    Integrable φ := by
  refine (integrable_w_inv.const_mul A).mono' hm (Eventually.of_forall fun η => ?_)
  rw [Real.norm_of_nonneg (hφ0 η)]
  exact hφ η

/-! ### Convolução com pesos -/

/-- **Estimativa de convolução com pesos (mansa).** -/
theorem conv_peso (m : ℕ) {φ ψ : E3 → ℝ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ0 : ∀ η, 0 ≤ φ η) (hψ0 : ∀ η, 0 ≤ ψ η) {A A' B B' : ℝ}
    (hA : ∀ η, φ η ≤ A * (w 4 η)⁻¹) (hA' : ∀ η, φ η ≤ A' * (w m η)⁻¹)
    (hB : ∀ η, ψ η ≤ B * (w 4 η)⁻¹) (hB' : ∀ η, ψ η ≤ B' * (w m η)⁻¹) (ξ : E3) :
    w m ξ * ∫ η, φ η * ψ (ξ - η) ≤ 2 ^ m * I4 * (A' * B + A * B') := by
  have hA0 : 0 ≤ A := by
    have := (hφ0 0).trans (hA 0)
    exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos 4 0))
  have hB0 : 0 ≤ B := by
    have := (hψ0 0).trans (hB 0)
    exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos 4 0))
  have hA'0 : 0 ≤ A' := by
    have := (hφ0 0).trans (hA' 0)
    exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos m 0))
  have hB'0 : 0 ≤ B' := by
    have := (hψ0 0).trans (hB' 0)
    exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos m 0))
  have hψs : Continuous fun η => ψ (ξ - η) := hψc.comp (continuous_const.sub continuous_id)
  have hψint : Integrable fun η => ψ (ξ - η) :=
    (integrable_of_le_w4 hψ0 hB hψc.aestronglyMeasurable).comp_sub_left ξ
  have hφint : Integrable φ := integrable_of_le_w4 hφ0 hA hφc.aestronglyMeasurable
  have hψle1 : ∀ η, ψ η ≤ B := fun η =>
    (hB η).trans (mul_le_of_le_one_right hB0 (inv_le_one_of_one_le₀ (one_le_w 4 η)))
  -- os dois pedaços
  have h1 : ∀ η, w m η * φ η * ψ (ξ - η) ≤ A' * ψ (ξ - η) := by
    intro η
    have : w m η * φ η ≤ A' := by
      have := mul_le_mul_of_nonneg_left (hA' η) (w_pos m η).le
      rwa [← mul_assoc, mul_comm (w m η) A', mul_assoc, mul_inv_cancel₀ (w_pos m η).ne',
        mul_one] at this
    exact mul_le_mul_of_nonneg_right this (hψ0 _)
  have h2 : ∀ η, φ η * (w m (ξ - η) * ψ (ξ - η)) ≤ φ η * B' := by
    intro η
    have : w m (ξ - η) * ψ (ξ - η) ≤ B' := by
      have := mul_le_mul_of_nonneg_left (hB' (ξ - η)) (w_pos m (ξ - η)).le
      rwa [← mul_assoc, mul_comm (w m (ξ - η)) B', mul_assoc,
        mul_inv_cancel₀ (w_pos m (ξ - η)).ne', mul_one] at this
    exact mul_le_mul_of_nonneg_left this (hφ0 _)
  have hcw : Continuous (w m) := continuous_w m
  have hi1 : Integrable fun η => w m η * φ η * ψ (ξ - η) := by
    refine (hψint.const_mul A').mono' ((hcw.mul hφc).mul hψs).aestronglyMeasurable
      (Eventually.of_forall fun η => ?_)
    have hnn : 0 ≤ w m η * φ η * ψ (ξ - η) :=
      mul_nonneg (mul_nonneg (w_pos m η).le (hφ0 η)) (hψ0 _)
    rw [Real.norm_of_nonneg hnn]
    exact h1 η
  have hi2 : Integrable fun η => φ η * (w m (ξ - η) * ψ (ξ - η)) := by
    refine (hφint.mul_const B').mono'
      (hφc.mul ((hcw.comp (continuous_const.sub continuous_id)).mul hψs)).aestronglyMeasurable
      (Eventually.of_forall fun η => ?_)
    have hnn : 0 ≤ φ η * (w m (ξ - η) * ψ (ξ - η)) :=
      mul_nonneg (hφ0 η) (mul_nonneg (w_pos m (ξ - η)).le (hψ0 _))
    rw [Real.norm_of_nonneg hnn]
    exact h2 η
  have hprod : Integrable fun η => φ η * ψ (ξ - η) := by
    refine (hφint.mul_const B).mono' (hφc.mul hψs).aestronglyMeasurable
      (Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hφ0 η) (hψ0 _))]
    exact mul_le_mul_of_nonneg_left (hψle1 _) (hφ0 η)
  calc w m ξ * ∫ η, φ η * ψ (ξ - η) = ∫ η, w m ξ * (φ η * ψ (ξ - η)) := by
        rw [integral_const_mul]
    _ ≤ ∫ η, 2 ^ m * (w m η * φ η * ψ (ξ - η) + φ η * (w m (ξ - η) * ψ (ξ - η))) := by
        refine integral_mono (hprod.const_mul _) ((hi1.add hi2).const_mul _) fun η => ?_
        have := w_le_add m ξ η
        have hp : 0 ≤ φ η * ψ (ξ - η) := mul_nonneg (hφ0 η) (hψ0 _)
        calc w m ξ * (φ η * ψ (ξ - η)) ≤ 2 ^ m * (w m η + w m (ξ - η)) * (φ η * ψ (ξ - η)) :=
              mul_le_mul_of_nonneg_right this hp
          _ = _ := by ring
    _ = 2 ^ m * ((∫ η, w m η * φ η * ψ (ξ - η)) + ∫ η, φ η * (w m (ξ - η) * ψ (ξ - η))) := by
        rw [integral_const_mul, integral_add hi1 hi2]
    _ ≤ 2 ^ m * ((∫ η, A' * ψ (ξ - η)) + ∫ η, φ η * B') := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact integral_mono hi1 (hψint.const_mul A') h1
        · exact integral_mono hi2 (hφint.mul_const B') h2
    _ = 2 ^ m * (A' * (∫ η, ψ η) + (∫ η, φ η) * B') := by
        rw [integral_const_mul, integral_mul_const, integral_sub_left_eq_self]
    _ ≤ 2 ^ m * (A' * (B * I4) + (A * I4) * B') := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact mul_le_mul_of_nonneg_left (integral_le_I4 hψ0 hB hψc.aestronglyMeasurable) hA'0
        · exact mul_le_mul_of_nonneg_right (integral_le_I4 hφ0 hA hφc.aestronglyMeasurable) hB'0
    _ = 2 ^ m * I4 * (A' * B + A * B') := by ring

/-! ### O núcleo do calor -/

/-- `y e^{−y²} ≤ 1`. -/
theorem mul_exp_neg_sq_le (y : ℝ) (hy : 0 ≤ y) : y * Real.exp (-(y ^ 2)) ≤ 1 := by
  have h1 : y ≤ Real.exp (y ^ 2) := by
    have := Real.add_one_le_exp (y ^ 2)
    nlinarith [sq_nonneg (y - 1)]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact h1

/-- **Calor**: `2π‖ξ‖ e^{−4π²ν‖ξ‖²τ} ≤ (ντ)^{−1/2}`. -/
theorem calor_grad_le {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (ξ : E3) :
    2 * π * ‖ξ‖ * Real.exp (-(4 * π ^ 2 * ν * ‖ξ‖ ^ 2 * τ)) ≤ (Real.sqrt (ν * τ))⁻¹ := by
  have hs : 0 < Real.sqrt (ν * τ) := Real.sqrt_pos.mpr (mul_pos hν hτ)
  set y := 2 * π * ‖ξ‖ * Real.sqrt (ν * τ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy2 : y ^ 2 = 4 * π ^ 2 * ν * ‖ξ‖ ^ 2 * τ := by
    rw [hy, mul_pow, Real.sq_sqrt (mul_pos hν hτ).le]; ring
  have := mul_exp_neg_sq_le y hy0
  rw [hy2] at this
  calc 2 * π * ‖ξ‖ * Real.exp (-(4 * π ^ 2 * ν * ‖ξ‖ ^ 2 * τ))
      = y * Real.exp (-(4 * π ^ 2 * ν * ‖ξ‖ ^ 2 * τ)) / Real.sqrt (ν * τ) := by
        rw [hy]; field_simp
    _ ≤ 1 / Real.sqrt (ν * τ) := div_le_div_of_nonneg_right this hs.le
    _ = (Real.sqrt (ν * τ))⁻¹ := one_div _

theorem calor_le_one {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (ξ : E3) :
    Real.exp (-(4 * π ^ 2 * ν * ‖ξ‖ ^ 2 * τ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : 0 ≤ 4 * π ^ 2 * ν * ‖ξ‖ ^ 2 * τ := by positivity
  linarith

/-! ### O projetor de Leray -/

/-- O vetor real `ξ` visto em `ℂ³`. -/
noncomputable def cpx (ξ : E3) : C3 := WithLp.toLp 2 (fun k => ((ξ k : ℝ) : ℂ))

theorem cpx_apply (ξ : E3) (k : Fin 3) : cpx ξ k = (ξ k : ℂ) := rfl

theorem norm_cpx (ξ : E3) : ‖cpx ξ‖ = ‖ξ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [cpx]

theorem inner_cpx (ξ : E3) (v : C3) : inner ℂ (cpx ξ) v = ∑ k, (ξ k : ℂ) * v k := by
  simp [cpx, PiLp.inner_apply, mul_comm]

theorem cpx_zero : cpx 0 = 0 := by
  ext k; simp [cpx]

theorem cpx_ne_zero {ξ : E3} (h : ξ ≠ 0) : cpx ξ ≠ 0 := by
  intro h0
  apply h
  have := congrArg norm h0
  rw [norm_cpx, norm_zero] at this
  exact norm_eq_zero.mp this

/-- **Projetor de Leray** `P(ξ) v = v − (⟪ξ, v⟫/‖ξ‖²) ξ` (identidade em `ξ = 0`). -/
noncomputable def lp (ξ : E3) (v : C3) : C3 :=
  v - (inner ℂ (cpx ξ) v / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • cpx ξ

theorem lp_zero_left (v : C3) : lp 0 v = v := by
  simp [lp, cpx_zero]

theorem inner_cpx_self (ξ : E3) : inner ℂ (cpx ξ) (cpx ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, norm_cpx]
  simp

/-- `⟪ξ, P(ξ) v⟫ = 0`. -/
theorem inner_lp (ξ : E3) (v : C3) : inner ℂ (cpx ξ) (lp ξ v) = 0 := by
  by_cases hξ : ξ = 0
  · subst hξ; simp [cpx_zero]
  have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ‖ξ‖ ^ 2 := by have := norm_pos_iff.mpr hξ; positivity
    exact_mod_cast this.ne'
  rw [lp, inner_sub_right, inner_smul_right, inner_cpx_self]
  field_simp
  ring

theorem lp_of_inner_eq_zero {ξ : E3} {v : C3} (h : inner ℂ (cpx ξ) v = 0) : lp ξ v = v := by
  simp [lp, h]

/-- `‖P(ξ) v‖ ≤ ‖v‖`. -/
theorem norm_lp_le (ξ : E3) (v : C3) : ‖lp ξ v‖ ≤ ‖v‖ := by
  set c : ℂ := inner ℂ (cpx ξ) v / ((‖ξ‖ ^ 2 : ℝ) : ℂ)
  have horth : inner ℂ (lp ξ v) (c • cpx ξ) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, inner_lp, map_zero, mul_zero]
  have hv : v = lp ξ v + c • cpx ξ := by simp [lp, c]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (lp ξ v) (c • cpx ξ) horth
  rw [← hv] at hpy
  have h2 : ‖lp ξ v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [hpy, mul_self_nonneg ‖c • cpx ξ‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

theorem lp_add (ξ : E3) (v v' : C3) : lp ξ (v + v') = lp ξ v + lp ξ v' := by
  simp only [lp, inner_add_right, add_div, add_smul]
  abel

theorem lp_smul (ξ : E3) (c : ℂ) (v : C3) : lp ξ (c • v) = c • lp ξ v := by
  simp only [lp, inner_smul_right, smul_sub, smul_smul, mul_div_assoc]

theorem lp_sub (ξ : E3) (v v' : C3) : lp ξ (v - v') = lp ξ v - lp ξ v' := by
  rw [sub_eq_add_neg, lp_add, show -v' = (-1 : ℂ) • v' by simp, lp_smul]
  simp [sub_eq_add_neg]

theorem lp_zero_right (ξ : E3) : lp ξ 0 = 0 := by
  simp [lp]

/-! ### O termo não linear -/

/-- `Nl f g ξ = 2πi ∫ ⟪ξ, f(η)⟫ g(ξ − η) dη` (a transformada de `div(u ⊗ v)`). -/
noncomputable def Nl (f g : E3 → C3) (ξ : E3) : C3 :=
  ((2 * π : ℝ) * Complex.I : ℂ) • ∫ η, inner ℂ (cpx ξ) (f η) • g (ξ - η)

theorem norm_inner_cpx_le (ξ : E3) (v : C3) : ‖inner ℂ (cpx ξ) v‖ ≤ ‖ξ‖ * ‖v‖ := by
  rw [← norm_cpx]; exact norm_inner_le_norm _ _

/-- `‖Nl f g ξ‖ ≤ 2π‖ξ‖ ∫ ‖f(η)‖‖g(ξ − η)‖`. -/
theorem norm_Nl_le {f g : E3 → C3} (ξ : E3)
    (hint : Integrable fun η => ‖f η‖ * ‖g (ξ - η)‖) :
    ‖Nl f g ξ‖ ≤ 2 * π * ‖ξ‖ * ∫ η, ‖f η‖ * ‖g (ξ - η)‖ := by
  unfold Nl
  rw [norm_smul]
  have hI : ‖((2 * π : ℝ) * Complex.I : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hI, mul_assoc (2 * π) ‖ξ‖]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 2 * π)
  calc ‖∫ η, inner ℂ (cpx ξ) (f η) • g (ξ - η)‖ ≤ ∫ η, ‖ξ‖ * (‖f η‖ * ‖g (ξ - η)‖) := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun η => ?_)
        rw [norm_smul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (norm_inner_cpx_le ξ _) (norm_nonneg _)
    _ = ‖ξ‖ * ∫ η, ‖f η‖ * ‖g (ξ - η)‖ := integral_const_mul _ _

end ATK.NSFourierBase

#print axioms ATK.NSFourierBase.w_pos
#print axioms ATK.NSFourierBase.one_le_w
#print axioms ATK.NSFourierBase.w_mono
#print axioms ATK.NSFourierBase.w_succ
#print axioms ATK.NSFourierBase.continuous_w
#print axioms ATK.NSFourierBase.w_le_add
#print axioms ATK.NSFourierBase.integrable_w_inv
#print axioms ATK.NSFourierBase.I4_nonneg
#print axioms ATK.NSFourierBase.integral_le_I4
#print axioms ATK.NSFourierBase.integrable_of_le_w4
#print axioms ATK.NSFourierBase.conv_peso
#print axioms ATK.NSFourierBase.mul_exp_neg_sq_le
#print axioms ATK.NSFourierBase.calor_grad_le
#print axioms ATK.NSFourierBase.calor_le_one
#print axioms ATK.NSFourierBase.cpx_apply
#print axioms ATK.NSFourierBase.norm_cpx
#print axioms ATK.NSFourierBase.inner_cpx
#print axioms ATK.NSFourierBase.cpx_zero
#print axioms ATK.NSFourierBase.cpx_ne_zero
#print axioms ATK.NSFourierBase.lp_zero_left
#print axioms ATK.NSFourierBase.inner_cpx_self
#print axioms ATK.NSFourierBase.inner_lp
#print axioms ATK.NSFourierBase.lp_of_inner_eq_zero
#print axioms ATK.NSFourierBase.norm_lp_le
#print axioms ATK.NSFourierBase.lp_add
#print axioms ATK.NSFourierBase.lp_smul
#print axioms ATK.NSFourierBase.lp_sub
#print axioms ATK.NSFourierBase.lp_zero_right
#print axioms ATK.NSFourierBase.norm_inner_cpx_le
#print axioms ATK.NSFourierBase.norm_Nl_le
