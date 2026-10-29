import ATK.NSFourierBase
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# ATK — Navier–Stokes no lado de Fourier: o operador de Duhamel e suas estimativas

Para uma amplitude `a : ℝ → ℝ³ → ℂ³` (tempo, frequência), o operador de Duhamel

  `duh ν a τ ξ = ∫₀^τ e^{−4π²ν‖ξ‖²(τ−s)} P(ξ) Nl(a(s), a(s))(ξ) ds`

é a parte não linear da forma branda de Navier–Stokes. Aqui:

* `Boa4 a A`: `a` contínua em `ℝ × ℝ³` com `‖a(s, ξ)‖ ≤ A w₄(ξ)⁻¹`;
* `continuous_lpNl`: `(s, ξ) ↦ P(ξ) Nl(a(s), a(s))(ξ)` é contínua (inclusive em `ξ = 0`, onde
  `P` é descontínuo mas `Nl` se anula);
* `norm_duh_le`: **estimativa de Duhamel com pesos**:
  `w_m(ξ) ‖duh a τ ξ‖ ≤ 2^m I₄ (2A) ∫₀^τ (ν(τ − s))^{−1/2} Y(s) ds` se `‖a(s,·)‖ ≤ Y(s) w_m⁻¹`;
* `norm_duh_sub_le`: a mesma estimativa para a diferença `duh a − duh b` (contração).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

namespace ATK.NSPicard

open ATK.LigacaoNS ATK.NSFourierBase

/-! ### Fator do calor -/

/-- `e^{−4π²ν‖ξ‖²t}`. -/
noncomputable def heat (ν t : ℝ) (ξ : E3) : ℝ := Real.exp (-(4 * π ^ 2 * ν * ‖ξ‖ ^ 2 * t))

theorem heat_pos (ν t : ℝ) (ξ : E3) : 0 < heat ν t ξ := Real.exp_pos _

theorem heat_le_one {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ξ : E3) : heat ν t ξ ≤ 1 :=
  calor_le_one hν ht ξ

theorem continuous_heat (ν : ℝ) : Continuous fun p : ℝ × E3 => heat ν p.1 p.2 := by
  unfold heat; fun_prop

theorem heat_zero (ν : ℝ) (ξ : E3) : heat ν 0 ξ = 1 := by simp [heat]

theorem heat_neg (ν t : ℝ) (ξ : E3) : heat ν t (-ξ) = heat ν t ξ := by simp [heat]

/-- `2π‖ξ‖ e^{−4π²ν‖ξ‖²τ} ≤ (ντ)^{−1/2}` (forma com `rpow`). -/
theorem heat_grad_le {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (ξ : E3) :
    2 * π * ‖ξ‖ * heat ν τ ξ ≤ (ν * τ) ^ (-(1 / 2 : ℝ)) := by
  have h := calor_grad_le hν hτ ξ
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (mul_pos hν hτ).le] at h
  exact h

/-! ### Amplitudes boas -/

/-- `a` contínua em `ℝ × ℝ³` com `‖a(s, ξ)‖ ≤ A w₄(ξ)⁻¹`. -/
structure Boa4 (a : ℝ → E3 → C3) (A : ℝ) : Prop where
  cont : Continuous fun p : ℝ × E3 => a p.1 p.2
  bound : ∀ s ξ, ‖a s ξ‖ ≤ A * (w 4 ξ)⁻¹

theorem Boa4.nonneg {a : ℝ → E3 → C3} {A : ℝ} (h : Boa4 a A) : 0 ≤ A := by
  have := (norm_nonneg _).trans (h.bound 0 0)
  exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos 4 0))

theorem Boa4.le {a : ℝ → E3 → C3} {A : ℝ} (h : Boa4 a A) (s : ℝ) (ξ : E3) : ‖a s ξ‖ ≤ A :=
  (h.bound s ξ).trans (mul_le_of_le_one_right h.nonneg (inv_le_one_of_one_le₀ (one_le_w 4 ξ)))

theorem Boa4.cont_s {a : ℝ → E3 → C3} {A : ℝ} (h : Boa4 a A) (s : ℝ) : Continuous (a s) :=
  h.cont.comp (continuous_const.prodMk continuous_id)

/-- `∫ ‖f(η)‖ ‖g(ξ − η)‖`. -/
noncomputable def convN (f g : E3 → C3) (ξ : E3) : ℝ := ∫ η, ‖f η‖ * ‖g (ξ - η)‖

theorem integrable_convN {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hfA : ∀ ξ, ‖f ξ‖ ≤ A * (w 4 ξ)⁻¹) (hgB : ∀ ξ, ‖g ξ‖ ≤ B) (ξ : E3) :
    Integrable fun η => ‖f η‖ * ‖g (ξ - η)‖ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0)
  refine ((integrable_w_inv.const_mul A).mul_const B).mono'
    ((hf.norm.mul (hg.comp (continuous_const.sub continuous_id)).norm).aestronglyMeasurable)
    (Eventually.of_forall fun η => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (hfA η) (hgB _) (norm_nonneg _) ((norm_nonneg _).trans (hfA η))

theorem convN_peso (m : ℕ) {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g)
    {A A' B B' : ℝ} (hA : ∀ η, ‖f η‖ ≤ A * (w 4 η)⁻¹) (hA' : ∀ η, ‖f η‖ ≤ A' * (w m η)⁻¹)
    (hB : ∀ η, ‖g η‖ ≤ B * (w 4 η)⁻¹) (hB' : ∀ η, ‖g η‖ ≤ B' * (w m η)⁻¹) (ξ : E3) :
    w m ξ * convN f g ξ ≤ 2 ^ m * I4 * (A' * B + A * B') :=
  conv_peso m hf.norm hg.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hA hA' hB hB' ξ

/-! ### Continuidade de `P(ξ) Nl(a(s), a(s))(ξ)` -/

theorem continuous_cpx : Continuous cpx := by unfold cpx; fun_prop

/-- Continuidade da integral do termo não linear. -/
theorem continuousAt_intNl {a b : ℝ → E3 → C3} {A B : ℝ} (ha : Boa4 a A) (hb : Boa4 b B)
    (p₀ : ℝ × E3) : ContinuousAt
      (fun p : ℝ × E3 => ∫ η, inner ℂ (cpx p.2) (a p.1 η) • b p.1 (p.2 - η)) p₀ := by
  have hA := ha.nonneg
  have hB := hb.nonneg
  refine continuousAt_of_dominated (bound := fun η => (‖p₀.2‖ + 1) * (A * (w 4 η)⁻¹) * B)
    ?_ ?_ ((integrable_w_inv.const_mul A |>.const_mul _).mul_const _) ?_
  · refine Eventually.of_forall fun p => Continuous.aestronglyMeasurable ?_
    have h1 := ha.cont_s p.1
    have h2 := hb.cont_s p.1
    fun_prop
  · have hball : ∀ᶠ p in 𝓝 p₀, ‖p.2‖ ≤ ‖p₀.2‖ + 1 := by
      have : ContinuousAt (fun p : ℝ × E3 => ‖p.2‖) p₀ := continuous_snd.norm.continuousAt
      filter_upwards [this.eventually (Iio_mem_nhds (lt_add_one ‖p₀.2‖))] with p hp
      exact hp.le
    filter_upwards [hball] with p hp
    refine Eventually.of_forall fun η => ?_
    rw [norm_smul]
    calc ‖inner ℂ (cpx p.2) (a p.1 η)‖ * ‖b p.1 (p.2 - η)‖
        ≤ (‖p.2‖ * ‖a p.1 η‖) * B :=
          mul_le_mul (norm_inner_cpx_le _ _) (hb.le _ _) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ ((‖p₀.2‖ + 1) * (A * (w 4 η)⁻¹)) * B := by
          gcongr
          exact ha.bound _ _
  · refine Eventually.of_forall fun η => Continuous.continuousAt ?_
    exact (Continuous.inner (𝕜 := ℂ) (continuous_cpx.comp continuous_snd)
      (ha.cont.comp (continuous_fst.prodMk continuous_const))).smul
      (hb.cont.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)))

/-- Continuidade do termo não linear, para amplitudes boas. -/
theorem continuous_Nl {a b : ℝ → E3 → C3} {A B : ℝ} (ha : Boa4 a A) (hb : Boa4 b B) :
    Continuous fun p : ℝ × E3 => Nl (a p.1) (b p.1) p.2 := by
  unfold Nl
  exact (continuous_const (y := ((2 * π : ℝ) * Complex.I : ℂ))).smul
    (continuous_iff_continuousAt.2 (continuousAt_intNl ha hb))

theorem Nl_zero (f g : E3 → C3) : Nl f g 0 = 0 := by
  simp [Nl, cpx_zero]

/-- `‖Nl(a(s), b(s))(ξ)‖ ≤ 2π‖ξ‖ A B I₄`. -/
theorem norm_Nl_le_AB {a b : ℝ → E3 → C3} {A B : ℝ} (ha : Boa4 a A) (hb : Boa4 b B)
    (s : ℝ) (ξ : E3) : ‖Nl (a s) (b s) ξ‖ ≤ 2 * π * ‖ξ‖ * (A * B * I4) := by
  have hint := integrable_convN (ha.cont_s s) (hb.cont_s s) (ha.bound s) (hb.le s) ξ
  refine (norm_Nl_le ξ hint).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ∀ η, ‖a s η‖ * ‖b s (ξ - η)‖ ≤ (A * B) * (w 4 η)⁻¹ := by
    intro η
    calc ‖a s η‖ * ‖b s (ξ - η)‖ ≤ (A * (w 4 η)⁻¹) * B :=
          mul_le_mul (ha.bound s η) (hb.le s _) (norm_nonneg _)
            ((norm_nonneg _).trans (ha.bound s η))
      _ = (A * B) * (w 4 η)⁻¹ := by ring
  exact integral_le_I4 (fun η => mul_nonneg (norm_nonneg _) (norm_nonneg _)) h1
    hint.aestronglyMeasurable

/-- **Continuidade de `P(ξ) Nl(a(s), b(s))(ξ)`** (em `ξ = 0` por esmagamento). -/
theorem continuous_lpNl {a b : ℝ → E3 → C3} {A B : ℝ} (ha : Boa4 a A) (hb : Boa4 b B) :
    Continuous fun p : ℝ × E3 => lp p.2 (Nl (a p.1) (b p.1) p.2) := by
  have hN := continuous_Nl ha hb
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  by_cases h0 : p₀.2 = 0
  · -- esmagamento
    have hval : lp p₀.2 (Nl (a p₀.1) (b p₀.1) p₀.2) = 0 := by
      rw [h0, lp_zero_left, Nl_zero]
    show Tendsto _ (𝓝 p₀) (𝓝 (lp p₀.2 (Nl (a p₀.1) (b p₀.1) p₀.2)))
    rw [hval]
    refine squeeze_zero_norm (fun p => (norm_lp_le _ _).trans (norm_Nl_le_AB ha hb p.1 p.2)) ?_
    have : Tendsto (fun p : ℝ × E3 => 2 * π * ‖p.2‖ * (A * B * I4)) (𝓝 p₀)
        (𝓝 (2 * π * ‖p₀.2‖ * (A * B * I4))) :=
      ((continuous_const.mul continuous_snd.norm).mul continuous_const).continuousAt
    rw [h0, norm_zero, mul_zero, zero_mul] at this
    exact this
  · -- fora de `ξ = 0`, `P` é contínuo
    unfold lp
    have hden : ((‖p₀.2‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < ‖p₀.2‖ ^ 2 := by have := norm_pos_iff.mpr h0; positivity
      exact_mod_cast this.ne'
    refine hN.continuousAt.sub (ContinuousAt.smul
      (f := fun p : ℝ × E3 => inner ℂ (cpx p.2) (Nl (a p.1) (b p.1) p.2) / ((‖p.2‖ ^ 2 : ℝ) : ℂ))
      (g := fun p : ℝ × E3 => cpx p.2) ?_ (continuous_cpx.comp continuous_snd).continuousAt)
    refine ContinuousAt.div ?_ ?_ hden
    · exact (Continuous.inner (𝕜 := ℂ) (continuous_cpx.comp continuous_snd) hN).continuousAt
    · exact (Complex.continuous_ofReal.comp (continuous_snd.norm.pow 2)).continuousAt

/-! ### Integrais singulares -/

theorem intervalIntegrable_sing (τ : ℝ) :
    IntervalIntegrable (fun s : ℝ => (τ - s) ^ (-(1 / 2 : ℝ))) volume 0 τ := by
  have h := (intervalIntegrable_rpow' (a := τ) (b := 0) (r := -(1 / 2 : ℝ))
    (by norm_num)).comp_sub_left τ
  simpa using h

/-- `∫₀^τ (τ − s)^{−1/2} ds = 2 τ^{1/2}`. -/
theorem integral_sing {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) = 2 * τ ^ (1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (-(1 / 2 : ℝ))) τ]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num)]
  norm_num
  ring

/-- `∫₀^τ u^{−1/2} e^{−κu} du ≤ 4 κ^{−1/2}`. -/
theorem integral_sing_exp_le {τ κ : ℝ} (hτ : 0 ≤ τ) (hκ : 0 < κ) :
    ∫ u in (0 : ℝ)..τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u)) ≤ 4 * κ ^ (-(1 / 2 : ℝ)) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u))) volume a b := fun a b =>
    (intervalIntegrable_rpow' (by norm_num)).mul_continuousOn (by fun_prop)
  have hpt1 : ∀ u ∈ Icc (0 : ℝ) τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u)) ≤
      u ^ (-(1 / 2 : ℝ)) := by
    intro u hu
    refine mul_le_of_le_one_right (Real.rpow_nonneg hu.1 _) ?_
    rw [Real.exp_le_one_iff]
    have := mul_nonneg hκ.le hu.1
    linarith
  have hr1 : (1 / κ) ^ (1 / 2 : ℝ) = (κ ^ (1 / 2 : ℝ))⁻¹ := by
    rw [Real.div_rpow zero_le_one hκ.le, Real.one_rpow]
    exact one_div _
  have hr2 : κ ^ (-(1 / 2 : ℝ)) = (κ ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hκ.le _
  have hr3 : (1 / κ) ^ (-(1 / 2 : ℝ)) = κ ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg (by positivity), hr1, inv_inv]
  have hκh : κ ^ (-(1 / 2 : ℝ)) = (1 / κ) ^ (1 / 2 : ℝ) := hr2.trans hr1.symm
  -- integral de `u^{−1/2}` até `c` vale `2 c^{1/2}`
  have hI : ∀ c : ℝ, 0 ≤ c → ∫ u in (0 : ℝ)..c, u ^ (-(1 / 2 : ℝ)) = 2 * c ^ (1 / 2 : ℝ) := by
    intro c hc
    rw [integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num)]
    norm_num
    ring
  rcases le_or_gt τ (1 / κ) with hsmall | hbig
  · calc ∫ u in (0 : ℝ)..τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u))
        ≤ ∫ u in (0 : ℝ)..τ, u ^ (-(1 / 2 : ℝ)) :=
          intervalIntegral.integral_mono_on hτ (hint 0 τ)
            (intervalIntegrable_rpow' (by norm_num)) hpt1
      _ = 2 * τ ^ (1 / 2 : ℝ) := hI τ hτ
      _ ≤ 2 * (1 / κ) ^ (1 / 2 : ℝ) := by
          gcongr
      _ ≤ 4 * κ ^ (-(1 / 2 : ℝ)) := by
          rw [hκh]; have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 / κ) (1 / 2 : ℝ)
          linarith
  · have h1κ : (0 : ℝ) < 1 / κ := by positivity
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / κ)) (hint (1 / κ) τ)]
    have hA : ∫ u in (0 : ℝ)..(1 / κ), u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u)) ≤
        2 * κ ^ (-(1 / 2 : ℝ)) := by
      calc ∫ u in (0 : ℝ)..(1 / κ), u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u))
          ≤ ∫ u in (0 : ℝ)..(1 / κ), u ^ (-(1 / 2 : ℝ)) :=
            intervalIntegral.integral_mono_on h1κ.le (hint 0 _)
              (intervalIntegrable_rpow' (by norm_num)) (fun u hu => by
                refine mul_le_of_le_one_right (Real.rpow_nonneg hu.1 _) ?_
                rw [Real.exp_le_one_iff]
                have := mul_nonneg hκ.le hu.1
                linarith)
        _ = 2 * (1 / κ) ^ (1 / 2 : ℝ) := hI _ h1κ.le
        _ = 2 * κ ^ (-(1 / 2 : ℝ)) := by rw [hκh]
    have hB : ∫ u in (1 / κ)..τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u)) ≤
        2 * κ ^ (-(1 / 2 : ℝ)) := by
      have hpt : ∀ u ∈ Icc (1 / κ) τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u)) ≤
          κ⁻¹ * u ^ (-(3 / 2 : ℝ)) := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le h1κ hu.1
        have he : Real.exp (-(κ * u)) ≤ (κ * u)⁻¹ := by
          rw [Real.exp_neg]
          refine inv_anti₀ (by positivity) ?_
          have := Real.add_one_le_exp (κ * u)
          linarith
        calc u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u)) ≤ u ^ (-(1 / 2 : ℝ)) * (κ * u)⁻¹ :=
              mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hu0.le _)
          _ = κ⁻¹ * (u ^ (-(1 / 2 : ℝ)) * u ^ (-(1 : ℝ))) := by
              rw [Real.rpow_neg_one, mul_inv]; ring
          _ = κ⁻¹ * u ^ (-(3 / 2 : ℝ)) := by
              rw [← Real.rpow_add hu0]; norm_num
      have hint2 : IntervalIntegrable (fun u : ℝ => κ⁻¹ * u ^ (-(3 / 2 : ℝ))) volume (1 / κ) τ := by
        have hc : ContinuousOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (uIcc (1 / κ) τ) := by
          refine ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl ?_
          rw [uIcc_of_le hbig.le] at hu
          exact (lt_of_lt_of_le h1κ hu.1).ne'
        exact hc.intervalIntegrable.const_mul _
      calc ∫ u in (1 / κ)..τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u))
          ≤ ∫ u in (1 / κ)..τ, κ⁻¹ * u ^ (-(3 / 2 : ℝ)) :=
            intervalIntegral.integral_mono_on hbig.le (hint _ _) hint2 hpt
        _ = κ⁻¹ * ((τ ^ (-(3 / 2 : ℝ) + 1) - (1 / κ) ^ (-(3 / 2 : ℝ) + 1)) / (-(3 / 2 : ℝ) + 1)) := by
            rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
            rw [uIcc_of_le hbig.le]
            exact fun h => absurd h.1 (not_le.mpr h1κ)
        _ = 2 * κ⁻¹ * ((1 / κ) ^ (-(1 / 2 : ℝ)) - τ ^ (-(1 / 2 : ℝ))) := by norm_num; ring
        _ ≤ 2 * κ⁻¹ * (1 / κ) ^ (-(1 / 2 : ℝ)) := by
            have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ τ) (-(1 / 2 : ℝ))
            have h2 : 0 ≤ 2 * κ⁻¹ := by positivity
            nlinarith
        _ = 2 * κ ^ (-(1 / 2 : ℝ)) := by
            rw [hr3, hr2]
            have hk : κ = κ ^ (1 / 2 : ℝ) * κ ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_add hκ]; norm_num
            have hkp : 0 < κ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hκ _
            have hk0 : κ ≠ 0 := hκ.ne'
            field_simp
            rw [sq, ← hk]
    linarith

/-- `∫₀^τ (τ − s)^{−1/2} e^{κs} ds ≤ 4 κ^{−1/2} e^{κτ}`. -/
theorem integral_sing_exp {τ κ : ℝ} (hτ : 0 ≤ τ) (hκ : 0 < κ) :
    ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * Real.exp (κ * s) ≤
      4 * κ ^ (-(1 / 2 : ℝ)) * Real.exp (κ * τ) := by
  have h : ∀ s : ℝ, (τ - s) ^ (-(1 / 2 : ℝ)) * Real.exp (κ * s) =
      Real.exp (κ * τ) * ((τ - s) ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * (τ - s)))) := by
    intro s
    rw [mul_comm (Real.exp (κ * τ)), mul_assoc, ← Real.exp_add]
    congr 2; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left
      (fun u => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u))) τ]
  simp only [sub_self, sub_zero]
  calc Real.exp (κ * τ) * ∫ u in (0 : ℝ)..τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ * u))
      ≤ Real.exp (κ * τ) * (4 * κ ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (integral_sing_exp_le hτ hκ) (Real.exp_pos _).le
    _ = 4 * κ ^ (-(1 / 2 : ℝ)) * Real.exp (κ * τ) := by ring

/-! ### O operador de Duhamel -/

/-- O integrando de Duhamel `e^{−4π²ν‖ξ‖²(τ−s)} P(ξ) Nl(a(s), b(s))(ξ)`. -/
noncomputable def duhI (ν : ℝ) (a b : ℝ → E3 → C3) (τ s : ℝ) (ξ : E3) : C3 :=
  heat ν (τ - s) ξ • lp ξ (Nl (a s) (b s) ξ)

theorem continuous_duhI {a b : ℝ → E3 → C3} {A B : ℝ} (ha : Boa4 a A) (hb : Boa4 b B) (ν : ℝ) :
    Continuous fun q : (ℝ × ℝ) × E3 => duhI ν a b q.1.1 q.1.2 q.2 := by
  unfold duhI
  have h1 : Continuous fun q : (ℝ × ℝ) × E3 => heat ν (q.1.1 - q.1.2) q.2 :=
    Continuous.comp (g := fun p : ℝ × E3 => heat ν p.1 p.2)
      (f := fun q : (ℝ × ℝ) × E3 => (q.1.1 - q.1.2, q.2)) (continuous_heat ν) (by fun_prop)
  have h2 : Continuous fun q : (ℝ × ℝ) × E3 => lp q.2 (Nl (a q.1.2) (b q.1.2) q.2) :=
    Continuous.comp (g := fun p : ℝ × E3 => lp p.2 (Nl (a p.1) (b p.1) p.2))
      (f := fun q : (ℝ × ℝ) × E3 => (q.1.2, q.2)) (continuous_lpNl ha hb) (by fun_prop)
  exact h1.smul h2

/-- Cota pontual do integrando de Duhamel. -/
theorem norm_duhI_le {ν : ℝ} (hν : 0 < ν) {a b : ℝ → E3 → C3} {A B A' B' : ℝ} (m : ℕ)
    (ha : Boa4 a A) (hb : Boa4 b B) {τ s : ℝ} (hs : s < τ)
    (hA' : ∀ η, ‖a s η‖ ≤ A' * (w m η)⁻¹) (hB' : ∀ η, ‖b s η‖ ≤ B' * (w m η)⁻¹) (ξ : E3) :
    ‖duhI ν a b τ s ξ‖ ≤
      (w m ξ)⁻¹ * ((ν * (τ - s)) ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4 * (A' * B + A * B'))) := by
  have hint := integrable_convN (ha.cont_s s) (hb.cont_s s) (ha.bound s) (hb.le s) ξ
  have hc := convN_peso m (ha.cont_s s) (hb.cont_s s) (ha.bound s) hA' (hb.bound s) hB' ξ
  have hw := w_pos m ξ
  have hconv : convN (a s) (b s) ξ ≤ (w m ξ)⁻¹ * (2 ^ m * I4 * (A' * B + A * B')) := by
    rw [le_inv_mul_iff₀ hw]; exact hc
  have hcn : 0 ≤ convN (a s) (b s) ξ :=
    integral_nonneg fun η => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hheat := heat_grad_le hν (sub_pos.mpr hs) ξ
  unfold duhI
  rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
  calc heat ν (τ - s) ξ * ‖lp ξ (Nl (a s) (b s) ξ)‖
      ≤ heat ν (τ - s) ξ * (2 * π * ‖ξ‖ * convN (a s) (b s) ξ) :=
        mul_le_mul_of_nonneg_left ((norm_lp_le _ _).trans (norm_Nl_le ξ hint))
          (heat_pos _ _ _).le
    _ = (2 * π * ‖ξ‖ * heat ν (τ - s) ξ) * convN (a s) (b s) ξ := by ring
    _ ≤ (ν * (τ - s)) ^ (-(1 / 2 : ℝ)) * ((w m ξ)⁻¹ * (2 ^ m * I4 * (A' * B + A * B'))) :=
        mul_le_mul hheat hconv hcn (Real.rpow_nonneg (by nlinarith) _)
    _ = _ := by ring

/-- **Estimativa de Duhamel com pesos.** -/
theorem norm_duh_le {ν : ℝ} (hν : 0 < ν) {a b : ℝ → E3 → C3} {A B : ℝ} (m : ℕ)
    (ha : Boa4 a A) (hb : Boa4 b B) {A' B' : ℝ → ℝ} (hA'c : Continuous A')
    (hB'c : Continuous B') {τ : ℝ} (hτ : 0 ≤ τ)
    (hA' : ∀ s ∈ Icc 0 τ, ∀ η, ‖a s η‖ ≤ A' s * (w m η)⁻¹)
    (hB' : ∀ s ∈ Icc 0 τ, ∀ η, ‖b s η‖ ≤ B' s * (w m η)⁻¹) (ξ : E3) :
    w m ξ * ‖∫ s in (0 : ℝ)..τ, duhI ν a b τ s ξ‖ ≤
      ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) *
        ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * (A' s * B + A * B' s) := by
  have hw := w_pos m ξ
  set g : ℝ → ℝ := fun s => (w m ξ)⁻¹ * (ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) *
    ((τ - s) ^ (-(1 / 2 : ℝ)) * (A' s * B + A * B' s))) with hg
  have hgint : IntervalIntegrable g volume 0 τ := by
    refine ((intervalIntegrable_sing τ).mul_continuousOn ?_).const_mul _ |>.const_mul _
    exact ((hA'c.mul continuous_const).add (continuous_const.mul hB'c)).continuousOn
  have hle : ‖∫ s in (0 : ℝ)..τ, duhI ν a b τ s ξ‖ ≤ ∫ s in (0 : ℝ)..τ, g s := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτ ?_ hgint
    filter_upwards [Measure.ae_ne volume τ] with s hsτ hs
    have hs' : s < τ := lt_of_le_of_ne hs.2 hsτ
    have hsI : s ∈ Icc 0 τ := ⟨hs.1.le, hs.2⟩
    refine (norm_duhI_le hν m ha hb hs' (hA' s hsI) (hB' s hsI) ξ).trans_eq ?_
    simp only [hg]
    rw [Real.mul_rpow hν.le (sub_nonneg.mpr hs'.le)]
    ring
  have hint_eq : ∫ s in (0 : ℝ)..τ, g s = (w m ξ)⁻¹ * (ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) *
      ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * (A' s * B + A * B' s)) := by
    simp only [hg]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hint_eq] at hle
  calc w m ξ * ‖∫ s in (0 : ℝ)..τ, duhI ν a b τ s ξ‖
      ≤ w m ξ * ((w m ξ)⁻¹ * (ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) *
        ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * (A' s * B + A * B' s))) :=
        mul_le_mul_of_nonneg_left hle hw.le
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

/-! ### Bilinearidade -/

theorem Nl_sub {f f' g g' : E3 → C3} (ξ : E3)
    (h1 : Integrable fun η => inner ℂ (cpx ξ) (f η) • g (ξ - η))
    (h2 : Integrable fun η => inner ℂ (cpx ξ) (f' η) • g' (ξ - η))
    (h3 : Integrable fun η => inner ℂ (cpx ξ) (f η - f' η) • g (ξ - η))
    (h4 : Integrable fun η => inner ℂ (cpx ξ) (f' η) • (g (ξ - η) - g' (ξ - η))) :
    Nl f g ξ - Nl f' g' ξ = Nl (f - f') g ξ + Nl f' (g - g') ξ := by
  unfold Nl
  rw [← smul_sub, ← smul_add, ← integral_sub h1 h2]
  simp only [Pi.sub_apply]
  rw [← integral_add h3 h4]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [inner_sub_right, sub_smul, smul_sub]
  abel

/-- Integrabilidade do integrando de `Nl` para amplitudes contínuas limitadas. -/
theorem integrable_Nl_integrand {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hfA : ∀ η, ‖f η‖ ≤ A * (w 4 η)⁻¹) (hgB : ∀ η, ‖g η‖ ≤ B) (ξ : E3) :
    Integrable fun η => inner ℂ (cpx ξ) (f η) • g (ξ - η) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0)
  refine ((integrable_w_inv.const_mul A).mul_const B |>.const_mul ‖ξ‖).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun η => ?_)
  rw [norm_smul]
  calc ‖inner ℂ (cpx ξ) (f η)‖ * ‖g (ξ - η)‖ ≤ (‖ξ‖ * ‖f η‖) * B :=
        mul_le_mul (norm_inner_cpx_le _ _) (hgB _) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖ξ‖ * ((A * (w 4 η)⁻¹) * B) := by
        rw [mul_assoc]; gcongr; exact hfA η

theorem Boa4.sub {a b : ℝ → E3 → C3} {A B D : ℝ} (ha : Boa4 a A) (hb : Boa4 b B)
    (hD : ∀ s ξ, ‖a s ξ - b s ξ‖ ≤ D * (w 4 ξ)⁻¹) : Boa4 (a - b) D :=
  ⟨ha.cont.sub hb.cont, fun s ξ => hD s ξ⟩

theorem duhI_sub {ν : ℝ} {a b : ℝ → E3 → C3} {A B D : ℝ} (ha : Boa4 a A) (hb : Boa4 b B)
    (hD : Boa4 (a - b) D) (τ s : ℝ) (ξ : E3) :
    duhI ν a a τ s ξ - duhI ν b b τ s ξ = duhI ν (a - b) a τ s ξ + duhI ν b (a - b) τ s ξ := by
  unfold duhI
  rw [← smul_sub, ← smul_add, ← lp_sub, ← lp_add]
  congr 2
  have e := Nl_sub (f := a s) (f' := b s) (g := a s) (g' := b s) ξ
    (integrable_Nl_integrand (ha.cont_s s) (ha.cont_s s) (ha.bound s) (ha.le s) ξ)
    (integrable_Nl_integrand (hb.cont_s s) (hb.cont_s s) (hb.bound s) (hb.le s) ξ)
    (by simpa using integrable_Nl_integrand (hD.cont_s s) (ha.cont_s s) (hD.bound s) (ha.le s) ξ)
    (by simpa using integrable_Nl_integrand (hb.cont_s s) (hD.cont_s s) (hb.bound s) (hD.le s) ξ)
  rw [e]
  rfl

end ATK.NSPicard

#print axioms ATK.NSPicard.heat_pos
#print axioms ATK.NSPicard.heat_le_one
#print axioms ATK.NSPicard.continuous_heat
#print axioms ATK.NSPicard.heat_zero
#print axioms ATK.NSPicard.heat_neg
#print axioms ATK.NSPicard.heat_grad_le
#print axioms ATK.NSPicard.Boa4.nonneg
#print axioms ATK.NSPicard.Boa4.le
#print axioms ATK.NSPicard.Boa4.cont_s
#print axioms ATK.NSPicard.integrable_convN
#print axioms ATK.NSPicard.convN_peso
#print axioms ATK.NSPicard.continuous_cpx
#print axioms ATK.NSPicard.continuousAt_intNl
#print axioms ATK.NSPicard.continuous_Nl
#print axioms ATK.NSPicard.Nl_zero
#print axioms ATK.NSPicard.norm_Nl_le_AB
#print axioms ATK.NSPicard.continuous_lpNl
#print axioms ATK.NSPicard.intervalIntegrable_sing
#print axioms ATK.NSPicard.integral_sing
#print axioms ATK.NSPicard.integral_sing_exp_le
#print axioms ATK.NSPicard.integral_sing_exp
#print axioms ATK.NSPicard.continuous_duhI
#print axioms ATK.NSPicard.norm_duhI_le
#print axioms ATK.NSPicard.norm_duh_le
#print axioms ATK.NSPicard.Nl_sub
#print axioms ATK.NSPicard.integrable_Nl_integrand
#print axioms ATK.NSPicard.Boa4.sub
#print axioms ATK.NSPicard.duhI_sub
