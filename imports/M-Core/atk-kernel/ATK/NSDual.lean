import ATK.NSFracaF

/-!
# ATK — Navier–Stokes, marco NS8d: pareamentos com testes de Fourier e a família do calor

Ponte B3, marco NS8 (quarta parte). Ferramentas para a fórmula de Duhamel "testada":

* `pr F g = ∫ ⟨F, Re F0 g⟩`: linear em `g`, com `|pr F g| ≤ M (‖F‖²₂ + |B_ρ|)/2` (`F ∈ L²`) ou
  `≤ ‖F‖₁ M |B_ρ|` (`F ∈ L¹`) quando `g` vive na bola `B_ρ` e `|g| ≤ M`;
* a família do calor `Hk c g k s = (c|η|²)^k e^{−c|η|² s} g`: `s ↦ pr F (Hk c g k s)` é derivável
  com derivada `−pr F (Hk c g (k+1) s)` (estimativa de Taylor uniforme na bola).

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology Asymptotics
open scoped ContDiff Interval
open ATK.LigacaoNS (E3 dX e div lap conv grad gradSq fatia NSEq SolucaoLocal EnergiaAte)
open ATK.NSFourierBase ATK.NSPicard ATK.NSFisico ATK.NSCampos ATK.NSFraca ATK.NSTeste
  ATK.NSFracaF
open ATK.NSEnergia (amgm amgm_w sq_le_of_forall)

namespace ATK.NSDual

/-! ### Pareamentos -/

/-- `pr F g = ∫ ⟨F(x), Re F0 g (x)⟩`. -/
noncomputable def pr (F : E3 → E3) (g : E3 → C3) : ℝ := ∫ x, inner ℝ (F x) (R0 g x)

/-- O volume da bola `B̄(0, ρ)`. -/
noncomputable def Vb (ρ : ℝ) : ℝ := (volume (Metric.closedBall (0 : E3) ρ)).toReal

theorem Vb_nonneg (ρ : ℝ) : 0 ≤ Vb ρ := ENNReal.toReal_nonneg

/-- `g` contínua, nula fora de `B̄(0, ρ)`, com `|g| ≤ M`. -/
def Bola (ρ M : ℝ) (g : E3 → C3) : Prop :=
  Continuous g ∧ (∀ η, ρ < ‖η‖ → g η = 0) ∧ ∀ η, ‖g η‖ ≤ M

theorem Bola.hasCompactSupport {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) :
    HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E3) ρ) fun η hη => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hη
  exact hg.2.1 η hη

theorem Bola.pesos {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) : Pesos g :=
  pesos_of_compact hg.1 hg.hasCompactSupport

theorem Bola.integral_sq_le {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) :
    ∫ η, ‖g η‖ ^ 2 ≤ M ^ 2 * Vb ρ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
  have hle : ∀ η, ‖g η‖ ^ 2 ≤ (Metric.closedBall (0 : E3) ρ).indicator (fun _ => M ^ 2) η := by
    intro η
    by_cases hη : η ∈ Metric.closedBall (0 : E3) ρ
    · rw [indicator_of_mem hη]
      exact pow_le_pow_left₀ (norm_nonneg _) (hg.2.2 η) 2
    · rw [indicator_of_notMem hη]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hη
      rw [hg.2.1 η hη, norm_zero]
      norm_num
  have hi : Integrable ((Metric.closedBall (0 : E3) ρ).indicator fun _ => M ^ 2) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (measure_closedBall_lt_top).ne)
  calc ∫ η, ‖g η‖ ^ 2 ≤ ∫ η, (Metric.closedBall (0 : E3) ρ).indicator (fun _ => M ^ 2) η :=
        integral_mono ((hg.pesos.1.norm.pow 2).integrable_of_hasCompactSupport
          (hcs_of_zero hg.hasCompactSupport fun η h0 => by simp [h0])) hi hle
    _ = M ^ 2 * Vb ρ := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
          mul_comm]
        rfl

theorem Bola.integral_le {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) :
    ∫ η, ‖g η‖ ≤ M * Vb ρ := by
  have hle : ∀ η, ‖g η‖ ≤ (Metric.closedBall (0 : E3) ρ).indicator (fun _ => M) η := by
    intro η
    by_cases hη : η ∈ Metric.closedBall (0 : E3) ρ
    · rw [indicator_of_mem hη]
      exact hg.2.2 η
    · rw [indicator_of_notMem hη]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hη
      rw [hg.2.1 η hη, norm_zero]
  have hi : Integrable ((Metric.closedBall (0 : E3) ρ).indicator fun _ => M) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (measure_closedBall_lt_top).ne)
  calc ∫ η, ‖g η‖ ≤ ∫ η, (Metric.closedBall (0 : E3) ρ).indicator (fun _ => M) η :=
        integral_mono (integrable_pesos hg.pesos).norm hi hle
    _ = M * Vb ρ := by
        rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
          mul_comm]
        rfl

theorem integrable_R0_sq {g : E3 → C3} (hg : Pesos g) : Integrable fun x => ‖R0 g x‖ ^ 2 :=
  (L2B_R0 hg).2.2

theorem integral_R0_sq_le {g : E3 → C3} (hg : Pesos g) :
    ∫ x, ‖R0 g x‖ ^ 2 ≤ ∫ η, ‖g η‖ ^ 2 := by
  rw [← (plancherel_F0 hg).2]
  exact integral_mono (integrable_R0_sq hg) (plancherel_F0 hg).1 fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_R0_le g x) 2

/-- Integrabilidade do pareamento (`F ∈ L²`). -/
theorem integrable_pr_L2 {F : E3 → E3} (hFm : AEStronglyMeasurable F)
    (hF : Integrable fun x => ‖F x‖ ^ 2) {g : E3 → C3} (hg : Pesos g) :
    Integrable fun x => inner ℝ (F x) (R0 g x) := by
  refine ((hF.add (integrable_R0_sq hg)).div_const 2).mono'
    (hFm.inner (contDiff_R0 hg).continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have h1 := norm_inner_le_norm (𝕜 := ℝ) (F x) (R0 g x)
  have : ‖F x‖ * ‖R0 g x‖ ≤ (‖F x‖ ^ 2 + ‖R0 g x‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖F x‖ - ‖R0 g x‖)]
  exact h1.trans this

/-- Integrabilidade do pareamento (`F ∈ L¹`). -/
theorem integrable_pr_L1 {F : E3 → E3} (hFm : AEStronglyMeasurable F)
    (hF : Integrable fun x => ‖F x‖) {g : E3 → C3} (hg : Pesos g) :
    Integrable fun x => inner ℝ (F x) (R0 g x) := by
  refine (hF.mul_const (∫ ξ, ‖g ξ‖)).mono'
    (hFm.inner (contDiff_R0 hg).continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  gcongr
  exact (norm_R0_le g x).trans (norm_F0_le g x)

theorem R0_lin {g₁ g₂ g₃ : E3 → C3} (h₁ : Integrable g₁) (h₂ : Integrable g₂)
    (h₃ : Integrable g₃) (δ : ℝ) (x : E3) :
    R0 (fun η => g₁ η - g₂ η - δ • g₃ η) x = R0 g₁ x - R0 g₂ x - δ • R0 g₃ x := by
  unfold R0 F0
  have i1 := integrable_ex_smul h₁ x
  have i2 := integrable_ex_smul h₂ x
  have i3 := integrable_ex_smul h₃ x
  have e : (fun ξ => ex ξ x • (g₁ ξ - g₂ ξ - δ • g₃ ξ)) =
      fun ξ => ex ξ x • g₁ ξ - ex ξ x • g₂ ξ - δ • (ex ξ x • g₃ ξ) := by
    funext ξ
    rw [smul_sub, smul_sub, smul_comm]
  show reV (∫ ξ, ex ξ x • (g₁ ξ - g₂ ξ - δ • g₃ ξ)) = _
  have j12 : Integrable fun ξ => ex ξ x • g₁ ξ - ex ξ x • g₂ ξ := i1.sub i2
  have j3 : Integrable fun ξ => δ • (ex ξ x • g₃ ξ) := i3.smul δ
  rw [e, integral_sub j12 j3, integral_sub i1 i2, integral_smul]
  simp [map_sub, map_smul]

/-- **Linearidade** do pareamento. -/
theorem pr_lin {F : E3 → E3} (hint : ∀ {g : E3 → C3}, Pesos g →
    Integrable fun x => inner ℝ (F x) (R0 g x)) {g₁ g₂ g₃ : E3 → C3} (h₁ : Pesos g₁)
    (h₂ : Pesos g₂) (h₃ : Pesos g₃) (δ : ℝ) :
    pr F (fun η => g₁ η - g₂ η - δ • g₃ η) = pr F g₁ - pr F g₂ - δ * pr F g₃ := by
  unfold pr
  have e : (fun x => inner ℝ (F x) (R0 (fun η => g₁ η - g₂ η - δ • g₃ η) x)) =
      fun x => inner ℝ (F x) (R0 g₁ x) - inner ℝ (F x) (R0 g₂ x) -
        δ * inner ℝ (F x) (R0 g₃ x) := by
    funext x
    rw [R0_lin (integrable_pesos h₁) (integrable_pesos h₂) (integrable_pesos h₃),
      inner_sub_right, inner_sub_right, real_inner_smul_right]
  have i1 : Integrable fun x => inner ℝ (F x) (R0 g₁ x) := hint h₁
  have i2 : Integrable fun x => inner ℝ (F x) (R0 g₂ x) := hint h₂
  have i3 : Integrable fun x => δ * inner ℝ (F x) (R0 g₃ x) := (hint h₃).const_mul δ
  have i12 : Integrable fun x => inner ℝ (F x) (R0 g₁ x) - inner ℝ (F x) (R0 g₂ x) := i1.sub i2
  rw [e, integral_sub i12 i3, integral_sub i1 i2, integral_const_mul]

/-- Cota `L²` do pareamento. -/
theorem pr_bound_L2 {F : E3 → E3} (hFm : AEStronglyMeasurable F)
    (hF : Integrable fun x => ‖F x‖ ^ 2) {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) :
    |pr F g| ≤ M * ((∫ x, ‖F x‖ ^ 2) + Vb ρ) / 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
  rcases hM.eq_or_lt with hM0 | hMp
  · have hg0 : ∀ η, g η = 0 := fun η => norm_le_zero_iff.mp (hM0 ▸ hg.2.2 η)
    have : pr F g = 0 := by
      unfold pr R0 F0
      simp [hg0]
    rw [this, ← hM0]
    simp
  have hi := integrable_pr_L2 hFm hF hg.pesos
  have hb : ∀ x, |inner ℝ (F x) (R0 g x)| ≤ (M * ‖F x‖ ^ 2 + ‖R0 g x‖ ^ 2 / M) / 2 := by
    intro x
    have h1 := abs_real_inner_le_norm (F x) (R0 g x)
    exact h1.trans (amgm _ _ hMp)
  have hbi : Integrable fun x => (M * ‖F x‖ ^ 2 + ‖R0 g x‖ ^ 2 / M) / 2 :=
    ((hF.const_mul M).add ((integrable_R0_sq hg.pesos).div_const M)).div_const 2
  have h2 := integral_R0_sq_le hg.pesos
  have h3 := hg.integral_sq_le
  calc |pr F g| ≤ ∫ x, |inner ℝ (F x) (R0 g x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x, (M * ‖F x‖ ^ 2 + ‖R0 g x‖ ^ 2 / M) / 2 := integral_mono hi.abs hbi hb
    _ = (M * (∫ x, ‖F x‖ ^ 2) + (∫ x, ‖R0 g x‖ ^ 2) / M) / 2 := by
        have j1 : Integrable fun x => M * ‖F x‖ ^ 2 := hF.const_mul M
        have j2 : Integrable fun x => ‖R0 g x‖ ^ 2 / M := (integrable_R0_sq hg.pesos).div_const M
        rw [integral_div, integral_add j1 j2, integral_const_mul, integral_div]
    _ ≤ (M * (∫ x, ‖F x‖ ^ 2) + M ^ 2 * Vb ρ / M) / 2 := by gcongr; linarith
    _ = M * ((∫ x, ‖F x‖ ^ 2) + Vb ρ) / 2 := by field_simp

/-- Cota `L¹` do pareamento. -/
theorem pr_bound_L1 {F : E3 → E3} (hFm : AEStronglyMeasurable F)
    (hF : Integrable fun x => ‖F x‖) {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) :
    |pr F g| ≤ (∫ x, ‖F x‖) * (M * Vb ρ) := by
  have hi := integrable_pr_L1 hFm hF hg.pesos
  have hb : ∀ x, |inner ℝ (F x) (R0 g x)| ≤ ‖F x‖ * (M * Vb ρ) := by
    intro x
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact (norm_R0_le g x).trans ((norm_F0_le g x).trans hg.integral_le)
  calc |pr F g| ≤ ∫ x, |inner ℝ (F x) (R0 g x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖F x‖ * (M * Vb ρ) := integral_mono hi.abs (hF.mul_const _) hb
    _ = (∫ x, ‖F x‖) * (M * Vb ρ) := integral_mul_const _ _


theorem pr_neg (F : E3 → E3) {g : E3 → C3} (_hg : Integrable g) :
    pr F (fun η => -g η) = -pr F g := by
  have e : ∀ x, R0 (fun η => -g η) x = -R0 g x := by
    intro x
    unfold R0 F0
    simp_rw [smul_neg]
    rw [integral_neg, map_neg]
  unfold pr
  simp_rw [e, inner_neg_right]
  exact integral_neg _

/-! ### A família do calor -/

/-- `Hk c g k s = (c|η|²)^k e^{−c|η|² s} g`. -/
noncomputable def Hk (c : ℝ) (g : E3 → C3) (k : ℕ) (s : ℝ) (η : E3) : C3 :=
  ((c * ‖η‖ ^ 2) ^ k * exp (-(c * ‖η‖ ^ 2 * s))) • g η

theorem continuous_Hk {c : ℝ} {g : E3 → C3} (hg : Continuous g) (k : ℕ) (s : ℝ) :
    Continuous (Hk c g k s) := by
  unfold Hk
  fun_prop

theorem Hk_zero_of {c : ℝ} {g : E3 → C3} {η : E3} (h0 : g η = 0) (k : ℕ) (s : ℝ) :
    Hk c g k s η = 0 := by
  simp [Hk, h0]

theorem Hk_succ (c : ℝ) (g : E3 → C3) (k : ℕ) (s : ℝ) (η : E3) :
    Hk c g (k + 1) s η = (c * ‖η‖ ^ 2) • Hk c g k s η := by
  unfold Hk
  rw [smul_smul, pow_succ]
  ring_nf

theorem Bola.heat {c : ℝ} (hc : 0 ≤ c) {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) (k : ℕ)
    (s : ℝ) : Bola ρ ((c * ρ ^ 2) ^ k * exp (c * ρ ^ 2 * |s|) * M) (Hk c g k s) := by
  have hρ : ∀ η, ‖g η‖ ≠ 0 → ‖η‖ ≤ ρ := fun η hη => by
    by_contra h
    exact hη (by rw [hg.2.1 η (not_le.mp h), norm_zero])
  refine ⟨continuous_Hk hg.1 k s, fun η hη => Hk_zero_of (hg.2.1 η hη) k s, fun η => ?_⟩
  unfold Hk
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  by_cases h0 : ‖g η‖ = 0
  · rw [h0, mul_zero]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
    positivity
  have hη := hρ η h0
  have h1 : c * ‖η‖ ^ 2 ≤ c * ρ ^ 2 := by gcongr
  have h2 : exp (-(c * ‖η‖ ^ 2 * s)) ≤ exp (c * ρ ^ 2 * |s|) := by
    rw [exp_le_exp]
    have : -(c * ‖η‖ ^ 2 * s) ≤ c * ‖η‖ ^ 2 * |s| := by
      rw [neg_le]
      have := neg_abs_le s
      have h3 : 0 ≤ c * ‖η‖ ^ 2 := by positivity
      nlinarith
    exact this.trans (by gcongr)
  calc (c * ‖η‖ ^ 2) ^ k * exp (-(c * ‖η‖ ^ 2 * s)) * ‖g η‖
      ≤ (c * ρ ^ 2) ^ k * exp (c * ρ ^ 2 * |s|) * M := by
        gcongr
        exact hg.2.2 η

/-- **Taylor uniforme** da família do calor na bola. -/
theorem Hk_taylor {c : ℝ} (hc : 0 ≤ c) {ρ M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) (k : ℕ)
    (s : ℝ) {δ : ℝ} (hδ : c * ρ ^ 2 * |δ| ≤ 1) :
    Bola ρ ((c * ρ ^ 2) ^ k * exp (c * ρ ^ 2 * |s|) * M * (c * ρ ^ 2) ^ 2 * δ ^ 2)
      (fun η => Hk c g k (s + δ) η - Hk c g k s η - δ • (fun η => -Hk c g (k + 1) s η) η) := by
  have hρ : ∀ η, ‖g η‖ ≠ 0 → ‖η‖ ≤ ρ := fun η hη => by
    by_contra h
    exact hη (by rw [hg.2.1 η (not_le.mp h), norm_zero])
  refine ⟨((continuous_Hk hg.1 k _).sub (continuous_Hk hg.1 k s)).sub
    ((continuous_Hk hg.1 (k + 1) s).neg.const_smul δ), fun η hη => ?_, fun η => ?_⟩
  · simp [Hk_zero_of (hg.2.1 η hη)]
  have e : Hk c g k (s + δ) η - Hk c g k s η - δ • (fun η => -Hk c g (k + 1) s η) η =
      ((c * ‖η‖ ^ 2) ^ k * exp (-(c * ‖η‖ ^ 2 * s)) *
        (exp (-(c * ‖η‖ ^ 2 * δ)) - 1 - -(c * ‖η‖ ^ 2 * δ))) • g η := by
    simp only [Hk, smul_neg, sub_neg_eq_add, smul_smul]
    rw [← sub_smul, ← add_smul]
    congr 1
    rw [show -(c * ‖η‖ ^ 2 * (s + δ)) = -(c * ‖η‖ ^ 2 * s) + -(c * ‖η‖ ^ 2 * δ) by ring,
      exp_add, pow_succ]
    ring
  show ‖Hk c g k (s + δ) η - Hk c g k s η - δ • (fun η => -Hk c g (k + 1) s η) η‖ ≤ _
  rw [e, norm_smul]
  by_cases h0 : ‖g η‖ = 0
  · rw [h0, mul_zero]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
    positivity
  have hη := hρ η h0
  have ha : c * ‖η‖ ^ 2 ≤ c * ρ ^ 2 := by gcongr
  have ha0 : 0 ≤ c * ‖η‖ ^ 2 := by positivity
  have hx : |-(c * ‖η‖ ^ 2 * δ)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_nonneg ha0]
    calc c * ‖η‖ ^ 2 * |δ| ≤ c * ρ ^ 2 * |δ| := by gcongr
      _ ≤ 1 := hδ
  have ht := Real.abs_exp_sub_one_sub_id_le hx
  have h2 : exp (-(c * ‖η‖ ^ 2 * s)) ≤ exp (c * ρ ^ 2 * |s|) := by
    rw [exp_le_exp]
    have : -(c * ‖η‖ ^ 2 * s) ≤ c * ‖η‖ ^ 2 * |s| := by
      rw [neg_le]
      have := neg_abs_le s
      nlinarith
    exact this.trans (by gcongr)
  have h3 : (-(c * ‖η‖ ^ 2 * δ)) ^ 2 ≤ (c * ρ ^ 2) ^ 2 * δ ^ 2 := by
    rw [neg_sq, mul_pow]
    gcongr
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (exp_pos _).le,
    Real.norm_eq_abs]
  calc (c * ‖η‖ ^ 2) ^ k * exp (-(c * ‖η‖ ^ 2 * s)) *
        |exp (-(c * ‖η‖ ^ 2 * δ)) - 1 - -(c * ‖η‖ ^ 2 * δ)| * ‖g η‖
      ≤ (c * ρ ^ 2) ^ k * exp (c * ρ ^ 2 * |s|) * ((c * ρ ^ 2) ^ 2 * δ ^ 2) * M := by
        gcongr
        · exact ht.trans h3
        · exact hg.2.2 η
    _ = (c * ρ ^ 2) ^ k * exp (c * ρ ^ 2 * |s|) * M * (c * ρ ^ 2) ^ 2 * δ ^ 2 := by ring

/-- **Derivada** de `s ↦ pr F (Hk c g k s)`. -/
theorem hasDerivAt_pr_Hk {F : E3 → E3}
    (hint : ∀ {g : E3 → C3}, Pesos g → Integrable fun x => inner ℝ (F x) (R0 g x))
    {ρ K : ℝ} (hK : 0 ≤ K) (hbd : ∀ {M : ℝ} {g : E3 → C3}, Bola ρ M g → |pr F g| ≤ K * M)
    {c : ℝ} (hc : 0 ≤ c) {M : ℝ} {g : E3 → C3} (hg : Bola ρ M g) (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s => pr F (Hk c g k s)) (-pr F (Hk c g (k + 1) s)) s := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2 0)
  set A : ℝ := c * ρ ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set L : ℝ := K * (A ^ k * exp (A * |s|) * M * A ^ 2) with hL
  have hL0 : 0 ≤ L := by positivity
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hδ0 : ∀ᶠ δ in 𝓝 (0 : ℝ), |δ| < min (1 / (A + 1)) (ε / (L + 1)) := by
    have : (0 : ℝ) < min (1 / (A + 1)) (ε / (L + 1)) := lt_min (by positivity) (by positivity)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) this] with δ hδ
    simpa [Metric.mem_ball, dist_zero_right] using hδ
  filter_upwards [hδ0] with δ hδ
  have hδ1 : A * |δ| ≤ 1 := by
    have h1 := (lt_min_iff.mp hδ).1
    have : |δ| ≤ 1 / (A + 1) := h1.le
    calc A * |δ| ≤ A * (1 / (A + 1)) := by gcongr
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  have hT := Hk_taylor hc hg k s (δ := δ) hδ1
  have hpg : ∀ k' s', Pesos (Hk c g k' s') := fun k' s' => (hg.heat hc k' s').pesos
  have hneg : Pesos fun η => -Hk c g (k + 1) s η := by
    have := (hg.heat hc (k + 1) s)
    exact Bola.pesos (ρ := ρ) ⟨this.1.neg, fun η hη => by simp [this.2.1 η hη],
      fun η => by rw [norm_neg]; exact this.2.2 η⟩
  have hlin := pr_lin hint (hpg k (s + δ)) (hpg k s) hneg δ
  rw [pr_neg F (integrable_pesos (hpg (k + 1) s))] at hlin
  have hb := hbd hT
  rw [hlin] at hb
  have e : pr F (Hk c g k (s + δ)) - pr F (Hk c g k s) - δ • -pr F (Hk c g (k + 1) s) =
      pr F (Hk c g k (s + δ)) - pr F (Hk c g k s) - δ * -pr F (Hk c g (k + 1) s) := by
    rw [smul_eq_mul]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, e]
  have hδ2 := (lt_min_iff.mp hδ).2
  calc |pr F (Hk c g k (s + δ)) - pr F (Hk c g k s) - δ * -pr F (Hk c g (k + 1) s)|
      ≤ K * (A ^ k * exp (A * |s|) * M * A ^ 2 * δ ^ 2) := hb
    _ = L * |δ| * |δ| := by rw [hL, ← sq_abs δ]; ring
    _ ≤ (L + 1) * (ε / (L + 1)) * |δ| := by
        have : L * |δ| ≤ (L + 1) * (ε / (L + 1)) := by
          calc L * |δ| ≤ (L + 1) * |δ| := by gcongr; linarith
            _ ≤ (L + 1) * (ε / (L + 1)) := by gcongr
        gcongr
    _ = ε * |δ| := by field_simp


theorem real_smul_C3 (r : ℝ) (a : C3) : r • a = (r : ℂ) • a := by
  ext j
  simp [Complex.real_smul]

/-- A família do calor preserva os dados teste. -/
theorem Teste.heat {c : ℝ} {h : E3 → C3} (hh : Teste h) (k : ℕ) (s : ℝ) :
    Teste (Hk c h k s) := by
  obtain ⟨a, ha, hz⟩ := hh.zero
  refine ⟨continuous_Hk hh.cont k s, hcs_of_zero hh.supp fun η h0 => Hk_zero_of h0 k s,
    ⟨a, ha, fun η hη => Hk_zero_of (hz η hη) k s⟩, fun η => ?_, fun η => ?_⟩
  · unfold Hk
    rw [real_smul_C3, ip_smul, hh.div, mul_zero]
  · unfold Hk
    rw [hh.herm, norm_neg, real_smul_C3, real_smul_C3, cj_smul, Complex.conj_ofReal]

theorem Teste.bola {h : E3 → C3} (hh : Teste h) : ∃ ρ M, 0 ≤ ρ ∧ Bola ρ M h := by
  obtain ⟨B, hB⟩ := hh.supp.exists_bound_of_continuous hh.cont
  obtain ⟨R, hR⟩ := hh.supp.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, B, le_max_right _ _, hh.cont, fun η hη => ?_, hB⟩
  by_contra hne
  have hmem : η ∈ tsupport h := subset_tsupport _ hne
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 0]

/-! ### Integração por partes no espaço todo -/

/-- `∫ ⟨∂_j F, ∂_j φ⟩ = −∫ ⟨F, ∂_j∂_j φ⟩` para `F, ∂_jF ∈ L²` e `φ = Re F0 g`. -/
theorem ibp_L2 {F : E3 → E3} (hF : ContDiff ℝ 1 F) (hF2 : Integrable fun x => ‖F x‖ ^ 2)
    (j : Fin 3) (hdF2 : Integrable fun x => ‖dX j F x‖ ^ 2) {g : E3 → C3} (hg : Pesos g) :
    ∫ x, inner ℝ (dX j F x) (dX j (R0 g) x) = -∫ x, inner ℝ (F x) (dX j (dX j (R0 g)) x) := by
  have hφ := contDiff_R0 hg
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hdφ : ContDiff ℝ ∞ (dX j (R0 g)) := contDiff_dX_top hφ j
  have e1 : ∀ x, dX j (R0 g) x = R0 (fun ξ => mj j ξ • g ξ) x := dX_R0 hg j
  have hg1 := pesos_mj hg j
  have hg2 := pesos_mj hg1 j
  have e2 : ∀ x, dX j (dX j (R0 g)) x = R0 (fun ξ => mj j ξ • (mj j ξ • g ξ)) x := by
    intro x
    have : dX j (R0 g) = R0 (fun ξ => mj j ξ • g ξ) := funext e1
    rw [this, dX_R0 hg1]
  have L1 := L2B_R0 hg1
  have L2 := L2B_R0 hg2
  have hFi : ∀ i, ContDiff ℝ 1 fun x => F x i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  have hφi : ∀ i, ContDiff ℝ ∞ fun x => dX j (R0 g) x i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hdφ
  -- integrabilidade dos produtos de funções `L²`
  have hprod : ∀ {a b : E3 → ℝ}, Continuous a → Continuous b → Integrable (fun x => a x ^ 2) →
      Integrable (fun x => b x ^ 2) → Integrable fun x => a x * b x := by
    intro a b ha hb ha2 hb2
    refine ((ha2.add hb2).div_const 2).mono' (ha.mul hb).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    show |a x| * |b x| ≤ (a x ^ 2 + b x ^ 2) / 2
    nlinarith [sq_nonneg (|a x| - |b x|), sq_abs (a x), sq_abs (b x)]
  have hsq : ∀ {G : E3 → E3} (i : Fin 3), Continuous G → Integrable (fun x => ‖G x‖ ^ 2) →
      Integrable fun x => G x i ^ 2 := by
    intro G i hG hG2
    refine hG2.mono' (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hG).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_coord_le _ i) 2
  have hR1 : Integrable fun x => ‖dX j (R0 g) x‖ ^ 2 := by
    simp_rw [e1]; exact L1.2.2
  have hR2 : Integrable fun x => ‖dX j (dX j (R0 g)) x‖ ^ 2 := by
    simp_rw [e2]; exact L2.2.2
  have hcdF : Continuous (dX j F) := continuous_dX_gen hF j
  have hcφ1 : Continuous (dX j (R0 g)) := hdφ.continuous
  have hcφ2 : Continuous (dX j (dX j (R0 g))) := (contDiff_dX_top hdφ j).continuous
  have e3 : (fun x => inner ℝ (dX j F x) (dX j (R0 g) x)) =
      fun x => ∑ i, dX j (fun y => F y i) x * dX j (R0 g) x i := by
    funext x
    rw [inner_E3]
    congr 1
    funext i
    rw [dX_coord (hF.differentiable one_ne_zero x)]
  have e4 : (fun x => inner ℝ (F x) (dX j (dX j (R0 g)) x)) =
      fun x => ∑ i, F x i * dX j (fun y => dX j (R0 g) y i) x := by
    funext x
    rw [inner_E3]
    congr 1
    funext i
    rw [dX_coord (hdφ.differentiable hne x)]
  rw [e3, e4, integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have i1 : Integrable fun x => fderiv ℝ (fun y => F y i) x (e j) * dX j (R0 g) x i := by
      have := hprod (continuous_dX (hFi i) j) ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcφ1)
        (by
          have := hsq i hcdF hdF2
          simp_rw [← dX_coord (hF.differentiable one_ne_zero _)]
          exact this) (hsq i hcφ1 hR1)
      exact this
    have i2 : Integrable fun x => F x i * fderiv ℝ (fun y => dX j (R0 g) y i) x (e j) := by
      have := hprod (hFi i).continuous (continuous_dX ((hφi i).of_le (by simp)) j)
        (hsq i hF.continuous hF2) (by
          have := hsq i hcφ2 hR2
          simp_rw [← dX_coord (hdφ.differentiable hne _)]
          exact this)
      exact this
    have i3 : Integrable fun x => F x i * dX j (R0 g) x i :=
      hprod (hFi i).continuous ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcφ1)
        (hsq i hF.continuous hF2) (hsq i hcφ1 hR1)
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
      (fun x _ => (hFi i).differentiable one_ne_zero x)
      (fun x _ => (hφi i).differentiable hne x)
    show ∫ x, fderiv ℝ (fun y => F y i) x (e j) * dX j (R0 g) x i =
      -∫ x, F x i * fderiv ℝ (fun y => dX j (R0 g) y i) x (e j)
    linarith [this]
  · intro i _
    exact hprod (hFi i).continuous (continuous_dX ((hφi i).of_le (by simp)) j)
      (hsq i hF.continuous hF2) (by
        have := hsq i hcφ2 hR2
        simp_rw [← dX_coord (hdφ.differentiable hne _)]
        exact this)
  · intro i _
    exact hprod (continuous_dX (hFi i) j) ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcφ1)
      (by
        have := hsq i hcdF hdF2
        simp_rw [← dX_coord (hF.differentiable one_ne_zero _)]
        exact this) (hsq i hcφ1 hR1)

end ATK.NSDual

#print axioms ATK.NSDual.pr
#print axioms ATK.NSDual.Vb
#print axioms ATK.NSDual.Vb_nonneg
#print axioms ATK.NSDual.Bola
#print axioms ATK.NSDual.Bola.hasCompactSupport
#print axioms ATK.NSDual.Bola.pesos
#print axioms ATK.NSDual.Bola.integral_sq_le
#print axioms ATK.NSDual.Bola.integral_le
#print axioms ATK.NSDual.integrable_R0_sq
#print axioms ATK.NSDual.integral_R0_sq_le
#print axioms ATK.NSDual.integrable_pr_L2
#print axioms ATK.NSDual.integrable_pr_L1
#print axioms ATK.NSDual.R0_lin
#print axioms ATK.NSDual.pr_lin
#print axioms ATK.NSDual.pr_bound_L2
#print axioms ATK.NSDual.pr_bound_L1
#print axioms ATK.NSDual.pr_neg
#print axioms ATK.NSDual.Hk
#print axioms ATK.NSDual.continuous_Hk
#print axioms ATK.NSDual.Hk_zero_of
#print axioms ATK.NSDual.Hk_succ
#print axioms ATK.NSDual.Bola.heat
#print axioms ATK.NSDual.Hk_taylor
#print axioms ATK.NSDual.hasDerivAt_pr_Hk
#print axioms ATK.NSDual.real_smul_C3
#print axioms ATK.NSDual.Teste.heat
#print axioms ATK.NSDual.Teste.bola
#print axioms ATK.NSDual.ibp_L2
