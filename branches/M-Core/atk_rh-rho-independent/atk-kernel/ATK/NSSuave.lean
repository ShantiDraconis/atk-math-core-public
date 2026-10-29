import ATK.NSFourierBase
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# ATK — Integrais de Fourier suaves em `ℝ³ × [0, T]`

Camada 3 do ataque a B3. Uma **amplitude suave** em `[0, T]` (`Amp T b`) é uma sequência
`b k : ℝ → ℝ³ → ℂ³` (a `k`-ésima derivada no tempo) com

* decaimento rápido uniforme: `‖b k t ξ‖ ≤ C_{k,m} (1 + ‖ξ‖)^{−m}` para `t ∈ [0, T]` e todo `m`;
* continuidade em `t` e mensurabilidade em `ξ`;
* `b k t ξ = b k 0 ξ + ∫₀ᵗ b (k+1) s ξ ds` (a derivada temporal, em forma integral).

Para uma amplitude suave, `V(x, t) = ∫ e^{2πi⟪ξ, x⟫} b 0 t ξ dξ` é **`C^∞` em `ℝ³ × [0, T]`**
(`contDiffOn_V`), com derivadas explícitas (`hasFDerivWithinAt_V`):
`∂_{x_j} V = V[2πiξ_j b]` e `∂_t V = V[b 1]`. A classe é estável por deslocamento (`Amp.shift`)
e por multiplicadores de crescimento polinomial (`Amp.mulc`), o que faz a indução funcionar.

Nada aqui é sobre Navier–Stokes; **CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped Real ContDiff

namespace ATK.NSSuave

open ATK.LigacaoNS ATK.NSFourierBase

/-! ### O caráter `e^{2πi⟪ξ, x⟫}` -/

/-- `ex x ξ = e^{2πi⟪ξ, x⟫}`. -/
noncomputable def ex (x ξ : E3) : ℂ := Complex.exp (((2 * π * inner ℝ ξ x : ℝ) : ℂ) * Complex.I)

theorem norm_ex (x ξ : E3) : ‖ex x ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_ex : Continuous fun p : E3 × E3 => ex p.1 p.2 := by
  unfold ex
  fun_prop

theorem continuous_ex_right (x : E3) : Continuous fun ξ : E3 => ex x ξ :=
  continuous_ex.comp (continuous_const.prodMk continuous_id)

theorem ex_add (x δ ξ : E3) : ex (x + δ) ξ = ex x ξ * ex δ ξ := by
  unfold ex
  rw [← Complex.exp_add, inner_add_right]
  congr 1
  push_cast
  ring

theorem norm_exp_I_sub_one_le (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
  rwa [mul_comm, Real.norm_eq_abs] at h

theorem norm_exp_I_sub_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ 3 * θ ^ 2 := by
  have hn : ‖(θ : ℂ) * Complex.I‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt |θ| 1 with h | h
  · have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by rw [hn]; exact h
    have := Complex.norm_exp_sub_one_sub_id_le hx
    rw [hn, sq_abs] at this
    nlinarith [sq_nonneg θ]
  · calc ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖
        ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ + ‖(θ : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ |θ| + |θ| := by rw [hn]; exact add_le_add (norm_exp_I_sub_one_le θ) le_rfl
      _ ≤ 3 * θ ^ 2 := by nlinarith [sq_abs θ, abs_nonneg θ]

theorem abs_inner_le (ξ δ : E3) : |inner ℝ ξ δ| ≤ ‖ξ‖ * ‖δ‖ := abs_real_inner_le_norm ξ δ

theorem norm_ex_sub_one_le (δ ξ : E3) : ‖ex δ ξ - 1‖ ≤ 2 * π * (‖δ‖ * ‖ξ‖) := by
  unfold ex
  refine (norm_exp_I_sub_one_le _).trans ?_
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have := abs_inner_le ξ δ
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hπ]

/-- `‖e^{2πi⟪ξ,δ⟫} − 1 − 2πi⟪ξ,δ⟫‖ ≤ 12π² ‖δ‖² ‖ξ‖²`. -/
theorem norm_ex_sub_le (δ ξ : E3) :
    ‖ex δ ξ - 1 - ((2 * π * inner ℝ ξ δ : ℝ) : ℂ) * Complex.I‖ ≤
      12 * π ^ 2 * (‖δ‖ ^ 2 * ‖ξ‖ ^ 2) := by
  unfold ex
  refine (norm_exp_I_sub_le _).trans ?_
  have h1 : (2 * π * inner ℝ ξ δ) ^ 2 ≤ 4 * π ^ 2 * (‖δ‖ ^ 2 * ‖ξ‖ ^ 2) := by
    have h := abs_inner_le ξ δ
    have h2 : (inner ℝ ξ δ) ^ 2 ≤ (‖ξ‖ * ‖δ‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    nlinarith [sq_nonneg π]
  nlinarith

/-! ### Pesos -/

theorem w_inv_anti {m n : ℕ} (h : n ≤ m) (ξ : E3) : (w m ξ)⁻¹ ≤ (w n ξ)⁻¹ :=
  inv_anti₀ (w_pos n ξ) (w_mono h ξ)

theorem w_add (m d : ℕ) (ξ : E3) : w (m + d) ξ = w m ξ * w d ξ := by
  unfold w; rw [pow_add]

theorem norm_le_w1 (ξ : E3) : ‖ξ‖ ≤ w 1 ξ := by unfold w; simp

theorem norm_sq_le_w2 (ξ : E3) : ‖ξ‖ ^ 2 ≤ w 2 ξ := by
  unfold w
  have := norm_nonneg ξ
  nlinarith

/-! ### Amplitudes suaves no tempo -/

/-- **Amplitude suave em `[0, T]`**: `b k` é a `k`-ésima derivada temporal, com decaimento rápido
uniforme em `ξ`. -/
structure Amp (T : ℝ) (b : ℕ → ℝ → E3 → C3) : Prop where
  meas : ∀ k t, AEStronglyMeasurable (b k t)
  cont : ∀ k ξ, ContinuousOn (fun t => b k t ξ) (Icc 0 T)
  bound : ∀ k (m : ℕ), ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ ξ, ‖b k t ξ‖ ≤ C * (w m ξ)⁻¹
  deriv : ∀ k ξ, ∀ t ∈ Icc 0 T, b k t ξ = b k 0 ξ + ∫ s in (0 : ℝ)..t, b (k + 1) s ξ

/-- Deslocamento: as derivadas de `b`. -/
def desloc (b : ℕ → ℝ → E3 → C3) : ℕ → ℝ → E3 → C3 := fun k => b (k + 1)

/-- Multiplicador escalar em `ξ`. -/
def mulC (c : E3 → ℂ) (b : ℕ → ℝ → E3 → C3) : ℕ → ℝ → E3 → C3 := fun k t ξ => c ξ • b k t ξ

theorem Amp.shift {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) : Amp T (desloc b) where
  meas k t := hb.meas (k + 1) t
  cont k ξ := hb.cont (k + 1) ξ
  bound k m := hb.bound (k + 1) m
  deriv k ξ t ht := hb.deriv (k + 1) ξ t ht

/-- Multiplicadores mensuráveis de crescimento polinomial preservam a classe. -/
theorem Amp.mulc {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) {c : E3 → ℂ}
    (hc : AEStronglyMeasurable c) {K : ℝ} (d : ℕ) (hK : ∀ ξ, ‖c ξ‖ ≤ K * w d ξ) :
    Amp T (mulC c b) where
  meas k t := hc.smul (hb.meas k t)
  cont k ξ := (hb.cont k ξ).const_smul (c ξ)
  bound k m := by
    obtain ⟨C, hC0, hC⟩ := hb.bound k (m + d)
    have hK0 : 0 ≤ K := by
      have := (norm_nonneg _).trans (hK 0)
      exact nonneg_of_mul_nonneg_left this (w_pos d 0)
    refine ⟨K * C, mul_nonneg hK0 hC0, fun t ht ξ => ?_⟩
    simp only [mulC]
    rw [norm_smul]
    calc ‖c ξ‖ * ‖b k t ξ‖ ≤ (K * w d ξ) * (C * (w (m + d) ξ)⁻¹) :=
          mul_le_mul (hK ξ) (hC t ht ξ) (norm_nonneg _) (mul_nonneg hK0 (w_pos d ξ).le)
      _ = K * C * (w m ξ)⁻¹ := by
          rw [w_add]
          have := w_pos d ξ
          have := w_pos m ξ
          field_simp
  deriv k ξ t ht := by
    simp only [mulC]
    rw [hb.deriv k ξ t ht, smul_add, intervalIntegral.integral_smul]

/-- Uma cota em `w_m` dá todas as cotas mais fracas. -/
theorem Amp.bound_le {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (k m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ ξ, ∀ n ≤ m, ‖b k t ξ‖ ≤ C * (w n ξ)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := hb.bound k m
  exact ⟨C, hC0, fun t ht ξ n hn =>
    (hC t ht ξ).trans (mul_le_mul_of_nonneg_left (w_inv_anti hn ξ) hC0)⟩

theorem Amp.intervalIntegrable {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (k : ℕ) (ξ : E3)
    {t r : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Icc 0 T) :
    IntervalIntegrable (fun s => b k s ξ) volume t r := by
  refine ((hb.cont k ξ).mono ?_).intervalIntegrable
  intro s hs
  rcases le_total t r with h | h
  · rw [uIcc_of_le h] at hs; exact ⟨ht.1.trans hs.1, hs.2.trans hr.2⟩
  · rw [uIcc_of_ge h] at hs; exact ⟨hr.1.trans hs.1, hs.2.trans ht.2⟩

/-- `b k r − b k t = ∫ₜʳ b (k+1)`. -/
theorem Amp.sub_eq {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (k : ℕ) (ξ : E3)
    {t r : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Icc 0 T) :
    b k r ξ - b k t ξ = ∫ s in t..r, b (k + 1) s ξ := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  rw [hb.deriv k ξ r hr, hb.deriv k ξ t ht, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hb.intervalIntegrable (k + 1) ξ h0 hr)
      (hb.intervalIntegrable (k + 1) ξ h0 ht)]

theorem mem_Icc_of_uIoc {T t r s : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Icc 0 T) (hs : s ∈ uIoc t r) :
    s ∈ Icc 0 T := by
  rcases le_total t r with h | h
  · rw [uIoc_of_le h] at hs; exact ⟨ht.1.trans hs.1.le, hs.2.trans hr.2⟩
  · rw [uIoc_of_ge h] at hs; exact ⟨hr.1.trans hs.1.le, hs.2.trans ht.2⟩

theorem abs_sub_le_of_uIoc {t r s : ℝ} (hs : s ∈ uIoc t r) : |s - t| ≤ |r - t| := by
  rcases le_total t r with h | h
  · rw [uIoc_of_le h] at hs
    rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]
    linarith [hs.2]
  · rw [uIoc_of_ge h] at hs
    rw [abs_le, abs_of_nonpos (by linarith)]
    constructor <;> linarith [hs.1, hs.2]

/-- Cota de primeira ordem: `‖b k r − b k t‖ ≤ |r − t| C w_m⁻¹`. -/
theorem Amp.norm_sub_le {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (k : ℕ) {m : ℕ}
    {C : ℝ} (hC : ∀ t ∈ Icc 0 T, ∀ ξ, ‖b (k + 1) t ξ‖ ≤ C * (w m ξ)⁻¹) (ξ : E3)
    {t r : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Icc 0 T) :
    ‖b k r ξ - b k t ξ‖ ≤ |r - t| * (C * (w m ξ)⁻¹) := by
  rw [hb.sub_eq k ξ ht hr, mul_comm]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun s hs =>
    hC s (mem_Icc_of_uIoc ht hr hs) ξ

/-- Cota de segunda ordem: `‖b k r − b k t − (r − t) b (k+1) t‖ ≤ |r − t|² C w_m⁻¹`. -/
theorem Amp.norm_sub_sub_le {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (k : ℕ) {m : ℕ}
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t ∈ Icc 0 T, ∀ ξ, ‖b (k + 2) t ξ‖ ≤ C * (w m ξ)⁻¹) (ξ : E3)
    {t r : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Icc 0 T) :
    ‖b k r ξ - b k t ξ - (r - t) • b (k + 1) t ξ‖ ≤ |r - t| ^ 2 * (C * (w m ξ)⁻¹) := by
  have hint := hb.intervalIntegrable (k + 1) ξ ht hr
  have e : b k r ξ - b k t ξ - (r - t) • b (k + 1) t ξ =
      ∫ s in t..r, (b (k + 1) s ξ - b (k + 1) t ξ) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, hb.sub_eq k ξ ht hr]
  rw [e, sq, mul_assoc, mul_comm]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
  have hs' := mem_Icc_of_uIoc ht hr hs
  have h1 := hb.norm_sub_le (k + 1) hC ξ ht hs'
  have h2 := abs_sub_le_of_uIoc hs
  calc ‖b (k + 1) s ξ - b (k + 1) t ξ‖ ≤ |s - t| * (C * (w m ξ)⁻¹) := h1
    _ ≤ |r - t| * (C * (w m ξ)⁻¹) :=
        mul_le_mul_of_nonneg_right h2 (by have := w_pos m ξ; positivity)

/-! ### A integral de Fourier -/

/-- `Vf f x = ∫ e^{2πi⟪ξ, x⟫} f(ξ) dξ`. -/
noncomputable def Vf (f : E3 → C3) (x : E3) : C3 := ∫ ξ, ex x ξ • f ξ

/-- `V b (x, t) = Vf (b t) x`. -/
noncomputable def V (b : ℝ → E3 → C3) (p : E3 × ℝ) : C3 := Vf (b p.2) p.1

theorem integrable_ex_smul {f : E3 → C3} (hf : AEStronglyMeasurable f) {C : ℝ}
    (hC : ∀ ξ, ‖f ξ‖ ≤ C * (w 4 ξ)⁻¹) (x : E3) : Integrable fun ξ => ex x ξ • f ξ := by
  refine (integrable_w_inv.const_mul C).mono' ((continuous_ex_right x).aestronglyMeasurable.smul hf)
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_smul, norm_ex, one_mul]
  exact hC ξ

theorem Amp.integrable {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : E3) : Integrable fun ξ => ex x ξ • b k t ξ := by
  obtain ⟨C, -, hC⟩ := hb.bound k 4
  exact integrable_ex_smul (hb.meas k t) (hC t ht) x

/-- **Continuidade** de `V` em `ℝ³ × [0, T]`. -/
theorem Amp.continuousOn_V {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (k : ℕ) :
    ContinuousOn (V (b k)) (univ ×ˢ Icc 0 T) := by
  obtain ⟨C, -, hC⟩ := hb.bound k 4
  unfold V Vf
  refine continuousOn_of_dominated (bound := fun ξ => C * (w 4 ξ)⁻¹) (fun p hp => ?_)
    (fun p hp => Eventually.of_forall fun ξ => ?_) (integrable_w_inv.const_mul C)
    (Eventually.of_forall fun ξ => ?_)
  · exact (continuous_ex_right p.1).aestronglyMeasurable.smul (hb.meas k p.2)
  · rw [norm_smul, norm_ex, one_mul]; exact hC p.2 hp.2 ξ
  · refine ContinuousOn.smul (f := fun p : E3 × ℝ => ex p.1 ξ)
      (g := fun p : E3 × ℝ => b k p.2 ξ) ?_ ?_
    · exact (continuous_ex.comp (continuous_fst.prodMk continuous_const)).continuousOn
    · exact (hb.cont k ξ).comp continuousOn_snd (fun p hp => hp.2)

/-! ### A derivada -/

/-- `c_j(ξ) = 2πi ξ_j` (a derivada `∂_{x_j}`). -/
noncomputable def cj (j : Fin 3) (ξ : E3) : ℂ := ((2 * π * ξ j : ℝ) : ℂ) * Complex.I

theorem norm_cj_le (j : Fin 3) (ξ : E3) : ‖cj j ξ‖ ≤ 2 * π * w 1 ξ := by
  unfold cj
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := PiLp.norm_apply_le ξ j
  rw [Real.norm_eq_abs] at h
  exact h.trans (norm_le_w1 ξ)

theorem continuous_cj (j : Fin 3) : Continuous (cj j) := by
  unfold cj; fun_prop

theorem Amp.mulcj {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) (j : Fin 3) :
    Amp T (mulC (cj j) b) :=
  hb.mulc (continuous_cj j).aestronglyMeasurable 1 (norm_cj_le j)

theorem sum_cj_smul (δ ξ : E3) (v : C3) :
    ∑ j, δ j • (cj j ξ • v) = (((2 * π * inner ℝ ξ δ : ℝ) : ℂ) * Complex.I) • v := by
  have hin : inner ℝ ξ δ = ∑ j, ξ j * δ j := by
    simp [PiLp.inner_apply, mul_comm]
  simp only [cj, ← smul_assoc]
  rw [← Finset.sum_smul]
  congr 1
  rw [hin]
  simp only [Fin.sum_univ_three, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- Projeções de `ℝ³ × ℝ`. -/
noncomputable def projX (j : Fin 3) : E3 × ℝ →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.fst ℝ E3 ℝ)

noncomputable def projT : E3 × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E3 ℝ

/-- A derivada de `V (b 0)` em `p`. -/
noncomputable def Lmap (b : ℕ → ℝ → E3 → C3) (p : E3 × ℝ) : E3 × ℝ →L[ℝ] C3 :=
  ∑ j, (projX j).smulRight (V (mulC (cj j) b 0) p) + projT.smulRight (V (b 1) p)

theorem Lmap_apply (b : ℕ → ℝ → E3 → C3) (p h : E3 × ℝ) :
    Lmap b p h = ∑ j, h.1 j • V (mulC (cj j) b 0) p + h.2 • V (b 1) p := by
  simp [Lmap, projX, projT, ContinuousLinearMap.smulRight_apply]

/-- **A derivada de `V` em `ℝ³ × [0, T]`**: `∂_{x_j} V = V[2πiξ_j b]`, `∂_t V = V[b 1]`. -/
theorem Amp.hasFDerivWithinAt_V {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) {p : E3 × ℝ}
    (hp : p ∈ univ ×ˢ Icc 0 T) :
    HasFDerivWithinAt (V (b 0)) (Lmap b p) (univ ×ˢ Icc 0 T) p := by
  obtain ⟨C0, hC00, hC0⟩ := hb.bound 0 6
  obtain ⟨C1, hC10, hC1⟩ := hb.bound 1 5
  obtain ⟨C2, hC20, hC2⟩ := hb.bound 2 4
  set K := 12 * π ^ 2 * C0 + 2 * π * C1 + C2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hbnd : ∀ q ∈ univ ×ˢ Icc 0 T,
      ‖V (b 0) q - V (b 0) p - Lmap b p (q - p)‖ ≤ K * I4 * ‖q - p‖ ^ 2 := by
    intro q hq
    obtain ⟨x, t⟩ := p
    obtain ⟨y, r⟩ := q
    have ht : t ∈ Icc 0 T := hp.2
    have hr : r ∈ Icc 0 T := hq.2
    set δ := y - x with hδ
    set τ := r - t with hτ
    have hδn : ‖δ‖ ≤ ‖(y, r) - (x, t)‖ := by
      rw [Prod.mk_sub_mk]; exact norm_fst_le (y - x, r - t)
    have hτn : |τ| ≤ ‖(y, r) - (x, t)‖ := by
      rw [Prod.mk_sub_mk, ← Real.norm_eq_abs]; exact norm_snd_le (y - x, r - t)
    -- os integrandos
    have i1 := hb.integrable 0 hr y
    have i2 := hb.integrable 0 ht x
    have i3 : ∀ j, Integrable fun ξ => ex x ξ • mulC (cj j) b 0 t ξ :=
      fun j => (hb.mulcj j).integrable 0 ht x
    have i4 := hb.integrable 1 ht x
    have i3' : ∀ j, Integrable fun ξ => δ j • (ex x ξ • mulC (cj j) b 0 t ξ) :=
      fun j => (i3 j).smul (δ j)
    have i4' : Integrable fun ξ => τ • (ex x ξ • b 1 t ξ) := i4.smul τ
    have i5 : Integrable fun ξ => ∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) :=
      integrable_finset_sum _ fun j _ => i3' j
    have i6 : Integrable fun ξ =>
        ∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) + τ • (ex x ξ • b 1 t ξ) := i5.add i4'
    have i12 : Integrable fun ξ => ex y ξ • b 0 r ξ - ex x ξ • b 0 t ξ := i1.sub i2
    have hL : Lmap b (x, t) ((y, r) - (x, t)) =
        ∫ ξ, (∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) + τ • (ex x ξ • b 1 t ξ)) := by
      rw [integral_add i5 i4', integral_finset_sum _ fun j _ => i3' j, Lmap_apply]
      simp only [integral_smul, Prod.mk_sub_mk, V, Vf]
      rfl
    have hR : V (b 0) (y, r) - V (b 0) (x, t) - Lmap b (x, t) ((y, r) - (x, t)) =
        ∫ ξ, (ex y ξ • b 0 r ξ - ex x ξ • b 0 t ξ -
          (∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) + τ • (ex x ξ • b 1 t ξ))) := by
      rw [hL, integral_sub i12 i6, integral_sub i1 i2]
      rfl
    rw [hR]
    have hpt : ∀ ξ, ‖ex y ξ • b 0 r ξ - ex x ξ • b 0 t ξ -
        (∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) + τ • (ex x ξ • b 1 t ξ))‖ ≤
        K * ‖(y, r) - (x, t)‖ ^ 2 * (w 4 ξ)⁻¹ := by
      intro ξ
      set D : ℂ := ((2 * π * inner ℝ ξ δ : ℝ) : ℂ) * Complex.I with hD
      have hsum : ∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) = D • (ex x ξ • b 0 t ξ) := by
        rw [hD, ← sum_cj_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [mulC]
        rw [smul_comm (ex x ξ) (cj j ξ)]
      have hy : y = x + δ := by rw [hδ]; abel
      have e : ex y ξ • b 0 r ξ - ex x ξ • b 0 t ξ -
          (∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) + τ • (ex x ξ • b 1 t ξ)) =
          ex x ξ • ((ex δ ξ - 1 - D) • b 0 r ξ + D • (b 0 r ξ - b 0 t ξ) +
            (b 0 r ξ - b 0 t ξ - τ • b 1 t ξ)) := by
        rw [hsum, hy, ex_add, mul_smul]
        simp only [smul_add, smul_sub, sub_smul, one_smul, smul_comm (ex x ξ) τ,
          smul_comm (ex x ξ) D]
        abel
      rw [e, norm_smul, norm_ex, one_mul]
      have n1 : ‖(ex δ ξ - 1 - D) • b 0 r ξ‖ ≤
          12 * π ^ 2 * (‖δ‖ ^ 2 * ‖ξ‖ ^ 2) * (C0 * (w 6 ξ)⁻¹) := by
        rw [norm_smul]
        exact mul_le_mul (norm_ex_sub_le δ ξ) (hC0 r hr ξ) (norm_nonneg _) (by positivity)
      have n2 : ‖D • (b 0 r ξ - b 0 t ξ)‖ ≤
          (2 * π * (‖δ‖ * ‖ξ‖)) * (|τ| * (C1 * (w 5 ξ)⁻¹)) := by
        rw [norm_smul]
        refine mul_le_mul ?_ (hb.norm_sub_le 0 hC1 ξ ht hr) (norm_nonneg _) (by positivity)
        rw [hD, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        exact mul_le_mul_of_nonneg_left (abs_inner_le ξ δ |>.trans_eq (mul_comm _ _))
          (by positivity)
      have n3 : ‖b 0 r ξ - b 0 t ξ - τ • b 1 t ξ‖ ≤ |τ| ^ 2 * (C2 * (w 4 ξ)⁻¹) :=
        hb.norm_sub_sub_le 0 hC20 hC2 ξ ht hr
      -- pesos
      have hw6 : ‖ξ‖ ^ 2 * (w 6 ξ)⁻¹ ≤ (w 4 ξ)⁻¹ := by
        have h := norm_sq_le_w2 ξ
        have e6 : w 6 ξ = w 4 ξ * w 2 ξ := w_add 4 2 ξ
        rw [e6, mul_inv]
        have := inv_pos.mpr (w_pos 4 ξ)
        have h2 : ‖ξ‖ ^ 2 * (w 2 ξ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (w_pos 2 ξ)]; exact h
        nlinarith [inv_pos.mpr (w_pos 2 ξ), sq_nonneg ‖ξ‖]
      have hw5 : ‖ξ‖ * (w 5 ξ)⁻¹ ≤ (w 4 ξ)⁻¹ := by
        have h := norm_le_w1 ξ
        have e5 : w 5 ξ = w 4 ξ * w 1 ξ := w_add 4 1 ξ
        rw [e5, mul_inv]
        have h2 : ‖ξ‖ * (w 1 ξ)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (w_pos 1 ξ)]; exact h
        have := inv_pos.mpr (w_pos 4 ξ)
        nlinarith [inv_pos.mpr (w_pos 1 ξ), norm_nonneg ξ]
      set N := ‖(y, r) - (x, t)‖
      have hδ2 : ‖δ‖ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hδn 2
      have hτ2 : |τ| ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hτn 2
      have hδτ : ‖δ‖ * |τ| ≤ N ^ 2 := by
        rw [sq]; exact mul_le_mul hδn hτn (abs_nonneg _) ((norm_nonneg _).trans hδn)
      have w4 := inv_pos.mpr (w_pos 4 ξ)
      have w5 := inv_pos.mpr (w_pos 5 ξ)
      have w6 := inv_pos.mpr (w_pos 6 ξ)
      have m1 : 12 * π ^ 2 * (‖δ‖ ^ 2 * ‖ξ‖ ^ 2) * (C0 * (w 6 ξ)⁻¹) ≤
          12 * π ^ 2 * C0 * N ^ 2 * (w 4 ξ)⁻¹ := by
        have : ‖δ‖ ^ 2 * (‖ξ‖ ^ 2 * (w 6 ξ)⁻¹) ≤ N ^ 2 * (w 4 ξ)⁻¹ :=
          mul_le_mul hδ2 hw6 (by positivity) (by positivity)
        have hc : 0 ≤ 12 * π ^ 2 * C0 := by positivity
        calc 12 * π ^ 2 * (‖δ‖ ^ 2 * ‖ξ‖ ^ 2) * (C0 * (w 6 ξ)⁻¹)
            = 12 * π ^ 2 * C0 * (‖δ‖ ^ 2 * (‖ξ‖ ^ 2 * (w 6 ξ)⁻¹)) := by ring
          _ ≤ 12 * π ^ 2 * C0 * (N ^ 2 * (w 4 ξ)⁻¹) := mul_le_mul_of_nonneg_left this hc
          _ = _ := by ring
      have m2 : (2 * π * (‖δ‖ * ‖ξ‖)) * (|τ| * (C1 * (w 5 ξ)⁻¹)) ≤
          2 * π * C1 * N ^ 2 * (w 4 ξ)⁻¹ := by
        have : (‖δ‖ * |τ|) * (‖ξ‖ * (w 5 ξ)⁻¹) ≤ N ^ 2 * (w 4 ξ)⁻¹ :=
          mul_le_mul hδτ hw5 (by positivity) (by positivity)
        have hc : 0 ≤ 2 * π * C1 := by positivity
        calc (2 * π * (‖δ‖ * ‖ξ‖)) * (|τ| * (C1 * (w 5 ξ)⁻¹))
            = 2 * π * C1 * ((‖δ‖ * |τ|) * (‖ξ‖ * (w 5 ξ)⁻¹)) := by ring
          _ ≤ 2 * π * C1 * (N ^ 2 * (w 4 ξ)⁻¹) := mul_le_mul_of_nonneg_left this hc
          _ = _ := by ring
      have m3 : |τ| ^ 2 * (C2 * (w 4 ξ)⁻¹) ≤ C2 * N ^ 2 * (w 4 ξ)⁻¹ := by
        calc |τ| ^ 2 * (C2 * (w 4 ξ)⁻¹) = C2 * (|τ| ^ 2 * (w 4 ξ)⁻¹) := by ring
          _ ≤ C2 * (N ^ 2 * (w 4 ξ)⁻¹) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hτ2 w4.le) hC20
          _ = _ := by ring
      calc ‖(ex δ ξ - 1 - D) • b 0 r ξ + D • (b 0 r ξ - b 0 t ξ) +
            (b 0 r ξ - b 0 t ξ - τ • b 1 t ξ)‖
          ≤ ‖(ex δ ξ - 1 - D) • b 0 r ξ‖ + ‖D • (b 0 r ξ - b 0 t ξ)‖ +
            ‖b 0 r ξ - b 0 t ξ - τ • b 1 t ξ‖ := norm_add₃_le
        _ ≤ 12 * π ^ 2 * C0 * N ^ 2 * (w 4 ξ)⁻¹ + 2 * π * C1 * N ^ 2 * (w 4 ξ)⁻¹ +
            C2 * N ^ 2 * (w 4 ξ)⁻¹ :=
            add_le_add (add_le_add (n1.trans m1) (n2.trans m2)) (n3.trans m3)
        _ = K * N ^ 2 * (w 4 ξ)⁻¹ := by rw [hK]; ring
    calc ‖∫ ξ, (ex y ξ • b 0 r ξ - ex x ξ • b 0 t ξ -
          (∑ j, δ j • (ex x ξ • mulC (cj j) b 0 t ξ) + τ • (ex x ξ • b 1 t ξ)))‖
        ≤ ∫ ξ, K * ‖(y, r) - (x, t)‖ ^ 2 * (w 4 ξ)⁻¹ :=
          norm_integral_le_of_norm_le (integrable_w_inv.const_mul _) (Eventually.of_forall hpt)
      _ = K * I4 * ‖(y, r) - (x, t)‖ ^ 2 := by
          rw [integral_const_mul, I4]; ring
  refine HasFDerivWithinAt.of_isLittleO ?_
  have hO : (fun q => V (b 0) q - V (b 0) p - Lmap b p (q - p)) =O[𝓝[univ ×ˢ Icc 0 T] p]
      (fun q => ‖q - p‖ ^ 2) := by
    refine IsBigO.of_bound (K * I4) ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbnd q hq
  exact hO.trans_isLittleO ((isLittleO_pow_sub_sub p one_lt_two).mono nhdsWithin_le_nhds)

theorem uniqueDiffOn_faixa {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ ((univ : Set E3) ×ˢ Icc (0 : ℝ) T) :=
  (uniqueDiffOn_univ (𝕜 := ℝ) (E := E3)).prod (uniqueDiffOn_Icc hT)

/-- **`V` é `C^∞` em `ℝ³ × [0, T]`.** -/
theorem contDiffOn_V {T : ℝ} (hT : 0 < T) :
    ∀ n : ℕ, ∀ b : ℕ → ℝ → E3 → C3, Amp T b → ContDiffOn ℝ n (V (b 0)) (univ ×ˢ Icc 0 T) := by
  intro n
  induction n with
  | zero =>
    intro b hb
    exact contDiffOn_zero.mpr (hb.continuousOn_V 0)
  | succ n ih =>
    intro b hb
    have hs := uniqueDiffOn_faixa hT
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderivWithin hs]
    refine ⟨fun p hp => (hb.hasFDerivWithinAt_V hp).differentiableWithinAt, by simp, ?_⟩
    have hEq : EqOn (fderivWithin ℝ (V (b 0)) (univ ×ˢ Icc 0 T)) (Lmap b)
        (univ ×ˢ Icc 0 T) := fun p hp => (hb.hasFDerivWithinAt_V hp).fderivWithin (hs p hp)
    refine ContDiffOn.congr ?_ hEq
    unfold Lmap
    refine ContDiffOn.add (ContDiffOn.sum fun j _ => ?_) ?_
    · have h := ih (mulC (cj j) b) (hb.mulcj j)
      exact ((ContinuousLinearMap.smulRightL ℝ (E3 × ℝ) C3 (projX j)).contDiff.comp_contDiffOn h)
    · have h := ih (desloc b) hb.shift
      exact ((ContinuousLinearMap.smulRightL ℝ (E3 × ℝ) C3 projT).contDiff.comp_contDiffOn h)

/-- **`V` é `C^∞` em `ℝ³ × [0, T]`** (`ContDiffOn ∞`). -/
theorem Amp.contDiffOn_V_infty {T : ℝ} (hT : 0 < T) {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) :
    ContDiffOn ℝ ∞ (V (b 0)) (univ ×ˢ Icc 0 T) :=
  contDiffOn_infty.mpr fun n => contDiffOn_V hT n b hb

end ATK.NSSuave

#print axioms ATK.NSSuave.norm_ex
#print axioms ATK.NSSuave.continuous_ex
#print axioms ATK.NSSuave.continuous_ex_right
#print axioms ATK.NSSuave.ex_add
#print axioms ATK.NSSuave.norm_exp_I_sub_one_le
#print axioms ATK.NSSuave.norm_exp_I_sub_le
#print axioms ATK.NSSuave.abs_inner_le
#print axioms ATK.NSSuave.norm_ex_sub_one_le
#print axioms ATK.NSSuave.norm_ex_sub_le
#print axioms ATK.NSSuave.w_inv_anti
#print axioms ATK.NSSuave.w_add
#print axioms ATK.NSSuave.norm_le_w1
#print axioms ATK.NSSuave.norm_sq_le_w2
#print axioms ATK.NSSuave.Amp.shift
#print axioms ATK.NSSuave.Amp.mulc
#print axioms ATK.NSSuave.Amp.bound_le
#print axioms ATK.NSSuave.Amp.intervalIntegrable
#print axioms ATK.NSSuave.Amp.sub_eq
#print axioms ATK.NSSuave.mem_Icc_of_uIoc
#print axioms ATK.NSSuave.abs_sub_le_of_uIoc
#print axioms ATK.NSSuave.Amp.norm_sub_le
#print axioms ATK.NSSuave.Amp.norm_sub_sub_le
#print axioms ATK.NSSuave.integrable_ex_smul
#print axioms ATK.NSSuave.Amp.integrable
#print axioms ATK.NSSuave.Amp.continuousOn_V
#print axioms ATK.NSSuave.norm_cj_le
#print axioms ATK.NSSuave.continuous_cj
#print axioms ATK.NSSuave.Amp.mulcj
#print axioms ATK.NSSuave.sum_cj_smul
#print axioms ATK.NSSuave.Lmap_apply
#print axioms ATK.NSSuave.Amp.hasFDerivWithinAt_V
#print axioms ATK.NSSuave.uniqueDiffOn_faixa
#print axioms ATK.NSSuave.contDiffOn_V
#print axioms ATK.NSSuave.Amp.contDiffOn_V_infty
