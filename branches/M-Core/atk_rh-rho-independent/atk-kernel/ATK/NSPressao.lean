import ATK.NSTempo
import ATK.NSFisico

/-!
# ATK — Navier–Stokes: a pressão no lado de Fourier

Camada 6 do ataque a B3. Com `N = Nl(a, a)` (a transformada de `div(u ⊗ u)`), a pressão tem
transformada `p̂ = (i/2π) ⟪ξ, N⟫/‖ξ‖²` — limitada, embora descontínua em `ξ = 0`, porque
`‖N(ξ)‖ ≤ ‖ξ‖ · C w_m(ξ)⁻¹`. Aqui:

* `norm_Nl_le_norm`, `norm_Nk_le`: as cotas com o fator `‖ξ‖`;
* `Nk_integral`: `N_k t = N_k 0 + ∫₀ᵗ N_{k+1}` (Leibniz + regra do produto);
* `pk`, `amp_pk`: a sequência de derivadas temporais da pressão é uma amplitude suave
  (na primeira componente de `ℂ³`);
* **`identidade_amp`**: a identidade pontual em `ξ` que, transformada de volta, é a equação de
  Navier–Stokes: `a₁ + N − ν Σ_j (2πiξ_j)² a + Σ_j (2πiξ_j p̂) e_j = 0`.

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace ATK.NSPressao

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard ATK.NSSuave ATK.NSTempo

/-! ### Cotas com o fator `‖ξ‖` -/

theorem norm_Nl_le_norm {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) (m : ℕ)
    {A A' B B' : ℝ} (hA : ∀ η, ‖f η‖ ≤ A * (w 4 η)⁻¹) (hA' : ∀ η, ‖f η‖ ≤ A' * (w m η)⁻¹)
    (hB : ∀ η, ‖g η‖ ≤ B * (w 4 η)⁻¹) (hB' : ∀ η, ‖g η‖ ≤ B' * (w m η)⁻¹) (ξ : E3) :
    ‖Nl f g ξ‖ ≤ ‖ξ‖ * ((2 * π * (2 ^ m * I4 * (A' * B + A * B'))) * (w m ξ)⁻¹) := by
  have hB1 : ∀ η, ‖g η‖ ≤ B := fun η => (hB η).trans (by
    have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hB 0))
      (inv_pos.mpr (w_pos 4 0))
    exact mul_le_of_le_one_right hB0 (inv_le_one_of_one_le₀ (one_le_w 4 η)))
  have hint := integrable_convN hf hg hA hB1 ξ
  have hc := convN_peso m hf hg hA hA' hB hB' ξ
  have hw := w_pos m ξ
  have hcm : convN f g ξ ≤ (2 ^ m * I4 * (A' * B + A * B')) * (w m ξ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hw, mul_comm]; exact hc
  refine (norm_Nl_le ξ hint).trans ?_
  calc 2 * π * ‖ξ‖ * convN f g ξ = ‖ξ‖ * (2 * π * convN f g ξ) := by ring
    _ ≤ ‖ξ‖ * (2 * π * ((2 ^ m * I4 * (A' * B + A * B')) * (w m ξ)⁻¹)) := by gcongr
    _ = _ := by ring

theorem nl_norm_bound {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ξ, ‖Nl (f t) (g t) ξ‖ ≤ ‖ξ‖ * (C * (w m ξ)⁻¹) := by
  obtain ⟨A, hA0, hA⟩ := hf.bound_le (max 4 m)
  obtain ⟨B, hB0, hB⟩ := hg.bound_le (max 4 m)
  refine ⟨2 * π * (2 ^ m * I4 * (A * B + A * B)), by have := I4_nonneg; positivity,
    fun t ξ => ?_⟩
  exact norm_Nl_le_norm (hf.cont_s t) (hg.cont_s t) m (fun η => hA t η 4 (le_max_left _ _))
    (fun η => hA t η m (le_max_right _ _)) (fun η => hB t η 4 (le_max_left _ _))
    (fun η => hB t η m (le_max_right _ _)) ξ

theorem norm_Nk_le {ν : ℝ} {a : ℝ → E3 → C3} (ha : BoaW a) (k m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ξ, ‖Nk (ader ν a) k t ξ‖ ≤ ‖ξ‖ * (C * (w m ξ)⁻¹) := by
  have hb := boaW_ader (ν := ν) ha
  have hC : ∀ i ∈ range (k + 1), ∃ C, 0 ≤ C ∧ ∀ t ξ,
      ‖(k.choose i) • Nl (ader ν a i t) (ader ν a (k - i) t) ξ‖ ≤ ‖ξ‖ * (C * (w m ξ)⁻¹) := by
    intro i _
    obtain ⟨C, hC0, hC⟩ := nl_norm_bound (hb i) (hb (k - i)) m
    refine ⟨k.choose i * C, by positivity, fun t ξ => ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
    calc (k.choose i : ℝ) * ‖Nl (ader ν a i t) (ader ν a (k - i) t) ξ‖
        ≤ (k.choose i : ℝ) * (‖ξ‖ * (C * (w m ξ)⁻¹)) :=
          mul_le_mul_of_nonneg_left (hC t ξ) (Nat.cast_nonneg _)
      _ = ‖ξ‖ * ((k.choose i * C) * (w m ξ)⁻¹) := by ring
  choose! C hC0 hCb using hC
  refine ⟨∑ i ∈ range (k + 1), C i, sum_nonneg hC0, fun t ξ => ?_⟩
  unfold Nk
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ range (k + 1), ‖(k.choose i) • Nl (ader ν a i t) (ader ν a (k - i) t) ξ‖
      ≤ ∑ i ∈ range (k + 1), ‖ξ‖ * (C i * (w m ξ)⁻¹) := sum_le_sum fun i hi => hCb i hi t ξ
    _ = ‖ξ‖ * ((∑ i ∈ range (k + 1), C i) * (w m ξ)⁻¹) := by
        rw [← mul_sum, sum_mul]

/-! ### A forma integral de `N_k` -/

theorem Nk_integral {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3} (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (k : ℕ) (ξ : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Nk (ader ν a) k t ξ = Nk (ader ν a) k 0 ξ + ∫ s in (0 : ℝ)..t, Nk (ader ν a) (k + 1) s ξ := by
  have hb := boaW_ader (ν := ν) ha
  have hd := ader_integral ha hmild
  have hterm : ∀ i ∈ range (k + 1),
      Nl (ader ν a i t) (ader ν a (k - i) t) ξ - Nl (ader ν a i 0) (ader ν a (k - i) 0) ξ =
      ∫ s in (0 : ℝ)..t, (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
        Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ) := by
    intro i hi
    have hi' : i < k + 1 := mem_range.mp hi
    have e : k + 1 - i = k - i + 1 := by omega
    rw [e]
    have := Nl_integral (T := T) (hb i) (hb (i + 1)) (hb (k - i)) (hb (k - i + 1))
      (fun η t ht => hd i η t ht) (fun η t ht => hd (k - i) η t ht) ξ ht
    rw [this]; abel
  have hint : ∀ i ∈ range (k + 1), IntervalIntegrable (fun s =>
      (k.choose i : ℂ) • (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
        Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ)) volume 0 t := by
    intro i _
    have hc : Continuous fun s => (k.choose i : ℂ) •
        (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
          Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ) :=
      ((((hb (i + 1)).nl (hb (k - i))).cont_t ξ).add
        (((hb i).nl (hb (k + 1 - i))).cont_t ξ)).const_smul (k.choose i : ℂ)
    exact hc.intervalIntegrable 0 t
  have eN : ∀ s, Nk (ader ν a) (k + 1) s ξ = ∑ i ∈ range (k + 1), (k.choose i : ℂ) •
      (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
        Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ) := by
    intro s
    rw [Nk_succ]
    simp only [nsmul_eq_cast_smul]
  simp only [eN]
  rw [intervalIntegral.integral_finsetSum hint]
  have : Nk (ader ν a) k t ξ - Nk (ader ν a) k 0 ξ = ∑ i ∈ range (k + 1), (k.choose i : ℂ) •
      ∫ s in (0 : ℝ)..t, (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
        Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ) := by
    rw [Nk, Nk, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [← hterm i hi, nsmul_eq_cast_smul, nsmul_eq_cast_smul, smul_sub]
  simp only [intervalIntegral.integral_smul]
  rw [← this]
  abel

/-! ### A amplitude da pressão -/

/-- `e₀ = (1, 0, 0)`. -/
noncomputable def e0 : C3 := EuclideanSpace.single 0 1

theorem norm_e0 : ‖e0‖ = 1 := by simp [e0]

/-- `q_ξ(v) = (i/2π) ⟪ξ, v⟫/‖ξ‖²`. -/
noncomputable def qx (ξ : E3) (v : C3) : ℂ :=
  Complex.I / ((2 * π : ℝ) : ℂ) * inner ℂ (cpx ξ) v / ((‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem norm_qx_le (ξ : E3) (v : C3) {C : ℝ} (hC0 : 0 ≤ C) (hv : ‖v‖ ≤ ‖ξ‖ * C) :
    ‖qx ξ v‖ ≤ C / (2 * π) := by
  rcases eq_or_ne ξ 0 with h0 | h0
  · subst h0
    simp only [qx, cpx_zero, inner_zero_left, mul_zero, zero_div, norm_zero]
    positivity
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr h0
    unfold qx
    rw [norm_div, norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hi := norm_inner_cpx_le ξ v
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 / (2 * π) * ‖inner ℂ (cpx ξ) v‖ * (2 * π)
        = ‖inner ℂ (cpx ξ) v‖ := by field_simp
      _ ≤ ‖ξ‖ * ‖v‖ := hi
      _ ≤ ‖ξ‖ * (‖ξ‖ * C) := mul_le_mul_of_nonneg_left hv hn.le
      _ = C * ‖ξ‖ ^ 2 := by ring

/-- As derivadas temporais da amplitude da pressão. -/
noncomputable def pk (ν : ℝ) (a : ℝ → E3 → C3) (k : ℕ) (t : ℝ) (ξ : E3) : C3 :=
  qx ξ (Nk (ader ν a) k t ξ) • e0

theorem measurable_qx_div : Measurable fun ξ : E3 => (((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
  have : Continuous fun ξ : E3 => (((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by fun_prop
  exact this.measurable.inv

theorem qx_eq (ξ : E3) (v : C3) : qx ξ v =
    (Complex.I / ((2 * π : ℝ) : ℂ)) * inner ℂ (cpx ξ) v * (((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
  unfold qx; rw [div_eq_mul_inv]

theorem qx_add (ξ : E3) (u v : C3) : qx ξ (u + v) = qx ξ u + qx ξ v := by
  simp only [qx, inner_add_right]; ring

theorem qx_integral (ξ : E3) {g : ℝ → C3} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    qx ξ (∫ s in a..b, g s) = ∫ s in a..b, qx ξ (g s) := by
  simp only [qx_eq]
  have hcomm := (innerSL ℂ (cpx ξ)).intervalIntegral_comp_comm hg
  simp only [innerSL_apply_apply] at hcomm
  rw [← hcomm, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]

/-- **A pressão é uma amplitude suave.** -/
theorem amp_pk {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3} (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ) :
    Amp T (pk ν a) where
  meas k t := by
    have hN : Continuous fun ξ => Nk (ader ν a) k t ξ := by
      unfold Nk
      exact continuous_finsetSum _ fun i _ =>
        (((boaW_ader ha i).nl (boaW_ader ha (k - i))).cont_s t).const_smul _
    have h1 : Measurable fun ξ => qx ξ (Nk (ader ν a) k t ξ) := by
      simp only [qx_eq]
      have hi : Continuous fun ξ => inner ℂ (cpx ξ) (Nk (ader ν a) k t ξ) :=
        Continuous.inner (𝕜 := ℂ) continuous_cpx hN
      exact (measurable_const.mul hi.measurable).mul measurable_qx_div
    exact (h1.smul_const e0).aestronglyMeasurable
  cont k ξ := by
    have hN : Continuous fun t => Nk (ader ν a) k t ξ := by
      unfold Nk
      exact continuous_finsetSum _ fun i _ =>
        (((boaW_ader ha i).nl (boaW_ader ha (k - i))).cont_t ξ).const_smul _
    have : Continuous fun t => pk ν a k t ξ := by
      unfold pk
      simp only [qx_eq]
      exact ((continuous_const.mul (Continuous.inner (𝕜 := ℂ) continuous_const hN)).mul
        continuous_const).smul continuous_const
    exact this.continuousOn
  bound k m := by
    obtain ⟨C, hC0, hC⟩ := norm_Nk_le (ν := ν) ha k m
    refine ⟨C / (2 * π), by positivity, fun t _ ξ => ?_⟩
    unfold pk
    rw [norm_smul, norm_e0, mul_one]
    have := norm_qx_le ξ _ (by have := w_pos m ξ; positivity) (hC t ξ)
    calc ‖qx ξ (Nk (ader ν a) k t ξ)‖ ≤ C * (w m ξ)⁻¹ / (2 * π) := this
      _ = C / (2 * π) * (w m ξ)⁻¹ := by ring
  deriv k ξ t ht := by
    unfold pk
    have hNc : Continuous fun s => Nk (ader ν a) (k + 1) s ξ := by
      unfold Nk
      exact continuous_finsetSum _ fun i _ =>
        (((boaW_ader ha i).nl (boaW_ader ha (k + 1 - i))).cont_t ξ).const_smul _
    rw [Nk_integral ha hmild k ξ ht, qx_add, qx_integral ξ (hNc.intervalIntegrable 0 t),
      add_smul, intervalIntegral.integral_smul_const]

/-! ### A identidade de Navier–Stokes no lado de Fourier -/

theorem sum_cj_cj (ξ : E3) (v : C3) :
    ∑ j, cj j ξ • (cj j ξ • v) = -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • v := by
  simp only [smul_smul, ← Finset.sum_smul]
  congr 1
  have hn : ‖ξ‖ ^ 2 = ∑ j, ξ j ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hn]
  simp only [cj, Fin.sum_univ_three]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem sum_cj_cpx (ξ : E3) : ∑ j, cj j ξ • cpx (e j) = ((2 * π : ℝ) * Complex.I : ℂ) • cpx ξ := by
  ext k
  simp only [cj, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply, cpx_apply, e,
    PiLp.single_apply]
  fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

/-- **A identidade de Navier–Stokes no lado de Fourier**, pontual em `ξ`:
`a₁ + N − ν Σ_j (2πiξ_j)² a + Σ_j (2πiξ_j p̂) e_j = 0`, com `a₁ = −κa − P N`. -/
theorem identidade_amp (ν : ℝ) (a : ℝ → E3 → C3) (t : ℝ) (ξ : E3) :
    ader ν a 1 t ξ + Nl (a t) (a t) ξ - (ν : ℂ) • ∑ j, cj j ξ • (cj j ξ • a t ξ) +
      ∑ j, (cj j ξ • pk ν a 0 t ξ) 0 • cpx (e j) = 0 := by
  have h1 : ader ν a 1 t ξ = -((kappa ν ξ : ℝ) : ℂ) • a t ξ - lp ξ (Nl (a t) (a t) ξ) := by
    rw [ader_succ, ader_zero, Nk_zero, ader_zero]
  have h2 : ∑ j, (cj j ξ • pk ν a 0 t ξ) 0 • cpx (e j) =
      qx ξ (Nl (a t) (a t) ξ) • (((2 * π : ℝ) * Complex.I : ℂ) • cpx ξ) := by
    rw [← sum_cj_cpx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pk, Nk_zero, ader_zero, PiLp.smul_apply, e0, PiLp.single_apply, smul_eq_mul,
      if_pos rfl, mul_one, smul_smul, ite_true]
    ring_nf
  rw [h1, h2, sum_cj_cj]
  set N := Nl (a t) (a t) ξ with hN
  set v := a t ξ with hv
  have hc2 : qx ξ N * ((2 * π : ℝ) * Complex.I : ℂ) =
      -(inner ℂ (cpx ξ) N / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
    have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    calc qx ξ N * ((2 * π : ℝ) * Complex.I : ℂ)
        = (Complex.I * Complex.I) * (((2 * π : ℝ) : ℂ) / ((2 * π : ℝ) : ℂ)) *
          (inner ℂ (cpx ξ) N / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by unfold qx; ring
      _ = -(inner ℂ (cpx ξ) N / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
          rw [Complex.I_mul_I, div_self hπ]; ring
  rw [smul_smul (qx ξ N), hc2]
  unfold lp kappa
  push_cast
  module

end ATK.NSPressao

#print axioms ATK.NSPressao.norm_Nl_le_norm
#print axioms ATK.NSPressao.nl_norm_bound
#print axioms ATK.NSPressao.norm_Nk_le
#print axioms ATK.NSPressao.Nk_integral
#print axioms ATK.NSPressao.norm_e0
#print axioms ATK.NSPressao.norm_qx_le
#print axioms ATK.NSPressao.measurable_qx_div
#print axioms ATK.NSPressao.qx_eq
#print axioms ATK.NSPressao.qx_add
#print axioms ATK.NSPressao.qx_integral
#print axioms ATK.NSPressao.amp_pk
#print axioms ATK.NSPressao.sum_cj_cj
#print axioms ATK.NSPressao.sum_cj_cpx
#print axioms ATK.NSPressao.identidade_amp
