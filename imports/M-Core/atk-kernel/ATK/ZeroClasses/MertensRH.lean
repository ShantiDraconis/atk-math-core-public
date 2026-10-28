import ATK.ZeroClasses.LittlewoodMu
import ATK.BaezDuarteBridge
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex

/-!
# O critério de Littlewood para a função de Mertens: `RH ⟺ M(x) = O(x^{1/2 + ε})` (rodada 51)

`M(N) = Σ_{n ≤ N} μ(n)` (`M`). **Teorema** (Littlewood, 1912; Titchmarsh §14.25):

  `RH ⟺ ∀ ε > 0, ∃ C, ∀ N, |M(N)| ≤ C (N + 1)^{1/2 + ε}`   (`rh_iff_mertens`).

* `abel`: somação por partes finita;
* **`mertens_of_RH`** (⇒): sob RH, `Σ_{n ≤ N} μ(n) n^{−w}` converge em `w = ½ + ε` (o teorema de Littlewood da
  rodada 46, `ATK.ZeroClasses.LittlewoodMu.littlewood`), logo é limitada por `B`; por partes,
  `|M(N)| ≤ 2B N^{1/2 + ε}`;
* **`RH_of_mertens`** (⇐): com `|M(N)| ≤ C(N + 1)^θ`, a série
  `G(z) = Σ_{n ≥ 0} M(n + 1)((n + 1)^{−z} − (n + 2)^{−z})` converge normalmente em compactos de `Re z > θ`
  (`norm_cpow_sub_le`, `summable_bound`) e é holomorfa lá (`differentiableAt_G`); em `Re z > 1`, `G = Σ μ(n)n^{−z} =
  1/ζ` (`G_eq_LSeries`, por partes). Pelo princípio da identidade, `ζ₁(z)G(z) = z − 1` em `Re z > θ`, logo `ζ` não se
  anula lá (`ζ₁(z) = (z − 1)ζ(z)`). Como `θ = ½ + ε` com `ε` arbitrário, vale RH.

Classificação (rodada 51): **reformulação** de RH (critério clássico, as duas direções). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.Mertens

open ATK.ZeroClasses.LittlewoodMu (mu norm_mu_le LSeries_mu littlewood)
open ATK.RHLogZeta (F F_eq zeta₁_eq)

/-- A função de Mertens `M(N) = Σ_{n ≤ N} μ(n)`. -/
noncomputable def M (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℝ)

/-- `M(N) = O(N^{1/2 + ε})` para todo `ε > 0`. -/
def MertensFraco : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + ε)

/-! ## 1. Somação por partes -/

/-- **Somação por partes finita**: `Σ_{n ≤ N} aₙbₙ = A_N b_N − Σ_{n < N} Aₙ(b_{n+1} − bₙ)`. -/
theorem abel (a b : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), a n * b n =
      (∑ n ∈ Finset.range (N + 1), a n) * b N -
        ∑ n ∈ Finset.range N, (∑ k ∈ Finset.range (n + 1), a k) * (b (n + 1) - b n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (fun n => a n * b n), ih,
      Finset.sum_range_succ (fun n => (∑ k ∈ Finset.range (n + 1), a k) * (b (n + 1) - b n)),
      Finset.sum_range_succ a (N + 1)]
    ring

theorem mu_eq_term_mul (w : ℝ) (n : ℕ) :
    mu n = LSeries.term mu (w : ℂ) n * (((n : ℝ) ^ w : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mu]
  · rw [LSeries.term_of_ne_zero hn.ne', ofReal_cpow (Nat.cast_nonneg n)]
    have h : ((n : ℝ) : ℂ) ^ (w : ℂ) ≠ 0 := by
      rw [← ofReal_cpow (Nat.cast_nonneg n)]
      exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hn) w).ne'
    push_cast at h ⊢
    field_simp

/-! ## 2. RH ⟹ `M(N) = O(N^{1/2 + ε})` -/

/-- **RH ⟹ `M(N) = O(N^{1/2 + ε})`** (Littlewood). -/
theorem mertens_of_RH (hRH : RiemannHypothesis) : MertensFraco := by
  suffices h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + ε) by
    intro ε hε
    rcases le_or_gt ε 1 with h1 | h1
    · exact h ε hε h1
    · obtain ⟨C, hC⟩ := h 1 one_pos le_rfl
      have hC0 : 0 ≤ C := by
        have := hC 0
        simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
        exact le_trans (abs_nonneg _) this
      refine ⟨C, fun N => (hC N).trans ?_⟩
      have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hC0
  intro ε hε hε1
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / 2 + ε := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; linarith
  have hlim := littlewood hRH (w := (w : ℂ)) (by rw [ofReal_re, hw]; linarith)
    (by rw [ofReal_re, hw]; linarith)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (isBounded_range_of_tendsto _ hlim)
  have hB' : ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term mu (w : ℂ) n‖ ≤ B :=
    fun N => hB _ ⟨N, rfl⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB' 0)
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℂ, b = fun n : ℕ => (((n : ℝ) ^ w : ℝ) : ℂ) := ⟨_, rfl⟩
  refine ⟨2 * B, fun N => ?_⟩
  have hab := abel (fun n => LSeries.term mu (w : ℂ) n) b N
  have hM : ((M N : ℝ) : ℂ) = ∑ n ∈ Finset.range (N + 1), LSeries.term mu (w : ℂ) n * b n := by
    unfold M
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hb]
    exact mu_eq_term_mul w n
  rw [hab] at hM
  have hmono : ∀ n : ℕ, (n : ℝ) ^ w ≤ ((n : ℝ) + 1) ^ w := fun n =>
    Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) hw0.le
  have hbsub : ∀ n : ℕ, ‖b (n + 1) - b n‖ = ((n : ℝ) + 1) ^ w - (n : ℝ) ^ w := by
    intro n
    rw [hb]
    simp only
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ,
      abs_of_nonneg (sub_nonneg.mpr (hmono n))]
  have htel : ∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ w - (n : ℝ) ^ w) = (N : ℝ) ^ w := by
    have := Finset.sum_range_sub (fun n : ℕ => (n : ℝ) ^ w) N
    simp only [Nat.cast_succ, Nat.cast_zero, Real.zero_rpow hw0.ne', sub_zero] at this
    exact this
  have h1 : ‖∑ n ∈ Finset.range N, (∑ k ∈ Finset.range (n + 1), LSeries.term mu (w : ℂ) k) *
      (b (n + 1) - b n)‖ ≤ B * (N : ℝ) ^ w := by
    refine (norm_sum_le _ _).trans ?_
    rw [← htel, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, hbsub n]
    exact mul_le_mul_of_nonneg_right (hB' n) (sub_nonneg.mpr (hmono n))
  have h2 : ‖(∑ n ∈ Finset.range (N + 1), LSeries.term mu (w : ℂ) n) * b N‖ ≤ B * (N : ℝ) ^ w := by
    have hbN : ‖b N‖ = (N : ℝ) ^ w := by
      rw [hb]
      simp only
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) w)]
    rw [norm_mul, hbN]
    exact mul_le_mul_of_nonneg_right (hB' N) (Real.rpow_nonneg (Nat.cast_nonneg N) w)
  have h3 : |M N| ≤ 2 * B * (N : ℝ) ^ w := by
    have hn := congrArg norm hM
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hn]
    refine (norm_sub_le _ _).trans ?_
    linarith
  calc |M N| ≤ 2 * B * (N : ℝ) ^ w := h3
    _ ≤ 2 * B * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
        rw [← hw]
        gcongr
        linarith

/-! ## 3. `M(N) = O(N^θ)` ⟹ `1/ζ` holomorfa em `Re z > θ` -/

/-- `|a^{−z} − (a + 1)^{−z}| ≤ |z| a^{−Re z − 1}` para `a ≥ 1`, `Re z ≥ −1`. -/
theorem norm_cpow_sub_le {a : ℝ} (ha : 1 ≤ a) {z : ℂ} (hz : -1 ≤ z.re) :
    ‖(a : ℂ) ^ (-z) - ((a + 1 : ℝ) : ℂ) ^ (-z)‖ ≤ ‖z‖ * a ^ (-z.re - 1) := by
  have hderiv : ∀ x ∈ Icc a (a + 1), HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (-z))
      (-z * (x : ℂ) ^ (-z - 1)) (Icc a (a + 1)) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have h := (Complex.hasStrictDerivAt_cpow_const (c := -z) (ofReal_mem_slitPlane.mpr hx0)).hasDerivAt
    exact h.comp_ofReal.hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a (a + 1), ‖-z * (x : ℂ) ^ (-z - 1)‖ ≤ ‖z‖ * a ^ (-z.re - 1) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have e : (-z - 1).re = -z.re - 1 := by simp
    rw [e]
    have := Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (show -z.re - 1 ≤ 0 by linarith)
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1)
    (right_mem_Icc.mpr (by linarith))
  rw [norm_sub_rev] at h
  simpa using h

/-- `gM n z = M(n + 1)((n + 1)^{−z} − (n + 2)^{−z})`. -/
noncomputable def gM (n : ℕ) (z : ℂ) : ℂ :=
  (M (n + 1) : ℂ) * (((n : ℂ) + 1) ^ (-z) - ((n : ℂ) + 2) ^ (-z))

/-- `G(z) = Σ_{n ≥ 0} M(n + 1)((n + 1)^{−z} − (n + 2)^{−z})`. -/
noncomputable def G (z : ℂ) : ℂ := ∑' n, gM n z

theorem norm_gM_le {C θ : ℝ} (hθ : 0 ≤ θ) (hC : ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ θ) (n : ℕ) {z : ℂ}
    (hz : -1 ≤ z.re) :
    ‖gM n z‖ ≤ C * 2 ^ θ * ‖z‖ * ((n : ℝ) + 1) ^ (θ - z.re - 1) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hs := norm_cpow_sub_le hn1 hz
  have e1 : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  have e2 : (((n : ℝ) + 1 + 1 : ℝ) : ℂ) = (n : ℂ) + 2 := by push_cast; ring
  rw [e1, e2] at hs
  have hM := hC (n + 1)
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
    exact le_trans (abs_nonneg _) this
  have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by push_cast; linarith
  have hpow : (((n + 1 : ℕ) : ℝ) + 1) ^ θ ≤ 2 ^ θ * ((n : ℝ) + 1) ^ θ := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) h2 hθ
  have hsplit : ((n : ℝ) + 1) ^ θ * ((n : ℝ) + 1) ^ (-z.re - 1) = ((n : ℝ) + 1) ^ (θ - z.re - 1) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  unfold gM
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |M (n + 1)| * ‖((n : ℂ) + 1) ^ (-z) - ((n : ℂ) + 2) ^ (-z)‖
      ≤ (C * (2 ^ θ * ((n : ℝ) + 1) ^ θ)) * (‖z‖ * ((n : ℝ) + 1) ^ (-z.re - 1)) := by
        apply mul_le_mul _ hs (norm_nonneg _) (by positivity)
        exact hM.trans (mul_le_mul_of_nonneg_left hpow hC0)
    _ = C * 2 ^ θ * ‖z‖ * (((n : ℝ) + 1) ^ θ * ((n : ℝ) + 1) ^ (-z.re - 1)) := by ring
    _ = C * 2 ^ θ * ‖z‖ * ((n : ℝ) + 1) ^ (θ - z.re - 1) := by rw [hsplit]

theorem summable_shift {p : ℝ} (hp : p < -1) : Summable fun n : ℕ => ((n : ℝ) + 1) ^ p := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa using h

theorem summable_gM {C θ : ℝ} (hθ : 0 ≤ θ) (hC : ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ θ) {z : ℂ}
    (hz : θ < z.re) : Summable fun n => gM n z := by
  have hs := (summable_shift (p := θ - z.re - 1) (by linarith)).mul_left (C * 2 ^ θ * ‖z‖)
  refine Summable.of_norm_bounded hs fun n => ?_
  exact norm_gM_le hθ hC n (by linarith)

theorem differentiableAt_G {C θ : ℝ} (hθ : 0 ≤ θ) (hC : ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ θ) {z : ℂ}
    (hz : θ < z.re) : DifferentiableAt ℂ G z := by
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = (θ + z.re) / 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖z‖ + 1 := ⟨_, rfl⟩
  have hU : IsOpen ({w : ℂ | θ' < w.re} ∩ ball 0 R) :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ball
  have hzU : z ∈ {w : ℂ | θ' < w.re} ∩ ball 0 R := by
    refine ⟨?_, ?_⟩
    · show θ' < z.re
      rw [hθ']; linarith
    · rw [mem_ball, dist_zero_right, hR]; linarith
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
    exact le_trans (abs_nonneg _) this
  have hsum := (summable_shift (p := θ - θ' - 1) (by rw [hθ']; linarith)).mul_left (C * 2 ^ θ * R)
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (gM n) ({w : ℂ | θ' < w.re} ∩ ball 0 R) := by
    intro n w _
    have h1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have h2 : ((n : ℂ) + 2) ≠ 0 := by
      have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : n + 2 ≠ 0)
    unfold gM
    exact ((differentiableAt_const _).mul ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
      (differentiableAt_id.neg.const_cpow (Or.inl h2)))).differentiableWithinAt
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ {w : ℂ | θ' < w.re} ∩ ball 0 R →
      ‖gM n w‖ ≤ C * 2 ^ θ * R * ((n : ℝ) + 1) ^ (θ - θ' - 1) := by
    intro n w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : θ' < w.re := hw1
    rw [mem_ball, dist_zero_right] at hw2
    have hθ'0 : 0 ≤ θ' := by rw [hθ']; linarith
    refine (norm_gM_le hθ hC n (by linarith)).trans ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    have hp : ((n : ℝ) + 1) ^ (θ - w.re - 1) ≤ ((n : ℝ) + 1) ^ (θ - θ' - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h2θ : 0 ≤ C * 2 ^ θ := by positivity
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw2.le h2θ) hp (by positivity) (by positivity)
  have hD := differentiableOn_tsum_of_summable_norm hsum hdiff hU hle
  exact hD.differentiableAt (hU.mem_nhds hzU)

theorem M_succ_eq (n : ℕ) :
    ((M (n + 1) : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), mu (k + 1) := by
  unfold M
  rw [Finset.sum_range_succ']
  simp [mu]

/-- Em `Re z > 1`, `G(z) = Σ μ(n) n^{−z}`. -/
theorem G_eq_LSeries {C θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ θ) {z : ℂ} (hz : 1 < z.re) : G z = LSeries mu z := by
  have hsum := summable_gM hθ hC (show θ < z.re by linarith)
  have hL : LSeriesSummable mu z :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_mu_le n) hz
  -- somas parciais da série L
  have hP : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), mu (n + 1) * ((n : ℂ) + 1) ^ (-z)) atTop
      (𝓝 (LSeries mu z)) := by
    have h := hL.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
    refine h.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [show N + 2 = (N + 1) + 1 by ring, Finset.sum_range_succ']
    simp only [LSeries.term_zero, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), cpow_neg, div_eq_mul_inv]
    push_cast
    ring
  -- por partes
  have hab : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), mu (n + 1) * ((n : ℂ) + 1) ^ (-z) =
      ((M (N + 1) : ℝ) : ℂ) * ((N : ℂ) + 1) ^ (-z) + ∑ n ∈ Finset.range N, gM n z := by
    intro N
    rw [abel (fun n => mu (n + 1)) (fun n => ((n : ℂ) + 1) ^ (-z)) N, M_succ_eq]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold gM
    rw [M_succ_eq]
    push_cast
    ring_nf
  -- o termo de fronteira tende a zero
  have hbd : Tendsto (fun N : ℕ => ((M (N + 1) : ℝ) : ℂ) * ((N : ℂ) + 1) ^ (-z)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun N : ℕ => C * 2 ^ θ * ((N : ℝ) + 1) ^ (-(z.re - θ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have := ((tendsto_rpow_neg_atTop (show 0 < z.re - θ by linarith)).comp h1).const_mul (C * 2 ^ θ)
      simpa using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
    have hn1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    have hC0 : 0 ≤ C := by
      have := hC 0
      simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
      exact le_trans (abs_nonneg _) this
    have hM := hC (N + 1)
    have h2 : ((N + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) := by push_cast; linarith
    have hpow : (((N + 1 : ℕ) : ℝ) + 1) ^ θ ≤ 2 ^ θ * ((N : ℝ) + 1) ^ θ := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by positivity) h2 hθ
    have e : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, e, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
      neg_re]
    have hsplit : ((N : ℝ) + 1) ^ θ * ((N : ℝ) + 1) ^ (-z.re) = ((N : ℝ) + 1) ^ (-(z.re - θ)) := by
      rw [← Real.rpow_add (by linarith)]; ring_nf
    calc |M (N + 1)| * ((N : ℝ) + 1) ^ (-z.re)
        ≤ (C * (2 ^ θ * ((N : ℝ) + 1) ^ θ)) * ((N : ℝ) + 1) ^ (-z.re) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact hM.trans (mul_le_mul_of_nonneg_left hpow hC0)
      _ = C * 2 ^ θ * (((N : ℝ) + 1) ^ θ * ((N : ℝ) + 1) ^ (-z.re)) := by ring
      _ = C * 2 ^ θ * ((N : ℝ) + 1) ^ (-(z.re - θ)) := by rw [hsplit]
  have hG : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, gM n z) atTop (𝓝 (G z)) :=
    hsum.hasSum.tendsto_sum_nat
  have hlim2 := hbd.add hG
  rw [zero_add] at hlim2
  refine tendsto_nhds_unique (hlim2.congr fun N => (hab N).symm) hP

/-- **`M(N) = O(N^{1/2 + ε})` ⟹ RH** (Littlewood). -/
theorem RH_of_mertens (h : MertensFraco) : RiemannHypothesis := by
  refine ATK.BaezDuarteBridge.riemannHypothesis_of_strip fun s hs1 hs2 hz => ?_
  obtain ⟨C, hC0⟩ := h ((s.re - 1 / 2) / 2) (by linarith)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 / 2 + (s.re - 1 / 2) / 2 := ⟨_, rfl⟩
  have hC : ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ θ := by rw [hθ]; exact hC0
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hθs : θ < s.re := by rw [hθ]; linarith
  have hV : IsOpen {w : ℂ | θ < w.re} := isOpen_lt continuous_const continuous_re
  have hA : AnalyticOnNhd ℂ (fun w => riemannZeta₁ w * G w - (w - 1)) {w : ℂ | θ < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hV
    exact (((differentiable_riemannZeta₁ w).mul (differentiableAt_G hθ0 hC hw)).sub
      (differentiableAt_id.sub (differentiableAt_const 1))).differentiableWithinAt
  have hev : (fun w => riemannZeta₁ w * G w - (w - 1)) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hmem : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hmem] with w hw
    have hw' : 1 < w.re := hw
    have hw1 : w ≠ 1 := fun h => by rw [h, one_re] at hw'; exact lt_irrefl 1 hw'
    have hz0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw'
    rw [G_eq_LSeries hθ0 hθ1 hC hw', LSeries_mu hw', F_eq hw1, zeta₁_eq hw1]
    simp only [Pi.zero_apply]
    field_simp
    ring
  have h2V : (2 : ℂ) ∈ {w : ℂ | θ < w.re} := by
    show θ < (2 : ℂ).re
    norm_num; linarith
  have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt θ).isPreconnected h2V hev
  have hs : s ∈ {w : ℂ | θ < w.re} := hθs
  have h0 := hzero hs
  simp only [Pi.zero_apply] at h0
  have hs1' : s ≠ 1 := fun h => by rw [h, one_re] at hs2; exact lt_irrefl 1 hs2
  rw [zeta₁_eq hs1', hz, mul_zero, zero_mul, zero_sub, neg_eq_zero, sub_eq_zero] at h0
  exact hs1' h0

/-- **Critério de Littlewood**: `RH ⟺ M(N) = O(N^{1/2 + ε})` para todo `ε > 0`. -/
theorem rh_iff_mertens : RiemannHypothesis ↔ MertensFraco :=
  ⟨mertens_of_RH, RH_of_mertens⟩

end ATK.ZeroClasses.Mertens

#print axioms ATK.ZeroClasses.Mertens.abel
#print axioms ATK.ZeroClasses.Mertens.mu_eq_term_mul
#print axioms ATK.ZeroClasses.Mertens.mertens_of_RH
#print axioms ATK.ZeroClasses.Mertens.norm_cpow_sub_le
#print axioms ATK.ZeroClasses.Mertens.norm_gM_le
#print axioms ATK.ZeroClasses.Mertens.summable_shift
#print axioms ATK.ZeroClasses.Mertens.summable_gM
#print axioms ATK.ZeroClasses.Mertens.differentiableAt_G
#print axioms ATK.ZeroClasses.Mertens.M_succ_eq
#print axioms ATK.ZeroClasses.Mertens.G_eq_LSeries
#print axioms ATK.ZeroClasses.Mertens.RH_of_mertens
#print axioms ATK.ZeroClasses.Mertens.rh_iff_mertens
