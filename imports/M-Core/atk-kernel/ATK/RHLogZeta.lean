import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import ATK.ZetaRegiao

/-!
# ATK — Sob RH, `1/ζ` cresce menos que qualquer potência em `Re s ≥ 1/2 + δ` (Titchmarsh 14.2)

Sob a hipótese de Riemann da Mathlib (`RiemannHypothesis`), `ζ` não se anula em `Re s > 1/2`, e
então um ramo holomorfo de `log ζ` existe em cada disco `|s − (3 + it)| < 5/2` (`existe_log_bola`,
pelo teorema das primitivas em discos da Mathlib). Com:

* `Re log ζ = log |ζ| ≤ log(2(|t| + 8))` (cota polinomial de `ζ`, `ATK.ZetaRegiao.norm_zeta_le`);
* **Borel–Carathéodory** (Mathlib): `|log ζ| ≤ 10(log(2(|t|+8)) + 1)/δ` em `Re s ≥ 1/2 + δ/2`;
* `|log ζ| ≤ 3/4` em `Re s ≥ 5/2` (ramo principal, `|ζ − 1| ≤ 1/2`);
* **três círculos** (das três retas de Hadamard da Mathlib, via `u ↦ 3 + it + eᵘ`):
  `|log ζ| ≤ B^θ` com `θ < 1` em `Re s ≥ 1/2 + δ`,

obtém-se **`norm_F_le`**: para todo `δ, η > 0`,
`‖(s − 1)/ζ₁(s)‖ ≤ C (1 + |Im s|)^η` em `Re s ≥ 1/2 + δ`, onde `(s − 1)/ζ₁(s) = 1/ζ(s)` para
`s ≠ 1` (`ζ₁ = (s − 1)ζ`, inteira, Mathlib).
-/

open Complex Set Metric Filter Topology
open scoped Real

namespace ATK.RHLogZeta

/-! ## RH: `ζ` não se anula em `Re s > 1/2` -/

theorem zeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta s ≠ 0 := by
  intro h0
  by_cases hs1 : s = 1
  · subst hs1; exact riemannZeta_one_ne_zero h0
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at hs
    simp at hs
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have := hRH s h0 htriv hs1
  linarith

/-- `ζ₁(s) = (s − 1) ζ(s)` (Mathlib: inteira, `ζ₁(1) = 1`). -/
theorem zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp [sub_ne_zero.mpr hs]

theorem zeta₁_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; rw [riemannZeta₁_one]; exact one_ne_zero
  rw [zeta₁_eq hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) (zeta_ne_zero_of_RH hRH hs)

/-- `F(s) = (s − 1)/ζ₁(s)`: a versão holomorfa de `1/ζ`. -/
noncomputable def F (s : ℂ) : ℂ := (s - 1) / riemannZeta₁ s

theorem F_eq {s : ℂ} (hs : s ≠ 1) : F s = (riemannZeta s)⁻¹ := by
  rw [F, zeta₁_eq hs]
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  by_cases hz : riemannZeta s = 0
  · simp [hz]
  · field_simp

theorem differentiableAt_F (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ F s :=
  ((differentiableAt_id.sub (differentiableAt_const _))).div
    (differentiable_riemannZeta₁ s) (zeta₁_ne_zero_of_RH hRH hs)

/-! ## Logaritmo holomorfo num disco -/

/-- **Ramo holomorfo do logaritmo** de uma função holomorfa sem zeros num disco. -/
theorem existe_log_bola {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0) {L0 : ℂ} (hL0 : Complex.exp L0 = f c) (hR : 0 < R) :
    ∃ L : ℂ → ℂ, L c = L0 ∧ (∀ z ∈ ball c R, Complex.exp (L z) = f z) ∧
      ∀ z ∈ ball c R, HasDerivAt L (deriv f z / f z) z := by
  have hopen : IsOpen (ball c R) := isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c R) :=
    (hf.deriv hopen).div hf hne
  obtain ⟨g, hgc, hg⟩ := hd.isExactOn_ball.with_val_at c L0
  refine ⟨g, hgc, ?_, hg⟩
  have hh : ∀ z ∈ ball c R, HasDerivAt (fun z => f z * Complex.exp (-g z)) 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z :=
      (hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hexp := ((hg z hz).neg).cexp
    convert hfz.mul hexp using 1
    have := hne z hz
    field_simp
    ring
  have hconst : ∀ z ∈ ball c R, f z * Complex.exp (-g z) = f c * Complex.exp (-g c) := by
    intro z hz
    refine hopen.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun x hx => (hh x hx).differentiableAt.differentiableWithinAt) ?_ hz (mem_ball_self hR)
    intro x hx
    exact (hh x hx).deriv
  intro z hz
  have h1 := hconst z hz
  rw [hgc, ← hL0, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero] at h1
  have h2 : f z = Complex.exp (g z) := by
    have := congrArg (· * Complex.exp (g z)) h1
    simp only [one_mul] at this
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] at this
    exact this
  exact h2.symm

/-! ## Três círculos (das três retas de Hadamard) -/

/-- **Teorema dos três círculos de Hadamard**, via `u ↦ c + eᵘ` e o teorema das três retas da
Mathlib. -/
theorem tres_circulos {L : ℂ → ℂ} {c : ℂ} {R r₁ r₃ : ℝ} (h1 : 0 < r₁) (h13 : r₁ < r₃)
    (h3R : r₃ < R) (hL : DifferentiableOn ℂ L (ball c R)) {a b : ℝ}
    (ha : ∀ z, ‖z - c‖ = r₁ → ‖L z‖ ≤ a) (hb : ∀ z, ‖z - c‖ = r₃ → ‖L z‖ ≤ b) {z : ℂ}
    (hz1 : r₁ ≤ ‖z - c‖) (hz3 : ‖z - c‖ ≤ r₃) :
    ‖L z‖ ≤ a ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      b ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  set g : ℂ → ℂ := fun u => L (c + Complex.exp u) with hg
  have hzc : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  set u₀ := Complex.log (z - c)
  have hu₀ : Complex.exp u₀ = z - c := Complex.exp_log hzc
  have hu₀re : u₀.re = Real.log ‖z - c‖ := Complex.log_re _
  have hl : Real.log r₁ < Real.log r₃ := Real.log_lt_log h1 h13
  have hmem : ∀ u : ℂ, u.re ≤ Real.log r₃ → c + Complex.exp u ∈ closedBall c r₃ := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp u.re ≤ Real.exp (Real.log r₃) := Real.exp_le_exp.mpr hu
      _ = r₃ := Real.exp_log (by linarith)
  have hball : closedBall c r₃ ⊆ ball c R := closedBall_subset_ball h3R
  have hgd : ∀ u : ℂ, u.re ≤ Real.log r₃ → DifferentiableAt ℂ g u := by
    intro u hu
    have hLd : DifferentiableAt ℂ L (c + Complex.exp u) :=
      hL.differentiableAt (isOpen_ball.mem_nhds (hball (hmem u hu)))
    exact hLd.comp u ((differentiableAt_const c).add Complex.differentiableAt_exp)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r₃).exists_bound_of_continuousOn
    ((hL.mono hball).continuousOn)
  have hcl : closure (Complex.HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) ⊆
      {u : ℂ | u.re ≤ Real.log r₃} := by
    refine closure_minimal (fun u (hu : u ∈ re ⁻¹' Ioo (Real.log r₁) (Real.log r₃)) =>
      show u.re ≤ Real.log r₃ from le_of_lt hu.2) ?_
    exact isClosed_le Complex.continuous_re continuous_const
  have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := g) (z := u₀) (a := a) (b := b) hl
    (show u₀ ∈ Complex.HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃) from by
      show u₀.re ∈ Icc (Real.log r₁) (Real.log r₃)
      rw [hu₀re]
      exact ⟨Real.log_le_log h1 hz1, Real.log_le_log (by linarith) hz3⟩)
    ⟨fun u (hu : u ∈ re ⁻¹' Ioo (Real.log r₁) (Real.log r₃)) =>
      (hgd u (le_of_lt hu.2)).differentiableWithinAt,
      fun u hu => (hgd u (hcl hu)).continuousAt.continuousWithinAt⟩
    ⟨C, by
      rintro _ ⟨u, hu, rfl⟩
      exact hC _ (hmem u hu.2)⟩
    (by
      intro u hu
      refine ha _ ?_
      rw [add_sub_cancel_left, Complex.norm_exp, show u.re = Real.log r₁ from hu,
        Real.exp_log h1])
    (by
      intro u hu
      refine hb _ ?_
      rw [add_sub_cancel_left, Complex.norm_exp, show u.re = Real.log r₃ from hu,
        Real.exp_log (by linarith)])
  simp only [hg, hu₀, add_sub_cancel] at h3
  rw [hu₀re] at h3
  exact h3

/-! ## `ζ` em `Re s ≥ 5/2` -/

theorem soma_inv_sq_add_two : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_add] at h
  norm_num at h
  convert h using 2 with n
  push_cast
  ring

theorem norm_zeta_sub_one_le {s : ℂ} (hs : 5 / 2 ≤ s.re) : ‖riemannZeta s - 1‖ ≤ 1 / 2 := by
  have h1 : 1 < s.re := by linarith
  have hsum0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) := Complex.summable_one_div_nat_cpow.mpr h1
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (summable_nat_add_iff 1).mpr hsum0
    simpa using this
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1, hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Complex.one_cpow, div_one, add_sub_cancel_left]
  have hterm : ∀ n : ℕ, ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ ≤ 71 / 100 * (1 / ((n : ℝ) + 2) ^ 2) := by
    intro n
    have hpos : 0 < n + 2 := by omega
    have hc : ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [hc, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos]
    have hx : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hx0 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by linarith
    have hpow : ((n + 2 : ℕ) : ℝ) ^ (5 / 2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    have h52 : ((n + 2 : ℕ) : ℝ) ^ (5 / 2 : ℝ) = ((n + 2 : ℕ) : ℝ) ^ 2 * √((n + 2 : ℕ) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hx0]
      norm_num
    have hsq : (141 / 100 : ℝ) ≤ √((n + 2 : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hx0.le]
      nlinarith
    have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [one_div, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hx0 _)]
    calc (1 : ℝ) ≤ 71 / 100 * (141 / 100) := by norm_num
      _ ≤ 71 / 100 * √((n + 2 : ℕ) : ℝ) := by gcongr
      _ = 71 / 100 * (1 / ((n : ℝ) + 2) ^ 2) *
            (((n + 2 : ℕ) : ℝ) ^ 2 * √((n + 2 : ℕ) : ℝ)) := by
          rw [hcast]; field_simp
      _ ≤ 71 / 100 * (1 / ((n : ℝ) + 2) ^ 2) * ((n + 2 : ℕ) : ℝ) ^ s.re := by
          rw [← h52]; gcongr
  have hsumR : Summable (fun n : ℕ => 71 / 100 * (1 / ((n : ℝ) + 2) ^ 2)) :=
    soma_inv_sq_add_two.summable.mul_left _
  have hsumN : Summable (fun n : ℕ => ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumR
  calc ‖∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ ∑' n : ℕ, 71 / 100 * (1 / ((n : ℝ) + 2) ^ 2) := hsumN.tsum_le_tsum hterm hsumR
    _ = 71 / 100 * (π ^ 2 / 6 - 1) := by rw [tsum_mul_left, soma_inv_sq_add_two.tsum_eq]
    _ ≤ 1 / 2 := by
        have := Real.pi_lt_d2
        have hp := Real.pi_pos
        nlinarith

theorem zeta_ne_zero_re_ge {s : ℂ} (hs : 5 / 2 ≤ s.re) : riemannZeta s ≠ 0 := by
  intro h
  have := norm_zeta_sub_one_le hs
  rw [h, zero_sub, norm_neg, norm_one] at this
  norm_num at this

theorem norm_log_zeta_le {s : ℂ} (hs : 5 / 2 ≤ s.re) : ‖Complex.log (riemannZeta s)‖ ≤ 3 / 4 := by
  have h := norm_zeta_sub_one_le hs
  have := Complex.norm_log_one_add_half_le_self h
  rw [add_sub_cancel] at this
  linarith

theorem norm_inv_zeta_le_two {s : ℂ} (hs : 5 / 2 ≤ s.re) : ‖(riemannZeta s)⁻¹‖ ≤ 2 := by
  have h := norm_zeta_sub_one_le hs
  have hz : 1 / 2 ≤ ‖riemannZeta s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (riemannZeta s)
    rw [norm_one, norm_sub_rev] at this
    linarith
  rw [norm_inv]
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-! ## Desigualdade de Young (`x^θ = o(x)`) -/

theorem young {A θ η : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hη : 0 < η) :
    ∃ K, ∀ x : ℝ, 0 ≤ x → A * x ^ θ ≤ η * x + K := by
  set X₀ := (A / η) ^ (1 / (1 - θ)) with hX₀
  have hX₀0 : 0 ≤ X₀ := Real.rpow_nonneg (div_nonneg hA hη.le) _
  refine ⟨A * X₀ ^ θ, fun x hx => ?_⟩
  rcases le_total x X₀ with hle | hle
  · have : A * x ^ θ ≤ A * X₀ ^ θ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hle hθ0) hA
    linarith [mul_nonneg hη.le hx]
  · have h1θ : 0 < 1 - θ := by linarith
    have hX : X₀ ^ (1 - θ) = A / η := by
      rw [hX₀, ← Real.rpow_mul (div_nonneg hA hη.le), one_div, inv_mul_cancel₀ h1θ.ne',
        Real.rpow_one]
    have hxX : A / η ≤ x ^ (1 - θ) := by
      rw [← hX]; exact Real.rpow_le_rpow hX₀0 hle h1θ.le
    have hxpos : 0 ≤ x := hx
    have hsplit : x = x ^ (1 - θ) * x ^ θ := by
      rcases eq_or_lt_of_le hxpos with h0 | hpos
      · subst h0
        rw [Real.zero_rpow h1θ.ne']; ring
      · rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
    have hAx : A * x ^ θ ≤ η * x := by
      calc A * x ^ θ = η * (A / η) * x ^ θ := by field_simp
        _ ≤ η * x ^ (1 - θ) * x ^ θ := by
          gcongr
        _ = η * x := by rw [mul_assoc, ← hsplit]
    have hK : 0 ≤ A * X₀ ^ θ := mul_nonneg hA (Real.rpow_nonneg hX₀0 _)
    linarith

/-! ## O disco `|s − (3 + it)| < 5/2` -/

/-- Centro do disco. -/
noncomputable def c₀ (t : ℝ) : ℂ := 3 + t * I

theorem c₀_re (t : ℝ) : (c₀ t).re = 3 := by simp [c₀]

theorem c₀_im (t : ℝ) : (c₀ t).im = t := by simp [c₀]

theorem bola_props {t : ℝ} (ht : 4 ≤ |t|) {z : ℂ} (hz : z ∈ ball (c₀ t) (5 / 2)) :
    1 / 2 < z.re ∧ z ≠ 1 ∧ ‖z‖ ≤ |t| + 6 ∧ 3 / 2 ≤ ‖z - 1‖ := by
  rw [mem_ball, dist_eq_norm] at hz
  have hre : |z.re - 3| < 5 / 2 := by
    have := Complex.abs_re_le_norm (z - c₀ t)
    rw [sub_re, c₀_re] at this; linarith
  have him : |z.im - t| < 5 / 2 := by
    have := Complex.abs_im_le_norm (z - c₀ t)
    rw [sub_im, c₀_im] at this; linarith
  have hre' := abs_lt.mp hre
  have him' := abs_lt.mp him
  have himz : 3 / 2 ≤ |z.im| := by
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht
      rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_nonpos h0] at ht
      rw [abs_of_neg (by linarith)]; linarith
  have hz1 : 3 / 2 ≤ ‖z - 1‖ := by
    refine himz.trans ?_
    have := Complex.abs_im_le_norm (z - 1)
    simpa using this
  refine ⟨by linarith, ?_, ?_, hz1⟩
  · intro h; rw [h] at hz1; simp at hz1; norm_num at hz1
  · have hc : ‖c₀ t‖ ≤ 3 + |t| := by
      unfold c₀
      refine (norm_add_le _ _).trans ?_
      simp
    calc ‖z‖ = ‖(z - c₀ t) + c₀ t‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c₀ t‖ + ‖c₀ t‖ := norm_add_le _ _
      _ ≤ 5 / 2 + (3 + |t|) := by linarith
      _ ≤ |t| + 6 := by linarith

theorem norm_zeta_le_bola {t : ℝ} (ht : 4 ≤ |t|) {z : ℂ} (hz : z ∈ ball (c₀ t) (5 / 2)) :
    ‖riemannZeta z‖ ≤ 2 * (|t| + 6) := by
  obtain ⟨hre, hz1, hn, hd⟩ := bola_props ht hz
  have h := ATK.ZetaRegiao.norm_zeta_le (by linarith) hz1
  have hd0 : 0 < ‖z - 1‖ := by linarith
  have h1 : ‖z‖ / ‖z - 1‖ ≤ |t| + 6 := by
    rw [div_le_iff₀ hd0]; nlinarith [norm_nonneg z]
  have h2 : ‖z‖ / (2 * z.re) ≤ |t| + 6 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg z]
  linarith

theorem log_zeta_c₀ (t : ℝ) : Complex.exp (Complex.log (riemannZeta (c₀ t))) = riemannZeta (c₀ t) :=
  Complex.exp_log (zeta_ne_zero_re_ge (by rw [c₀_re]; norm_num))

/-- **Sob RH**: o ramo de `log ζ` no disco, com `L(c₀) = Log ζ(c₀)`. -/
theorem existe_log_zeta (hRH : RiemannHypothesis) {t : ℝ} (ht : 4 ≤ |t|) :
    ∃ L : ℂ → ℂ, L (c₀ t) = Complex.log (riemannZeta (c₀ t)) ∧
      (∀ z ∈ ball (c₀ t) (5 / 2), Complex.exp (L z) = riemannZeta z) ∧
      ∀ z ∈ ball (c₀ t) (5 / 2), HasDerivAt L (deriv riemannZeta z / riemannZeta z) z := by
  refine existe_log_bola ?_ ?_ (log_zeta_c₀ t) (by norm_num)
  · intro z hz
    exact (differentiableAt_riemannZeta (bola_props ht hz).2.1).differentiableWithinAt
  · intro z hz
    exact zeta_ne_zero_of_RH hRH (bola_props ht hz).1

/-- O expoente dos três círculos. -/
noncomputable def θ₂ (δ : ℝ) : ℝ :=
  (Real.log (5 / 2 - δ) - Real.log (1 / 4)) / (Real.log (5 / 2 - δ / 2) - Real.log (1 / 4))

theorem θ₂_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ θ₂ δ ∧ θ₂ δ < 1 := by
  have h1 : Real.log (1 / 4) < Real.log (5 / 2 - δ) := Real.log_lt_log (by norm_num) (by linarith)
  have h2 : Real.log (5 / 2 - δ) < Real.log (5 / 2 - δ / 2) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold θ₂
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]; linarith

/-- O ramo de `log ζ` coincide com o logaritmo principal perto de `Re s = 3`. -/
theorem L_eq_log (hRH : RiemannHypothesis) {t : ℝ} (ht : 4 ≤ |t|) {L : ℂ → ℂ}
    (hL0 : L (c₀ t) = Complex.log (riemannZeta (c₀ t)))
    (hLd : ∀ z ∈ ball (c₀ t) (5 / 2), HasDerivAt L (deriv riemannZeta z / riemannZeta z) z) :
    EqOn L (fun z => Complex.log (riemannZeta z)) (ball (c₀ t) (1 / 2)) := by
  have hsub : ball (c₀ t) (1 / 2) ⊆ ball (c₀ t) (5 / 2) := ball_subset_ball (by norm_num)
  have hre : ∀ z ∈ ball (c₀ t) (1 / 2), 5 / 2 ≤ z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - c₀ t)
    rw [sub_re, c₀_re] at this
    linarith [abs_lt.mp (lt_of_le_of_lt this hz)]
  have hg : ∀ z ∈ ball (c₀ t) (1 / 2), HasDerivAt (fun z => Complex.log (riemannZeta z))
      (deriv riemannZeta z / riemannZeta z) z := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; have := hre z hz; rw [h, one_re] at this; norm_num at this
    have hζ := (differentiableAt_riemannZeta hz1).hasDerivAt
    refine hζ.clog ?_
    left
    have h := norm_zeta_sub_one_le (hre z hz)
    have := Complex.abs_re_le_norm (riemannZeta z - 1)
    rw [sub_re, one_re] at this
    linarith [abs_le.mp (this.trans h)]
  refine isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
    (fun z hz => (hLd z (hsub hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt) ?_
    (mem_ball_self (by norm_num)) hL0
  intro z hz
  rw [(hLd z (hsub hz)).deriv, (hg z hz).deriv]

/-- **A cota de `log ζ` em `Re s ≥ 1/2 + δ`** (três círculos + Borel–Carathéodory), `|t| ≥ 4`. -/
theorem norm_L_le (hRH : RiemannHypothesis) {t δ : ℝ} (ht : 4 ≤ |t|) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {L : ℂ → ℂ} (hL0 : L (c₀ t) = Complex.log (riemannZeta (c₀ t)))
    (hLe : ∀ z ∈ ball (c₀ t) (5 / 2), Complex.exp (L z) = riemannZeta z)
    (hLd : ∀ z ∈ ball (c₀ t) (5 / 2), HasDerivAt L (deriv riemannZeta z / riemannZeta z) z)
    {z : ℂ} (hz : ‖z - c₀ t‖ ≤ 5 / 2 - δ) :
    ‖L z‖ ≤ (10 * (Real.log (2 * (|t| + 6)) + 1) / δ) ^ θ₂ δ := by
  set M := Real.log (2 * (|t| + 6)) with hMdef
  set B₃ := 10 * (M + 1) / δ with hB₃
  have hM0 : 0 < M := Real.log_pos (by linarith [abs_nonneg t])
  have hB₃1 : 1 ≤ B₃ := by
    rw [hB₃, le_div_iff₀ hδ]; linarith
  have hθ := θ₂_bounds hδ hδ1
  have hLdiff : DifferentiableOn ℂ L (ball (c₀ t) (5 / 2)) :=
    fun z hz => (hLd z hz).differentiableAt.differentiableWithinAt
  have hEq := L_eq_log hRH ht hL0 hLd
  -- interior: `‖L‖ ≤ 3/4`
  have hin : ∀ w ∈ ball (c₀ t) (1 / 2), ‖L w‖ ≤ 3 / 4 := by
    intro w hw
    rw [hEq hw]
    apply norm_log_zeta_le
    rw [mem_ball, dist_eq_norm] at hw
    have := Complex.abs_re_le_norm (w - c₀ t)
    rw [sub_re, c₀_re] at this
    linarith [abs_lt.mp (lt_of_le_of_lt this hw)]
  have hLc₀ : ‖L (c₀ t)‖ ≤ 3 / 4 := hin _ (mem_ball_self (by norm_num))
  -- Borel–Carathéodory no círculo de raio `5/2 − δ/2`
  have hout : ∀ w, ‖w - c₀ t‖ = 5 / 2 - δ / 2 → ‖L w‖ ≤ B₃ := by
    intro w hw
    have hmem : w - c₀ t ∈ ball (0 : ℂ) (5 / 2) := by
      rw [mem_ball_zero_iff, hw]; linarith
    have hBC := Complex.borelCaratheodory (f := fun u => L (c₀ t + u)) (M := M) (R := 5 / 2)
      hM0 (fun u hu => by
        have : c₀ t + u ∈ ball (c₀ t) (5 / 2) := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact mem_ball_zero_iff.mp hu
        exact ((hLd _ this).differentiableAt.comp u
          ((differentiableAt_const _).add differentiableAt_id)).differentiableWithinAt)
      (fun u hu => by
        have hmb : c₀ t + u ∈ ball (c₀ t) (5 / 2) := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact mem_ball_zero_iff.mp hu
        show (L (c₀ t + u)).re ≤ M
        have hre : (L (c₀ t + u)).re = Real.log ‖riemannZeta (c₀ t + u)‖ := by
          rw [← hLe _ hmb, Complex.norm_exp, Real.log_exp]
        rw [hre, hMdef]
        have hne := zeta_ne_zero_of_RH hRH (bola_props ht hmb).1
        exact Real.log_le_log (norm_pos_iff.mpr hne) (norm_zeta_le_bola ht hmb))
      (by norm_num) hmem
    simp only [add_sub_cancel, add_zero] at hBC
    rw [hw] at hBC
    have hden : (5 / 2 : ℝ) - (5 / 2 - δ / 2) = δ / 2 := by ring
    rw [hden] at hBC
    refine hBC.trans ?_
    rw [hB₃]
    have h1 : 2 * M * (5 / 2 - δ / 2) / (δ / 2) ≤ 10 * M / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ]; nlinarith [mul_pos hM0 (mul_pos hδ hδ)]
    have h2 : ‖L (c₀ t)‖ * (5 / 2 + (5 / 2 - δ / 2)) / (δ / 2) ≤ 10 / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ]
      have hk : ‖L (c₀ t)‖ * ((5 / 2 + (5 / 2 - δ / 2)) * δ) ≤ 3 / 4 * ((5 / 2 + (5 / 2 - δ / 2)) * δ) :=
        mul_le_mul_of_nonneg_right hLc₀ (by nlinarith)
      nlinarith
    calc 2 * M * (5 / 2 - δ / 2) / (δ / 2) + ‖L (c₀ t)‖ * (5 / 2 + (5 / 2 - δ / 2)) / (δ / 2)
        ≤ 10 * M / δ + 10 / δ := add_le_add h1 h2
      _ = 10 * (M + 1) / δ := by ring
  -- três círculos
  rcases lt_or_ge ‖z - c₀ t‖ (1 / 4) with hz4 | hz4
  · have hzb : z ∈ ball (c₀ t) (1 / 2) := by
      rw [mem_ball, dist_eq_norm]; linarith
    calc ‖L z‖ ≤ 3 / 4 := hin z hzb
      _ ≤ 1 := by norm_num
      _ ≤ B₃ ^ θ₂ δ := Real.one_le_rpow hB₃1 hθ.1
  · have h3 := tres_circulos (L := L) (c := c₀ t) (R := 5 / 2) (r₁ := 1 / 4)
      (r₃ := 5 / 2 - δ / 2) (by norm_num) (by linarith) (by linarith) hLdiff (a := 1) (b := B₃)
      (fun w hw => by
        have : w ∈ ball (c₀ t) (1 / 2) := by rw [mem_ball, dist_eq_norm, hw]; norm_num
        linarith [hin w this])
      hout hz4 (by linarith)
    rw [Real.one_rpow, one_mul] at h3
    refine h3.trans (Real.rpow_le_rpow_of_exponent_le hB₃1 ?_)
    unfold θ₂
    have hden : 0 < Real.log (5 / 2 - δ / 2) - Real.log (1 / 4) := by
      have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) (by linarith : (1 / 4 : ℝ) < 5 / 2 - δ / 2)
      linarith
    rw [div_le_div_iff_of_pos_right hden]
    have := Real.log_le_log (by linarith) hz
    linarith

/-- **Titchmarsh 14.2 (a forma usada)**: sob RH, para `δ ∈ (0, 1]` e `η > 0` existe `C > 0` com
`‖F(s)‖ ≤ C (1 + |Im s|)^η` em todo o semiplano `Re s ≥ 1/2 + δ` (`F = 1/ζ` fora de `s = 1`). -/
theorem norm_F_le (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → ‖F s‖ ≤ C * (1 + |s.im|) ^ η := by
  have hθ := θ₂_bounds hδ hδ1
  obtain ⟨K, hK⟩ := young (A := (10 / δ) ^ θ₂ δ) (θ := θ₂ δ) (η := η)
    (Real.rpow_nonneg (by positivity) _) hθ.1 hθ.2 hη
  set C₁ := Real.exp (η + K) * 12 ^ η with hC₁
  set Kc : Set ℂ := {s : ℂ | 1 / 2 + δ ≤ s.re} ∩ {s : ℂ | s.re ≤ 3} ∩ {s : ℂ | |s.im| ≤ 4}
    with hKcdef
  have hKc : IsCompact Kc := by
    refine (isCompact_closedBall (0 : ℂ) 10).of_isClosed_subset ?_ ?_
    · exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
    · rintro s ⟨⟨h1, h2⟩, h3⟩
      simp only [mem_setOf_eq] at h1 h2 h3
      rw [mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 3 + 4 := by
            gcongr
            rw [abs_le]; constructor <;> linarith
        _ ≤ 10 := by norm_num
  have hFc : ContinuousOn F Kc := fun s hs =>
    (differentiableAt_F hRH (by have := hs.1.1; simp only [mem_setOf_eq] at this; linarith)
      ).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn hFc
  set C := max (max 2 C₀) C₁ + 1 with hCdef
  have hC2 : 2 ≤ C := by
    have := le_max_left (max 2 C₀) C₁; have := le_max_left 2 C₀; linarith
  have hCC₀ : C₀ ≤ C := by
    have := le_max_left (max 2 C₀) C₁; have := le_max_right 2 C₀; linarith
  have hCC₁ : C₁ ≤ C := by have := le_max_right (max 2 C₀) C₁; linarith
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun s hs => ?_⟩
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCle : ∀ x, x ≤ C → x ≤ C * (1 + |s.im|) ^ η := fun x hx =>
    hx.trans (le_mul_of_one_le_right hCpos.le h1)
  rcases le_or_gt (5 / 2) s.re with h52 | h52
  · have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h52; norm_num at h52
    rw [F_eq hs1]
    exact hCle _ ((norm_inv_zeta_le_two h52).trans hC2)
  rcases le_or_gt |s.im| 4 with h4 | h4
  · exact hCle _ ((hC₀ s ⟨⟨hs, show s.re ≤ 3 by linarith⟩, h4⟩).trans hCC₀)
  · set t := s.im with htdef
    have ht : 4 ≤ |t| := h4.le
    obtain ⟨L, hL0, hLe, hLd⟩ := existe_log_zeta hRH ht
    have hsc : s - c₀ t = ((s.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c₀, htdef]
    have hz : ‖s - c₀ t‖ ≤ 5 / 2 - δ := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hsmem : s ∈ ball (c₀ t) (5 / 2) := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hLs := norm_L_le hRH ht hδ hδ1 hL0 hLe hLd hz
    have hs1 : s ≠ 1 := by
      intro h
      have h0 : t = 0 := by rw [htdef, h, one_im]
      rw [h0, abs_zero] at h4
      norm_num at h4
    rw [F_eq hs1, ← hLe s hsmem, ← Complex.exp_neg, Complex.norm_exp, neg_re]
    set M := Real.log (2 * (|t| + 6)) with hM
    have hM0 : 0 ≤ M := (Real.log_pos (by linarith [abs_nonneg t])).le
    have hsplit : (10 * (M + 1) / δ) ^ θ₂ δ = (10 / δ) ^ θ₂ δ * (M + 1) ^ θ₂ δ := by
      rw [show 10 * (M + 1) / δ = (10 / δ) * (M + 1) by ring,
        Real.mul_rpow (by positivity) (by linarith)]
    have hY := hK (M + 1) (by linarith)
    have hexpM : Real.exp (η * M) = (2 * (|t| + 6)) ^ η := by
      rw [Real.rpow_def_of_pos (by positivity), hM, mul_comm]
    have hpow : (2 * (|t| + 6)) ^ η ≤ 12 ^ η * (1 + |t|) ^ η := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t]) hη.le
    calc Real.exp (-(L s).re) ≤ Real.exp ‖L s‖ := by
          apply Real.exp_le_exp.mpr
          have := Complex.abs_re_le_norm (L s)
          linarith [neg_abs_le (L s).re]
      _ ≤ Real.exp ((10 * (M + 1) / δ) ^ θ₂ δ) := Real.exp_le_exp.mpr hLs
      _ ≤ Real.exp (η * (M + 1) + K) := by rw [hsplit]; exact Real.exp_le_exp.mpr hY
      _ = Real.exp (η + K) * Real.exp (η * M) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := by
          rw [hexpM]; gcongr
      _ = C₁ * (1 + |t|) ^ η := by rw [hC₁]; ring
      _ ≤ C * (1 + |t|) ^ η := by gcongr

/-- **Lindelöf à direita da reta crítica (sob RH)**: para `δ ∈ (0, 1]` e `η > 0` existe `C > 0`
com `‖ζ(s)‖ ≤ C (1 + |Im s|)^η` na faixa `1/2 + δ ≤ Re s ≤ 3/4` (faixa não-vazia quando `δ ≤ 1/4`;
mesma prova de `norm_F_le`, com `exp(Re L)` no lugar de `exp(−Re L)`). -/
theorem norm_zeta_le_RH (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 < η) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 3 / 4 →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ η := by
  have hθ := θ₂_bounds hδ hδ1
  obtain ⟨K, hK⟩ := young (A := (10 / δ) ^ θ₂ δ) (θ := θ₂ δ) (η := η)
    (Real.rpow_nonneg (by positivity) _) hθ.1 hθ.2 hη
  set C₁ := Real.exp (η + K) * 12 ^ η with hC₁
  set Kc : Set ℂ := {s : ℂ | 1 / 2 + δ ≤ s.re} ∩ {s : ℂ | s.re ≤ 3 / 4} ∩ {s : ℂ | |s.im| ≤ 4}
    with hKcdef
  have hKc : IsCompact Kc := by
    refine (isCompact_closedBall (0 : ℂ) 10).of_isClosed_subset ?_ ?_
    · exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
    · rintro s ⟨⟨h1, h2⟩, h3⟩
      simp only [mem_setOf_eq] at h1 h2 h3
      rw [mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 3 + 4 := by
            gcongr
            rw [abs_le]; constructor <;> linarith
        _ ≤ 10 := by norm_num
  have hζc : ContinuousOn riemannZeta Kc := fun s hs => by
    have h2 := hs.1.2
    simp only [mem_setOf_eq] at h2
    have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h2; norm_num at h2
    exact (differentiableAt_riemannZeta hs1).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn hζc
  set C := max C₀ C₁ + 1 with hCdef
  have hCC₀ : C₀ ≤ C := by have := le_max_left C₀ C₁; linarith
  have hCC₁ : C₁ ≤ C := by have := le_max_right C₀ C₁; linarith
  have hC₁0 : 0 < C₁ := by positivity
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun s hs hs34 => ?_⟩
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCle : ∀ x, x ≤ C → x ≤ C * (1 + |s.im|) ^ η := fun x hx =>
    hx.trans (le_mul_of_one_le_right hCpos.le h1)
  rcases le_or_gt |s.im| 4 with h4 | h4
  · exact hCle _ ((hC₀ s ⟨⟨hs, hs34⟩, h4⟩).trans hCC₀)
  · set t := s.im with htdef
    have ht : 4 ≤ |t| := h4.le
    obtain ⟨L, hL0, hLe, hLd⟩ := existe_log_zeta hRH ht
    have hsc : s - c₀ t = ((s.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c₀, htdef]
    have hz : ‖s - c₀ t‖ ≤ 5 / 2 - δ := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hsmem : s ∈ ball (c₀ t) (5 / 2) := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hLs := norm_L_le hRH ht hδ hδ1 hL0 hLe hLd hz
    rw [← hLe s hsmem, Complex.norm_exp]
    set M := Real.log (2 * (|t| + 6)) with hM
    have hM0 : 0 ≤ M := (Real.log_pos (by linarith [abs_nonneg t])).le
    have hsplit : (10 * (M + 1) / δ) ^ θ₂ δ = (10 / δ) ^ θ₂ δ * (M + 1) ^ θ₂ δ := by
      rw [show 10 * (M + 1) / δ = (10 / δ) * (M + 1) by ring,
        Real.mul_rpow (by positivity) (by linarith)]
    have hY := hK (M + 1) (by linarith)
    have hexpM : Real.exp (η * M) = (2 * (|t| + 6)) ^ η := by
      rw [Real.rpow_def_of_pos (by positivity), hM, mul_comm]
    have hpow : (2 * (|t| + 6)) ^ η ≤ 12 ^ η * (1 + |t|) ^ η := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t]) hη.le
    calc Real.exp (L s).re ≤ Real.exp ‖L s‖ := by
          apply Real.exp_le_exp.mpr
          exact (le_abs_self _).trans (Complex.abs_re_le_norm (L s))
      _ ≤ Real.exp ((10 * (M + 1) / δ) ^ θ₂ δ) := Real.exp_le_exp.mpr hLs
      _ ≤ Real.exp (η * (M + 1) + K) := by rw [hsplit]; exact Real.exp_le_exp.mpr hY
      _ = Real.exp (η + K) * Real.exp (η * M) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := by
          rw [hexpM]; gcongr
      _ = C₁ * (1 + |t|) ^ η := by rw [hC₁]; ring
      _ ≤ C * (1 + |t|) ^ η := by gcongr

end ATK.RHLogZeta

#print axioms ATK.RHLogZeta.zeta_ne_zero_of_RH
#print axioms ATK.RHLogZeta.zeta₁_eq
#print axioms ATK.RHLogZeta.zeta₁_ne_zero_of_RH
#print axioms ATK.RHLogZeta.F_eq
#print axioms ATK.RHLogZeta.differentiableAt_F
#print axioms ATK.RHLogZeta.existe_log_bola
#print axioms ATK.RHLogZeta.tres_circulos
#print axioms ATK.RHLogZeta.soma_inv_sq_add_two
#print axioms ATK.RHLogZeta.norm_zeta_sub_one_le
#print axioms ATK.RHLogZeta.zeta_ne_zero_re_ge
#print axioms ATK.RHLogZeta.norm_log_zeta_le
#print axioms ATK.RHLogZeta.norm_inv_zeta_le_two
#print axioms ATK.RHLogZeta.young
#print axioms ATK.RHLogZeta.c₀_re
#print axioms ATK.RHLogZeta.c₀_im
#print axioms ATK.RHLogZeta.bola_props
#print axioms ATK.RHLogZeta.norm_zeta_le_bola
#print axioms ATK.RHLogZeta.log_zeta_c₀
#print axioms ATK.RHLogZeta.existe_log_zeta
#print axioms ATK.RHLogZeta.θ₂_bounds
#print axioms ATK.RHLogZeta.L_eq_log
#print axioms ATK.RHLogZeta.norm_L_le
#print axioms ATK.RHLogZeta.norm_F_le
#print axioms ATK.RHLogZeta.norm_zeta_le_RH
