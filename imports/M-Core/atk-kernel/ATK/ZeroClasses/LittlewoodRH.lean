import ATK.ZeroClasses.RegiaoLivre
import Mathlib.Analysis.Complex.Hadamard

/-!
# Littlewood sob RH: `1/ζ(σ + it) = O(|t|^ε)` em `σ ≥ ½ + δ` (rodada 38)

**Teorema (Littlewood 1912; Titchmarsh §14.2).** Sob RH, para todos `δ, ε > 0` existe `C` com

  `‖ζ(σ + it)⁻¹‖ ≤ C|t|^ε` e `‖ζ(σ + it)‖ ≤ C|t|^ε`   (`σ ≥ ½ + δ`, `|t| ≥ 1`).

A primeira é exatamente `ATK.FechamentoO1.LittlewoodSobRH` (`littlewoodSobRH`), uma das três peças de
`NecessidadeRH` que estavam BUILD_PENDING; com `HadamardXi` (rodada 33), sobra só `RiemannVonMangoldt` e a dedução
(`necessidade_iff_rvm`). A prova é a clássica:

1. **três círculos de Hadamard** (`tres_circulos`), a partir do teorema das três retas da Mathlib aplicado a
   `w ↦ g(c + e^w)` na faixa `log r₁ ≤ Re w ≤ log r₃`;
2. **o logaritmo num disco** (`log_bola`): `F ≠ 0` holomorfa em `B(c, R)` dá `F = F(c)·e^H`, `H(c) = 0`;
3. sob RH, `ζ ≠ 0` em `Re s > ½` (`zeta_ne_zero_RH`); no disco `‖s − (3 + it)‖ < 5/2 − δ/4`,
   `Re H = log|ζ/ζ(3 + it)| ≤ log(36|t|)`, e Borel–Carathéodory dá `|H| ≤ 20 log(36|t|)/δ` no círculo
   `5/2 − δ/2`; no disco `7/4` (dentro de `Re s > 5/4`, onde `|ζ| ≤ K`), `|H| ≤ M₁` no círculo `3/2`;
4. três círculos: `|H(σ + it)| ≤ M₁·(20 log(36|t|)/δ)^a` com `a = a(δ) < 1` (`nucleo`), e `B x^a ≤ εx + C`
   (`young_rpow`) troca `exp(B (log|t|)^a)` por `C|t|^ε` (`cota_grande`);
5. compacidade em `1 ≤ |t| ≤ 3` (`cota_compacta`) e `|ζ| ≥ 2 − π²/6` em `Re s ≥ 2`.

Classificação (rodada 38): **consequência** (de RH) e **alavanca** (fecha uma das três peças de `NecessidadeRH`).
RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.LittlewoodRH

/-! ## 1. Os três círculos de Hadamard -/

/-- **Três círculos de Hadamard**: se `g` é holomorfa em `B(c, R)`, `0 < r₁ < r₃ < R`, `‖g‖ ≤ M₁` em `‖z − c‖ = r₁`
e `‖g‖ ≤ M₃` em `‖z − c‖ = r₃`, então em `r₁ ≤ ‖z − c‖ ≤ r₃`,
`‖g(z)‖ ≤ M₁^{1−a} M₃^a`, `a = log(‖z − c‖/r₁)/log(r₃/r₁)`. -/
theorem tres_circulos {g : ℂ → ℂ} {c : ℂ} {R r₁ r₃ M₁ M₃ : ℝ} (hr₁ : 0 < r₁) (h13 : r₁ < r₃)
    (h3R : r₃ < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hM₁ : ∀ z ∈ sphere c r₁, ‖g z‖ ≤ M₁) (hM₃ : ∀ z ∈ sphere c r₃, ‖g z‖ ≤ M₃)
    {z : ℂ} (hz1 : r₁ ≤ ‖z - c‖) (hz3 : ‖z - c‖ ≤ r₃) :
    ‖g z‖ ≤ M₁ ^ (1 - Real.log (‖z - c‖ / r₁) / Real.log (r₃ / r₁)) *
      M₃ ^ (Real.log (‖z - c‖ / r₁) / Real.log (r₃ / r₁)) := by
  have hr₃ : 0 < r₃ := by linarith
  set l := Real.log r₁ with hl
  set u := Real.log r₃ with hu
  have hlu : l < u := Real.log_lt_log hr₁ h13
  set h : ℂ → ℂ := fun w => g (c + cexp w) with hh
  have hzpos : 0 < ‖z - c‖ := by linarith
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp hzpos
  set w := Complex.log (z - c) with hw
  have hwre : w.re = Real.log ‖z - c‖ := Complex.log_re _
  have hhw : h w = g z := by
    simp only [hh, hw, Complex.exp_log hz0, add_sub_cancel]
  have hU : ∀ v : ℂ, v.re ≤ u → c + cexp v ∈ ball c R := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp v.re ≤ Real.exp u := Real.exp_le_exp.mpr hv
      _ = r₃ := Real.exp_log hr₃
      _ < R := h3R
  have hdiff : DifferentiableOn ℂ h (Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    intro v hv
    have hv' : v.re ≤ u := hv.2
    have hgd := (hg (c + cexp v) (hU v hv')).differentiableAt (isOpen_ball.mem_nhds (hU v hv'))
    exact (hgd.comp v ((differentiableAt_const c).add
      Complex.differentiable_exp.differentiableAt)).differentiableWithinAt
  have hclos : closure (Complex.HadamardThreeLines.verticalStrip l u) ⊆
      Complex.HadamardThreeLines.verticalClosedStrip l u :=
    closure_minimal (fun v hv => ⟨hv.1.le, hv.2.le⟩) (isClosed_Icc.preimage continuous_re)
  have hd : DiffContOnCl ℂ h (Complex.HadamardThreeLines.verticalStrip l u) :=
    (hdiff.mono hclos).diffContOnCl
  obtain ⟨K, hK⟩ := (isCompact_closedBall c r₃).exists_bound_of_continuousOn
    (hg.continuousOn.mono (closedBall_subset_ball h3R))
  have hB : BddAbove ((norm ∘ h) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    apply hK
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp v.re ≤ Real.exp u := Real.exp_le_exp.mpr hv.2
      _ = r₃ := Real.exp_log hr₃
  have ha : ∀ v ∈ re ⁻¹' {l}, ‖h v‖ ≤ M₁ := by
    intro v hv
    apply hM₁
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hv
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp, hv, hl, Real.exp_log hr₁]
  have hb : ∀ v ∈ re ⁻¹' {u}, ‖h v‖ ≤ M₃ := by
    intro v hv
    apply hM₃
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hv
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp, hv, hu, Real.exp_log hr₃]
  have hwS : w ∈ Complex.HadamardThreeLines.verticalClosedStrip l u := by
    show w.re ∈ Icc l u
    rw [hwre]
    exact ⟨Real.log_le_log hr₁ hz1, Real.log_le_log hzpos hz3⟩
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hwS hd hB ha hb
  rw [hhw, hwre] at key
  have e : (Real.log ‖z - c‖ - l) / (u - l) = Real.log (‖z - c‖ / r₁) / Real.log (r₃ / r₁) := by
    rw [Real.log_div hzpos.ne' hr₁.ne', Real.log_div hr₃.ne' hr₁.ne']
  rwa [e] at key

/-! ## 2. O logaritmo num disco -/

/-- **Logaritmo num disco**: `F` holomorfa e sem zeros em `B(c, R)` é `F(c)·e^H` com `H` holomorfa, `H(c) = 0`. -/
theorem log_bola {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hF : DifferentiableOn ℂ F (ball c R))
    (h0 : ∀ z ∈ ball c R, F z ≠ 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball c R) ∧ H c = 0 ∧
      ∀ z ∈ ball c R, F z = F c * cexp (H z) := by
  have hFa : ∀ z ∈ ball c R, AnalyticAt ℂ F z := fun z hz =>
    hF.analyticAt (isOpen_ball.mem_nhds hz)
  have hΦ : DifferentiableOn ℂ (fun z => deriv F z / F z) (ball c R) := by
    intro z hz
    have hza := hFa z hz
    exact (hza.deriv.differentiableAt.div hza.differentiableAt (h0 z hz)).differentiableWithinAt
  obtain ⟨H, hH0, hH⟩ := (hΦ.isExactOn_ball).with_val_at c 0
  have hHd : DifferentiableOn ℂ H (ball c R) := fun z hz =>
    (hH z hz).differentiableAt.differentiableWithinAt
  refine ⟨H, hHd, hH0, fun z hz => ?_⟩
  have hd : ∀ w ∈ ball c R, HasDerivAt (fun w => F w * cexp (-H w)) 0 w := by
    intro w hw
    have h1 := (hFa w hw).differentiableAt.hasDerivAt
    have h2 := ((hH w hw).neg).cexp
    convert h1.mul h2 using 1
    field_simp [h0 w hw]
    ring
  have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (mem_ball_self hR)
  have hK : F z * cexp (-H z) = F c := by
    rw [hc, hH0, neg_zero, Complex.exp_zero, mul_one]
  calc F z = F z * cexp (-H z) * cexp (H z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = F c * cexp (H z) := by rw [hK]

/-! ## 3. Ingredientes sobre ζ -/

/-- Sob RH, `ζ(s) ≠ 0` em `Re s > ½`. -/
theorem zeta_ne_zero_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  · have hs1 : s ≠ 1 := by
      rintro rfl
      simp at h1
    have hnt : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      have e : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [e] at hs
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have := hRH s hz hnt hs1
    linarith

/-- `|ζ(s)|` é limitada em `Re s ≥ 5/4`. -/
theorem cota_zeta_re : ∃ K : ℝ, ∀ s : ℂ, 5 / 4 ≤ s.re → ‖riemannZeta s‖ ≤ K := by
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4))
    refine this.congr fun n => ?_
    push_cast
    ring
  refine ⟨∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ), fun s hs => ?_⟩
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith)]
  refine tsum_of_norm_bounded hsum.hasSum fun n => ?_
  simp only [norm_div, norm_one]
  have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_natCast_cpow_of_pos (by omega)]
  have e2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [e2]
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 hs)

theorem um_terco_le : (1 : ℝ) / 3 ≤ 2 - π ^ 2 / 6 := by
  have := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

/-- **Young**: para `0 ≤ a < 1`, `B x^a ≤ εx + C` em `x ≥ 0`. -/
theorem young_rpow {a B ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → B * x ^ a ≤ ε * x + C := by
  have hBε : 0 ≤ B / ε := div_nonneg hB hε.le
  set X₀ : ℝ := (B / ε) ^ (1 / (1 - a)) + 1 with hX₀
  have hY0 : 0 ≤ (B / ε) ^ (1 / (1 - a)) := Real.rpow_nonneg hBε _
  have hX₀pos : 0 < X₀ := by linarith
  have hC0 : 0 ≤ B * X₀ ^ a := mul_nonneg hB (Real.rpow_nonneg hX₀pos.le _)
  refine ⟨B * X₀ ^ a, fun x hx => ?_⟩
  rcases le_or_gt x X₀ with h | h
  · have : x ^ a ≤ X₀ ^ a := Real.rpow_le_rpow hx h ha0
    have := mul_le_mul_of_nonneg_left this hB
    nlinarith
  · have hxpos : 0 < x := by linarith
    have h1a : 0 < 1 - a := by linarith
    have hY : B / ε ≤ x ^ (1 - a) := by
      have hle : (B / ε) ^ (1 / (1 - a)) ≤ x := by linarith
      have := Real.rpow_le_rpow hY0 hle h1a.le
      rwa [← Real.rpow_mul hBε, one_div_mul_cancel h1a.ne', Real.rpow_one] at this
    have hxa : x ^ (1 - a) * x ^ a = x := by
      rw [← Real.rpow_add hxpos, sub_add_cancel, Real.rpow_one]
    have hB' : B ≤ ε * x ^ (1 - a) := by
      rw [div_le_iff₀ hε] at hY
      linarith
    have hxa0 : 0 ≤ x ^ a := Real.rpow_nonneg hx a
    calc B * x ^ a ≤ ε * x ^ (1 - a) * x ^ a := mul_le_mul_of_nonneg_right hB' hxa0
      _ = ε * x := by rw [mul_assoc, hxa]
      _ ≤ ε * x + B * X₀ ^ a := by linarith

/-! ## 4. O núcleo: três círculos para `log ζ` -/

/-- **O núcleo**: sob RH, para `0 < δ ≤ ½`, `½ + δ ≤ σ ≤ 2` e `|t| ≥ 3`,
`‖ζ(σ + it)⁻¹‖ ≤ 3 e^X` e `‖ζ(σ + it)‖ ≤ K e^X` com `X = 12 max(log 3K, 1)·(20 log(36|t|)/δ)^a`,
`a = log((5/2 − δ)/(3/2))/log((5/2 − δ/2)/(3/2)) < 1`. -/
theorem nucleo (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {K₁ : ℝ}
    (hK₁ : ∀ s : ℂ, 5 / 4 ≤ s.re → ‖riemannZeta s‖ ≤ K₁) {σ t : ℝ} (h1 : 1 / 2 + δ ≤ σ) (h2 : σ ≤ 2)
    (ht : 3 ≤ |t|) :
    ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ 3 * Real.exp (12 * max (Real.log (3 * K₁)) 1 *
        (20 * Real.log (36 * |t|) / δ) ^
          (Real.log ((5 / 2 - δ) / (3 / 2)) / Real.log ((5 / 2 - δ / 2) / (3 / 2)))) ∧
      ‖riemannZeta (σ + t * I)‖ ≤ K₁ * Real.exp (12 * max (Real.log (3 * K₁)) 1 *
        (20 * Real.log (36 * |t|) / δ) ^
          (Real.log ((5 / 2 - δ) / (3 / 2)) / Real.log ((5 / 2 - δ / 2) / (3 / 2)))) := by
  set c : ℂ := 3 + t * I with hc
  set R : ℝ := 5 / 2 - δ / 4 with hR
  have hRpos : 0 < R := by linarith
  have hcre : c.re = 3 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have coord : ∀ z : ℂ, |z.re - 3| ≤ ‖z - c‖ ∧ |z.im - t| ≤ ‖z - c‖ := by
    intro z
    have h1 := Complex.abs_re_le_norm (z - c)
    have h2 := Complex.abs_im_le_norm (z - c)
    rw [sub_re, hcre] at h1
    rw [sub_im, hcim] at h2
    exact ⟨h1, h2⟩
  have geo : ∀ z ∈ ball c R, 1 / 2 + δ / 4 < z.re ∧ z.re < 3 + R ∧ |t| - R < |z.im| ∧
      |z.im| < |t| + R := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    obtain ⟨h1, h2⟩ := coord z
    have hr := abs_lt.mp (lt_of_le_of_lt h1 hz)
    have hi := abs_lt.mp (lt_of_le_of_lt h2 hz)
    have hi1 := abs_sub_abs_le_abs_sub t z.im
    have hi2 := abs_sub_abs_le_abs_sub z.im t
    rw [abs_sub_comm] at hi1
    refine ⟨by linarith [hr.1], by linarith [hr.2], ?_, ?_⟩
    · linarith [lt_of_le_of_lt h2 hz]
    · linarith [lt_of_le_of_lt h2 hz]
  have hne1 : ∀ z ∈ ball c R, z ≠ 1 := by
    intro z hz h
    have := (geo z hz).2.2.1
    rw [h, one_im, abs_zero] at this
    linarith
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c R) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hnz : ∀ z ∈ ball c R, riemannZeta z ≠ 0 := fun z hz =>
    zeta_ne_zero_RH hRH (by linarith [(geo z hz).1])
  obtain ⟨H, hHd, hH0, hHe⟩ := log_bola hRpos hdiff hnz
  have hζc : 1 / 3 ≤ ‖riemannZeta c‖ :=
    um_terco_le.trans (ATK.ZeroClasses.Expoente.zeta_lb_re_ge_dois (by rw [hcre]; norm_num))
  have hζc0 : 0 < ‖riemannZeta c‖ := by linarith
  have hζcK : ‖riemannZeta c‖ ≤ K₁ := hK₁ c (by rw [hcre]; norm_num)
  have hnorm : ∀ z ∈ ball c R, ‖riemannZeta z‖ = ‖riemannZeta c‖ * Real.exp (H z).re := by
    intro z hz
    rw [hHe z hz, norm_mul, Complex.norm_exp]
  have hreH : ∀ z ∈ ball c R, ∀ K : ℝ, ‖riemannZeta z‖ ≤ K → (H z).re ≤ Real.log (3 * K) := by
    intro z hz K hK
    have hz0 : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr (hnz z hz)
    have hK0 : 0 < K := lt_of_lt_of_le hz0 hK
    rw [Real.le_log_iff_exp_le (by positivity)]
    have e : Real.exp (H z).re = ‖riemannZeta z‖ / ‖riemannZeta c‖ := by
      rw [hnorm z hz]
      field_simp
    rw [e, div_le_iff₀ hζc0]
    nlinarith [mul_le_mul_of_nonneg_left hζc hK0.le]
  have hbig : ∀ z ∈ ball c R, ‖riemannZeta z‖ ≤ 12 * |t| := by
    intro z hz
    obtain ⟨hre, hre2, hi1, hi2⟩ := geo z hz
    have hcz := ATK.ZeroClasses.Jensen.cota_zeta (by linarith : 1 / 2 ≤ z.re) (hne1 z hz)
    rw [norm_mul] at hcz
    have hn1 : 1 / 2 ≤ ‖z - 1‖ := by
      have h := Complex.abs_im_le_norm (z - 1)
      rw [sub_im, one_im, sub_zero] at h
      linarith
    have hzn : ‖z‖ ≤ |t| + 8 := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos (by linarith)] at h
      linarith
    have hz1 : ‖riemannZeta z‖ ≤ 1 / ‖z - 1‖ + (1 / 2 + 3 * ‖z‖) := by
      rw [div_add' _ _ _ (by linarith), le_div_iff₀ (by linarith)]
      nlinarith
    have hz2 : 1 / ‖z - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  set A : ℝ := Real.log (36 * |t|) with hA
  have hA1 : 1 ≤ A := by
    rw [hA, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hreA : ∀ z ∈ ball c R, (H z).re ≤ A := fun z hz => by
    have h := hreH z hz (12 * |t|) (hbig z hz)
    rwa [show 3 * (12 * |t|) = 36 * |t| by ring] at h
  have BC : ∀ ρ A' : ℝ, 0 < ρ → ρ ≤ R → 0 < A' → (∀ z ∈ ball c ρ, (H z).re ≤ A') →
      ∀ z : ℂ, ‖z - c‖ < ρ → ‖H z‖ ≤ 2 * A' * ‖z - c‖ / (ρ - ‖z - c‖) := by
    intro ρ A' hρ hρR hA' hre z hz
    have hdiff' : DifferentiableOn ℂ (fun w => H (c + w)) (ball 0 ρ) := by
      intro w hw
      have hw' : c + w ∈ ball c R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact lt_of_lt_of_le (mem_ball_zero_iff.mp hw) hρR
      exact (((hHd (c + w) hw').differentiableAt (isOpen_ball.mem_nhds hw')).comp w
        ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
    have hmaps : MapsTo (fun w => H (c + w)) (ball 0 ρ) {z | z.re ≤ A'} := by
      intro w hw
      show (H (c + w)).re ≤ A'
      apply hre
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact mem_ball_zero_iff.mp hw
    have hzz : z - c ∈ ball (0 : ℂ) ρ := by rw [mem_ball_zero_iff]; exact hz
    have := Complex.borelCaratheodory_zero hA' hdiff' hmaps hρ hzz (by simp [hH0])
    simpa only [add_sub_cancel] using this
  have mono : ∀ A' ρ r x : ℝ, 0 ≤ A' → 0 ≤ x → x ≤ r → r < ρ →
      2 * A' * x / (ρ - x) ≤ 2 * A' * r / (ρ - r) := by
    intro A' ρ r x hA' hx hxr hr
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by linarith) (by linarith)
  set r₃ : ℝ := 5 / 2 - δ / 2 with hr₃
  have hM₃ : ∀ z ∈ sphere c r₃, ‖H z‖ ≤ 20 * A / δ := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have h := BC R A hRpos le_rfl (by linarith) hreA z (by rw [hz]; linarith)
    rw [hz] at h
    calc ‖H z‖ ≤ 2 * A * r₃ / (R - r₃) := h
      _ ≤ 20 * A / δ := by
          rw [div_le_div_iff₀ (by linarith) hδ, hR, hr₃]
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ A) hδ.le) hδ.le]
  set A₁ : ℝ := max (Real.log (3 * K₁)) 1 with hA₁
  have hA₁1 : 1 ≤ A₁ := le_max_right _ _
  have hsmall : ∀ z : ℂ, ‖z - c‖ ≤ 3 / 2 → ‖H z‖ ≤ 12 * A₁ := by
    intro z hz
    have hre1 : ∀ w ∈ ball c (7 / 4), (H w).re ≤ A₁ := by
      intro w hw
      have hwR : w ∈ ball c R := ball_subset_ball (by linarith) hw
      have hw54 : 5 / 4 ≤ w.re := by
        rw [mem_ball, dist_eq_norm] at hw
        have := abs_lt.mp (lt_of_le_of_lt (coord w).1 hw)
        linarith [this.1]
      exact le_trans (hreH w hwR K₁ (hK₁ w hw54)) (le_max_left _ _)
    have h := BC (7 / 4) A₁ (by norm_num) (by linarith) (by linarith) hre1 z (by linarith)
    calc ‖H z‖ ≤ 2 * A₁ * ‖z - c‖ / (7 / 4 - ‖z - c‖) := h
      _ ≤ 2 * A₁ * (3 / 2) / (7 / 4 - 3 / 2) := mono _ _ _ _ (by linarith) (norm_nonneg _) hz (by norm_num)
      _ = 12 * A₁ := by ring
  set z : ℂ := σ + t * I with hzdef
  have hzc : ‖z - c‖ = 3 - σ := by
    have e : z - c = ((σ - 3 : ℝ) : ℂ) := by
      rw [hzdef, hc]
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hzR : z ∈ ball c R := by
    rw [mem_ball, dist_eq_norm, hzc]
    linarith
  set D : ℝ := Real.log ((5 / 2 - δ / 2) / (3 / 2)) with hD
  set a : ℝ := Real.log ((5 / 2 - δ) / (3 / 2)) / D with ha
  have hDpos : 0 < D := Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have ha0 : 0 ≤ a := div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)) hDpos.le
  set M₁ : ℝ := 12 * A₁ with hM₁
  set M₃ : ℝ := 20 * A / δ with hM₃def
  have hM₁1 : 1 ≤ M₁ := by linarith
  have hM₃1 : 1 ≤ M₃ := by
    rw [hM₃def, le_div_iff₀ hδ]
    linarith
  have hHz : ‖H z‖ ≤ M₁ * M₃ ^ a := by
    rcases le_or_gt (3 - σ) (3 / 2) with hs | hs
    · calc ‖H z‖ ≤ M₁ := hsmall z (by rw [hzc]; exact hs)
        _ ≤ M₁ * M₃ ^ a := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hM₃1 ha0)
    · have h3c := tres_circulos (g := H) (c := c) (R := R) (r₁ := 3 / 2) (r₃ := r₃) (M₁ := M₁) (M₃ := M₃)
        (by norm_num) (by linarith) (by linarith) hHd
        (fun w hw => hsmall w (by rw [mem_sphere, dist_eq_norm] at hw; linarith)) hM₃
        (z := z) (by rw [hzc]; linarith) (by rw [hzc]; linarith)
      rw [hzc] at h3c
      set b : ℝ := Real.log ((3 - σ) / (3 / 2)) / Real.log (r₃ / (3 / 2)) with hb
      have hb1 : b ≤ a := by
        rw [hb, ha, hD, hr₃]
        exact div_le_div_of_nonneg_right
          (Real.log_le_log (by rw [lt_div_iff₀ (by norm_num)]; linarith)
            (div_le_div_of_nonneg_right (by linarith) (by norm_num))) hDpos.le
      have hb0 : 0 ≤ b := div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith))
        (by rw [hr₃]; exact hDpos.le)
      have hb1' : b ≤ 1 := by
        rw [hb, div_le_one (by rw [hr₃]; exact hDpos)]
        exact Real.log_le_log (by rw [lt_div_iff₀ (by norm_num)]; linarith)
          (div_le_div_of_nonneg_right (by linarith) (by norm_num))
      have e1 : M₁ ^ (1 - b) ≤ M₁ := by
        calc M₁ ^ (1 - b) ≤ M₁ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM₁1 (by linarith)
          _ = M₁ := Real.rpow_one _
      have e2 : M₃ ^ b ≤ M₃ ^ a := Real.rpow_le_rpow_of_exponent_le hM₃1 hb1
      calc ‖H z‖ ≤ M₁ ^ (1 - b) * M₃ ^ b := h3c
        _ ≤ M₁ * M₃ ^ a := mul_le_mul e1 e2 (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hexp : Real.exp ‖H z‖ ≤ Real.exp (M₁ * M₃ ^ a) := Real.exp_le_exp.mpr hHz
  refine ⟨?_, ?_⟩
  · rw [norm_inv, hnorm z hzR, mul_inv, ← Real.exp_neg]
    have hle : Real.exp (-(H z).re) ≤ Real.exp ‖H z‖ :=
      Real.exp_le_exp.mpr (by linarith [(abs_le.mp (Complex.abs_re_le_norm (H z))).1])
    have h3 : ‖riemannZeta c‖⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ hζc0 (by norm_num)]
      linarith
    calc ‖riemannZeta c‖⁻¹ * Real.exp (-(H z).re) ≤ 3 * Real.exp ‖H z‖ :=
          mul_le_mul h3 hle (Real.exp_pos _).le (by norm_num)
      _ ≤ 3 * Real.exp (M₁ * M₃ ^ a) := by gcongr
  · rw [hnorm z hzR]
    have hle : Real.exp (H z).re ≤ Real.exp ‖H z‖ :=
      Real.exp_le_exp.mpr (Complex.re_le_norm (H z))
    calc ‖riemannZeta c‖ * Real.exp (H z).re ≤ K₁ * Real.exp ‖H z‖ :=
          mul_le_mul hζcK hle (Real.exp_pos _).le (by linarith)
      _ ≤ K₁ * Real.exp (M₁ * M₃ ^ a) := by gcongr; linarith

/-! ## 5. De `exp(B (log|t|)^a)` a `C|t|^ε` -/

/-- **Para `|t| ≥ 3`**: sob RH, `‖ζ(σ + it)^{±1}‖ ≤ C|t|^ε` em `½ + δ ≤ σ ≤ 2`. -/
theorem cota_grande (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → 3 ≤ |t| →
      ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * |t| ^ ε ∧ ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε := by
  obtain ⟨K₁, hK₁⟩ := cota_zeta_re
  have hK₁0 : 0 ≤ K₁ := le_trans (norm_nonneg _) (hK₁ 2 (by norm_num))
  set a := Real.log ((5 / 2 - δ) / (3 / 2)) / Real.log ((5 / 2 - δ / 2) / (3 / 2)) with ha
  have hD : 0 < Real.log ((5 / 2 - δ / 2) / (3 / 2)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have ha0 : 0 ≤ a := div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)) hD.le
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hD]
    exact Real.log_lt_log (by rw [lt_div_iff₀ (by norm_num)]; linarith)
      (div_lt_div_of_pos_right (by linarith) (by norm_num))
  have hA₁ : 0 ≤ max (Real.log (3 * K₁)) 1 := le_trans zero_le_one (le_max_right _ _)
  set B := 12 * max (Real.log (3 * K₁)) 1 * (20 / δ) ^ a with hBdef
  have hB : 0 ≤ B := mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  obtain ⟨Cy, hCy⟩ := young_rpow ha0 ha1 hB hε
  set C₀ := Real.exp (ε * Real.log 36 + Cy) with hC₀
  refine ⟨max 3 K₁ * C₀, fun σ t h1 h2 ht => ?_⟩
  obtain ⟨hn1, hn2⟩ := nucleo hRH hδ hδ2 hK₁ h1 h2 ht
  set x := Real.log (36 * |t|) with hx
  have htpos : 0 < |t| := by linarith
  have hx0 : 0 ≤ x := Real.log_nonneg (by linarith)
  have hsplit : (20 * x / δ) ^ a = (20 / δ) ^ a * x ^ a := by
    rw [show 20 * x / δ = (20 / δ) * x by ring, Real.mul_rpow (by positivity) hx0]
  have hy := hCy x hx0
  have hxlog : x = Real.log 36 + Real.log |t| := Real.log_mul (by norm_num) htpos.ne'
  rw [hxlog, mul_add] at hy
  have htε : |t| ^ ε = Real.exp (ε * Real.log |t|) := by
    rw [Real.rpow_def_of_pos htpos, mul_comm]
  have hX : Real.exp (12 * max (Real.log (3 * K₁)) 1 * (20 * x / δ) ^ a) ≤ C₀ * |t| ^ ε := by
    rw [htε, hC₀, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hsplit, show 12 * max (Real.log (3 * K₁)) 1 * ((20 / δ) ^ a * x ^ a) = B * x ^ a by
      rw [hBdef]; ring]
    rw [hxlog]
    linarith
  have hC₀0 : 0 ≤ C₀ * |t| ^ ε := by positivity
  refine ⟨?_, ?_⟩
  · calc ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ 3 * Real.exp (12 * max (Real.log (3 * K₁)) 1 *
          (20 * x / δ) ^ a) := hn1
      _ ≤ 3 * (C₀ * |t| ^ ε) := by gcongr
      _ ≤ max 3 K₁ * C₀ * |t| ^ ε := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hC₀0
  · calc ‖riemannZeta (σ + t * I)‖ ≤ K₁ * Real.exp (12 * max (Real.log (3 * K₁)) 1 *
          (20 * x / δ) ^ a) := hn2
      _ ≤ K₁ * (C₀ * |t| ^ ε) := by gcongr
      _ ≤ max 3 K₁ * C₀ * |t| ^ ε := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hC₀0

/-- **Para `1 ≤ |t| ≤ 3`**: sob RH, `ζ^{±1}` é limitada em `½ + δ ≤ σ ≤ 2` (compacidade). -/
theorem cota_compacta (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → 1 ≤ |t| → |t| ≤ 3 →
      ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C ∧ ‖riemannZeta (σ + t * I)‖ ≤ C := by
  set K : Set (ℝ × ℝ) := Icc (1 / 2 + δ) 2 ×ˢ {t : ℝ | 1 ≤ |t| ∧ |t| ≤ 3} with hKdef
  have hK : IsCompact K := by
    refine isCompact_Icc.prod (Metric.isCompact_of_isClosed_isBounded ?_ ?_)
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · exact (Metric.isBounded_Icc (-3 : ℝ) 3).subset fun t ht => abs_le.mp ht.2
  have hpt : ∀ p ∈ K, (p.1 : ℂ) + p.2 * I ≠ 1 ∧ riemannZeta (p.1 + p.2 * I) ≠ 0 := by
    intro p hp
    refine ⟨fun h => ?_, zeta_ne_zero_RH hRH (by simp; linarith [hp.1.1])⟩
    have := congrArg Complex.im h
    simp at this
    have h1 := hp.2.1
    rw [this, abs_zero] at h1
    linarith
  have hc : ∀ p : ℝ × ℝ, ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) p := fun p => by
    fun_prop
  have hζ : ContinuousOn (fun p : ℝ × ℝ => riemannZeta (p.1 + p.2 * I)) K := fun p hp =>
    ((differentiableAt_riemannZeta (hpt p hp).1).continuousAt.comp
      (f := fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) (hc p)).continuousWithinAt
  have hζi : ContinuousOn (fun p : ℝ × ℝ => (riemannZeta (p.1 + p.2 * I))⁻¹) K := fun p hp =>
    (((differentiableAt_riemannZeta (hpt p hp).1).continuousAt.comp
      (f := fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) (hc p)).inv₀
      (hpt p hp).2).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hζi
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hζ
  exact ⟨max C₁ C₂, fun σ t h1 h2 h3 h4 =>
    ⟨(hC₁ (σ, t) ⟨⟨h1, h2⟩, h3, h4⟩).trans (le_max_left _ _),
      (hC₂ (σ, t) ⟨⟨h1, h2⟩, h3, h4⟩).trans (le_max_right _ _)⟩⟩

/-! ## 6. Os teoremas -/

/-- **Littlewood e Lindelöf fora da reta, sob RH**: para `δ, ε > 0` existe `C` com `‖ζ(σ + it)^{±1}‖ ≤ C|t|^ε` em
`σ ≥ ½ + δ`, `|t| ≥ 1`. -/
theorem cota_sob_RH (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → 1 ≤ |t| →
      ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * |t| ^ ε ∧ ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε := by
  set δ' := min δ (1 / 2) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'2 : δ' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C₁, hC₁⟩ := cota_grande hRH hδ' hδ'2 hε
  obtain ⟨C₂, hC₂⟩ := cota_compacta hRH hδ'
  obtain ⟨K₁, hK₁⟩ := cota_zeta_re
  set C := max (max C₁ C₂) (max 3 K₁) with hC
  have hC3 : 3 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨C, fun σ t hσ ht => ?_⟩
  have hσ' : 1 / 2 + δ' ≤ σ := le_trans (by linarith [min_le_left δ (1 / 2)]) hσ
  have ht1 : 1 ≤ |t| ^ ε := Real.one_le_rpow ht hε.le
  have htε : 0 ≤ |t| ^ ε := by positivity
  have hC0 : 0 ≤ C := by linarith
  rcases le_or_gt σ 2 with h2 | h2
  · rcases le_or_gt |t| 3 with h3 | h3
    · obtain ⟨a1, a2⟩ := hC₂ σ t hσ' h2 ht h3
      have hCC : C₂ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
      exact ⟨a1.trans (hCC.trans (le_mul_of_one_le_right hC0 ht1)),
        a2.trans (hCC.trans (le_mul_of_one_le_right hC0 ht1))⟩
    · obtain ⟨a1, a2⟩ := hC₁ σ t hσ' h2 h3.le
      have hCC : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
      exact ⟨a1.trans (mul_le_mul_of_nonneg_right hCC htε),
        a2.trans (mul_le_mul_of_nonneg_right hCC htε)⟩
  · have hre : 2 ≤ ((σ : ℂ) + t * I).re := by simp; linarith
    have hlb := um_terco_le.trans (ATK.ZeroClasses.Expoente.zeta_lb_re_ge_dois hre)
    have hub := hK₁ ((σ : ℂ) + t * I) (by linarith)
    have hK3 : K₁ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨?_, hub.trans (hK3.trans (le_mul_of_one_le_right hC0 ht1))⟩
    rw [norm_inv]
    have : ‖riemannZeta ((σ : ℂ) + t * I)‖⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact this.trans (hC3.trans (le_mul_of_one_le_right hC0 ht1))

/-- **`LittlewoodSobRH`** (`ATK.FechamentoO1`): sob RH, `1/ζ(σ + it) = O(|t|^ε)` em `σ ≥ ½ + δ`. -/
theorem littlewoodSobRH : ATK.FechamentoO1.LittlewoodSobRH := by
  intro hRH δ hδ ε hε
  obtain ⟨C, hC⟩ := cota_sob_RH hRH hδ hε
  exact ⟨C, fun σ t h1 h2 => (hC σ t h1 h2).1⟩

/-- **Lindelöf fora da reta, sob RH**: `ζ(σ + it) = O(|t|^ε)` em `σ ≥ ½ + δ`. -/
theorem lindelof_fora_sob_RH (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → 1 ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε := by
  obtain ⟨C, hC⟩ := cota_sob_RH hRH hδ hε
  exact ⟨C, fun σ t h1 h2 => (hC σ t h1 h2).2⟩

/-- **`NecessidadeRH` reduz-se a Riemann–von Mangoldt e à dedução**: `HadamardXi` (rodada 33) e
`LittlewoodSobRH` (aqui) já são teoremas. -/
theorem necessidade_iff_rvm : ATK.FechamentoO1.NecessidadeRH ↔
    ATK.FechamentoO1.RiemannVonMangoldt ∧
      (ATK.FechamentoO1.RiemannVonMangoldt → ATK.FechamentoO1.HadamardXi →
        ATK.FechamentoO1.LittlewoodSobRH → RiemannHypothesis → ATK.NecessidadeBD.EntradasNecessidade) := by
  rw [ATK.ZeroClasses.Hadamard.necessidade_iff]
  exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, littlewoodSobRH, h3⟩⟩

end ATK.ZeroClasses.LittlewoodRH

#print axioms ATK.ZeroClasses.LittlewoodRH.tres_circulos
#print axioms ATK.ZeroClasses.LittlewoodRH.log_bola
#print axioms ATK.ZeroClasses.LittlewoodRH.zeta_ne_zero_RH
#print axioms ATK.ZeroClasses.LittlewoodRH.cota_zeta_re
#print axioms ATK.ZeroClasses.LittlewoodRH.um_terco_le
#print axioms ATK.ZeroClasses.LittlewoodRH.young_rpow
#print axioms ATK.ZeroClasses.LittlewoodRH.nucleo
#print axioms ATK.ZeroClasses.LittlewoodRH.cota_grande
#print axioms ATK.ZeroClasses.LittlewoodRH.cota_compacta
#print axioms ATK.ZeroClasses.LittlewoodRH.cota_sob_RH
#print axioms ATK.ZeroClasses.LittlewoodRH.littlewoodSobRH
#print axioms ATK.ZeroClasses.LittlewoodRH.lindelof_fora_sob_RH
#print axioms ATK.ZeroClasses.LittlewoodRH.necessidade_iff_rvm
