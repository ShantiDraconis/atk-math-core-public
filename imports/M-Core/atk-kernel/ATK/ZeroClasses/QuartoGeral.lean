import ATK.ZeroClasses.QuartoAval
import ATK.ZeroClasses.FinalAudit

/-!
# Ferramentas gerais para certificar `ζ ≠ 0` num segmento vertical (rodada 28)

* **cota grosseira** (`cota_geral`, `cotaQ`, `cotaQ_spec`): para `Re w > 0`, `w ≠ 1`, `‖w‖ ≤ R` e
  `‖w − 1‖ ≥ d`, `‖ζ(w)‖ ≤ N + N/d + ½ + Σ_{j=2}^{M} |B_j|/j!·(R)_{j−1}·N^{1−j} + (R)_M/M!·C_M·N^{1−M}/(M − 1)`,
  com o valor racional `cotaQ` calculado pelo kernel;
* **a região de uma peça** (`Reg`, `reg_props`): `|Re w − ¼| ≤ r`, `a − r ≤ Im w ≤ b + r`;
* **Cauchy** (`deriv_cota`): `‖ζ′‖ ≤ B/r` no segmento `seg a b = {¼ + it : a ≤ t ≤ b}`;
* **a peça** (`peca`): malha com passo `h`, valores `‖ζ(c)‖ ≥ (B/r)h + δ` nos centros ⟹ `‖ζ‖ ≥ δ` no segmento;
* **cobertura** (`cobre`, `centros`, `cobre_seg`, `centros_seg`): os centros `a + h(2k + 1)`, `h = (b − a)/(2n)`.
-/

open Complex Metric Set

namespace ATK.ZeroClasses.Quarto

open ATK.Cert ATK.EMGeral ATK.ZeroCert ATK.ZeroClasses.Regions

/-! ## 5. Cota grosseira de `ζ` -/

/-- `(R)_k = R(R+1)⋯(R+k−1)`. -/
noncomputable def pochR (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => pochR R k * (R + k)

theorem pochR_nonneg {R : ℝ} (hR : 0 ≤ R) : ∀ k, 0 ≤ pochR R k
  | 0 => by simp [pochR]
  | k + 1 => by
    simp only [pochR]
    exact mul_nonneg (pochR_nonneg hR k) (by positivity)

theorem norm_poch_le {w : ℂ} {R : ℝ} (hR : ‖w‖ ≤ R) : ∀ k, ‖poch w k‖ ≤ pochR R k
  | 0 => by simp [poch, pochR]
  | k + 1 => by
    simp only [poch, pochR]
    rw [norm_mul]
    have h1 : ‖w + k‖ ≤ R + k := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_natCast]
      linarith
    exact mul_le_mul (norm_poch_le hR k) h1 (norm_nonneg _) (pochR_nonneg ((norm_nonneg w).trans hR) k)

/-- **Cota grosseira geral.** -/
theorem cota_geral {w : ℂ} {N M : ℕ} {R d : ℝ} (hN : 1 ≤ N) (hM : 2 ≤ M)
    (h0 : 0 < w.re) (hw1 : w ≠ 1) (hR : ‖w‖ ≤ R) (hd : 0 < d) (hdw : d ≤ ‖w - 1‖) :
    ‖riemannZeta w‖ ≤ N + N / d + 1 / 2 +
      (∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) *
        ((N : ℝ) ^ (j - 1))⁻¹) +
      pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNp : 0 < N := by omega
  have hR0 : 0 ≤ R := (norm_nonneg w).trans hR
  have hE := norm_zeta_sub_EM_le h0 hw1 hN (by omega : 1 ≤ M)
  have hS : ‖∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ Finset.range N, ‖((n : ℂ) + 1) ^ (-w)‖ ≤ 1 := by
      intro n _
      have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_natCast_cpow_of_pos (by omega)]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ n + 1))
      simp only [neg_re]
      linarith
    calc ∑ n ∈ Finset.range N, ‖((n : ℂ) + 1) ^ (-w)‖ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum this
      _ = N := by simp
  have hP : ‖(N : ℂ) ^ (1 - w) / (w - 1)‖ ≤ N / d := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hNp]
    have h1 : (N : ℝ) ^ (1 - w).re ≤ N := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 (show (1 - w).re ≤ 1 by simp; linarith)
      simpa using this
    have hw1n : 0 < ‖w - 1‖ := lt_of_lt_of_le hd hdw
    calc (N : ℝ) ^ (1 - w).re / ‖w - 1‖ ≤ N / ‖w - 1‖ := div_le_div_of_nonneg_right h1 hw1n.le
      _ ≤ N / d := div_le_div_of_nonneg_left hN0.le hd hdw
  have hH : ‖(N : ℂ) ^ (-w) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hNp]
    have : (N : ℝ) ^ (-w).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by simp only [neg_re]; linarith)
    rw [Complex.norm_ofNat]
    linarith
  have hJ : ‖∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) * poch w (j - 1) *
      (N : ℂ) ^ (-w - ((j - 1 : ℕ) : ℂ))‖ ≤ ∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| /
        (j.factorial : ℝ) * pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, norm_div, Complex.norm_natCast_cpow_of_pos hNp]
    have hb : ‖(bernoulli j : ℂ)‖ = |(bernoulli j : ℝ)| := by
      rw [show ((bernoulli j : ℚ) : ℂ) = (((bernoulli j : ℚ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
    have hf : ‖(j.factorial : ℂ)‖ = (j.factorial : ℝ) := Complex.norm_natCast _
    rw [hb, hf]
    have hpw : (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re ≤ ((N : ℝ) ^ (j - 1))⁻¹ := by
      have e : (-w - ((j - 1 : ℕ) : ℂ)).re = -w.re - ((j - 1 : ℕ) : ℝ) := by simp
      rw [e]
      have := Real.rpow_le_rpow_of_exponent_le hN1
        (show -w.re - ((j - 1 : ℕ) : ℝ) ≤ -((j - 1 : ℕ) : ℝ) by linarith)
      rw [Real.rpow_neg hN0.le, Real.rpow_natCast] at this
      exact this
    have hp := norm_poch_le hR (j - 1)
    have hc : 0 ≤ |(bernoulli j : ℝ)| / (j.factorial : ℝ) := by positivity
    have hpow0 : 0 ≤ (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re := Real.rpow_nonneg hN0.le _
    calc |(bernoulli j : ℝ)| / (j.factorial : ℝ) * ‖poch w (j - 1)‖ *
          (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re
        ≤ |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) *
          (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re := by gcongr
      _ ≤ |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹ := by
          gcongr
          exact mul_nonneg hc (pochR_nonneg hR0 _)
  have hrem : ‖riemannZeta w - EM N M w‖ ≤
      pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
    refine hE.trans ?_
    have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
    have hpw : (N : ℝ) ^ (1 - w.re - M) ≤ ((N : ℝ) ^ (M - 1))⁻¹ := by
      have hc : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ M)]
        simp
      have := Real.rpow_le_rpow_of_exponent_le hN1
        (show 1 - w.re - (M : ℝ) ≤ -((M - 1 : ℕ) : ℝ) by rw [hc]; linarith)
      rw [Real.rpow_neg hN0.le, Real.rpow_natCast] at this
      exact this
    have hden0 : 0 < (M : ℝ) - 1 := by linarith
    have hfac : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
    have hp := norm_poch_le hR M
    have hCb := Cb_nonneg M
    have hpow0 : 0 ≤ (N : ℝ) ^ (1 - w.re - M) := Real.rpow_nonneg hN0.le _
    calc ‖poch w M‖ / (M.factorial : ℝ) * (Cb M * (N : ℝ) ^ (1 - w.re - M) / (w.re + M - 1))
        ≤ pochR R M / (M.factorial : ℝ) * (Cb M * (N : ℝ) ^ (1 - w.re - M) / (w.re + M - 1)) := by
          gcongr
          · exact div_nonneg (mul_nonneg hCb hpow0) (by linarith)
      _ ≤ pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (pochR_nonneg hR0 M) hfac.le)
          exact div_le_div₀ (mul_nonneg hCb (by positivity)) (mul_le_mul_of_nonneg_left hpw hCb)
            hden0 (by linarith)
  have hEM : ‖EM N M w‖ ≤ N + N / d + 1 / 2 + ∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| /
      (j.factorial : ℝ) * pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹ := by
    unfold EM
    have t1 := norm_add_le ((∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)) + (N : ℂ) ^ (1 - w) / (w - 1) -
      (N : ℂ) ^ (-w) / 2) (∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) *
        poch w (j - 1) * (N : ℂ) ^ (-w - ((j - 1 : ℕ) : ℂ)))
    have t2 := norm_sub_le ((∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)) + (N : ℂ) ^ (1 - w) / (w - 1))
      ((N : ℂ) ^ (-w) / 2)
    have t3 := norm_add_le (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)) ((N : ℂ) ^ (1 - w) / (w - 1))
    linarith
  have htri : ‖riemannZeta w‖ ≤ ‖riemannZeta w - EM N M w‖ + ‖EM N M w‖ := by
    have := norm_add_le (riemannZeta w - EM N M w) (EM N M w)
    rwa [sub_add_cancel] at this
  linarith

/-! ### O valor racional da cota -/

def pochRQ (R : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => pochRQ R k * (R + k)

def somaBQ (N : ℕ) (R : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | M + 2 => somaBQ N R (M + 1) + |Btab (M + 2)| / ((M + 2).factorial : ℚ) * pochRQ R (M + 1) /
      (N : ℚ) ^ (M + 1)

/-- O valor racional da cota grosseira. -/
def cotaQ (N M : ℕ) (R d : ℚ) : ℚ :=
  N + N / d + 1 / 2 + somaBQ N R M +
    pochRQ R M / (M.factorial : ℚ) * (CbR M (M + 1) / (N : ℚ) ^ (M - 1) / ((M : ℚ) - 1))

theorem pochRQ_spec (R : ℚ) : ∀ k, ((pochRQ R k : ℚ) : ℝ) = pochR R k
  | 0 => by simp [pochRQ, pochR]
  | k + 1 => by
    simp only [pochRQ, pochR]
    push_cast
    rw [pochRQ_spec R k]

theorem somaBQ_spec (N : ℕ) (R : ℚ) : ∀ M : ℕ, M ≤ 10 →
    ((somaBQ N R M : ℚ) : ℝ) = ∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| / (j.factorial : ℝ) *
      pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹
  | 0, _ => by simp [somaBQ]
  | 1, _ => by simp [somaBQ]
  | M + 2, hM => by
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ M + 2), ← somaBQ_spec N R (M + 1) (by omega)]
    simp only [somaBQ]
    rw [show M + 2 - 1 = M + 1 by omega, ← pochRQ_spec R (M + 1), bern_eq (by omega : M + 2 ≤ 10)]
    push_cast
    ring

theorem cotaQ_spec {N M : ℕ} (hM : M ≤ 10) (R d : ℚ) :
    ((cotaQ N M R d : ℚ) : ℝ) = N + N / (d : ℝ) + 1 / 2 +
      (∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) *
        ((N : ℝ) ^ (j - 1))⁻¹) +
      pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
  have hCb : Cb M = ((CbR M (M + 1) : ℚ) : ℝ) := by rw [CbR_spec M hM (M + 1) le_rfl]; rfl
  unfold cotaQ
  rw [hCb, ← somaBQ_spec N R M hM, ← pochRQ_spec R M]
  push_cast
  ring

/-! ## 6. A região de uma peça e Cauchy -/

/-- O segmento `{¼ + it : a ≤ t ≤ b}`. -/
def seg (a b : ℝ) : Set ℂ := {z | z.re = 1 / 4 ∧ a ≤ z.im ∧ z.im ≤ b}

theorem convex_seg (a b : ℝ) : Convex ℝ (seg a b) := by
  intro x hx y hy u v hu hv huv
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · simp only [add_re, Complex.smul_re, hx1, hy1, smul_eq_mul]
    rw [← add_mul, huv, one_mul]
  · simp only [add_im, Complex.smul_im, smul_eq_mul]
    have e1 := mul_le_mul_of_nonneg_left hx2 hu
    have e2 := mul_le_mul_of_nonneg_left hy2 hv
    have e : u * a + v * a = a := by rw [← add_mul, huv, one_mul]
    linarith
  · simp only [add_im, Complex.smul_im, smul_eq_mul]
    have e1 := mul_le_mul_of_nonneg_left hx3 hu
    have e2 := mul_le_mul_of_nonneg_left hy3 hv
    have e : u * b + v * b = b := by rw [← add_mul, huv, one_mul]
    linarith

/-- As propriedades geométricas da região `|Re w − ¼| ≤ r`, `a − r ≤ Im w ≤ b + r`. -/
theorem reg_props {a b r R d : ℝ} (hr4 : r < 1 / 4) (ha : r ≤ a)
    (hR : (1 / 4 + r) ^ 2 + (b + r) ^ 2 ≤ R ^ 2) (hR0 : 0 ≤ R) (hd0 : 0 < d)
    (hdd : d ^ 2 ≤ (3 / 4 - r) ^ 2 + (a - r) ^ 2) {w : ℂ} (h1 : |w.re - 1 / 4| ≤ r)
    (h2 : a - r ≤ w.im) (h3 : w.im ≤ b + r) : 0 < w.re ∧ w ≠ 1 ∧ ‖w‖ ≤ R ∧ d ≤ ‖w - 1‖ := by
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  have hre0 : 0 < w.re := by linarith
  refine ⟨hre0, ?_, ?_, ?_⟩
  · intro e
    rw [e, one_re] at h1b
    linarith
  · have hsq : ‖w‖ ^ 2 ≤ R ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have e1 : w.re * w.re ≤ (1 / 4 + r) ^ 2 := by nlinarith
      have e2 : w.im * w.im ≤ (b + r) ^ 2 := by nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg w) hR0 (by norm_num)).mp hsq
  · have hsq : d ^ 2 ≤ ‖w - 1‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [sub_re, one_re, sub_im, one_im, sub_zero]
      have e1 : (3 / 4 - r) ^ 2 ≤ (w.re - 1) * (w.re - 1) := by nlinarith
      have e2 : (a - r) ^ 2 ≤ w.im * w.im := by nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ hd0.le (norm_nonneg _) (by norm_num)).mp hsq

/-- **Cauchy**: `‖ζ′‖ ≤ B/r` no segmento, se `‖ζ‖ ≤ B` na região. -/
theorem deriv_cota {a b r B : ℝ} (hr : 0 < r) (hr4 : r < 1 / 4)
    (hB : ∀ w : ℂ, |w.re - 1 / 4| ≤ r → a - r ≤ w.im → w.im ≤ b + r → ‖riemannZeta w‖ ≤ B)
    {x : ℂ} (hx : x ∈ seg a b) : ‖deriv riemannZeta x‖ ≤ B / r := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have prox : ∀ y ∈ closedBall x r, |y.re - 1 / 4| ≤ r ∧ a - r ≤ y.im ∧ y.im ≤ b + r := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have e1 := Complex.abs_re_le_norm (y - x)
    have e2 := Complex.abs_im_le_norm (y - x)
    rw [sub_re, hx1] at e1
    rw [sub_im] at e2
    obtain ⟨f1, f2⟩ := abs_le.mp (e2.trans hy)
    exact ⟨e1.trans hy, by linarith, by linarith⟩
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · apply difOn_zeta.diffContOnCl_ball
    intro y hy
    obtain ⟨p1, -, -⟩ := prox y hy
    simp only [mem_compl_iff, mem_singleton_iff]
    intro e
    rw [e, one_re] at p1
    rw [abs_le] at p1
    linarith [p1.2]
  · intro y hy
    obtain ⟨p1, p2, p3⟩ := prox y (sphere_subset_closedBall hy)
    exact hB y p1 p2 p3

/-- **Uma peça**: malha + cota da derivada ⟹ `‖ζ‖ ≥ δ` no segmento. -/
theorem peca {a b r B h δ : ℝ} {C : Finset ℂ} (hr : 0 < r) (hr4 : r < 1 / 4) (hB0 : 0 ≤ B)
    (hB : ∀ w : ℂ, |w.re - 1 / 4| ≤ r → a - r ≤ w.im → w.im ≤ b + r → ‖riemannZeta w‖ ≤ B)
    (hC : ∀ c ∈ C, c ∈ seg a b) (hcov : ∀ z ∈ seg a b, ∃ c ∈ C, ‖z - c‖ ≤ h)
    (hval : ∀ c ∈ C, B / r * h + δ ≤ ‖riemannZeta c‖) : ∀ z ∈ seg a b, δ ≤ ‖riemannZeta z‖ := by
  refine certificado_derivada (convex_seg a b) subset_rfl hC (fun x hx => ?_)
    (fun x hx => deriv_cota hr hr4 hB hx) (div_nonneg hB0 hr.le) hcov hval
  apply differentiableAt_riemannZeta
  intro e
  have := hx.1
  rw [e, one_re] at this
  norm_num at this

/-! ## 7. Os centros e a cobertura -/

/-- **Cobertura de `[a, b]`** pelos centros `a + h(2k + 1)`, `k < n`, se `b ≤ a + 2hn`. -/
theorem cobre {a b h : ℝ} {n : ℕ} (hn : 1 ≤ n) (hh : 0 < h) (hb : b ≤ a + 2 * h * n) {t : ℝ}
    (ht1 : a ≤ t) (ht2 : t ≤ b) : ∃ k < n, |t - (a + h * (2 * k + 1))| ≤ h := by
  set x : ℝ := (t - a) / (2 * h)
  have hx0 : 0 ≤ x := div_nonneg (by linarith) (by linarith)
  have hxe : t = a + 2 * h * x := by
    simp only [x]
    field_simp
    ring
  by_cases hk : ⌊x⌋₊ < n
  · refine ⟨⌊x⌋₊, hk, ?_⟩
    have f1 := Nat.floor_le hx0
    have f2 := Nat.lt_floor_add_one x
    rw [abs_le]
    constructor <;> nlinarith
  · have hn' : (n : ℝ) ≤ x := by
      have : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast not_lt.mp hk
      exact this.trans (Nat.floor_le hx0)
    refine ⟨n - 1, by omega, ?_⟩
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]
      simp
    rw [hc, abs_le]
    have : t = a + 2 * h * n := by nlinarith
    constructor <;> nlinarith

/-- Os centros `¼ + i(a + h(2k + 1))`. -/
noncomputable def centros (a h : ℚ) (n : ℕ) : Finset ℂ :=
  (Finset.range n).image fun k : ℕ => (1 / 4 : ℂ) + (((a + h * (2 * (k : ℚ) + 1) : ℚ) : ℝ) : ℂ) * I

theorem centro_re (a h : ℚ) (k : ℕ) :
    ((1 / 4 : ℂ) + (((a + h * (2 * (k : ℚ) + 1) : ℚ) : ℝ) : ℂ) * I).re = 1 / 4 := by simp

theorem centro_im (a h : ℚ) (k : ℕ) :
    ((1 / 4 : ℂ) + (((a + h * (2 * (k : ℚ) + 1) : ℚ) : ℝ) : ℂ) * I).im = (a : ℝ) + h * (2 * k + 1) := by
  simp

theorem cobre_seg {a h : ℚ} {n : ℕ} (hn : 1 ≤ n) (hh : 0 < h) {b : ℝ}
    (hb : b ≤ (a : ℝ) + 2 * h * n) : ∀ z ∈ seg a b, ∃ c ∈ centros a h n, ‖z - c‖ ≤ h := by
  intro z ⟨hz1, hz2, hz3⟩
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  obtain ⟨k, hk, hkt⟩ := cobre hn hh' hb hz2 hz3
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk), ?_⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [sub_re, sub_im, centro_re, centro_im, hz1, sub_self, abs_zero, zero_add]
  exact hkt

theorem centros_seg {a h : ℚ} {n : ℕ} (hh : 0 ≤ h) {b : ℝ} (hb : (a : ℝ) + 2 * h * n ≤ b) :
    ∀ c ∈ centros a h n, c ∈ seg a b := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  have hk' : (k : ℝ) + 1 ≤ n := by
    have := Finset.mem_range.mp hk
    exact_mod_cast this
  have hh' : (0 : ℝ) ≤ h := by exact_mod_cast hh
  refine ⟨centro_re a h k, ?_, ?_⟩
  · rw [centro_im]
    have : (0 : ℝ) ≤ h * (2 * k + 1) := mul_nonneg hh' (by positivity)
    linarith
  · rw [centro_im]
    have : (h : ℝ) * (2 * k + 1) ≤ 2 * h * n := by nlinarith
    linarith

/-! ## 8. A verificação dos centros pelo kernel -/

/-- Todas as verificações dos centros de uma peça. -/
def chk (N M K nT p : ℕ) (a h v : ℚ) (n : ℕ) : Bool :=
  (List.range n).all fun k : ℕ => okAll4 N K nT p (a + h * (2 * (k : ℚ) + 1)) &&
    decide (v ^ 2 ≤ nMinSq (zetaI4 N M K nT p (a + h * (2 * (k : ℚ) + 1))))

theorem chk_spec {N M K nT p : ℕ} {a h v : ℚ} {n : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 10)
    (hv : 0 ≤ v) (hc : chk N M K nT p a h v n = true) :
    ∀ c ∈ centros a h n, (v : ℝ) ≤ ‖riemannZeta c‖ := by
  intro c hcen
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hcen
  unfold chk at hc
  rw [List.all_eq_true] at hc
  have := hc k (List.mem_range.mpr (Finset.mem_range.mp hk))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨hok, hle⟩ := this
  exact le_norm_de (mem_zetaI4 hN hM1 hM _ hok) hv hle

end ATK.ZeroClasses.Quarto

#print axioms ATK.ZeroClasses.Quarto.pochR_nonneg
#print axioms ATK.ZeroClasses.Quarto.norm_poch_le
#print axioms ATK.ZeroClasses.Quarto.cota_geral
#print axioms ATK.ZeroClasses.Quarto.pochRQ_spec
#print axioms ATK.ZeroClasses.Quarto.somaBQ_spec
#print axioms ATK.ZeroClasses.Quarto.cotaQ_spec
#print axioms ATK.ZeroClasses.Quarto.convex_seg
#print axioms ATK.ZeroClasses.Quarto.reg_props
#print axioms ATK.ZeroClasses.Quarto.deriv_cota
#print axioms ATK.ZeroClasses.Quarto.peca
#print axioms ATK.ZeroClasses.Quarto.cobre
#print axioms ATK.ZeroClasses.Quarto.centro_re
#print axioms ATK.ZeroClasses.Quarto.centro_im
#print axioms ATK.ZeroClasses.Quarto.cobre_seg
#print axioms ATK.ZeroClasses.Quarto.centros_seg
#print axioms ATK.ZeroClasses.Quarto.chk_spec
