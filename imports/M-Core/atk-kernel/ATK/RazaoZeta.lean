import ATK.GammaVertical
import ATK.RHLogZeta

/-!
# ATK — Sob RH, `|ζ(s)/ζ(s + ε)| ≤ C |s + 3|^(ε/2)` na reta crítica, uniformemente em `ε`

Para `0 < ε ≤ 1/4`, a função

  `E(w) = ζ₁(w) · F(w + ε) / (w + 2) · (w + 3)^(−ε/2)`     (`= ζ(w)/ζ(w+ε) · (w−1)/(w+2) · …`)

é holomorfa na faixa `1/2 − ε/2 ≤ Re w ≤ 5/2` (sob RH, `F = 1/ζ` é holomorfa em `Re > 1/2`). Na reta
da esquerda, `w = 1 − w'` com `w + ε = conj w'`, e a equação funcional (`ATK.GammaVertical`) dá
`|ζ(w)/ζ(w+ε)| ≤ 2CΓ |1 − w|^(ε/2)`; na da direita, `|E| ≤ 3`. Por **Phragmén–Lindelöf** (Mathlib),
`|E| ≤ max(2CΓ, 3)` na faixa, com constante que **não depende de `ε`** (`norm_razao_le`).
-/

open Complex Set Filter Asymptotics

namespace ATK.RazaoZeta

open ATK.RHLogZeta ATK.GammaVertical

/-- A função de Phragmén–Lindelöf. -/
noncomputable def E (ε : ℝ) (w : ℂ) : ℂ :=
  riemannZeta₁ w * F (w + ε) / (w + 2) * (w + 3) ^ ((-(ε / 2) : ℝ) : ℂ)

/-- `‖ζ₁(w)‖ ≤ 11(1 + |Im w|)²` em `3/8 ≤ Re w ≤ 5/2`. -/
theorem norm_zeta₁_le {w : ℂ} (h1 : 3 / 8 ≤ w.re) (h2 : w.re ≤ 5 / 2) :
    ‖riemannZeta₁ w‖ ≤ 11 * (1 + |w.im|) ^ 2 := by
  have hy := abs_nonneg w.im
  by_cases hw1 : w = 1
  · subst hw1; rw [riemannZeta₁_one, norm_one]; nlinarith
  rw [zeta₁_eq hw1, norm_mul]
  have hz := ATK.ZetaRegiao.norm_zeta_le (by linarith : 0 < w.re) hw1
  have hn : ‖w‖ ≤ 3 * (1 + |w.im|) := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 5 / 2 + |w.im| := by rw [abs_of_pos (by linarith)]; linarith
      _ ≤ 3 * (1 + |w.im|) := by linarith
  have hn1 : ‖w - 1‖ ≤ 2 * (1 + |w.im|) := by
    calc ‖w - 1‖ ≤ |(w - 1).re| + |(w - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 3 / 2 + |w.im| := by
          have : |(w - 1).re| ≤ 3 / 2 := by
            rw [sub_re, one_re, abs_le]; constructor <;> linarith
          have h' : (w - 1).im = w.im := by simp
          rw [h']; linarith
      _ ≤ 2 * (1 + |w.im|) := by linarith
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  calc ‖w - 1‖ * ‖riemannZeta w‖ ≤ ‖w - 1‖ * (‖w‖ / ‖w - 1‖ + ‖w‖ / (2 * w.re)) :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = ‖w‖ + ‖w - 1‖ * ‖w‖ / (2 * w.re) := by field_simp
    _ ≤ 3 * (1 + |w.im|) + (2 * (1 + |w.im|)) * (3 * (1 + |w.im|)) / (3 / 4) := by
        gcongr
        linarith
    _ ≤ 11 * (1 + |w.im|) ^ 2 := by nlinarith

theorem norm_peso (ε : ℝ) {w : ℂ} (hw : 0 < (w + 3).re) :
    ‖(w + 3) ^ ((-(ε / 2) : ℝ) : ℂ)‖ = ‖w + 3‖ ^ (-(ε / 2)) := Complex.norm_cpow_real _ _

theorem differentiableAt_E (hRH : RiemannHypothesis) {ε : ℝ} {w : ℂ} (hw : 1 / 2 < (w + ε).re)
    (hw3 : 0 < (w + 3).re) (hw2 : w + 2 ≠ 0) : DifferentiableAt ℂ (E ε) w := by
  have hF : DifferentiableAt ℂ (fun w : ℂ => F (w + ε)) w :=
    (differentiableAt_F hRH hw).comp w (differentiableAt_id.add (differentiableAt_const _))
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (w + 3) ^ ((-(ε / 2) : ℝ) : ℂ)) w :=
    (differentiableAt_id.add (differentiableAt_const _)).cpow (differentiableAt_const _)
      (Or.inl hw3)
  exact (((differentiable_riemannZeta₁ w).mul hF).div
    (differentiableAt_id.add (differentiableAt_const _)) hw2).mul hpow

/-- Para `w ≠ 1`, `w + ε ≠ 1`: `E(w) = ζ(w)/ζ(w+ε) · (w−1)/(w+2) · (w+3)^(−ε/2)`. -/
theorem E_eq {ε : ℝ} {w : ℂ} (hw1 : w ≠ 1) (hwe : w + ε ≠ 1) :
    E ε w = riemannZeta w * (riemannZeta (w + ε))⁻¹ * ((w - 1) / (w + 2)) *
      (w + 3) ^ ((-(ε / 2) : ℝ) : ℂ) := by
  rw [E, zeta₁_eq hw1, F_eq hwe]
  ring

/-- **Reta da esquerda**: `‖E‖ ≤ 2CΓ`. -/
theorem norm_E_esq (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) {w : ℂ}
    (hw : w.re = 1 / 2 - ε / 2) : ‖E ε w‖ ≤ 2 * CΓ := by
  have hw1 : w ≠ 1 := by intro h; rw [h, one_re] at hw; linarith
  have hwe : w + ε ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  rw [E_eq hw1 hwe]
  set w' : ℂ := 1 - w with hw'
  have hw're : w'.re = 1 / 2 + ε / 2 := by simp [hw', hw]; ring
  have hw'1 : w' ≠ 1 := by intro h; rw [h, one_re] at hw're; linarith
  have hconj : w + ε = (starRingEnd ℂ) w' := by
    apply Complex.ext <;> simp [hw', hw] <;> ring
  have hzw : riemannZeta w = riemannZeta (1 - w') := by rw [hw']; ring_nf
  have hFE := norm_zeta_one_sub_le (w := w') (by rw [hw're]; linarith) (by rw [hw're]; linarith)
    hw'1
  have hne : riemannZeta w' ≠ 0 := zeta_ne_zero_of_RH hRH (by rw [hw're]; linarith)
  have hnconj : ‖riemannZeta (w + ε)‖ = ‖riemannZeta w'‖ := by
    rw [hconj, riemannZeta_conj, Complex.norm_conj]
  have hpos : 0 < ‖riemannZeta w'‖ := norm_pos_iff.mpr hne
  have hratio : ‖riemannZeta w * (riemannZeta (w + ε))⁻¹‖ ≤ 2 * CΓ * ‖w'‖ ^ (ε / 2) := by
    rw [norm_mul, norm_inv, hnconj, hzw]
    rw [mul_inv_le_iff₀ hpos]
    have : w'.re - 1 / 2 = ε / 2 := by rw [hw're]; ring
    rw [this] at hFE
    exact hFE
  have hfrac : ‖(w - 1) / (w + 2)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr (fun h => by
      have := congrArg Complex.re h; simp [hw] at this; linarith))]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp [hw]
    nlinarith
  have h3 : 0 < (w + 3).re := by simp [hw]; linarith
  have hw3 : 0 < ‖w + 3‖ := norm_pos_iff.mpr (fun h => by rw [h, zero_re] at h3; exact lt_irrefl 0 h3)
  have hcmp : ‖w'‖ ≤ ‖w + 3‖ := by
    rw [hw', ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp [hw]
    nlinarith
  have hpeso : ‖w'‖ ^ (ε / 2) * ‖w + 3‖ ^ (-(ε / 2)) ≤ 1 := by
    rw [Real.rpow_neg hw3.le, ← div_eq_mul_inv]
    rw [div_le_one (Real.rpow_pos_of_pos hw3 _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hcmp (by linarith)
  rw [norm_mul, norm_mul, norm_peso ε h3]
  have hC : 0 ≤ 2 * CΓ := by have := CΓ_pos; linarith
  calc ‖riemannZeta w * (riemannZeta (w + ε))⁻¹‖ * ‖(w - 1) / (w + 2)‖ * ‖w + 3‖ ^ (-(ε / 2))
      ≤ (2 * CΓ * ‖w'‖ ^ (ε / 2)) * 1 * ‖w + 3‖ ^ (-(ε / 2)) := by
        gcongr
    _ = 2 * CΓ * (‖w'‖ ^ (ε / 2) * ‖w + 3‖ ^ (-(ε / 2))) := by ring
    _ ≤ 2 * CΓ * 1 := by gcongr
    _ = 2 * CΓ := mul_one _

/-- **Reta da direita** (`Re w = 5/2`): `‖E‖ ≤ 3`. -/
theorem norm_E_dir {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : w.re = 5 / 2) : ‖E ε w‖ ≤ 3 := by
  have hw1 : w ≠ 1 := by intro h; rw [h, one_re] at hw; norm_num at hw
  have hwe : w + ε ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hw] at this; linarith
  rw [E_eq hw1 hwe]
  have hz : ‖riemannZeta w‖ ≤ 3 / 2 := by
    have := norm_zeta_sub_one_le (s := w) (by rw [hw])
    have h2 := norm_le_norm_sub_add (riemannZeta w) 1
    rw [norm_one] at h2; linarith
  have hzi : ‖(riemannZeta (w + ε))⁻¹‖ ≤ 2 :=
    norm_inv_zeta_le_two (by simp [hw]; linarith)
  have hfrac : ‖(w - 1) / (w + 2)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr (fun h => by
      have := congrArg Complex.re h; simp [hw] at this; norm_num at this))]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp [hw]
    nlinarith
  have h3 : 0 < (w + 3).re := by simp [hw]; norm_num
  have hn3 : 1 ≤ ‖w + 3‖ := by
    have := Complex.re_le_norm (w + 3)
    simp [hw] at this ⊢
    linarith
  have hpeso : ‖w + 3‖ ^ (-(ε / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn3 (by linarith)
  rw [norm_mul, norm_mul, norm_mul, norm_peso ε h3]
  calc ‖riemannZeta w‖ * ‖(riemannZeta (w + ε))⁻¹‖ * ‖(w - 1) / (w + 2)‖ * ‖w + 3‖ ^ (-(ε / 2))
      ≤ 3 / 2 * 2 * 1 * 1 := by gcongr
    _ = 3 := by norm_num

/-- A constante uniforme. -/
noncomputable def CE : ℝ := max (2 * CΓ) 3

theorem CE_pos : 0 < CE := lt_of_lt_of_le (by norm_num) (le_max_right _ _)

/-- **Phragmén–Lindelöf**: `‖E ε w‖ ≤ CE` na faixa `1/2 − ε/2 ≤ Re w ≤ 5/2`. -/
theorem norm_E_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) {w : ℂ}
    (h1 : 1 / 2 - ε / 2 ≤ w.re) (h2 : w.re ≤ 5 / 2) : ‖E ε w‖ ≤ CE := by
  obtain ⟨CF, hCF, hF⟩ := norm_F_le hRH (δ := ε / 2) (η := 1) (by linarith) (by linarith)
    one_pos
  have hdiff : ∀ z : ℂ, 1 / 2 - ε / 2 ≤ z.re → DifferentiableAt ℂ (E ε) z := by
    intro z hz
    refine differentiableAt_E hRH (by simp; linarith) (by simp; linarith) (fun h => ?_)
    have := congrArg Complex.re h; simp at this; linarith
  have hsub : closure (re ⁻¹' Ioo (1 / 2 - ε / 2) (5 / 2)) ⊆ {z : ℂ | 1 / 2 - ε / 2 ≤ z.re} :=
    closure_minimal (fun z (hz : z ∈ re ⁻¹' Ioo (1 / 2 - ε / 2) (5 / 2)) =>
      show 1 / 2 - ε / 2 ≤ z.re from le_of_lt hz.1)
      (isClosed_le continuous_const Complex.continuous_re)
  refine PhragmenLindelof.vertical_strip (a := 1 / 2 - ε / 2) (b := 5 / 2) ?_ ?_ ?_ ?_ h1 h2
  · exact ⟨fun z (hz : z ∈ re ⁻¹' Ioo (1 / 2 - ε / 2) (5 / 2)) =>
      (hdiff z (le_of_lt hz.1)).differentiableWithinAt,
      fun z (hz : z ∈ closure (re ⁻¹' Ioo (1 / 2 - ε / 2) (5 / 2))) =>
        (hdiff z (hsub hz)).continuousAt.continuousWithinAt⟩
  · refine ⟨1, by
      have := Real.pi_gt_three
      rw [lt_div_iff₀ (show (0 : ℝ) < 5 / 2 - (1 / 2 - ε / 2) by linarith)]; linarith, 3, ?_⟩
    refine Asymptotics.IsBigO.of_bound (6 * CF) ?_
    refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun z hz => ?_)
    have hz1 : 1 / 2 - ε / 2 ≤ z.re := le_of_lt hz.1
    have hz2 : z.re ≤ 5 / 2 := le_of_lt hz.2
    have hy := abs_nonneg z.im
    have h3 : 0 < (z + 3).re := by simp; linarith
    have hn3 : 1 ≤ ‖z + 3‖ := by
      have := Complex.re_le_norm (z + 3); simp at this ⊢; linarith
    have hpeso : ‖(z + 3) ^ ((-(ε / 2) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_peso ε h3]; exact Real.rpow_le_one_of_one_le_of_nonpos hn3 (by linarith)
    have hz₁ := norm_zeta₁_le (w := z) (by linarith) hz2
    have hFz := hF (z + ε) (by simp; linarith)
    have him : (z + ε).im = z.im := by simp
    rw [him, Real.rpow_one] at hFz
    have hn2 : 2 ≤ ‖z + 2‖ := by
      have := Complex.re_le_norm (z + 2); simp at this ⊢; linarith
    have hEb : ‖E ε z‖ ≤ 6 * CF * (1 + |z.im|) ^ 3 := by
      rw [E, norm_mul, norm_div, norm_mul]
      calc ‖riemannZeta₁ z‖ * ‖F (z + ε)‖ / ‖z + 2‖ * ‖(z + 3) ^ ((-(ε / 2) : ℝ) : ℂ)‖
          ≤ 11 * (1 + |z.im|) ^ 2 * (CF * (1 + |z.im|)) / 2 * 1 := by
            gcongr
        _ = 11 / 2 * (CF * (1 + |z.im|) ^ 3) := by ring
        _ ≤ 6 * CF * (1 + |z.im|) ^ 3 := by
            have : 0 ≤ CF * (1 + |z.im|) ^ 3 := by positivity
            nlinarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : (1 + |z.im|) ^ 3 ≤ Real.exp (3 * Real.exp (1 * |z.im|)) := by
      have h1 : 1 + |z.im| ≤ Real.exp |z.im| := by linarith [Real.add_one_le_exp |z.im|]
      have h2 : (1 + |z.im|) ^ 3 ≤ Real.exp |z.im| ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
      rw [← Real.exp_nat_mul] at h2
      refine h2.trans (Real.exp_le_exp.mpr ?_)
      push_cast
      rw [one_mul]
      have := Real.add_one_le_exp |z.im|
      nlinarith
    calc ‖E ε z‖ ≤ 6 * CF * (1 + |z.im|) ^ 3 := hEb
      _ ≤ 6 * CF * Real.exp (3 * Real.exp (1 * |z.im|)) := by gcongr
  · intro z hz
    exact (norm_E_esq hRH hε hε1 hz).trans (le_max_left _ _)
  · intro z hz
    exact (norm_E_dir hε hz).trans (le_max_right _ _)

/-- **A razão na reta crítica**, uniforme em `ε ∈ (0, 1/4]`:
`‖ζ(1/2+iτ) / ζ(1/2+ε+iτ)‖ ≤ 7 CE · ‖1/2 + iτ + 3‖^(ε/2)`. -/
theorem norm_razao_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (τ : ℝ) :
    ‖riemannZeta (1 / 2 + τ * I) * (riemannZeta (1 / 2 + τ * I + ε))⁻¹‖ ≤
      7 * CE * ‖1 / 2 + τ * I + 3‖ ^ (ε / 2) := by
  set s : ℂ := 1 / 2 + τ * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at hsre; norm_num at hsre
  have hse : s + ε ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hsre] at this; linarith
  have hE := norm_E_le hRH hε hε1 (w := s) (by rw [hsre]; linarith) (by rw [hsre]; norm_num)
  rw [E_eq hs1 hse, norm_mul, norm_mul] at hE
  have h3 : 0 < (s + 3).re := by simp [hsre]; norm_num
  rw [norm_peso ε h3] at hE
  have hn3 : 0 < ‖s + 3‖ := norm_pos_iff.mpr (fun h => by rw [h, zero_re] at h3; exact lt_irrefl 0 h3)
  have hd : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hd2 : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    simp [hsre] at this
    rw [abs_of_neg (by norm_num)] at this
    linarith
  have hs2 : 0 < ‖s + 2‖ := norm_pos_iff.mpr (fun h => by
    have := congrArg Complex.re h; simp [hsre] at this; norm_num at this)
  have hfrac : ‖s + 2‖ / ‖s - 1‖ ≤ 7 := by
    rw [div_le_iff₀ hd]
    have := norm_add_le (s - 1) 3
    rw [show s - 1 + 3 = s + 2 by ring] at this
    have h3n : ‖(3 : ℂ)‖ = 3 := by simp
    rw [h3n] at this
    linarith
  -- `‖ζ/ζ‖ = ‖E‖ · ‖s+2‖/‖s−1‖ · ‖s+3‖^(ε/2)`
  set R := ‖riemannZeta s * (riemannZeta (s + ε))⁻¹‖
  have hfr : ‖(s - 1) / (s + 2)‖ = ‖s - 1‖ / ‖s + 2‖ := norm_div _ _
  rw [hfr] at hE
  have hpinv : ‖s + 3‖ ^ (-(ε / 2)) = (‖s + 3‖ ^ (ε / 2))⁻¹ := Real.rpow_neg hn3.le _
  have hP : 0 < ‖s + 3‖ ^ (ε / 2) := Real.rpow_pos_of_pos hn3 _
  have key : R ≤ CE * (‖s + 2‖ / ‖s - 1‖) * ‖s + 3‖ ^ (ε / 2) := by
    have h1 : R * (‖s - 1‖ / ‖s + 2‖) * (‖s + 3‖ ^ (ε / 2))⁻¹ ≤ CE := by rw [← hpinv]; exact hE
    have hdne := hd.ne'
    have hs2ne := hs2.ne'
    have hPne := hP.ne'
    calc R = R * (‖s - 1‖ / ‖s + 2‖) * (‖s + 3‖ ^ (ε / 2))⁻¹ *
          ((‖s + 2‖ / ‖s - 1‖) * ‖s + 3‖ ^ (ε / 2)) := by
          field_simp
      _ ≤ CE * ((‖s + 2‖ / ‖s - 1‖) * ‖s + 3‖ ^ (ε / 2)) := by
          gcongr
      _ = CE * (‖s + 2‖ / ‖s - 1‖) * ‖s + 3‖ ^ (ε / 2) := by ring
  calc R ≤ CE * (‖s + 2‖ / ‖s - 1‖) * ‖s + 3‖ ^ (ε / 2) := key
    _ ≤ CE * 7 * ‖s + 3‖ ^ (ε / 2) := by
        have := CE_pos
        gcongr
    _ = 7 * CE * ‖s + 3‖ ^ (ε / 2) := by ring

end ATK.RazaoZeta

#print axioms ATK.RazaoZeta.norm_zeta₁_le
#print axioms ATK.RazaoZeta.norm_peso
#print axioms ATK.RazaoZeta.differentiableAt_E
#print axioms ATK.RazaoZeta.E_eq
#print axioms ATK.RazaoZeta.norm_E_esq
#print axioms ATK.RazaoZeta.norm_E_dir
#print axioms ATK.RazaoZeta.CE_pos
#print axioms ATK.RazaoZeta.norm_E_le
#print axioms ATK.RazaoZeta.norm_razao_le
