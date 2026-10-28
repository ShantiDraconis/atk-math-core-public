import ATK.ZeroClasses.SomaZeros
import ATK.ZeroClasses.PerronDirichlet
import ATK.ZeroClasses.ChebyshevSuave
import ATK.ZeroClasses.TNP
import ATK.ZeroClasses.VonKoch

/-!
# RH ⟺ `ψ(x) = x + O(√x log³ x)` (rodada 64)

**Teorema** (von Koch, 1901, com `log³`). Sob RH, existe `K` tal que

  `|ψ(x) − x| ≤ K √x log³ x`   para `x ≥ 100`   (**`psi_RH`**),

e a recíproca vale (rodada 55): **`rh_iff_psiLog3 : RiemannHypothesis ↔ PsiLog3`**. A prova é a de Perron com
deslocamento de contorno, sem fórmula explícita:

1. **Perron para `Λ`** (`perron_psi`): com `f_η(n) = η Λ(n) n^{−η}` (`|f_η| ≤ 1`, `norm_fL_le`) e `s = −η`, a fórmula
   de Perron truncada da rodada 45 dá, para `x = N + ½`,
   `|ψ(N) − (1/2π) ∫_{−T}^{T} F(c + it) dt| ≤ x^c (4x + 2) · 8/(ηπT(c − η − 1))`, `F(s) = x^s (−ζ′/ζ)(s)/s`;
2. **o retângulo** (`bordo_Fx`): `∮ F = 2πi x` em `[a, c] × [−T, T]` quando `G(s) = (s − 1)ζ(s)` não se anula lá
   (sob RH, para `a > ½`);
3. **as cotas** sob RH: `|ζ′/ζ(σ + it)| ≤ C log(2 + |t|)/(σ − ½)` (rodada 63, `logDeriv_RH`, e compacidade em
   `|t| ≤ 6`, `logDeriv_RH_unif`), e `∫_{−T}^{T} dy/(1 + |y|) = 2 log(1 + T)` (`integral_um_abs`);
4. **a escolha** `η = 1/log x`, `c = 1 + 2η`, `a = ½ + η`, `T = x²` (`psi_RH_meio`): Perron custa `O(log² x)`, os
   lados horizontais `O(log² x)` e o lado vertical `Re s = a` custa `O(√x log³ x)`.

Classificação (rodada 64): **reformulação/consequência** — a forma quantitativa de von Koch (a fórmula explícita dá
`log² x`; aqui `log³ x`). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.PsiRH

open ATK.ZeroClasses.PerronD (xN xN_pos perron_LSeries)
open ATK.ZeroClasses.RegiaoLivre (Gp Gp_diff Gp_eq Gp_ne_zero)
open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_cauchy bordo_inv
  bordo_const_mul)
open ATK.ZeroClasses.PNT (vM LSeries_vM logDeriv_eq_Gp)

/-! ## 1. Os coeficientes `η Λ(n) n^{−η}` -/

/-- `f_η(n) = η Λ(n) n^{−η}`. -/
noncomputable def fL (η : ℝ) (n : ℕ) : ℂ :=
  ((η * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-η) : ℝ) : ℂ)

theorem norm_fL_le {η : ℝ} (hη : 0 < η) (n : ℕ) : ‖fL η n‖ ≤ 1 := by
  unfold fL
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) ^ (-η) := Real.rpow_pos_of_pos hn0 _
  rw [abs_of_nonneg (by positivity)]
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h1 : η * Real.log n ≤ (n : ℝ) ^ η := by
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn0 η)
    rw [Real.log_rpow hn0] at this
    linarith
  have h2 : (n : ℝ) ^ η * (n : ℝ) ^ (-η) = 1 := by
    rw [← Real.rpow_add hn0]
    simp
  calc η * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-η)
      ≤ η * Real.log n * (n : ℝ) ^ (-η) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ hη.le) hp.le
    _ ≤ (n : ℝ) ^ η * (n : ℝ) ^ (-η) := mul_le_mul_of_nonneg_right h1 hp.le
    _ = 1 := h2

theorem term_fL_neg (η : ℝ) (n : ℕ) :
    LSeries.term (fL η) (-(η : ℂ)) n = ((η * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn.ne']
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℂ) ^ (-(η : ℂ)) = (((n : ℝ) ^ (-η) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hn0.le, Complex.ofReal_natCast, Complex.ofReal_neg]
  have hp : (n : ℝ) ^ (-η) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
  rw [e, fL, ← Complex.ofReal_div]
  congr 1
  field_simp

theorem soma_fL (η : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), LSeries.term (fL η) (-(η : ℂ)) n =
      ((η * Chebyshev.psi N : ℝ) : ℂ) := by
  simp_rw [term_fL_neg]
  rw [ATK.ZeroClasses.PNT.psi_eq_range (N : ℝ) (N := N + 1) (by rw [Nat.floor_natCast]),
    Finset.mul_sum, Complex.ofReal_sum]

theorem LSeries_fL (η : ℝ) {w : ℂ} (hw : 1 < w.re) :
    LSeries (fL η) (-(η : ℂ) + w) = (η : ℂ) * -logDeriv riemannZeta w := by
  rw [← LSeries_vM hw, LSeries, LSeries, ← tsum_mul_left]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : (n : ℂ) ^ (-(η : ℂ) + w) = (((n : ℝ) ^ (-η) : ℝ) : ℂ) * (n : ℂ) ^ w := by
    rw [Complex.cpow_add _ _ hnc, Complex.ofReal_cpow hn0.le, Complex.ofReal_natCast,
      Complex.ofReal_neg]
  have hp : (((n : ℝ) ^ (-η) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hn0 _).ne'
  have hw0 : (n : ℂ) ^ w ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnc]
    exact Complex.exp_ne_zero _
  rw [e, fL, vM, Complex.ofReal_mul, Complex.ofReal_mul]
  field_simp

/-! ## 2. `Σ n^{−σ} ≤ 8/(σ − 1)` -/

theorem tsum_um_le {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) (σ : ℂ) n‖ ≤ 8 / (σ - 1) := by
  have hre : 1 < (σ : ℂ).re := by simpa using h1
  have hS : LSeriesSummable (fun _ => (1 : ℂ)) (σ : ℂ) := LSeriesSummable_one_iff.mpr hre
  have e : ∀ n, ‖LSeries.term (fun _ => (1 : ℂ)) (σ : ℂ) n‖ =
      (LSeries.term (fun _ => (1 : ℂ)) (σ : ℂ) n).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne']
    show ‖(1 : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ = ((1 : ℂ) / (n : ℂ) ^ (σ : ℂ)).re
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have e' : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hn0.le, Complex.ofReal_natCast]
    rw [e', ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.norm_real, Complex.ofReal_re,
      Real.norm_of_nonneg (by positivity)]
  rw [tsum_congr e, ← Complex.re_tsum hS]
  have hz : ∑' n, LSeries.term (fun _ => (1 : ℂ)) (σ : ℂ) n = riemannZeta σ :=
    LSeries_one_eq_riemannZeta hre
  rw [hz]
  exact (Complex.re_le_norm _).trans (ATK.ZeroClasses.RegiaoLivre.cota_zeta_real h1 h2)

/-- **Perron para `ψ`**: `|ψ(N) − (1/2π) ∫ F(c + it) dt| ≤ x^c(4x + 2)/(πT) · 8/((c − η − 1)η)`. -/
theorem perron_psi (N : ℕ) {η c T : ℝ} (hη : 0 < η) (hc1 : 1 < c - η) (hc2 : c - η ≤ 2) (hT : 0 < T) :
    η * ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (xN N : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)‖ ≤
      xN N ^ c * (4 * xN N + 2) / (π * T) * (8 / (c - η - 1)) := by
  have hc0 : 0 < c := by linarith
  have hsc : 1 < (-(η : ℂ)).re + c := by
    rw [neg_re, ofReal_re]
    linarith
  have hP := perron_LSeries (f := fL η) (norm_fL_le hη) N (s := -(η : ℂ)) (c := c) (T := T) hc0 hsc hT
  have hint : ∫ t in (-T)..T, LSeries (fL η) (-(η : ℂ) + ((c : ℂ) + t * I)) *
      (xN N : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) =
      (η : ℂ) * ∫ t in (-T)..T, (xN N : ℂ) ^ ((c : ℂ) + t * I) *
        (-logDeriv riemannZeta ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : 1 < ((c : ℂ) + t * I).re := by simp; linarith
    simp only [LSeries_fL η hre]
    ring
  rw [soma_fL, hint] at hP
  have hσ' : (-(η : ℂ)).re + c = c - η := by rw [neg_re, ofReal_re]; ring
  rw [hσ'] at hP
  have htsum := tsum_um_le (σ := c - η) hc1 hc2
  have hpos : 0 ≤ xN N ^ c * (4 * xN N + 2) / (π * T) := by
    have := xN_pos N
    positivity
  have e : ((η * Chebyshev.psi N : ℝ) : ℂ) - (2 * π : ℂ)⁻¹ * ((η : ℂ) *
      ∫ t in (-T)..T, (xN N : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)) =
      (η : ℂ) * ((Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ *
      ∫ t in (-T)..T, (xN N : ℂ) ^ ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) /
        ((c : ℂ) + t * I)) := by
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη] at hP
  calc _ ≤ _ := hP
    _ ≤ _ := mul_le_mul_of_nonneg_left htsum hpos

/-! ## 3. O retângulo -/

/-- O integrando `F(s) = x^s (−ζ′/ζ)(s)/s`. -/
noncomputable def Fx (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s * (-logDeriv riemannZeta s) / s

/-- `φ(s) = x^s/s`. -/
noncomputable def px (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s / s

theorem px_diff {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (px x) s := by
  have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  unfold px
  exact (differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))).div differentiableAt_id h0

theorem px_one {x : ℝ} : px x 1 = x := by
  unfold px
  rw [cpow_one, div_one]

theorem norm_Fx {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖Fx x s‖ = x ^ s.re * ‖logDeriv riemannZeta s‖ / ‖s‖ := by
  unfold Fx
  rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- **O resíduo**: `∮ x^s(−ζ′/ζ)(s)/s ds = 2πi x` no retângulo `[a, c] × [−T, T]` onde `G ≠ 0`. -/
theorem bordo_Fx {x a c T : ℝ} (hx : 0 < x) (ha : 0 < a) (h1 : a < 1) (hc : 1 < c) (hT : 0 < T)
    (hG : ∀ s ∈ Ret ⟨a, -T⟩ ⟨c, T⟩, Gp s ≠ 0) :
    bordo (Fx x) ⟨a, -T⟩ ⟨c, T⟩ = 2 * π * I * x := by
  set z : ℂ := ⟨a, -T⟩ with hz
  set w : ℂ := ⟨c, T⟩ with hw
  have hRre : ∀ p ∈ Ret z w, a ≤ p.re := by
    intro p hp
    have h := (mem_reProdIm.mp hp).1
    change p.re ∈ [[a, c]] at h
    rw [uIcc_of_le (by linarith)] at h
    exact h.1
  have hU : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const continuous_re
  have h1U : (1 : ℂ) ∈ {p : ℂ | 0 < p.re} := by show (0 : ℝ) < (1 : ℂ).re; simp
  have hφd : DifferentiableOn ℂ (px x) {p : ℂ | 0 < p.re} := fun p hp =>
    (px_diff hx hp).differentiableWithinAt
  have hD : DifferentiableOn ℂ (dslope (px x) 1) {p : ℂ | 0 < p.re} :=
    (differentiableOn_dslope (hU.mem_nhds h1U)).mpr hφd
  have hV : IsOpen {p : ℂ | p ≠ 0} := isOpen_ne
  have hGd : DifferentiableOn ℂ Gp {p : ℂ | p ≠ 0} := fun p hp => (Gp_diff hp).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv Gp) {p : ℂ | p ≠ 0} := hGd.deriv hV
  have hne0 : ∀ p ∈ Ret z w, p ≠ 0 := fun p hp h0 => by
    have := hRre p hp; rw [h0, zero_re] at this; linarith
  have hhd : DifferentiableOn ℂ (fun p => dslope (px x) 1 p - px x p * logDeriv Gp p) (Ret z w) := by
    intro p hp
    have hp0 : 0 < p.re := lt_of_lt_of_le ha (hRre p hp)
    have hpn := hne0 p hp
    have hl : DifferentiableAt ℂ (logDeriv Gp) p := by
      have e : logDeriv Gp = fun z => deriv Gp z / Gp z := funext fun z => logDeriv_apply Gp z
      rw [e]
      exact (hdd.differentiableAt (hV.mem_nhds hpn)).div (Gp_diff hpn) (hG p hp)
    exact ((hD.differentiableAt (hU.mem_nhds hp0)).sub ((px_diff hx hp0).mul hl)).differentiableWithinAt
  have hne1 : ∀ p ∈ Bordo z w, p ≠ 1 := by
    rintro p ⟨_, h⟩ hp
    change p.re = a ∨ p.re = c ∨ p.im = -T ∨ p.im = T at h
    have hr : p.re = 1 := by rw [hp, one_re]
    have hi : p.im = 0 := by rw [hp, one_im]
    rcases h with h | h | h | h <;> linarith
  have heq : EqOn (Fx x) (fun p => (dslope (px x) 1 p - px x p * logDeriv Gp p) +
      px x 1 * (p - 1)⁻¹) (Bordo z w) := by
    intro p hp
    have hp1 := hne1 p hp
    have hpR : p ∈ Ret z w := hp.1
    have hp0 : 0 < p.re := lt_of_lt_of_le ha (hRre p hpR)
    have hpn := hne0 p hpR
    have hzp : riemannZeta p ≠ 0 := by
      intro h0
      apply hG p hpR
      rw [Gp_eq hp0 hp1, h0, mul_zero]
    simp only [Fx]
    rw [logDeriv_eq_Gp hp0 hp1 hzp, dslope_of_ne _ hp1, slope_def_field]
    have hs1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
    unfold px
    field_simp
    ring
  have hBR : Bordo z w ⊆ Ret z w := fun p hp => hp.1
  have hc1 : ContinuousOn (fun p => dslope (px x) 1 p - px x p * logDeriv Gp p) (Bordo z w) :=
    (hhd.mono hBR).continuousOn
  have hc2 : ContinuousOn (fun p : ℂ => px x 1 * (p - 1)⁻¹) (Bordo z w) := fun p hp =>
    (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr (hne1 p hp)))).continuousWithinAt
  rw [bordo_congr heq, bordo_add hc1 hc2, bordo_cauchy hhd, bordo_const_mul,
    bordo_inv (z := z) (w := w) (u := 1) (by simp [hz]; linarith) (by simp [hw]; linarith)
      (by simp [hz]; linarith) (by simp [hw]; linarith), px_one]
  ring

/-! ## 4. As cotas de `ζ′/ζ` sob RH -/

theorem zeta_ne_zero_RH (hRH : RiemannHypothesis) {s : ℂ} (h : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  by_cases hs1 : s = 1
  · rw [hs1] at hz
    exact riemannZeta_one_ne_zero hz
  have hre := hRH s hz (by
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith) hs1
  linarith

/-- `ζ′/ζ` é limitada no compacto `½ ≤ σ ≤ ¾`, `|t| ≤ 6` (sem zeros: `|γ| > 13`). -/
theorem compacto_logDeriv : ∃ M : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 4 → |s.im| ≤ 6 →
    ‖logDeriv riemannZeta s‖ ≤ M := by
  set K : Set ℂ := (Icc (1 / 2 : ℝ) (3 / 4)) ×ℂ (Icc (-6 : ℝ) 6) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hmem : ∀ s ∈ K, s ≠ 1 ∧ riemannZeta s ≠ 0 := by
    intro s hs
    rw [hK, mem_reProdIm] at hs
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, one_re] at h2
      norm_num at h2
    · have hz : s ∈ ATK.ZetaSimetria.Z := ⟨h, by linarith, by linarith⟩
      have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 s hz
      have : |s.im| ≤ 6 := abs_le.mpr ⟨h3, h4⟩
      linarith
  have hV : IsOpen {p : ℂ | p ≠ 1} := isOpen_ne
  have hζd : DifferentiableOn ℂ riemannZeta {p : ℂ | p ≠ 1} := fun p hp =>
    (differentiableAt_riemannZeta hp).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv riemannZeta) {p : ℂ | p ≠ 1} := hζd.deriv hV
  have hcont : ContinuousOn (logDeriv riemannZeta) K := by
    intro s hs
    obtain ⟨hs1, hz⟩ := hmem s hs
    have e : logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z :=
      funext fun z => logDeriv_apply _ z
    rw [e]
    exact ((hdd.differentiableAt (hV.mem_nhds hs1)).continuousAt.div
      (differentiableAt_riemannZeta hs1).continuousAt hz).continuousWithinAt
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  exact ⟨M, fun s h1 h2 h3 => hM s (by rw [hK, mem_reProdIm]; exact ⟨⟨h1, h2⟩, abs_le.mp h3⟩)⟩

/-- **Sob RH**, `|ζ′/ζ(σ + iy)| ≤ C log(2 + |y|)/(σ − ½)` em `½ < σ ≤ ¾`, para todo `y`. -/
theorem logDeriv_RH_unif (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y σ : ℝ, 1 / 2 < σ →
    σ ≤ 3 / 4 → ‖logDeriv riemannZeta ((σ : ℂ) + y * I)‖ ≤ C * Real.log (2 + |y|) / (σ - 1 / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := ATK.ZeroClasses.SomaZeros.logDeriv_RH hRH
  obtain ⟨M, hM⟩ := compacto_logDeriv
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₁ + |M| / (4 * Real.log 2), by positivity, fun y σ hσ hσ2 => ?_⟩
  have hd : 0 < σ - 1 / 2 := by linarith
  have hL2 : Real.log 2 ≤ Real.log (2 + |y|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])
  have hL0 : 0 < Real.log (2 + |y|) := hl2.trans_le hL2
  rw [add_mul, add_div]
  rcases le_or_gt 6 |y| with hy | hy
  · have h := hC₁ y σ hy hσ (by linarith)
    have : 0 ≤ |M| / (4 * Real.log 2) * Real.log (2 + |y|) / (σ - 1 / 2) := by positivity
    linarith
  · have h := hM ((σ : ℂ) + y * I) (by simp; linarith) (by simp; linarith) (by simp; linarith)
    have h2 : |M| ≤ |M| / (4 * Real.log 2) * Real.log (2 + |y|) / (σ - 1 / 2) := by
      rw [le_div_iff₀ hd]
      have hM0 := abs_nonneg M
      calc |M| * (σ - 1 / 2) ≤ |M| * (1 / 4) := mul_le_mul_of_nonneg_left (by linarith) hM0
        _ = |M| / (4 * Real.log 2) * Real.log 2 := by field_simp
        _ ≤ |M| / (4 * Real.log 2) * Real.log (2 + |y|) :=
          mul_le_mul_of_nonneg_left hL2 (by positivity)
    have : 0 ≤ C₁ * Real.log (2 + |y|) / (σ - 1 / 2) := by positivity
    linarith [le_abs_self M]

/-! ## 5. `∫_{−T}^{T} dy/(1 + |y|) = 2 log(1 + T)` -/

theorem continuous_um_abs : Continuous (fun y : ℝ => 1 / (1 + |y|)) := by
  refine continuous_const.div (continuous_const.add continuous_abs) fun y => ?_
  positivity

theorem integral_um_abs {T : ℝ} (hT : 0 ≤ T) :
    ∫ y in (-T)..T, 1 / (1 + |y|) = 2 * Real.log (1 + T) := by
  have hc := continuous_um_abs
  have hI : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => 1 / (1 + |y|)) volume a b :=
    fun a b => hc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-T) 0) (hI 0 T)]
  have hpos : ∫ y in (0 : ℝ)..T, 1 / (1 + |y|) = Real.log (1 + T) := by
    have e1 : ∫ y in (0 : ℝ)..T, 1 / (1 + |y|) = ∫ y in (0 : ℝ)..T, 1 / (1 + y) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le hT] at hy
      simp only [abs_of_nonneg hy.1]
    have e2 := intervalIntegral.integral_comp_add_left (fun u : ℝ => 1 / u) (1 : ℝ) (a := 0) (b := T)
    rw [e1, e2, integral_one_div_of_pos (by norm_num) (by linarith)]
    simp
  have hneg : ∫ y in (-T)..0, 1 / (1 + |y|) = ∫ y in (0 : ℝ)..T, 1 / (1 + |y|) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := T) (fun y : ℝ => 1 / (1 + |y|))
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [hneg, hpos]
  ring

/-! ## 6. A montagem -/

/-- **Sob RH, `|ψ(N) − (N + ½)| ≤ K √(N + ½) log³(N + ½)`** quando `log(N + ½) ≥ 4`. -/
theorem psi_RH_meio (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 4 ≤ Real.log (xN N) →
    |Chebyshev.psi N - xN N| ≤ K * Real.sqrt (xN N) * Real.log (xN N) ^ 3 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := ATK.ZeroClasses.SomaZeros.logDeriv_RH hRH
  obtain ⟨C₂, hC₂0, hC₂⟩ := logDeriv_RH_unif hRH
  refine ⟨128 + 8 * C₁ + 36 * C₂, by positivity, fun N hL4 => ?_⟩
  set x := xN N with hxdef
  set L := Real.log x with hLdef
  have hx0 : 0 < x := xN_pos N
  have hL0 : 0 < L := by linarith
  have hxe : x = Real.exp L := (Real.exp_log hx0).symm
  have hx5 : 5 ≤ x := by
    have := Real.add_one_le_exp L
    linarith
  have hx1 : 1 ≤ x := by linarith
  set η : ℝ := 1 / L with hηdef
  have hη0 : 0 < η := by positivity
  have hηL : η * L = 1 := by rw [hηdef]; field_simp
  have hη4 : η ≤ 1 / 4 := by
    rw [hηdef]
    exact one_div_le_one_div_of_le (by norm_num) hL4
  set c : ℝ := 1 + 2 * η with hcdef
  set a : ℝ := 1 / 2 + η with hadef
  set T : ℝ := x ^ 2 with hTdef
  have hT0 : 0 < T := by positivity
  have hT6 : 6 ≤ T := by
    have h := mul_le_mul hx5 hx5 (by norm_num) (by linarith)
    rw [hTdef, sq]
    linarith
  have hac : a < c := by linarith
  -- as potências
  have hxpow : ∀ u : ℝ, x ^ (u * η) = Real.exp u := by
    intro u
    rw [Real.rpow_def_of_pos hx0, ← hLdef]
    congr 1
    rw [hηdef]
    field_simp
  have hxc : x ^ c = Real.exp 2 * x := by
    rw [hcdef, Real.rpow_add hx0, Real.rpow_one, hxpow 2]
    ring
  have hxa : x ^ a = Real.exp 1 * Real.sqrt x := by
    rw [hadef, Real.rpow_add hx0, Real.sqrt_eq_rpow, show η = 1 * η by ring, hxpow 1]
    ring
  have hlog3 : Real.log 3 ≤ L := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlogT : Real.log (2 + T) ≤ 3 * L := by
    have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
    have h1 : 2 + T ≤ 3 * x ^ 2 := by rw [hTdef]; linarith
    have h2 : Real.log (3 * x ^ 2) = Real.log 3 + 2 * L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have := Real.log_le_log (by positivity) h1
    linarith
  have hlogT1 : Real.log (1 + T) ≤ 3 * L :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlogT
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he2 : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have h0 := (Real.exp_pos 1).le
    have h' : Real.exp 1 ≤ 2.72 := by linarith
    have := mul_le_mul h' h' h0 (by norm_num)
    norm_num at this
    linarith
  have hpi := Real.pi_gt_three
  -- (1) Perron
  set Vc : ℂ := ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) *
      (-logDeriv riemannZeta ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) with hVc
  have hP := perron_psi N (η := η) (c := c) (T := T) hη0 (by linarith) (by linarith) hT0
  rw [← hxdef, ← hVc] at hP
  have hPerron : ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤ 48 * Real.exp 2 * L ^ 2 / π := by
    have e8 : 8 / (c - η - 1) = 8 * L := by
      rw [hcdef, show 1 + 2 * η - η - 1 = η by ring, hηdef]
      field_simp
    rw [e8, hxc, hTdef] at hP
    have hbound : Real.exp 2 * x * (4 * x + 2) / (π * x ^ 2) * (8 * L) ≤
        η * (48 * Real.exp 2 * L ^ 2 / π) := by
      have e1 : Real.exp 2 * x * (4 * x + 2) / (π * x ^ 2) * (8 * L) =
          8 * Real.exp 2 * L * (4 * x + 2) / (π * x) := by
        field_simp
      have e2 : η * (48 * Real.exp 2 * L ^ 2 / π) = 48 * Real.exp 2 * L / π := by
        rw [hηdef]
        field_simp
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ 8 * Real.exp 2 * L * π := by positivity
      have h := mul_le_mul_of_nonneg_left hx1 this
      linarith
    have h := hP.trans hbound
    exact le_of_mul_le_mul_left h hη0
  -- (2) o retângulo
  have hG : ∀ s ∈ Ret ⟨a, -T⟩ ⟨c, T⟩, Gp s ≠ 0 := by
    intro s hs
    have h := (mem_reProdIm.mp hs).1
    change s.re ∈ [[a, c]] at h
    rw [uIcc_of_le hac.le] at h
    by_cases hs1 : s = 1
    · rw [hs1]
      simpa using Gp_ne_zero (σ := 1) le_rfl
    · rw [Gp_eq (by linarith [h.1]) hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (zeta_ne_zero_RH hRH (by linarith [h.1]))
  have hbordo := bordo_Fx hx0 (a := a) (c := c) (T := T) (by linarith) (by linarith) (by linarith) hT0 hG
  set B : ℂ := ∫ u in a..c, Fx x ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hB
  set Tp : ℂ := ∫ u in a..c, Fx x ((u : ℂ) + (T : ℂ) * I) with hTp
  set Va : ℂ := ∫ y in (-T)..T, Fx x ((a : ℂ) + (y : ℂ) * I) with hVa
  have hunf : bordo (Fx x) ⟨a, -T⟩ ⟨c, T⟩ = B - Tp + I • Vc - I • Va := rfl
  rw [hunf, smul_eq_mul, smul_eq_mul] at hbordo
  have h2 : I * (Vc - 2 * π * x) = Tp - B + I * Va := by linear_combination hbordo
  have h3 : ‖Vc - 2 * π * x‖ ≤ ‖B‖ + ‖Tp‖ + ‖Va‖ := by
    have h := congrArg norm h2
    rw [norm_mul, Complex.norm_I, one_mul] at h
    rw [h]
    have a1 := norm_add_le (Tp - B) (I * Va)
    have a2 := norm_sub_le Tp B
    rw [norm_mul, Complex.norm_I, one_mul] at a1
    linarith
  have hπ : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hcont : ‖(2 * π : ℂ)⁻¹ * Vc - x‖ ≤ (‖B‖ + ‖Tp‖ + ‖Va‖) / (2 * π) := by
    have e : (2 * π : ℂ)⁻¹ * Vc - x = (2 * π : ℂ)⁻¹ * (Vc - 2 * π * x) := by
      field_simp
    rw [e, norm_mul, norm_inv, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right h3 (by positivity)
  -- (3) os lados horizontais
  have hhor : ∀ t : ℝ, |t| = T → ‖∫ u in a..c, Fx x ((u : ℂ) + (t : ℂ) * I)‖ ≤
      3 * Real.exp 2 * C₁ * L ^ 2 := by
    intro t ht
    have hbound : ∀ u ∈ Ι a c, ‖Fx x ((u : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp 2 * x * (C₁ * (3 * L) * L) / T := by
      intro u hu
      rw [uIoc_of_le hac.le] at hu
      obtain ⟨hu1, hu2⟩ := hu
      rw [norm_Fx hx0]
      have hre : ((u : ℂ) + (t : ℂ) * I).re = u := by simp
      rw [hre]
      have h1 : x ^ u ≤ Real.exp 2 * x := by
        rw [← hxc]
        exact Real.rpow_le_rpow_of_exponent_le hx1 hu2
      have h2 := hC₁ t u (by rw [ht]; exact hT6) (by linarith) (by linarith)
      have hLu : 1 ≤ L * (u - 1 / 2) := by
        calc (1 : ℝ) = η * L := hηL.symm
          _ ≤ (u - 1 / 2) * L := mul_le_mul_of_nonneg_right (by linarith) hL0.le
          _ = L * (u - 1 / 2) := mul_comm _ _
      have h3 : C₁ * Real.log (2 + |t|) / (u - 1 / 2) ≤ C₁ * (3 * L) * L := by
        rw [div_le_iff₀ (by linarith), ht]
        have hA : C₁ * Real.log (2 + T) ≤ C₁ * (3 * L) := mul_le_mul_of_nonneg_left hlogT hC₁0
        have hB' : 0 ≤ C₁ * (3 * L) := by positivity
        have hC := mul_le_mul_of_nonneg_left hLu hB'
        calc C₁ * Real.log (2 + T) ≤ C₁ * (3 * L) * 1 := by rw [mul_one]; exact hA
          _ ≤ C₁ * (3 * L) * (L * (u - 1 / 2)) := hC
          _ = C₁ * (3 * L) * L * (u - 1 / 2) := by ring
      have h23 := h2.trans h3
      have h4 : T ≤ ‖(u : ℂ) + (t : ℂ) * I‖ := by
        rw [← ht]
        have := abs_im_le_norm ((u : ℂ) + (t : ℂ) * I)
        simpa using this
      have hlz := norm_nonneg (logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I))
      have hxu := Real.rpow_nonneg hx0.le u
      have hE0 : 0 ≤ Real.exp 2 * x := by positivity
      exact div_le_div₀ (mul_nonneg hE0 (h23.trans' hlz)) (mul_le_mul h1 h23 hlz hE0) hT0 h4
    calc ‖∫ u in a..c, Fx x ((u : ℂ) + (t : ℂ) * I)‖
        ≤ Real.exp 2 * x * (C₁ * (3 * L) * L) / T * |c - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ ≤ Real.exp 2 * x * (C₁ * (3 * L) * L) / T * 1 := by
          gcongr
          rw [abs_of_pos (by linarith)]
          linarith
      _ = 3 * Real.exp 2 * C₁ * L ^ 2 / x := by
          rw [hTdef]
          field_simp
      _ ≤ 3 * Real.exp 2 * C₁ * L ^ 2 := by
          apply div_le_self _ hx1
          positivity
  have hBb : ‖B‖ ≤ 3 * Real.exp 2 * C₁ * L ^ 2 := hhor (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hTpb : ‖Tp‖ ≤ 3 * Real.exp 2 * C₁ * L ^ 2 := hhor T (abs_of_pos hT0)
  -- (4) o lado vertical `Re s = a`
  have hvert : ‖Va‖ ≤ 72 * Real.exp 1 * C₂ * Real.sqrt x * L ^ 3 := by
    set K₀ : ℝ := Real.exp 1 * Real.sqrt x * (C₂ * (3 * L) * L) * 4 with hK₀
    have hK₀0 : 0 ≤ K₀ := by positivity
    have hbound : ∀ y ∈ Ioc (-T) T, ‖Fx x ((a : ℂ) + (y : ℂ) * I)‖ ≤ K₀ * (1 / (1 + |y|)) := by
      intro y hy
      have hyT : |y| ≤ T := abs_le.mpr ⟨hy.1.le, hy.2⟩
      rw [norm_Fx hx0]
      have hre : ((a : ℂ) + (y : ℂ) * I).re = a := by simp
      rw [hre, hxa]
      have h2 := hC₂ y a (by linarith) (by linarith)
      have h3 : C₂ * Real.log (2 + |y|) / (a - 1 / 2) ≤ C₂ * (3 * L) * L := by
        have ha' : a - 1 / 2 = η := by rw [hadef]; ring
        rw [ha', div_le_iff₀ hη0]
        have hly : Real.log (2 + |y|) ≤ 3 * L :=
          (Real.log_le_log (by positivity) (by linarith)).trans hlogT
        have hA : C₂ * Real.log (2 + |y|) ≤ C₂ * (3 * L) := mul_le_mul_of_nonneg_left hly hC₂0
        have e : C₂ * (3 * L) * L * η = C₂ * (3 * L) := by
          rw [mul_assoc (C₂ * (3 * L)), mul_comm L η, hηL, mul_one]
        rw [e]
        exact hA
      have h23 := h2.trans h3
      have h4 : (1 + |y|) / 4 ≤ ‖(a : ℂ) + (y : ℂ) * I‖ := by
        have hr := abs_re_le_norm ((a : ℂ) + (y : ℂ) * I)
        have hi := abs_im_le_norm ((a : ℂ) + (y : ℂ) * I)
        have hre' : ((a : ℂ) + (y : ℂ) * I).re = a := by simp
        have him' : ((a : ℂ) + (y : ℂ) * I).im = y := by simp
        rw [hre', abs_of_pos (by linarith)] at hr
        rw [him'] at hi
        linarith
      have h4p : 0 < (1 + |y|) / 4 := by positivity
      have hlz := norm_nonneg (logDeriv riemannZeta ((a : ℂ) + (y : ℂ) * I))
      have hE0 : 0 ≤ Real.exp 1 * Real.sqrt x := by positivity
      calc Real.exp 1 * Real.sqrt x * ‖logDeriv riemannZeta ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖(a : ℂ) + (y : ℂ) * I‖
          ≤ Real.exp 1 * Real.sqrt x * (C₂ * (3 * L) * L) / ((1 + |y|) / 4) :=
            div_le_div₀ (mul_nonneg hE0 (hlz.trans h23)) (mul_le_mul_of_nonneg_left h23 hE0) h4p h4
        _ = K₀ * (1 / (1 + |y|)) := by
            rw [hK₀]
            field_simp
    have hgi : IntervalIntegrable (fun y : ℝ => K₀ * (1 / (1 + |y|))) volume (-T) T := by
      exact (continuous_const.mul continuous_um_abs).intervalIntegrable _ _
    have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
      (ae_of_all _ hbound) hgi
    rw [intervalIntegral.integral_const_mul, integral_um_abs hT0.le] at hint
    calc ‖Va‖ ≤ K₀ * (2 * Real.log (1 + T)) := hint
      _ ≤ K₀ * (2 * (3 * L)) := by gcongr
      _ = 72 * Real.exp 1 * C₂ * Real.sqrt x * L ^ 3 := by rw [hK₀]; ring
  -- (5) a soma
  have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
  have htri : |Chebyshev.psi N - x| ≤ ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ +
      ‖(2 * π : ℂ)⁻¹ * Vc - x‖ := by
    have e : |Chebyshev.psi N - x| = ‖(Chebyshev.psi N : ℂ) - (x : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [e]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have p1 : 48 * Real.exp 2 * L ^ 2 / π ≤ 128 * L ^ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    have a1 := mul_le_mul_of_nonneg_right he2 hL2
    have a2 := mul_le_mul_of_nonneg_left hpi.le hL2
    linarith
  have p23 : (‖B‖ + ‖Tp‖ + ‖Va‖) / (2 * π) ≤ 8 * C₁ * L ^ 2 + 36 * C₂ * Real.sqrt x * L ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have hq1 : 0 ≤ C₁ * L ^ 2 := by positivity
    have hq2 : 0 ≤ C₂ * Real.sqrt x * L ^ 3 := by positivity
    have a1 := mul_le_mul_of_nonneg_right he2 hq1
    have a2 := mul_le_mul_of_nonneg_left hpi.le hq1
    have a3 := mul_le_mul_of_nonneg_right he1 hq2
    have a4 := mul_le_mul_of_nonneg_left hpi.le hq2
    linarith
  have p4 : L ^ 2 ≤ Real.sqrt x * L ^ 3 := by
    have h1 : L ^ 2 * 1 ≤ L ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) hL2
    have h2 : 1 * L ^ 3 ≤ Real.sqrt x * L ^ 3 := mul_le_mul_of_nonneg_right hsq1 (by positivity)
    have e : L ^ 2 * L = L ^ 3 := by ring
    linarith
  have hfin : |Chebyshev.psi N - x| ≤ 128 * L ^ 2 + (8 * C₁ * L ^ 2 + 36 * C₂ * Real.sqrt x * L ^ 3) := by
    linarith
  have hq : 128 * L ^ 2 + 8 * C₁ * L ^ 2 ≤ (128 + 8 * C₁) * (Real.sqrt x * L ^ 3) := by
    have := mul_le_mul_of_nonneg_left p4 (by positivity : (0 : ℝ) ≤ 128 + 8 * C₁)
    linarith
  calc |Chebyshev.psi N - x| ≤ 128 * L ^ 2 + (8 * C₁ * L ^ 2 + 36 * C₂ * Real.sqrt x * L ^ 3) := hfin
    _ ≤ (128 + 8 * C₁ + 36 * C₂) * Real.sqrt x * L ^ 3 := by linarith

/-- **RH ⟹ `|ψ(x) − x| ≤ K √x log³ x`** para `x ≥ 100`. -/
theorem psi_RH (hRH : RiemannHypothesis) : ∃ K : ℝ, ∀ x : ℝ, 100 ≤ x →
    |Chebyshev.psi x - x| ≤ K * Real.sqrt x * Real.log x ^ 3 := by
  obtain ⟨K, hK0, hK⟩ := psi_RH_meio hRH
  refine ⟨16 * K + 1, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  set N := ⌊x⌋₊ with hN
  have hN1 : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hN2 : x < N + 1 := Nat.lt_floor_add_one x
  have hxN : xN N = (N : ℝ) + 1 / 2 := rfl
  have hxN0 : 0 < xN N := xN_pos N
  have he4 : Real.exp 4 ≤ 99 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 := Real.exp_pos 1
    have h1 : Real.exp 1 ≤ 2.72 := by linarith
    calc Real.exp 1 ^ 4 ≤ 2.72 ^ 4 := by gcongr
      _ ≤ 99 := by norm_num
  have hL4 : 4 ≤ Real.log (xN N) := by
    rw [Real.le_log_iff_exp_le hxN0, hxN]
    linarith
  have h := hK N hL4
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hxNx : xN N ≤ 2 * x := by rw [hxN]; linarith
  have hsq : Real.sqrt (xN N) ≤ 2 * Real.sqrt x := by
    have h1 : Real.sqrt (xN N) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at h1
    exact h1
  have hlog : Real.log (xN N) ≤ 2 * Real.log x := by
    have h1 : Real.log (xN N) ≤ Real.log (2 * x) := Real.log_le_log hxN0 hxNx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hlog0 : 0 ≤ Real.log (xN N) := by linarith
  have hlog3 : Real.log (xN N) ^ 3 ≤ 8 * Real.log x ^ 3 := by
    calc Real.log (xN N) ^ 3 ≤ (2 * Real.log x) ^ 3 := pow_le_pow_left₀ hlog0 hlog 3
      _ = 8 * Real.log x ^ 3 := by ring
  have hsx : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  have hl3 : 1 ≤ Real.log x ^ 3 := one_le_pow₀ hlogx
  rw [Chebyshev.psi_eq_psi_coe_floor x, ← hN]
  have hdist : |xN N - x| ≤ 1 / 2 := by
    rw [hxN, abs_le]
    constructor <;> linarith
  have htri : |Chebyshev.psi N - x| ≤ |Chebyshev.psi N - xN N| + |xN N - x| := by
    have := abs_sub_le (Chebyshev.psi N) (xN N) x
    linarith
  have hmain : K * Real.sqrt (xN N) * Real.log (xN N) ^ 3 ≤
      16 * K * Real.sqrt x * Real.log x ^ 3 := by
    have hs0 : 0 ≤ Real.sqrt (xN N) := Real.sqrt_nonneg _
    have hl0 : 0 ≤ Real.log (xN N) ^ 3 := by positivity
    calc K * Real.sqrt (xN N) * Real.log (xN N) ^ 3 ≤ K * (2 * Real.sqrt x) * (8 * Real.log x ^ 3) := by
          gcongr
      _ = 16 * K * Real.sqrt x * Real.log x ^ 3 := by ring
  have hone : (1 : ℝ) * 1 ≤ Real.sqrt x * Real.log x ^ 3 :=
    mul_le_mul hsx hl3 (by norm_num) (Real.sqrt_nonneg _)
  linarith

/-! ## 7. A recíproca -/

/-- **`ψ(x) = x + O(√x log³ x)`**. -/
def PsiLog3 : Prop :=
  ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |Chebyshev.psi x - x| ≤ K * Real.sqrt x * Real.log x ^ 3

theorem psi_le_sq (N : ℕ) : Chebyshev.psi N ≤ (N : ℝ) ^ 2 := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  calc ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n ≤ ∑ n ∈ Finset.Ioc 0 N, (N : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Ioc] at hn
        have h1 : (n : ℝ) ≤ N := by exact_mod_cast hn.2
        have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        exact ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_self h2).trans h1)
    _ = (N : ℝ) ^ 2 := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        simp
        ring

theorem vonKoch_of_psiLog3 (h : PsiLog3) : ATK.ZeroClasses.VonKoch.VonKochFraco := by
  obtain ⟨K, x₀, hK⟩ := h
  intro ε hε
  set x₁ : ℝ := max x₀ 1 with hx₁
  set B : ℝ := (x₁ + 1) ^ 2 + x₁ + 1 with hB
  refine ⟨max (|K| * (3 / ε) ^ 3) B, fun N => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpow1 : 1 ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) := Real.one_le_rpow (by linarith) (by linarith)
  rcases le_or_gt x₁ N with hN | hN
  · have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
    have hNpos : (0 : ℝ) < N := by linarith
    have h := hK N ((le_max_left _ _).trans hN)
    have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hl : Real.log N ≤ (3 / ε) * (N : ℝ) ^ (ε / 3) := by
      have := Real.log_le_rpow_div hN0 (by positivity : 0 < ε / 3)
      rw [div_div_eq_mul_div] at this
      calc Real.log N ≤ (N : ℝ) ^ (ε / 3) * 3 / ε := this
        _ = (3 / ε) * (N : ℝ) ^ (ε / 3) := by ring
    have hl3 : Real.log N ^ 3 ≤ (3 / ε) ^ 3 * (N : ℝ) ^ ε := by
      have := pow_le_pow_left₀ hlog0 hl 3
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (ε / 3)) 3, ← Real.rpow_mul hN0] at this
      convert this using 2
      push_cast
      ring_nf
    have hsq : Real.sqrt N * (N : ℝ) ^ ε ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow hN0 (by linarith) (by linarith)
    have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    calc |Chebyshev.psi N - N| ≤ K * Real.sqrt N * Real.log N ^ 3 := h
      _ ≤ |K| * Real.sqrt N * ((3 / ε) ^ 3 * (N : ℝ) ^ ε) := by
          have h3 : 0 ≤ Real.log N ^ 3 := by positivity
          calc K * Real.sqrt N * Real.log N ^ 3 ≤ |K| * Real.sqrt N * Real.log N ^ 3 := by
                gcongr
                exact le_abs_self K
            _ ≤ |K| * Real.sqrt N * ((3 / ε) ^ 3 * (N : ℝ) ^ ε) := by gcongr
      _ = |K| * (3 / ε) ^ 3 * (Real.sqrt N * (N : ℝ) ^ ε) := by ring
      _ ≤ |K| * (3 / ε) ^ 3 * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by gcongr
      _ ≤ max (|K| * (3 / ε) ^ 3) B * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
          gcongr
          exact le_max_left _ _
  · have hx₁1 : 1 ≤ x₁ := le_max_right _ _
    have hψ := psi_le_sq N
    have hψ0 := Chebyshev.psi_nonneg (N : ℝ)
    have habs : |Chebyshev.psi N - N| ≤ (N : ℝ) ^ 2 + N := by
      rw [abs_le]
      have := sq_nonneg (N : ℝ)
      constructor <;> linarith
    have hB' : (N : ℝ) ^ 2 + N ≤ B := by
      rw [hB]
      have h := mul_le_mul hN.le hN.le hN0 (by linarith)
      have e : (N : ℝ) ^ 2 = N * N := sq _
      nlinarith
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    calc |Chebyshev.psi N - N| ≤ B := habs.trans hB'
      _ ≤ max (|K| * (3 / ε) ^ 3) B := le_max_right _ _
      _ ≤ max (|K| * (3 / ε) ^ 3) B * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
          have : 0 ≤ max (|K| * (3 / ε) ^ 3) B := hB0.trans (le_max_right _ _)
          exact le_mul_of_one_le_right this hpow1

/-- **RH ⟺ `ψ(x) = x + O(√x log³ x)`.** -/
theorem rh_iff_psiLog3 : RiemannHypothesis ↔ PsiLog3 := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := psi_RH hRH
    exact ⟨K, 100, hK⟩
  · intro h
    exact ATK.ZeroClasses.VonKoch.RH_of_psi (vonKoch_of_psiLog3 h)

end ATK.ZeroClasses.PsiRH

#print axioms ATK.ZeroClasses.PsiRH.norm_fL_le
#print axioms ATK.ZeroClasses.PsiRH.term_fL_neg
#print axioms ATK.ZeroClasses.PsiRH.soma_fL
#print axioms ATK.ZeroClasses.PsiRH.LSeries_fL
#print axioms ATK.ZeroClasses.PsiRH.tsum_um_le
#print axioms ATK.ZeroClasses.PsiRH.perron_psi
#print axioms ATK.ZeroClasses.PsiRH.px_diff
#print axioms ATK.ZeroClasses.PsiRH.px_one
#print axioms ATK.ZeroClasses.PsiRH.norm_Fx
#print axioms ATK.ZeroClasses.PsiRH.bordo_Fx
#print axioms ATK.ZeroClasses.PsiRH.zeta_ne_zero_RH
#print axioms ATK.ZeroClasses.PsiRH.compacto_logDeriv
#print axioms ATK.ZeroClasses.PsiRH.logDeriv_RH_unif
#print axioms ATK.ZeroClasses.PsiRH.continuous_um_abs
#print axioms ATK.ZeroClasses.PsiRH.integral_um_abs
#print axioms ATK.ZeroClasses.PsiRH.psi_RH_meio
#print axioms ATK.ZeroClasses.PsiRH.psi_RH
#print axioms ATK.ZeroClasses.PsiRH.psi_le_sq
#print axioms ATK.ZeroClasses.PsiRH.vonKoch_of_psiLog3
#print axioms ATK.ZeroClasses.PsiRH.rh_iff_psiLog3
