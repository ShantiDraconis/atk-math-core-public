import ATK.NecessidadeBD
import ATK.PerronSuave
import ATK.RazaoZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import ATK.BDDistSqPort

/-!
# ATK — A recíproca de Báez-Duarte: RH ⇒ `D_N → 0`, e **RH ⟺ `D_N → 0`** (sem pontes)

`ATK.BaezDuarteBridge` provou `D_N → 0 ⇒ RH` (a ponte B1). Aqui fica a recíproca. A prova clássica
usa o mollificador `μ(n) n^(−ε)` com corte abrupto, o que exige o teorema de Littlewood; trocamos
pelo mollificador **suavizado**

  `a_{ε,N}(n) = μ(n) (1 − n/N)₊ n^(−ε)`,   `Σ_{n ≤ N} a_{ε,N}(n) n^(−s) = A_N(s + ε)`,

cuja análise é só a fórmula de Perron suavizada (`ATK.PerronSuave`). Sob RH, com `s = 1/2 + iτ`,
`w = s + ε` e `ρ = 1 + |τ|`:

* `|A_N(w) − 1/ζ(w)| ≤ C_A N^(−ε/2) ρ^(1/16)` (deslocamento de contorno e Titchmarsh 14.2,
  `ATK.PerronSuave.norm_AN_sub_le`);
* `|ζ(w)| ≤ C_Z ρ^(1/16)` (Lindelöf à direita da reta crítica, `ATK.RHLogZeta.norm_zeta_le_RH`);
* `|ζ(s)/ζ(s + ε)| ≤ 28 C_E ρ^(1/8)`, **uniforme em `ε`** (Phragmén–Lindelöf,
  `ATK.RazaoZeta.norm_razao_le`).

Logo `|1 − ζ(s) A_N(w)| ≤ K ρ^(1/4)` e o erro espectral `|1 − ζ(s) A_N(w)|²/|s|²` é dominado por
`8K² ρ^(−3/2)`, integrável; por convergência dominada `inf_N D_N ≤ (1/2π) J(ε)` para todo
`ε ∈ (0, 1/4]` (`iInf_DN_le_J_RH`). Como os zeros de `ζ` na reta crítica são enumeráveis
(`riemannZetaZeros` é discreto), `ζ(s)/ζ(s+ε) → 1` q.t.p. e, de novo por convergência dominada,
`J(ε) → 0` (`tendsto_J_RH`). Daí:

* `necessidade : RiemannHypothesis → Tendsto DN atTop (𝓝 0)`;
* **`rh_iff_DN : RiemannHypothesis ↔ Tendsto DN atTop (𝓝 0)`** — o critério de
  Nyman–Beurling–Báez-Duarte completo, sem pontes;
* `bdDistSq_iff_rh`: a forma `⟺` da linha `m-core-riemann` (`bdDistSq = D_N`), sem hipóteses.

Isto **não** prova RH: é uma equivalência. **CLOSED_MATH continua false.**
-/

open MeasureTheory Set Real Filter Topology Complex
open ATK.Conditional.Riemann ATK.BaezDuarteBridge ATK.MellinRho ATK.EspectralDN ATK.NecessidadeBD

namespace ATK.NecessidadeRH

/-! ### Convergência dominada com coeficientes que dependem de `N` -/

/-- Variante de `iInf_DN_le_of_aprox` em que os coeficientes do `N`-ésimo polinômio dependem de
`N`. -/
theorem iInf_DN_le_of_aprox_var (a : ℕ → ℕ → ℝ) (m : ℝ → ℂ) (B : ℝ → ℝ) (hB : Integrable B)
    (hdom : ∀ N, ∀ᵐ τ, erro (polD (a N) N (lc τ)) τ ≤ B τ)
    (hconv : ∀ᵐ τ, Tendsto (fun N => polD (a N) N (lc τ)) atTop (𝓝 (m τ))) :
    ⨅ N, DN N ≤ (2 * π)⁻¹ * ∫ τ, erro (m τ) τ := by
  have hbdd : BddBelow (range DN) := ⟨0, by rintro _ ⟨N, rfl⟩; exact DN_nonneg N⟩
  have hle : ∀ N : ℕ, ⨅ n, DN n ≤ (2 * π)⁻¹ * ∫ τ, erro (polD (a N) N (lc τ)) τ := by
    intro N
    refine (ciInf_le hbdd N).trans ?_
    refine (ATK.RiemannConcrete.DN_le_residualSq N
      (fun k : Fin N => -a N (k.val + 1))).trans_eq ?_
    rw [residualSq_espectral]
    congr 2
    funext τ
    exact espectro_neg (a N) N τ
  have hlim : Tendsto (fun N => ∫ τ, erro (polD (a N) N (lc τ)) τ) atTop
      (𝓝 (∫ τ, erro (m τ) τ)) := by
    refine tendsto_integral_of_dominated_convergence B (fun N => ?_) hB (fun N => ?_) ?_
    · exact (integrable_espectro (fun k : Fin N => -a N (k.val + 1))).aestronglyMeasurable.congr
        (ae_of_all _ fun τ => espectro_neg (a N) N τ)
    · filter_upwards [hdom N] with τ hτ
      rw [Real.norm_of_nonneg (erro_nonneg _ _)]
      exact hτ
    · filter_upwards [hconv] with τ hτ
      unfold erro
      exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hτ)).div_const _).norm.pow 2
  exact ge_of_tendsto' (hlim.const_mul _) hle

/-! ### O mollificador suavizado -/

/-- `a_{ε,N}(n) = μ(n) (1 − n/N)₊ n^(−ε)`. -/
noncomputable def mollS (ε : ℝ) (N n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * ATK.PerronSuave.kk ((n : ℝ) / N) * (n : ℝ) ^ (-ε)

theorem polD_mollS (ε : ℝ) (N : ℕ) (s : ℂ) :
    polD (mollS ε N) N s = ATK.PerronSuave.AN N (s + ε) := by
  unfold polD mollS ATK.PerronSuave.AN
  rw [Fin.sum_univ_eq_sum_range (fun k => (((ArithmeticFunction.moebius (k + 1) : ℝ) *
    ATK.PerronSuave.kk (((k + 1 : ℕ) : ℝ) / N) * ((k + 1 : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) *
    ((k + 1 : ℕ) : ℂ) ^ (-s)) N]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hn : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have hc : ((((k + 1 : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) = ((k + 1 : ℕ) : ℂ) ^ (-(ε : ℂ)) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [Complex.ofReal_mul, hc, mul_assoc, ← Complex.cpow_add _ _ hn]
  have e : -(ε : ℂ) + -s = -(s + ε) := by ring
  rw [e]
  push_cast
  ring

/-! ### Cotas na reta crítica -/

theorem norm_lc_sq (τ : ℝ) : ‖lc τ‖ ^ 2 = 1 / 4 + τ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [lc]
  ring

theorem um_add_abs_sq_le (τ : ℝ) : (1 + |τ|) ^ 2 ≤ 8 * ‖lc τ‖ ^ 2 := by
  rw [norm_lc_sq]
  nlinarith [sq_abs τ, sq_nonneg (|τ| - 1)]

/-- Do erro pontual `|1 − ζ(s) m| ≤ K ρ^(1/4)` à cota integrável `8K² ρ^(−3/2)`. -/
theorem erro_le_de {m : ℂ} {τ K : ℝ} (hK : 0 ≤ K)
    (h : ‖1 - riemannZeta (lc τ) * m‖ ≤ K * (1 + |τ|) ^ (1 / 4 : ℝ)) :
    erro m τ ≤ 8 * K ^ 2 * (1 + |τ|) ^ (-(2 - 1 / 2 : ℝ)) := by
  unfold erro
  have hρ : 0 < 1 + |τ| := by positivity
  have hs : 0 < ‖lc τ‖ := norm_pos_iff.mpr (lc_ne_zero τ)
  rw [norm_div, div_pow]
  have h2 : ‖1 - riemannZeta (lc τ) * m‖ ^ 2 ≤ K ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
    calc ‖1 - riemannZeta (lc τ) * m‖ ^ 2 ≤ (K * (1 + |τ|) ^ (1 / 4 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = K ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + |τ|) ^ (1 / 4 : ℝ)), ← Real.rpow_mul hρ.le]
          norm_num
  have h3 : (1 + |τ|) ^ (-(2 - 1 / 2 : ℝ)) = (1 + |τ|) ^ (1 / 2 : ℝ) / (1 + |τ|) ^ 2 := by
    rw [show -(2 - 1 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hρ, Real.rpow_two]
  rw [h3, div_le_iff₀ (by positivity)]
  have h4 := um_add_abs_sq_le τ
  have h5 : 0 ≤ K ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) / (1 + |τ|) ^ 2 := by positivity
  calc ‖1 - riemannZeta (lc τ) * m‖ ^ 2 ≤ K ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := h2
    _ = K ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) / (1 + |τ|) ^ 2 * (1 + |τ|) ^ 2 := by field_simp
    _ ≤ K ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) / (1 + |τ|) ^ 2 * (8 * ‖lc τ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h4 h5
    _ = 8 * K ^ 2 * ((1 + |τ|) ^ (1 / 2 : ℝ) / (1 + |τ|) ^ 2) * ‖lc τ‖ ^ 2 := by ring

theorem integrable_cota (K : ℝ) :
    Integrable (fun τ : ℝ => 8 * K ^ 2 * (1 + |τ|) ^ (-(2 - 1 / 2 : ℝ))) :=
  (ATK.PerronSuave.integrable_peso (η := 1 / 2) (by norm_num)).const_mul _

/-- `|ζ(s)/ζ(s+ε)| ≤ 28 C_E ρ^(1/8)` na reta crítica, uniformemente em `ε ∈ (0, 1/4]` (sob RH). -/
theorem norm_razao_rho (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (τ : ℝ) :
    ‖riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹‖ ≤
      28 * ATK.RazaoZeta.CE * (1 + |τ|) ^ (1 / 8 : ℝ) := by
  have h := ATK.RazaoZeta.norm_razao_le hRH hε hε1 τ
  have hlc : lc τ = 1 / 2 + τ * I := rfl
  have hCE := ATK.RazaoZeta.CE_pos
  rw [hlc]
  refine h.trans ?_
  set u := ‖(1 / 2 + τ * I + 3 : ℂ)‖ with hu
  have hre : (1 / 2 + τ * I + 3 : ℂ).re = 7 / 2 := by simp; norm_num
  have him : (1 / 2 + τ * I + 3 : ℂ).im = τ := by simp
  have hu1 : 1 ≤ u := by
    have := Complex.abs_re_le_norm (1 / 2 + τ * I + 3 : ℂ)
    rw [hre] at this
    rw [hu]; linarith [le_abs_self (7 / 2 : ℝ)]
  have hu4 : u ≤ 4 * (1 + |τ|) := by
    have := Complex.norm_le_abs_re_add_abs_im (1 / 2 + τ * I + 3 : ℂ)
    rw [hre, him] at this
    rw [hu]; linarith [abs_nonneg τ, show |(7 / 2 : ℝ)| = 7 / 2 by norm_num]
  have h4 : (4 : ℝ) ^ (1 / 8 : ℝ) ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (1 / 8 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have h7 : 0 ≤ 7 * ATK.RazaoZeta.CE := by linarith
  calc 7 * ATK.RazaoZeta.CE * u ^ (ε / 2)
      ≤ 7 * ATK.RazaoZeta.CE * u ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)) h7
    _ ≤ 7 * ATK.RazaoZeta.CE * (4 * (1 + |τ|)) ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hu4 (by norm_num)) h7
    _ = 7 * ATK.RazaoZeta.CE * ((4 : ℝ) ^ (1 / 8 : ℝ) * (1 + |τ|) ^ (1 / 8 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
    _ ≤ 7 * ATK.RazaoZeta.CE * (4 * (1 + |τ|) ^ (1 / 8 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ h7
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 28 * ATK.RazaoZeta.CE * (1 + |τ|) ^ (1 / 8 : ℝ) := by ring

theorem lc_add_re (τ ε : ℝ) : (lc τ + ε).re = 1 / 2 + ε := by simp [lc]

theorem lc_add_im (τ ε : ℝ) : (lc τ + ε).im = τ := by simp [lc]

/-- Potências de `ρ = 1 + |τ|`. -/
theorem rho_pows (τ : ℝ) :
    1 ≤ (1 + |τ|) ^ (1 / 16 : ℝ) ∧
    (1 + |τ|) ^ (1 / 16 : ℝ) * (1 + |τ|) ^ (1 / 16 : ℝ) = (1 + |τ|) ^ (1 / 8 : ℝ) ∧
    (1 + |τ|) ^ (1 / 8 : ℝ) * (1 + |τ|) ^ (1 / 8 : ℝ) = (1 + |τ|) ^ (1 / 4 : ℝ) ∧
    1 ≤ (1 + |τ|) ^ (1 / 8 : ℝ) ∧ (1 + |τ|) ^ (1 / 8 : ℝ) ≤ (1 + |τ|) ^ (1 / 4 : ℝ) ∧
    1 ≤ (1 + |τ|) ^ (1 / 4 : ℝ) := by
  have hρ : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have hρ0 : 0 < 1 + |τ| := by linarith
  refine ⟨Real.one_le_rpow hρ (by norm_num), ?_, ?_, Real.one_le_rpow hρ (by norm_num),
    Real.rpow_le_rpow_of_exponent_le hρ (by norm_num), Real.one_le_rpow hρ (by norm_num)⟩
  · rw [← Real.rpow_add hρ0]; norm_num
  · rw [← Real.rpow_add hρ0]; norm_num

/-! ### `inf_N D_N ≤ (1/2π) J(ε)` sob RH -/

/-- **Sob RH, para todo `ε ∈ (0, 1/4]`: `inf_N D_N ≤ (1/2π) J(ε)`** (mollificador suavizado). -/
theorem iInf_DN_le_J_RH (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ⨅ N, DN N ≤ (2 * π)⁻¹ * J ε := by
  obtain ⟨CA, hCA, hA⟩ := ATK.PerronSuave.norm_AN_sub_le hRH hε hε1 (η := 1 / 16)
    (by norm_num) (by norm_num)
  obtain ⟨CZ, hCZ, hZ⟩ := ATK.RHLogZeta.norm_zeta_le_RH hRH (δ := ε) (η := 1 / 16) hε
    (by linarith) (by norm_num)
  set CR := 28 * ATK.RazaoZeta.CE with hCR
  have hCR0 : 0 < CR := by have := ATK.RazaoZeta.CE_pos; rw [hCR]; linarith
  set K := 1 + CR + CR * CZ * CA with hK
  have hP0 : 0 ≤ CR * CZ * CA := mul_nonneg (mul_nonneg hCR0.le hCZ.le) hCA.le
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  -- a cota pontual
  have hpt : ∀ N : ℕ, ∀ τ : ℝ, ‖1 - riemannZeta (lc τ) * ATK.PerronSuave.AN N (lc τ + ε)‖ ≤
      K * (1 + |τ|) ^ (1 / 4 : ℝ) := by
    intro N τ
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := rho_pows τ
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [ATK.PerronSuave.AN, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero,
        norm_one]
      calc (1 : ℝ) ≤ K := by rw [hK]; linarith
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (1 + |τ|) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left p6 hK0
    set s := lc τ with hs
    set w := lc τ + (ε : ℂ) with hw
    have hwre : w.re = 1 / 2 + ε := lc_add_re τ ε
    have hwim : w.im = τ := lc_add_im τ ε
    have hζw : riemannZeta w ≠ 0 :=
      ATK.RHLogZeta.zeta_ne_zero_of_RH hRH (by rw [hwre]; linarith)
    set R := riemannZeta s * (riemannZeta w)⁻¹ with hR
    set E := ATK.PerronSuave.AN N w - (riemannZeta w)⁻¹ with hE
    have hid : 1 - riemannZeta s * ATK.PerronSuave.AN N w =
        (1 - R) - R * (riemannZeta w * E) := by
      rw [hR, hE]
      field_simp
      ring
    have hRb : ‖R‖ ≤ CR * (1 + |τ|) ^ (1 / 8 : ℝ) := norm_razao_rho hRH hε hε1 τ
    have hZb : ‖riemannZeta w‖ ≤ CZ * (1 + |τ|) ^ (1 / 16 : ℝ) := by
      have := hZ w (by rw [hwre]) (by rw [hwre]; linarith)
      rwa [hwim] at this
    have hEb : ‖E‖ ≤ CA * (1 + |τ|) ^ (1 / 16 : ℝ) := by
      have := hA N hN w hwre
      rw [hwim] at this
      refine this.trans ?_
      have hN1 : (N : ℝ) ^ (-(ε / 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
      have := mul_le_mul_of_nonneg_left hN1 hCA.le
      have h16 : 0 ≤ (1 + |τ|) ^ (1 / 16 : ℝ) := by positivity
      nlinarith
    have h8 : 0 ≤ (1 + |τ|) ^ (1 / 8 : ℝ) := by positivity
    have h16 : 0 ≤ (1 + |τ|) ^ (1 / 16 : ℝ) := by positivity
    have hZE : ‖riemannZeta w * E‖ ≤ CZ * CA * (1 + |τ|) ^ (1 / 8 : ℝ) := by
      rw [norm_mul, ← p2]
      calc ‖riemannZeta w‖ * ‖E‖ ≤ (CZ * (1 + |τ|) ^ (1 / 16 : ℝ)) *
            (CA * (1 + |τ|) ^ (1 / 16 : ℝ)) :=
            mul_le_mul hZb hEb (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hRZE : ‖R * (riemannZeta w * E)‖ ≤ CR * CZ * CA * (1 + |τ|) ^ (1 / 4 : ℝ) := by
      rw [norm_mul, ← p3]
      calc ‖R‖ * ‖riemannZeta w * E‖ ≤ (CR * (1 + |τ|) ^ (1 / 8 : ℝ)) *
            (CZ * CA * (1 + |τ|) ^ (1 / 8 : ℝ)) :=
            mul_le_mul hRb hZE (norm_nonneg _) (by positivity)
        _ = _ := by ring
    rw [hid]
    calc ‖(1 - R) - R * (riemannZeta w * E)‖ ≤ ‖1 - R‖ + ‖R * (riemannZeta w * E)‖ :=
          norm_sub_le _ _
      _ ≤ (1 + ‖R‖) + ‖R * (riemannZeta w * E)‖ := by
          gcongr
          exact (norm_sub_le _ _).trans (by rw [norm_one])
      _ ≤ (1 + CR * (1 + |τ|) ^ (1 / 8 : ℝ)) + CR * CZ * CA * (1 + |τ|) ^ (1 / 4 : ℝ) := by
          gcongr
      _ ≤ K * (1 + |τ|) ^ (1 / 4 : ℝ) := by
          rw [hK]
          nlinarith [mul_le_mul_of_nonneg_left p5 hCR0.le]
  refine iInf_DN_le_of_aprox_var (mollS ε) (fun τ => (riemannZeta (lc τ + ε))⁻¹)
    (fun τ => 8 * K ^ 2 * (1 + |τ|) ^ (-(2 - 1 / 2 : ℝ))) (integrable_cota K) ?_ ?_
  · intro N
    refine ae_of_all _ fun τ => erro_le_de hK0 ?_
    rw [polD_mollS]
    exact hpt N τ
  · refine ae_of_all _ fun τ => ?_
    simp_rw [polD_mollS]
    have hlim : Tendsto (fun N : ℕ => CA * (N : ℝ) ^ (-(ε / 2)) * (1 + |τ|) ^ (1 / 16 : ℝ))
        atTop (𝓝 0) := by
      have h := (((tendsto_rpow_neg_atTop (by linarith : 0 < ε / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul CA).mul_const ((1 + |τ|) ^ (1 / 16 : ℝ))
      simpa using h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with N hN
    have := hA N hN (lc τ + ε) (lc_add_re τ ε)
    rwa [lc_add_im] at this

/-! ### `J(ε) → 0` sob RH -/

theorem lc_injective : Function.Injective lc := by
  intro a b h
  have := congrArg Complex.im h
  simpa [lc] using this

/-- Os zeros de `ζ` na reta crítica formam um conjunto enumerável. -/
theorem countable_zeros_lc : Set.Countable {τ : ℝ | riemannZeta (lc τ) = 0} := by
  have hsub : {τ : ℝ | riemannZeta (lc τ) = 0} ⊆
      ⋃ n : ℕ, lc ⁻¹' (lc '' Icc (-(n : ℝ)) n ∩ riemannZetaZeros) := by
    intro τ hτ
    obtain ⟨n, hn⟩ := exists_nat_ge |τ|
    refine mem_iUnion.2 ⟨n, ⟨τ, ⟨?_, ?_⟩, rfl⟩, mem_riemannZetaZeros.mpr hτ⟩
    · linarith [neg_abs_le τ]
    · linarith [le_abs_self τ]
  refine Set.Countable.mono hsub (Set.countable_iUnion fun n => ?_)
  exact (((isCompact_Icc.image continuous_lc).inter_riemannZetaZeros_finite).preimage
    lc_injective.injOn).countable

theorem ae_zeta_lc_ne_zero : ∀ᵐ τ : ℝ, riemannZeta (lc τ) ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact countable_zeros_lc.measure_zero _

theorem continuous_zeta_lc_add {ε : ℝ} (hε1 : ε ≤ 1 / 4) :
    Continuous (fun τ : ℝ => riemannZeta (lc τ + ε)) := by
  refine continuous_iff_continuousAt.2 fun τ => ?_
  have hne : lc τ + ε ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [lc_add_re, one_re] at this
    linarith
  exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
    (continuous_lc.add continuous_const).continuousAt

/-- **Sob RH, `J(ε) → 0` quando `ε → 0⁺`.** -/
theorem tendsto_J_RH (hRH : RiemannHypothesis) : Tendsto J (𝓝[>] 0) (𝓝 0) := by
  set K := 1 + 28 * ATK.RazaoZeta.CE with hK
  have hCE := ATK.RazaoZeta.CE_pos
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 / 4 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with ε h1 h2
    exact ⟨h1, h2.le⟩
  have hmain := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := 𝓝[>] (0 : ℝ)) (F := fun ε τ => erro (riemannZeta (lc τ + ε))⁻¹ τ)
    (f := fun _ => (0 : ℝ)) (fun τ => 8 * K ^ 2 * (1 + |τ|) ^ (-(2 - 1 / 2 : ℝ))) ?_ ?_
    (integrable_cota K) ?_
  · show Tendsto (fun ε : ℝ => ∫ τ, erro (riemannZeta (lc τ + ε))⁻¹ τ) _ _
    simpa using hmain
  · filter_upwards [hev] with ε hε
    have hnz : ∀ τ : ℝ, riemannZeta (lc τ + ε) ≠ 0 := fun τ =>
      ATK.RHLogZeta.zeta_ne_zero_of_RH hRH (by rw [lc_add_re]; linarith [hε.1])
    refine Continuous.aestronglyMeasurable ?_
    unfold erro
    exact ((continuous_const.sub (continuous_zeta_lc.mul
      ((continuous_zeta_lc_add hε.2).inv₀ hnz))).div continuous_lc lc_ne_zero).norm.pow 2
  · filter_upwards [hev] with ε hε
    refine ae_of_all _ fun τ => ?_
    rw [Real.norm_of_nonneg (erro_nonneg _ _)]
    refine erro_le_de hK0 ?_
    obtain ⟨-, -, -, -, p5, p6⟩ := rho_pows τ
    have hR := norm_razao_rho hRH hε.1 hε.2 τ
    calc ‖1 - riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹‖
        ≤ ‖(1 : ℂ)‖ + ‖riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹‖ := norm_sub_le _ _
      _ ≤ 1 + 28 * ATK.RazaoZeta.CE * (1 + |τ|) ^ (1 / 8 : ℝ) := by rw [norm_one]; linarith
      _ ≤ K * (1 + |τ|) ^ (1 / 4 : ℝ) := by
          rw [hK]
          have : 0 ≤ 28 * ATK.RazaoZeta.CE := by linarith
          nlinarith [mul_le_mul_of_nonneg_left p5 this]
  · filter_upwards [ae_zeta_lc_ne_zero] with τ hζ
    have hne : lc τ ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [lc_re, one_re] at this
      norm_num at this
    have h1 : Tendsto (fun ε : ℝ => lc τ + (ε : ℂ)) (𝓝 0) (𝓝 (lc τ)) := by
      have : Continuous (fun ε : ℝ => lc τ + (ε : ℂ)) := by fun_prop
      simpa using this.tendsto 0
    have hz : Tendsto (fun ε : ℝ => riemannZeta (lc τ + ε)) (𝓝 0) (𝓝 (riemannZeta (lc τ))) :=
      ((differentiableAt_riemannZeta hne).continuousAt.tendsto).comp h1
    have h2 : Tendsto (fun ε : ℝ => riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹) (𝓝 0)
        (𝓝 1) := by
      have := (hz.inv₀ hζ).const_mul (riemannZeta (lc τ))
      rwa [mul_inv_cancel₀ hζ] at this
    have h3 : Tendsto (fun ε : ℝ => erro (riemannZeta (lc τ + ε))⁻¹ τ) (𝓝 0) (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (1 : ℂ))).sub h2).div_const (lc τ) |>.norm.pow 2
      simpa [erro] using this
    exact h3.mono_left nhdsWithin_le_nhds

/-! ### A recíproca e o critério completo -/

/-- **A recíproca de Báez-Duarte**: RH ⇒ `D_N → 0`. -/
theorem necessidade (hRH : RiemannHypothesis) : Tendsto DN atTop (𝓝 0) := by
  rw [ATK.RiemannConcrete.O1_iff_iInf_zero]
  refine le_antisymm ?_ (le_ciInf DN_nonneg)
  have h0 : Tendsto (fun ε => (2 * π)⁻¹ * J ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_J_RH hRH).const_mul ((2 * π)⁻¹)
  refine ge_of_tendsto h0 ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with ε h1 h2
  exact iInf_DN_le_J_RH hRH h1 h2.le

/-- **Critério de Nyman–Beurling–Báez-Duarte, sem pontes**: `RH ⟺ D_N → 0`. -/
theorem rh_iff_DN : RiemannHypothesis ↔ Tendsto DN atTop (𝓝 0) :=
  ⟨necessidade, baezDuarteCriterion⟩

/-- Forma equivalente: `RH ⟺ inf_N D_N = 0`. -/
theorem rh_iff_iInf_DN : RiemannHypothesis ↔ ⨅ N, DN N = 0 :=
  rh_iff_DN.trans ATK.RiemannConcrete.O1_iff_iInf_zero

/-- **A forma `⟺` da linha `m-core-riemann`** (`ATK.RHConvergence.rh_iff_limit_zero_of_criterion`),
agora sem hipóteses: `bdDistSq → 0 ⟺ RH` (`bdDistSq = D_N` por `rfl`). -/
theorem bdDistSq_iff_rh : Tendsto ATK.Riemann.bdDistSq atTop (𝓝 0) ↔ RiemannHypothesis := by
  rw [ATK.BDDistSqPort.bdDistSq_eq_DN]
  exact rh_iff_DN.symm

end ATK.NecessidadeRH

#print axioms ATK.NecessidadeRH.iInf_DN_le_of_aprox_var
#print axioms ATK.NecessidadeRH.polD_mollS
#print axioms ATK.NecessidadeRH.norm_lc_sq
#print axioms ATK.NecessidadeRH.um_add_abs_sq_le
#print axioms ATK.NecessidadeRH.erro_le_de
#print axioms ATK.NecessidadeRH.integrable_cota
#print axioms ATK.NecessidadeRH.norm_razao_rho
#print axioms ATK.NecessidadeRH.lc_add_re
#print axioms ATK.NecessidadeRH.lc_add_im
#print axioms ATK.NecessidadeRH.rho_pows
#print axioms ATK.NecessidadeRH.iInf_DN_le_J_RH
#print axioms ATK.NecessidadeRH.lc_injective
#print axioms ATK.NecessidadeRH.countable_zeros_lc
#print axioms ATK.NecessidadeRH.ae_zeta_lc_ne_zero
#print axioms ATK.NecessidadeRH.continuous_zeta_lc_add
#print axioms ATK.NecessidadeRH.tendsto_J_RH
#print axioms ATK.NecessidadeRH.necessidade
#print axioms ATK.NecessidadeRH.rh_iff_DN
#print axioms ATK.NecessidadeRH.rh_iff_iInf_DN
#print axioms ATK.NecessidadeRH.bdDistSq_iff_rh
