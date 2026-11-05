import ATK.EspectralDN
import ATK.RiemannConcrete
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# ATK — Necessidade de Báez-Duarte: esqueleto analítico e entradas isoladas

`ATK.EspectralDN` reduz a direção de necessidade (RH ⇒ `D_N → 0`) a um enunciado sobre `ζ` na
linha crítica. Aqui o esqueleto analítico da prova clássica é formalizado e as entradas de teoria
dos números que ela tira de RH ficam isoladas como enunciados nomeados.

Incondicional:

* `integrable_espectro`, `integrable_inv_sq`, `integrable_zeta_sq`: **`|ζ(½+iτ)|²/|½+iτ|²` é
  integrável em `ℝ`** (via Plancherel de Mellin aplicado a `ρ_1`);
* `iInf_DN_le_of_aprox`: convergência dominada — se polinômios de Dirichlet com coeficientes reais
  convergem q.t.p. na linha crítica para `m` com erro espectral dominado, então
  `inf_N D_N ≤ (1/2π) ∫ |1 − ζ(s) m(s)|²/|s|²`;
* `tendsto_polD_moll`, `entradaLittlewood_of_gt_half`, `iInf_DN_le_J_of_gt_half`: com o
  mollificador `a_ε(n) = μ(n) n^{−ε}` e `ε > 1/2`, **`inf_N D_N ≤ (1/2π) J(ε)`**, onde
  `J(ε) = ∫ |1 − ζ(s)/ζ(s+ε)|²/|s|²`.

Condicional (as entradas):

* `EntradaLittlewood ε`: convergência q.t.p. de `Σ μ(n) n^{−ε−s}` para `1/ζ(s+ε)` na linha crítica
  com dominação integrável (provada aqui para `ε > 1/2`; para `0 < ε ≤ 1/2` é a parte que, na
  prova clássica, vem de RH via Littlewood e as cotas de Lindelöf/Titchmarsh);
* `J(ε) → 0` quando `ε → 0⁺` (na prova clássica, de RH via o produto de Hadamard);
* `necessidade_de_entradas`: (RH ⇒ entradas) ⇒ (RH ⇒ `D_N → 0`);
* `rh_iff_DN_of_entradas`: (RH ⇒ entradas) ⇒ (RH ⟺ `D_N → 0`);
* `rh_of_entradas`: entradas ⇒ RH (as entradas têm a força exata de RH).

Nada aqui prova RH nem a necessidade. **CLOSED_MATH continua false.**
-/

open MeasureTheory Set Real Filter Topology FourierTransform
open ATK.Conditional.Riemann ATK.BaezDuarteBridge ATK.MellinRho ATK.EspectralDN

namespace ATK.NecessidadeBD

/-- Ponto `1/2 + iτ` da linha crítica. -/
noncomputable def lc (τ : ℝ) : ℂ := 1 / 2 + (τ : ℂ) * Complex.I

theorem lc_re (τ : ℝ) : (lc τ).re = 1 / 2 := by simp [lc]

theorem lc_ne_zero (τ : ℝ) : lc τ ≠ 0 := by
  intro h
  have := lc_re τ
  rw [h, Complex.zero_re] at this
  norm_num at this

theorem continuous_lc : Continuous lc := by
  unfold lc
  fun_prop

/-! ### Integrabilidade na linha crítica (incondicional) -/

/-- O lado de Mellin do Plancherel é integrável. -/
theorem integrable_mellin_sq {f : ℝ → ℂ} (h1 : MellinConvergent f ((1 / 2 : ℝ) : ℂ))
    (h2 : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi 0)) :
    Integrable (fun τ : ℝ => ‖mellin f (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2) := by
  have hg1 := ATK.MellinPlancherel.integrable_lado h1
  have hsq : Integrable (fun u => ‖ATK.MellinPlancherel.lado f u‖ ^ 2) := by
    have h := (ATK.MellinPlancherel.integrableOn_Ioi_iff (fun t => ‖f t‖ ^ 2)).mp h2
    simpa [ATK.MellinPlancherel.norm_sq_lado] using h
  have hg2 : MemLp (ATK.MellinPlancherel.lado f) 2 :=
    (memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable).mpr hsq
  have hF : Integrable (fun ξ => ‖𝓕 (ATK.MellinPlancherel.lado f) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm
      (ATK.PlancherelL1L2.continuous_fourier hg1).aestronglyMeasurable).mp
      (ATK.PlancherelL1L2.memLp_two_fourier hg1 hg2)
  have hF' := hF.comp_mul_left' (inv_ne_zero (by positivity : (2 * π : ℝ) ≠ 0))
  refine hF'.congr (ae_of_all _ fun τ => ?_)
  simp only
  rw [ATK.MellinPlancherel.fourier_lado, show 2 * π * ((2 * π)⁻¹ * τ) = τ by field_simp]

/-- O integrando espectral é integrável para todo vetor de coeficientes. -/
theorem integrable_espectro {N : ℕ} (c : Fin N → ℝ) : Integrable (espectro c) := by
  have hhalf0 : 0 < (((1 / 2 : ℝ) : ℂ)).re := by simp
  have hhalf1 : (((1 / 2 : ℝ) : ℂ)).re < 1 := by norm_num
  have h1 := (mellin_res_geral c hhalf0 hhalf1).1
  have h2 : IntegrableOn (fun t => ‖((res c t : ℝ) : ℂ)‖ ^ 2) (Ioi 0) := by
    refine (integrable_res_sq c).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Complex.norm_real, sq_abs]
  refine (integrable_mellin_sq h1 h2).congr (ae_of_all _ fun τ => ?_)
  have hre : (1 / 2 + (τ : ℂ) * Complex.I).re = 1 / 2 := by simp
  simp only
  rw [(mellin_res_geral c (by rw [hre]; norm_num) (by rw [hre]; norm_num)).2]
  rfl

/-- `|1/s|²` é integrável na linha crítica. -/
theorem integrable_inv_sq : Integrable (fun τ : ℝ => ‖1 / lc τ‖ ^ 2) := by
  refine (integrable_espectro (fun _ : Fin 0 => (0 : ℝ))).congr (ae_of_all _ fun τ => ?_)
  simp [espectro, lc]

/-- `|(1 + ζ(s))/s|²` é integrável na linha crítica. -/
theorem integrable_one_add_zeta_sq :
    Integrable (fun τ : ℝ => ‖(1 + riemannZeta (lc τ)) / lc τ‖ ^ 2) := by
  refine (integrable_espectro (fun _ : Fin 1 => (1 : ℝ))).congr (ae_of_all _ fun τ => ?_)
  simp [espectro, lc]

theorem continuous_zeta_lc : Continuous (fun τ : ℝ => riemannZeta (lc τ)) := by
  refine continuous_iff_continuousAt.2 fun τ => ?_
  have hne : lc τ ≠ 1 := by
    intro h
    have := lc_re τ
    rw [h, Complex.one_re] at this
    norm_num at this
  exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
    continuous_lc.continuousAt

/-- **`|ζ(½+iτ)|²/|½+iτ|²` é integrável em `ℝ`** (incondicional). -/
theorem integrable_zeta_sq : Integrable (fun τ : ℝ => ‖riemannZeta (lc τ) / lc τ‖ ^ 2) := by
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => ‖riemannZeta (lc τ) / lc τ‖ ^ 2) volume :=
    ((continuous_zeta_lc.div continuous_lc lc_ne_zero).norm.pow 2).aestronglyMeasurable
  refine ((integrable_one_add_zeta_sq.add integrable_inv_sq).const_mul 2).mono' hmeas
    (ae_of_all _ fun τ => ?_)
  have hsplit : riemannZeta (lc τ) / lc τ =
      (1 + riemannZeta (lc τ)) / lc τ - 1 / lc τ := by
    field_simp [lc_ne_zero τ]
    ring
  rw [Real.norm_of_nonneg (by positivity), hsplit]
  set a := (1 + riemannZeta (lc τ)) / lc τ
  set b := 1 / lc τ
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  have h2 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact h1.trans h2

/-! ### Redução por convergência dominada -/

/-- Polinômio de Dirichlet `Σ_{n=1}^{N} a(n) n^{-s}` com coeficientes reais. -/
noncomputable def polD (a : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k : Fin N, (a (k.val + 1) : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-s)

/-- Erro espectral de um alvo `m` em `s = ½ + iτ`: `|1 − ζ(s)·m|²/|s|²`. -/
noncomputable def erro (m : ℂ) (τ : ℝ) : ℝ := ‖(1 - riemannZeta (lc τ) * m) / lc τ‖ ^ 2

theorem erro_nonneg (m : ℂ) (τ : ℝ) : 0 ≤ erro m τ := by
  unfold erro
  positivity

theorem espectro_neg (a : ℕ → ℝ) (N : ℕ) (τ : ℝ) :
    espectro (fun k : Fin N => -a (k.val + 1)) τ = erro (polD a N (lc τ)) τ := by
  simp only [espectro, erro, polD, lc]
  congr 3
  push_cast
  simp [neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- **Convergência dominada.** Se `Σ_{n≤N} a(n) n^{-s} → m(s)` q.t.p. na linha crítica com erro
espectral dominado por uma função integrável, então `inf_N D_N ≤ (1/2π) ∫ |1 − ζ m|²/|s|²`. -/
theorem iInf_DN_le_of_aprox (a : ℕ → ℝ) (m : ℝ → ℂ) (B : ℝ → ℝ) (hB : Integrable B)
    (hdom : ∀ N, ∀ᵐ τ, erro (polD a N (lc τ)) τ ≤ B τ)
    (hconv : ∀ᵐ τ, Tendsto (fun N => polD a N (lc τ)) atTop (𝓝 (m τ))) :
    ⨅ N, DN N ≤ (2 * π)⁻¹ * ∫ τ, erro (m τ) τ := by
  have hbdd : BddBelow (range DN) := ⟨0, by rintro _ ⟨N, rfl⟩; exact DN_nonneg N⟩
  have hle : ∀ N : ℕ, ⨅ n, DN n ≤ (2 * π)⁻¹ * ∫ τ, erro (polD a N (lc τ)) τ := by
    intro N
    refine (ciInf_le hbdd N).trans ?_
    refine (ATK.RiemannConcrete.DN_le_residualSq N (fun k : Fin N => -a (k.val + 1))).trans_eq ?_
    rw [residualSq_espectral]
    congr 2
    funext τ
    exact espectro_neg a N τ
  have hlim : Tendsto (fun N => ∫ τ, erro (polD a N (lc τ)) τ) atTop
      (𝓝 (∫ τ, erro (m τ) τ)) := by
    refine tendsto_integral_of_dominated_convergence B (fun N => ?_) hB (fun N => ?_) ?_
    · exact (integrable_espectro (fun k : Fin N => -a (k.val + 1))).aestronglyMeasurable.congr
        (ae_of_all _ fun τ => espectro_neg a N τ)
    · filter_upwards [hdom N] with τ hτ
      rw [Real.norm_of_nonneg (erro_nonneg _ _)]
      exact hτ
    · filter_upwards [hconv] with τ hτ
      unfold erro
      exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hτ)).div_const _).norm.pow 2
  exact ge_of_tendsto' (hlim.const_mul _) hle

/-- **Forma de família.** Se, ao longo de um filtro, as aproximações valem eventualmente e o erro
limite tende a zero, então `D_N → 0`. -/
theorem DN_tendsto_zero_of_aprox {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → ℕ → ℝ) (m : ι → ℝ → ℂ) (B : ι → ℝ → ℝ)
    (hap : ∀ᶠ j in l, Integrable (B j) ∧ (∀ N, ∀ᵐ τ, erro (polD (a j) N (lc τ)) τ ≤ B j τ) ∧
      ∀ᵐ τ, Tendsto (fun N => polD (a j) N (lc τ)) atTop (𝓝 (m j τ)))
    (hlim : Tendsto (fun j => ∫ τ, erro (m j τ) τ) l (𝓝 0)) :
    Tendsto DN atTop (𝓝 0) := by
  rw [ATK.RiemannConcrete.O1_iff_iInf_zero]
  refine le_antisymm ?_ (le_ciInf DN_nonneg)
  have h0 : Tendsto (fun j => (2 * π)⁻¹ * ∫ τ, erro (m j τ) τ) l (𝓝 0) := by
    simpa using hlim.const_mul ((2 * π)⁻¹)
  refine ge_of_tendsto h0 ?_
  filter_upwards [hap] with j hj
  exact iInf_DN_le_of_aprox (a j) (m j) (B j) hj.1 hj.2.1 hj.2.2

/-! ### O mollificador de Möbius -/

/-- Coeficientes do mollificador: `a_ε(n) = μ(n) n^{-ε}`. -/
noncomputable def moll (ε : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-ε)

/-- `J(ε) = ∫ |1 − ζ(s)/ζ(s+ε)|²/|s|²` na linha crítica. -/
noncomputable def J (ε : ℝ) : ℝ := ∫ τ, erro (riemannZeta (lc τ + ε))⁻¹ τ

theorem polD_moll_eq_term (ε : ℝ) (N : ℕ) (s : ℂ) :
    polD (moll ε) N s = ∑ k : Fin N,
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + ε) (k.val + 1) := by
  unfold polD moll
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k.val)]
  have hn : ((k.val + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k.val)
  have hc : (((((k.val + 1 : ℕ) : ℝ) ^ (-ε) : ℝ)) : ℂ) = ((k.val + 1 : ℕ) : ℂ) ^ (-(ε : ℂ)) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [Complex.ofReal_mul, hc, mul_assoc, ← Complex.cpow_add _ _ hn, div_eq_mul_inv,
    ← Complex.cpow_neg]
  push_cast
  congr 2
  ring

/-- Para `Re(s+ε) > 1`, as somas parciais do mollificador convergem para `1/ζ(s+ε)`. -/
theorem tendsto_polD_moll {ε : ℝ} {s : ℂ} (h : 1 < (s + ε).re) :
    Tendsto (fun N => polD (moll ε) N s) atTop (𝓝 (riemannZeta (s + ε))⁻¹) := by
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + ε) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr h
  have hL : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + ε) =
      (riemannZeta (s + ε))⁻¹ := by
    have := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius h
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta h] at this
    exact eq_inv_of_mul_eq_one_right this
  have h1 := (hasSum_nat_add_iff' 1).mpr hsum.LSeriesHasSum
  simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero, hL] at h1
  refine h1.tendsto_sum_nat.congr fun N => ?_
  rw [polD_moll_eq_term, Fin.sum_univ_eq_sum_range
    (fun i => LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + ε) (i + 1)) N]

/-- Cota uniforme das somas parciais para `ε > 1/2`. -/
theorem norm_polD_moll_le {ε : ℝ} (hε : 1 / 2 < ε) (N : ℕ) (τ : ℝ) :
    ‖polD (moll ε) N (lc τ)‖ ≤ ∑' n : ℕ, (((n : ℝ) + 1) ^ (1 / 2 + ε))⁻¹ := by
  have hsumm : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (1 / 2 + ε))⁻¹) := by
    have := (Real.summable_nat_rpow_inv (p := 1 / 2 + ε)).mpr (by linarith)
    have h2 := (summable_nat_add_iff 1).mpr this
    simpa using h2
  rw [polD_moll_eq_term]
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (lc τ + ε) (i + 1)‖) N]
  refine le_trans (Finset.sum_le_sum fun n _ => ?_)
    (hsumm.sum_le_tsum (Finset.range N) (fun _ _ => by positivity))
  simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, ↓reduceIte]
  have hre : (lc τ + ε).re = 1 / 2 + ε := by simp [lc]
  rw [hre, div_eq_mul_inv]
  push_cast
  refine mul_le_of_le_one_left (by positivity) ?_
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **Entrada analítica em `ε`**: as somas parciais de `Σ μ(n) n^{-ε-s}` convergem q.t.p. na linha
crítica para `1/ζ(s+ε)`, com erro espectral dominado por uma função integrável. -/
def EntradaLittlewood (ε : ℝ) : Prop :=
  (∃ B : ℝ → ℝ, Integrable B ∧ ∀ N, ∀ᵐ τ, erro (polD (moll ε) N (lc τ)) τ ≤ B τ) ∧
    ∀ᵐ τ, Tendsto (fun N => polD (moll ε) N (lc τ)) atTop (𝓝 (riemannZeta (lc τ + ε))⁻¹)

/-- **A entrada vale incondicionalmente para `ε > 1/2`.** -/
theorem entradaLittlewood_of_gt_half {ε : ℝ} (hε : 1 / 2 < ε) : EntradaLittlewood ε := by
  set C := ∑' n : ℕ, (((n : ℝ) + 1) ^ (1 / 2 + ε))⁻¹ with hCdef
  have hC : 0 ≤ C := tsum_nonneg fun n => by positivity
  refine ⟨⟨fun τ => 2 * (1 + C) ^ 2 *
      (‖1 / lc τ‖ ^ 2 + ‖(1 + riemannZeta (lc τ)) / lc τ‖ ^ 2), ?_, ?_⟩, ?_⟩
  · exact (integrable_inv_sq.add integrable_one_add_zeta_sq).const_mul _
  · intro N
    refine ae_of_all _ fun τ => ?_
    have hP := norm_polD_moll_le hε N τ
    unfold erro
    simp only
    set P := polD (moll ε) N (lc τ)
    set z := riemannZeta (lc τ)
    set s := lc τ
    have hs : s ≠ 0 := lc_ne_zero τ
    have hz : ‖z‖ ≤ 1 + ‖1 + z‖ := by
      have e : z = (1 + z) - 1 := by ring
      calc ‖z‖ = ‖(1 + z) - 1‖ := by rw [← e]
        _ ≤ ‖1 + z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + ‖1 + z‖ := by rw [norm_one]; ring
    have h1 : ‖1 - z * P‖ ≤ (1 + C) * (1 + ‖1 + z‖) := by
      calc ‖1 - z * P‖ ≤ ‖(1 : ℂ)‖ + ‖z * P‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ * ‖P‖ := by rw [norm_one, norm_mul]
        _ ≤ 1 + (1 + ‖1 + z‖) * C := by gcongr
        _ ≤ (1 + C) * (1 + ‖1 + z‖) := by nlinarith [norm_nonneg (1 + z)]
    have h2 : ‖1 - z * P‖ ^ 2 ≤ 2 * (1 + C) ^ 2 * (1 + ‖1 + z‖ ^ 2) := by
      calc ‖1 - z * P‖ ^ 2 ≤ ((1 + C) * (1 + ‖1 + z‖)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ 2 * (1 + C) ^ 2 * (1 + ‖1 + z‖ ^ 2) := by
            nlinarith [mul_nonneg (sq_nonneg (1 + C)) (sq_nonneg (1 - ‖1 + z‖))]
    have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have e : 2 * (1 + C) ^ 2 * (‖1 / s‖ ^ 2 + ‖(1 + z) / s‖ ^ 2) =
        (2 * (1 + C) ^ 2 * (1 + ‖1 + z‖ ^ 2)) / ‖s‖ ^ 2 := by
      rw [norm_div, norm_div, norm_one]
      field_simp
    rw [e, norm_div, div_pow]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  · refine ae_of_all _ fun τ => tendsto_polD_moll ?_
    have hre : (lc τ + ε).re = 1 / 2 + ε := by simp [lc]
    rw [hre]
    linarith

/-- Uma entrada em `ε` dá `inf_N D_N ≤ (1/2π) J(ε)`. -/
theorem iInf_DN_le_J {ε : ℝ} (h : EntradaLittlewood ε) : ⨅ N, DN N ≤ (2 * π)⁻¹ * J ε := by
  obtain ⟨⟨B, hB, hd⟩, hc⟩ := h
  exact iInf_DN_le_of_aprox (moll ε) (fun τ => (riemannZeta (lc τ + ε))⁻¹) B hB hd hc

/-- **Cota incondicional**: para todo `ε > 1/2`,
`inf_N D_N ≤ (1/2π) ∫ |1 − ζ(½+iτ)/ζ(½+ε+iτ)|²/|½+iτ|² dτ`. -/
theorem iInf_DN_le_J_of_gt_half {ε : ℝ} (hε : 1 / 2 < ε) : ⨅ N, DN N ≤ (2 * π)⁻¹ * J ε :=
  iInf_DN_le_J (entradaLittlewood_of_gt_half hε)

/-! ### As entradas da prova clássica -/

/-- As entradas que a prova clássica tira de RH: a entrada de Littlewood para `ε` pequeno e
`J(ε) → 0` quando `ε → 0⁺`. -/
def EntradasNecessidade : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), EntradaLittlewood ε) ∧ Tendsto J (𝓝[>] 0) (𝓝 0)

/-- **Entradas ⇒ `D_N → 0`.** -/
theorem DN_tendsto_zero_of_entradas (h : EntradasNecessidade) : Tendsto DN atTop (𝓝 0) := by
  rw [ATK.RiemannConcrete.O1_iff_iInf_zero]
  refine le_antisymm ?_ (le_ciInf DN_nonneg)
  have h0 : Tendsto (fun ε => (2 * π)⁻¹ * J ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using h.2.const_mul ((2 * π)⁻¹)
  refine ge_of_tendsto h0 ?_
  filter_upwards [h.1] with ε hε
  exact iInf_DN_le_J hε

/-- **Necessidade de Báez-Duarte, módulo as entradas.** -/
theorem necessidade_de_entradas (h : RiemannHypothesis → EntradasNecessidade) :
    RiemannHypothesis → Tendsto DN atTop (𝓝 0) := fun hRH =>
  DN_tendsto_zero_of_entradas (h hRH)

/-- Com B1: se RH entrega as entradas, então **RH ⟺ `D_N → 0`**. -/
theorem rh_iff_DN_of_entradas (h : RiemannHypothesis → EntradasNecessidade) :
    RiemannHypothesis ↔ Tendsto DN atTop (𝓝 0) :=
  ⟨necessidade_de_entradas h, baezDuarteCriterion⟩

/-- As entradas implicam RH: elas têm a força exata de RH (a volta é a análise clássica). -/
theorem rh_of_entradas (h : EntradasNecessidade) : RiemannHypothesis :=
  baezDuarteCriterion (DN_tendsto_zero_of_entradas h)

end ATK.NecessidadeBD

#print axioms ATK.NecessidadeBD.integrable_mellin_sq
#print axioms ATK.NecessidadeBD.integrable_espectro
#print axioms ATK.NecessidadeBD.integrable_inv_sq
#print axioms ATK.NecessidadeBD.integrable_one_add_zeta_sq
#print axioms ATK.NecessidadeBD.integrable_zeta_sq
#print axioms ATK.NecessidadeBD.espectro_neg
#print axioms ATK.NecessidadeBD.iInf_DN_le_of_aprox
#print axioms ATK.NecessidadeBD.DN_tendsto_zero_of_aprox
#print axioms ATK.NecessidadeBD.polD_moll_eq_term
#print axioms ATK.NecessidadeBD.tendsto_polD_moll
#print axioms ATK.NecessidadeBD.norm_polD_moll_le
#print axioms ATK.NecessidadeBD.entradaLittlewood_of_gt_half
#print axioms ATK.NecessidadeBD.iInf_DN_le_J
#print axioms ATK.NecessidadeBD.iInf_DN_le_J_of_gt_half
#print axioms ATK.NecessidadeBD.DN_tendsto_zero_of_entradas
#print axioms ATK.NecessidadeBD.necessidade_de_entradas
#print axioms ATK.NecessidadeBD.rh_iff_DN_of_entradas
#print axioms ATK.NecessidadeBD.rh_of_entradas
