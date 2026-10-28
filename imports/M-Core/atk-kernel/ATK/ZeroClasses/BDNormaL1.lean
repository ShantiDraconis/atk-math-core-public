import ATK.ZeroClasses.TNPPi
import ATK.ZeroClasses.ExplicitaInteira

/-!
# `‖c‖₁` controlado por `‖res‖²_σ` à direita de `Θ`, e `κ(σ) ≤ (2σ + 3)(σ − Θ)/Θ` (rodada 82)

A rodada 79 provou o piso `ℓ¹` só na classe restrita `‖c‖₁ ≤ N^A`. Aqui mostramos que, para `σ > Θ`, **todo** `c` com
`‖res_c‖²_σ ≤ 1` já está numa classe dessas:

  **`‖c‖₁ ≤ K N^{σ + 3/2 + 2η}`**   (`norma_l1_le`).

Isso vale sob `SemZeros θ`, com `θ < σ < 1` e `η > 0`. A prova tem três peças:
* **valor médio** (`media_inf`): `∫_{−T}^{T} |Σ_k a_k (k+1)^{−iτ}|² dτ ≥ (2T − 2N(N + 1)) Σ a_k²`. Os termos fora da
  diagonal custam `≤ 2/|log((j+1)/(k+1))| ≤ 2(N + 1)` (`abs_log_ge_N`, rodada 78). É a forma elementar de
  Montgomery–Vaughan;
* **`1/ζ` na reta** (`QuasiRH.norm_F_le`): `|1/ζ(σ + iτ)| ≤ C(1 + |τ|)^η` sob `SemZeros θ`, e então
  `P = (1 + ζP)/ζ − 1/ζ` com `∫ |1 + ζP|²/|s|² = 2π‖res‖²_σ` (Plancherel, `int_espectro_le`);
* `T = 2N(N + 1)` e Cauchy–Schwarz.

Classificação (rodada 82): **ferramenta** (consumida na rodada 83). RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology Metric FourierTransform
open scoped Real Interval

namespace ATK.ZeroClasses.BDNormaL1

open ATK.BaezDuarteBridge (res)
open ATK.ZeroClasses.BDPonderado (Wσ DNσ Wσ_nonneg integrable_w)
open ATK.ZeroClasses.BDEspectral (espectroσ Wσ_espectral)
open ATK.ZeroClasses.QuasiRH (SemZeros norm_F_le)
open ATK.RHLogZeta (F F_eq)

/-! ## 1. A densidade espectral é integrável -/

/-- `τ ↦ |M f(½ + iτ)|²` é integrável (Plancherel `L¹ ∩ L²`). -/
theorem integrable_mellin_meio {f : ℝ → ℂ} (h1 : MellinConvergent f ((1 / 2 : ℝ) : ℂ))
    (h2 : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi 0)) :
    Integrable (fun τ : ℝ => ‖mellin f (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2) := by
  have hg1 : Integrable (ATK.MellinPlancherel.lado f) := ATK.MellinPlancherel.integrable_lado h1
  have hsq : Integrable (fun u => ‖ATK.MellinPlancherel.lado f u‖ ^ 2) := by
    have h := (ATK.MellinPlancherel.integrableOn_Ioi_iff (fun t => ‖f t‖ ^ 2)).mp h2
    simpa [ATK.MellinPlancherel.norm_sq_lado] using h
  have hg2 : MemLp (ATK.MellinPlancherel.lado f) 2 :=
    (memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable).mpr hsq
  have hF := ATK.PlancherelL1L2.memLp_two_fourier hg1 hg2
  have hFi : Integrable (fun ξ => ‖𝓕 (ATK.MellinPlancherel.lado f) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have e : (fun ξ => ‖𝓕 (ATK.MellinPlancherel.lado f) ξ‖ ^ 2) =
      fun ξ : ℝ => (fun τ : ℝ => ‖mellin f (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2) ((2 * π) * ξ) := by
    funext ξ
    rw [ATK.MellinPlancherel.fourier_lado]
  rw [e] at hFi
  exact (integrable_comp_mul_left_iff _ (by positivity : (2 * π : ℝ) ≠ 0)).mp hFi

/-- **`espectroσ σ c` é integrável** em `ℝ` (`0 < σ < 1`). -/
theorem integrable_espectro {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) :
    Integrable (espectroσ σ c) := by
  set f : ℝ → ℂ := fun t => ((res c t : ℝ) : ℂ) with hf
  have hM := (ATK.EspectralDN.mellin_res_geral c (s := (σ : ℂ)) (by simpa using hσ0)
    (by simpa using hσ1)).1
  have h2 : IntegrableOn (fun t => ‖f t‖ ^ 2 * t ^ (2 * σ - 1)) (Ioi 0) := by
    refine (integrable_w c hσ0 hσ1).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [hf, Complex.norm_real, sq_abs]
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (((σ - 1 / 2 : ℝ)) : ℂ) • f t with hg
  have hg1 : MellinConvergent g ((1 / 2 : ℝ) : ℂ) := by
    rw [hg, MellinConvergent.cpow_smul]
    have e : ((1 / 2 : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
    rw [e]
    exact hM
  have hnorm : ∀ t ∈ Ioi (0 : ℝ), ‖g t‖ ^ 2 = ‖f t‖ ^ 2 * t ^ (2 * σ - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [hg]
    simp only
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, ofReal_re, mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    push_cast
    rw [show (σ - 1 / 2) * 2 = 2 * σ - 1 by ring]
    ring
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioi 0) :=
    h2.congr_fun (fun t ht => (hnorm t ht).symm) measurableSet_Ioi
  have hI := integrable_mellin_meio hg1 hg2
  have e2 : ∀ τ : ℝ, mellin g (1 / 2 + (τ : ℂ) * I) = mellin f ((σ : ℂ) + (τ : ℂ) * I) := by
    intro τ
    rw [hg, mellin_cpow_smul]
    congr 1
    push_cast
    ring
  refine hI.congr (ae_of_all _ fun τ => ?_)
  have hre : ((σ : ℂ) + (τ : ℂ) * I).re = σ := by simp
  simp only [espectroσ]
  rw [e2, (ATK.EspectralDN.mellin_res_geral c (by rw [hre]; exact hσ0) (by rw [hre]; exact hσ1)).2]

/-- `∫_{−T}^{T} espectroσ ≤ 2π ‖res‖²_σ`. -/
theorem int_espectro_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in (-T)..T, espectroσ σ c τ ≤ 2 * π * Wσ σ c := by
  have hI := integrable_espectro hσ0 hσ1 c
  have hW := Wσ_espectral hσ0 hσ1 c
  have hnn : ∀ τ, 0 ≤ espectroσ σ c τ := fun τ => by unfold espectroσ; positivity
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∫ τ in Ioc (-T) T, espectroσ σ c τ ≤ ∫ τ, espectroσ σ c τ :=
    setIntegral_le_integral hI (ae_of_all _ hnn)
  rw [hW]
  have : 2 * π * ((2 * π)⁻¹ * ∫ τ : ℝ, espectroσ σ c τ) = ∫ τ : ℝ, espectroσ σ c τ := by
    field_simp
  rw [this]
  exact h1

/-! ## 2. Valor médio de polinômios de Dirichlet -/

/-- `|∫_{−T}^{T} cos(μτ) dτ| ≤ 2/|μ|` para `μ ≠ 0`. -/
theorem int_cos_abs {μ T : ℝ} (hμ : μ ≠ 0) : |∫ τ in (-T)..T, Real.cos (μ * τ)| ≤ 2 / |μ| := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hμ, integral_cos, smul_eq_mul]
  have hs : |Real.sin (μ * T) - Real.sin (μ * -T)| ≤ 2 := by
    have h1 := Real.abs_sin_le_one (μ * T)
    have h2 := Real.abs_sin_le_one (μ * -T)
    calc |Real.sin (μ * T) - Real.sin (μ * -T)| ≤ |Real.sin (μ * T)| + |Real.sin (μ * -T)| :=
          abs_sub _ _
      _ ≤ 2 := by linarith
  rw [abs_mul, abs_inv, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hs (abs_nonneg μ)

/-- `|Σ_k a_k e^{−iτλ_k}|² = Σ_j Σ_k a_j a_k cos((λ_j − λ_k)τ)`. -/
theorem norm_sq_soma {N : ℕ} (a lam : Fin N → ℝ) (τ : ℝ) :
    ‖∑ k, (a k : ℂ) * Complex.exp (((-(τ * lam k) : ℝ) : ℂ) * I)‖ ^ 2 =
      ∑ j, ∑ k, a j * a k * Real.cos ((lam j - lam k) * τ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hre : (∑ k, (a k : ℂ) * Complex.exp (((-(τ * lam k) : ℝ) : ℂ) * I)).re =
      ∑ k, a k * Real.cos (τ * lam k) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : (∑ k, (a k : ℂ) * Complex.exp (((-(τ * lam k) : ℝ) : ℂ) * I)).im =
      -∑ k, a k * Real.sin (τ * lam k) := by
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring
  rw [hre, him, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (lam j - lam k) * τ = τ * lam j - τ * lam k by ring, Real.cos_sub]
  ring

/-- `(k + 1)^{−iτ} = e^{−iτ log(k+1)}`. -/
theorem cpow_neg_I (k : ℕ) (τ : ℝ) :
    ((k + 1 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)) = Complex.exp (((-(τ * Real.log (k + 1)) : ℝ) : ℂ) * I) := by
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  rw [Complex.cpow_def_of_ne_zero hk]
  congr 1
  have hl : Complex.log ((k + 1 : ℕ) : ℂ) = ((Real.log (k + 1) : ℝ) : ℂ) := by
    rw [show ((k + 1 : ℕ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  rw [hl]
  push_cast
  ring

/-- **Valor médio (forma elementar de Montgomery–Vaughan)**: para `a` real,
`∫_{−T}^{T} |Σ_{k<N} a_k (k+1)^{−iτ}|² dτ ≥ (2T − 2(N + 1)N) Σ a_k²`. -/
theorem media_inf {N : ℕ} (a : Fin N → ℝ) (T : ℝ) :
    (2 * T - 2 * ((N : ℝ) + 1) * N) * ∑ k, a k ^ 2 ≤
      ∫ τ in (-T)..T, ‖∑ k : Fin N, (a k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-((τ : ℂ) * I))‖ ^ 2 := by
  set lam : Fin N → ℝ := fun k => Real.log ((k.val : ℝ) + 1) with hlam
  have e : ∀ τ : ℝ, ‖∑ k : Fin N, (a k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-((τ : ℂ) * I))‖ ^ 2 =
      ∑ j, ∑ k, a j * a k * Real.cos ((lam j - lam k) * τ) := by
    intro τ
    rw [← norm_sq_soma a lam τ]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cpow_neg_I]
  simp_rw [e]
  have hint : ∀ j k : Fin N, IntervalIntegrable (fun τ => a j * a k * Real.cos ((lam j - lam k) * τ))
      volume (-T) T := fun j k => (by fun_prop : Continuous fun τ : ℝ =>
        a j * a k * Real.cos ((lam j - lam k) * τ)).intervalIntegrable _ _
  have hint2 : ∀ j : Fin N, IntervalIntegrable
      (fun τ => ∑ k, a j * a k * Real.cos ((lam j - lam k) * τ)) volume (-T) T := fun j =>
    (continuous_finsetSum _ fun k _ => (by fun_prop : Continuous fun τ : ℝ =>
      a j * a k * Real.cos ((lam j - lam k) * τ))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum fun j _ => hint2 j]
  have hin : ∀ j : Fin N, ∫ τ in (-T)..T, ∑ k, a j * a k * Real.cos ((lam j - lam k) * τ) =
      ∑ k, a j * a k * ∫ τ in (-T)..T, Real.cos ((lam j - lam k) * τ) := by
    intro j
    rw [intervalIntegral.integral_finsetSum fun k _ => hint j k]
    simp_rw [intervalIntegral.integral_const_mul]
  simp_rw [hin]
  have hterm : ∀ j k : Fin N, (if j = k then 2 * T * a j ^ 2 else 0) - 2 * ((N : ℝ) + 1) * (|a j| * |a k|) ≤
      a j * a k * ∫ τ in (-T)..T, Real.cos ((lam j - lam k) * τ) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      have h0 : ∫ τ in (-T)..T, Real.cos ((lam j - lam j) * τ) = 2 * T := by
        simp only [sub_self, zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
        ring
      rw [h0, ite_eq_left_of_eq_true _ _ (eq_self j)]
      have : 0 ≤ 2 * ((N : ℝ) + 1) * (|a j| * |a j|) := by positivity
      nlinarith
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hjk), zero_sub]
      have hne : (j.val + 1 : ℕ) ≠ (k.val + 1 : ℕ) := fun h => hjk (Fin.ext (by omega))
      have hab := ATK.ZeroClasses.ExplicitaInteira.abs_log_ge_N (N := j.val + 1) (n := k.val + 1)
        (Nat.succ_ne_zero _) (Nat.succ_ne_zero _) (Ne.symm hne)
      have hμ : lam j - lam k = Real.log (((j.val + 1 : ℕ) : ℝ) / ((k.val + 1 : ℕ) : ℝ)) := by
        simp only [hlam]
        rw [Real.log_div (by positivity) (by positivity)]
        push_cast
        ring
      have hj : (((j.val + 1 : ℕ) : ℝ) + 1) ≤ (N : ℝ) + 1 := by
        have h1 := j.isLt
        have h2 : ((j.val + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
        linarith
      have hN1 : 1 / ((N : ℝ) + 1) ≤ |lam j - lam k| := by
        rw [hμ]
        exact le_trans (one_div_le_one_div_of_le (by positivity) hj) hab
      have hμ0 : 0 < |lam j - lam k| := lt_of_lt_of_le (by positivity) hN1
      have hμle : 2 / |lam j - lam k| ≤ 2 * ((N : ℝ) + 1) := by
        rw [div_le_iff₀ hμ0]
        rw [div_le_iff₀ (by positivity)] at hN1
        nlinarith
      have hI := int_cos_abs (T := T) (abs_pos.mp hμ0)
      have hprod : |a j * a k * ∫ τ in (-T)..T, Real.cos ((lam j - lam k) * τ)| ≤
          2 * ((N : ℝ) + 1) * (|a j| * |a k|) := by
        rw [abs_mul, abs_mul]
        have := mul_le_mul_of_nonneg_left (hI.trans hμle) (mul_nonneg (abs_nonneg (a j)) (abs_nonneg (a k)))
        linarith
      exact neg_le_of_abs_le hprod
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm j k
  refine le_trans ?_ hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hcs : (∑ k, |a k|) ^ 2 ≤ (N : ℝ) * ∑ k, a k ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k : Fin N => |a k|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    exact h
  have hdd : ∑ j : Fin N, ∑ k : Fin N, 2 * ((N : ℝ) + 1) * (|a j| * |a k|) =
      2 * ((N : ℝ) + 1) * (∑ k, |a k|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  rw [hdd, ← Finset.mul_sum]
  have : 0 ≤ 2 * ((N : ℝ) + 1) := by positivity
  nlinarith

/-! ## 3. `‖c‖₁` controlado por `‖res‖²_σ` -/

/-- `P_c(σ + iτ) = Σ_k a_k (k+1)^{−iτ}`, `a_k = c_k (k+1)^{−σ}`. -/
theorem soma_sigma {N : ℕ} (c : Fin N → ℝ) (σ τ : ℝ) :
    ∑ k : Fin N, (c k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * I)) =
      ∑ k : Fin N, ((c k * ((k.val : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((k.val + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  rw [neg_add, Complex.cpow_add _ _ hk]
  have e : ((k.val + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) = ((((k.val : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    rw [show ((k.val + 1 : ℕ) : ℂ) = (((k.val : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity)]
  rw [e]
  push_cast
  ring

/-- **Cota pontual**: na reta `Re s = σ`, com `|1/ζ(s)| ≤ B` e `‖s‖ ≤ 1 + T`,
`|P_c(s)|² ≤ 2B²(espectroσ · (1 + T)² + 1)`. -/
theorem norm_P_sq_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) {τ T B : ℝ}
    (hs : ‖(σ : ℂ) + (τ : ℂ) * I‖ ≤ 1 + T)
    (hζ : riemannZeta ((σ : ℂ) + (τ : ℂ) * I) ≠ 0) (hF : ‖F ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ B) :
    ‖∑ k : Fin N, (c k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * I))‖ ^ 2 ≤
      2 * B ^ 2 * (espectroσ σ c τ * (1 + T) ^ 2 + 1) := by
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hsdef
  set P : ℂ := ∑ k : Fin N, (c k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-s) with hP
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [hsdef] at this
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hsdef] at this
    linarith
  have hζF : riemannZeta s * F s = 1 := by rw [F_eq hs1, mul_inv_cancel₀ hζ]
  have eP : P = (1 + riemannZeta s * P) * F s - F s := by linear_combination (-P) * hζF
  have hB : 0 ≤ B := (norm_nonneg _).trans hF
  have h1 : ‖P‖ ≤ (‖1 + riemannZeta s * P‖ + 1) * B := by
    calc ‖P‖ = ‖(1 + riemannZeta s * P) * F s - F s‖ := congrArg norm eP
      _ ≤ ‖(1 + riemannZeta s * P) * F s‖ + ‖F s‖ := norm_sub_le _ _
      _ = (‖1 + riemannZeta s * P‖ + 1) * ‖F s‖ := by rw [norm_mul]; ring
      _ ≤ (‖1 + riemannZeta s * P‖ + 1) * B := mul_le_mul_of_nonneg_left hF (by positivity)
  have hesp : espectroσ σ c τ = ‖1 + riemannZeta s * P‖ ^ 2 / ‖s‖ ^ 2 := by
    simp only [espectroσ, hP, hsdef]
    rw [norm_div, div_pow]
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have h2 : ‖1 + riemannZeta s * P‖ ^ 2 ≤ espectroσ σ c τ * (1 + T) ^ 2 := by
    rw [hesp, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (norm_nonneg s) hs 2
    nlinarith [sq_nonneg ‖1 + riemannZeta s * P‖]
  have h3 : ‖P‖ ^ 2 ≤ ((‖1 + riemannZeta s * P‖ + 1) * B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : (‖1 + riemannZeta s * P‖ + 1) ^ 2 ≤ 2 * (‖1 + riemannZeta s * P‖ ^ 2 + 1) := by
    nlinarith [sq_nonneg (‖1 + riemannZeta s * P‖ - 1)]
  calc ‖P‖ ^ 2 ≤ ((‖1 + riemannZeta s * P‖ + 1) * B) ^ 2 := h3
    _ = (‖1 + riemannZeta s * P‖ + 1) ^ 2 * B ^ 2 := by ring
    _ ≤ 2 * (‖1 + riemannZeta s * P‖ ^ 2 + 1) * B ^ 2 :=
        mul_le_mul_of_nonneg_right h4 (sq_nonneg B)
    _ ≤ 2 * (espectroσ σ c τ * (1 + T) ^ 2 + 1) * B ^ 2 := by
        have := mul_le_mul_of_nonneg_right h2 (sq_nonneg B)
        nlinarith [sq_nonneg B]
    _ = 2 * B ^ 2 * (espectroσ σ c τ * (1 + T) ^ 2 + 1) := by ring

/-- **A média superior**: na reta `Re s = σ`, se `ζ ≠ 0` e `|1/ζ| ≤ B` em `|τ| ≤ T`, então
`∫_{−T}^{T} |Σ_k a_k (k+1)^{−iτ}|² ≤ 2B²((1 + T)² · 2π‖res‖²_σ + 2T)`, `a_k = c_k (k+1)^{−σ}`. -/
theorem media_sup {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) {T B : ℝ} (hT0 : 0 ≤ T)
    (hζ : ∀ τ ∈ Icc (-T) T, riemannZeta ((σ : ℂ) + (τ : ℂ) * I) ≠ 0)
    (hF : ∀ τ ∈ Icc (-T) T, ‖F ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ B) :
    ∫ τ in (-T)..T, ‖∑ k : Fin N, ((c k * ((k.val : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
        ((k.val + 1 : ℕ) : ℂ) ^ (-((τ : ℂ) * I))‖ ^ 2 ≤
      2 * B ^ 2 * ((1 + T) ^ 2 * (2 * π * Wσ σ c) + 2 * T) := by
  set G : ℝ → ℝ := fun τ => ‖∑ k : Fin N, ((c k * ((k.val : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
      ((k.val + 1 : ℕ) : ℂ) ^ (-((τ : ℂ) * I))‖ ^ 2 with hG
  have hGpt : ∀ τ ∈ Icc (-T) T, G τ ≤ 2 * B ^ 2 * (espectroσ σ c τ * (1 + T) ^ 2 + 1) := by
    intro τ hτ
    have hτa : |τ| ≤ T := abs_le.mpr ⟨hτ.1, hτ.2⟩
    have hs : ‖(σ : ℂ) + (τ : ℂ) * I‖ ≤ 1 + T := by
      calc ‖(σ : ℂ) + (τ : ℂ) * I‖ ≤ ‖(σ : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + |τ| := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 + T := by rw [abs_of_pos hσ0]; linarith
    have h := norm_P_sq_le hσ0 hσ1 c hs (hζ τ hτ) (hF τ hτ)
    rw [soma_sigma] at h
    exact h
  have hGi : IntervalIntegrable G volume (-T) T := by
    apply Continuous.intervalIntegrable
    have hc : Continuous fun τ : ℝ => ∑ k : Fin N, ((c k * ((k.val : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
        ((k.val + 1 : ℕ) : ℂ) ^ (-((τ : ℂ) * I)) := by
      refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
      have hk : ((k.val + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      exact continuous_iff_continuousAt.mpr fun τ => (continuousAt_const_cpow hk).comp
        (by fun_prop : Continuous fun τ : ℝ => -((τ : ℂ) * I)).continuousAt
    exact (continuous_norm.comp hc).pow 2
  have hEi : IntervalIntegrable (espectroσ σ c) volume (-T) T :=
    (integrable_espectro hσ0 hσ1 c).intervalIntegrable
  have hmono : ∫ τ in (-T)..T, G τ ≤ ∫ τ in (-T)..T, 2 * B ^ 2 * (espectroσ σ c τ * (1 + T) ^ 2 + 1) :=
    intervalIntegral.integral_mono_on (by linarith) hGi
      (((hEi.mul_const _).add intervalIntegrable_const).const_mul _) hGpt
  have hval : ∫ τ in (-T)..T, 2 * B ^ 2 * (espectroσ σ c τ * (1 + T) ^ 2 + 1) =
      2 * B ^ 2 * ((1 + T) ^ 2 * (∫ τ in (-T)..T, espectroσ σ c τ) + 2 * T) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hEi.mul_const _)
      intervalIntegrable_const, intervalIntegral.integral_mul_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one, sub_neg_eq_add]
    ring
  have h1 := int_espectro_le hσ0 hσ1 c hT0
  rw [hval] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have : 0 ≤ (1 + T) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h1 this
  linarith

/-- Aritmética: com `T = 2N(N + 1)`, `N ≥ 1`, `W ≤ 1`, `0 ≤ B ≤ D`,
`2N(N + 1) X ≤ 2B²((1 + T)² · 2πW + 2T)` dá `X ≤ D²(50π + 8)N²`. -/
theorem arit_X {N X B D W : ℝ} (hN : 1 ≤ N) (hB : 0 ≤ B) (hBD : B ≤ D) (hW0 : 0 ≤ W) (hW : W ≤ 1)
    (h : 2 * N * (N + 1) * X ≤ 2 * B ^ 2 * ((1 + 2 * N * (N + 1)) ^ 2 * (2 * π * W) + 2 * (2 * N * (N + 1)))) :
    X ≤ D ^ 2 * (50 * π + 8) * N ^ 2 := by
  have hpi := Real.pi_pos
  set T : ℝ := 2 * N * (N + 1) with hT
  have hT4 : T ≤ 4 * N ^ 2 := by rw [hT]; nlinarith
  have h1T : 0 ≤ 1 + T := by rw [hT]; positivity
  have h5 : (1 + T) ^ 2 ≤ 25 * N ^ 4 := by
    have : 1 + T ≤ 5 * N ^ 2 := by nlinarith
    have h' := pow_le_pow_left₀ h1T this 2
    nlinarith
  have hN24 : N ^ 2 ≤ N ^ 4 := by nlinarith
  have hpoly : (1 + T) ^ 2 * (2 * π * W) + 2 * T ≤ (50 * π + 8) * N ^ 4 := by
    have a1 : (1 + T) ^ 2 * (2 * π * W) ≤ 25 * N ^ 4 * (2 * π) := by
      have : 2 * π * W ≤ 2 * π := by nlinarith
      have h2pw : 0 ≤ 2 * π * W := by positivity
      calc (1 + T) ^ 2 * (2 * π * W) ≤ 25 * N ^ 4 * (2 * π * W) := mul_le_mul_of_nonneg_right h5 h2pw
        _ ≤ 25 * N ^ 4 * (2 * π) := mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  have hB2 : B ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hB hBD 2
  have hp : 0 ≤ (1 + T) ^ 2 * (2 * π * W) + 2 * T := by rw [hT]; positivity
  have hstep : 2 * B ^ 2 * ((1 + T) ^ 2 * (2 * π * W) + 2 * T) ≤ 2 * D ^ 2 * ((50 * π + 8) * N ^ 4) := by
    have := mul_le_mul hB2 hpoly hp (sq_nonneg _)
    linarith
  have hN2 : 2 * N ^ 2 ≤ 2 * N * (N + 1) := by nlinarith
  have hXpos_or : 0 ≤ X ∨ X < 0 := le_or_gt 0 X
  have hN2pos : 0 < 2 * N ^ 2 := by positivity
  rcases hXpos_or with hX | hX
  · have hfin : 2 * N ^ 2 * X ≤ 2 * N ^ 2 * (D ^ 2 * (50 * π + 8) * N ^ 2) := by
      have := mul_le_mul_of_nonneg_right hN2 hX
      nlinarith
    exact le_of_mul_le_mul_left hfin hN2pos
  · have : 0 ≤ D ^ 2 * (50 * π + 8) * N ^ 2 := by positivity
    linarith

/-- `(Σ|a|)² ≤ N Σ a²` e `Σ a² ≤ D²(50π + 8)N²` dão `Σ|a| ≤ D √(50π + 8) N √N`. -/
theorem soma_abs_le {N : ℕ} (a : Fin N → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (h : ∑ k, a k ^ 2 ≤ D ^ 2 * (50 * π + 8) * (N : ℝ) ^ 2) :
    ∑ k, |a k| ≤ D * Real.sqrt (50 * π + 8) * ((N : ℝ) * Real.sqrt N) := by
  have hcs : (∑ k, |a k|) ^ 2 ≤ (N : ℝ) * ∑ k, a k ^ 2 := by
    have h' := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k : Fin N => |a k|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h'
    exact h'
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have hM0 : 0 ≤ D * Real.sqrt (50 * π + 8) * ((N : ℝ) * Real.sqrt N) := by positivity
  have hsqN : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hN0
  have hsq8 : Real.sqrt (50 * π + 8) ^ 2 = 50 * π + 8 := Real.sq_sqrt (by positivity)
  have hM2 : (D * Real.sqrt (50 * π + 8) * ((N : ℝ) * Real.sqrt N)) ^ 2 =
      (N : ℝ) * (D ^ 2 * (50 * π + 8) * (N : ℝ) ^ 2) := by
    have e : (D * Real.sqrt (50 * π + 8) * ((N : ℝ) * Real.sqrt N)) ^ 2 =
        D ^ 2 * Real.sqrt (50 * π + 8) ^ 2 * (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) ^ 2 := by ring
    rw [e, hsqN, hsq8]
    ring
  have h2 : (∑ k, |a k|) ^ 2 ≤ (D * Real.sqrt (50 * π + 8) * ((N : ℝ) * Real.sqrt N)) ^ 2 := by
    rw [hM2]
    exact hcs.trans (mul_le_mul_of_nonneg_left h hN0)
  have h0 : 0 ≤ ∑ k, |a k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  exact (pow_le_pow_iff_left₀ h0 hM0 two_ne_zero).mp h2

/-- `Σ|c_k| ≤ N^σ Σ|a_k|`, `a_k = c_k (k+1)^{−σ}`, `σ ≥ 0`. -/
theorem soma_c_le {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ k, |c k| ≤ (N : ℝ) ^ σ * ∑ k, |c k * ((k.val : ℝ) + 1) ^ (-σ)| := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk0 : (0 : ℝ) < (k.val : ℝ) + 1 := by positivity
  have hkN : (k.val : ℝ) + 1 ≤ N := by
    have h1 := k.isLt
    have h2 : ((k.val + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    push_cast at h2
    exact h2
  have e : |c k| = ((k.val : ℝ) + 1) ^ σ * |c k * ((k.val : ℝ) + 1) ^ (-σ)| := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hk0 _), ← mul_assoc, mul_comm (((k.val : ℝ) + 1) ^ σ),
      mul_assoc, ← Real.rpow_add hk0, add_neg_cancel, Real.rpow_zero, mul_one]
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hk0.le hkN hσ) (abs_nonneg _)

/-- `N^σ · (C 5^η (N^η)² √(50π + 8) · N √N) = (C 5^η √(50π + 8)) N^{σ + 3/2 + 2η}`. -/
theorem expoentes {N σ η C : ℝ} (hN : 0 < N) :
    N ^ σ * (C * 5 ^ η * (N ^ η) ^ 2 * Real.sqrt (50 * π + 8) * (N * Real.sqrt N)) =
      C * 5 ^ η * Real.sqrt (50 * π + 8) * N ^ (σ + 3 / 2 + 2 * η) := by
  simp only [Real.sqrt_eq_rpow]
  rw [Real.rpow_add hN, Real.rpow_add hN,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN, Real.rpow_one,
    show (2 : ℝ) * η = η + η by ring, Real.rpow_add hN]
  ring

/-- **`‖c‖₁` controlado por `‖res‖²_σ`**: sob `SemZeros θ`, `θ < σ < 1`, `η > 0`, há `K` com
`Σ|c_k| ≤ K N^{σ + 3/2 + 2η}` para todo `N ≥ 1` e todo `c` com `‖res_c‖²_σ ≤ 1`. -/
theorem norma_l1_le {θ σ η : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ : θ < σ) (hσ1 : σ < 1)
    (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : Fin N → ℝ, Wσ σ c ≤ 1 →
      ∑ k, |c k| ≤ K * (N : ℝ) ^ (σ + 3 / 2 + 2 * η) := by
  have hσ0 : 0 < σ := by linarith
  obtain ⟨C, hC0, hC⟩ := norm_F_le hZ hθ hθ1 (δ := σ - θ) (by linarith) (by linarith) hη
  refine ⟨C * 5 ^ η * Real.sqrt (50 * π + 8), by positivity, fun N hN c hW => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set T : ℝ := 2 * N * (N + 1) with hT
  have hT0 : 0 ≤ T := by positivity
  set B : ℝ := C * (1 + T) ^ η with hB
  have hre : ∀ τ : ℝ, ((σ : ℂ) + (τ : ℂ) * I).re = σ := fun τ => by simp
  have hζ : ∀ τ ∈ Icc (-T) T, riemannZeta ((σ : ℂ) + (τ : ℂ) * I) ≠ 0 := fun τ _ =>
    hZ _ (by rw [hre]; exact hσ)
  have hF : ∀ τ ∈ Icc (-T) T, ‖F ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ B := by
    intro τ hτ
    have hτa : |τ| ≤ T := abs_le.mpr ⟨hτ.1, hτ.2⟩
    have h := hC ((σ : ℂ) + (τ : ℂ) * I) (by rw [hre]; linarith)
    have him : ((σ : ℂ) + (τ : ℂ) * I).im = τ := by simp
    rw [him] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
    exact Real.rpow_le_rpow (by positivity) (by linarith) hη.le
  set a : Fin N → ℝ := fun k => c k * ((k.val : ℝ) + 1) ^ (-σ) with ha
  have hup := media_sup hσ0 hσ1 c hT0 hζ hF
  have hlow := media_inf a T
  have hTN : 2 * T - 2 * ((N : ℝ) + 1) * N = 2 * N * (N + 1) := by rw [hT]; ring
  rw [hTN] at hlow
  set q : ℝ := (N : ℝ) ^ η with hq
  have hBle : B ≤ C * 5 ^ η * q ^ 2 := by
    rw [hB, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0.le
    have h1T : 1 + T ≤ 5 * (N : ℝ) ^ 2 := by rw [hT]; nlinarith
    calc (1 + T) ^ η ≤ (5 * (N : ℝ) ^ 2) ^ η := Real.rpow_le_rpow (by positivity) h1T hη.le
      _ = 5 ^ η * q ^ 2 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), hq, Real.rpow_pow_comm hN0.le]
  have hsa : ∑ k, a k ^ 2 ≤ (C * 5 ^ η * q ^ 2) ^ 2 * (50 * π + 8) * (N : ℝ) ^ 2 :=
    arit_X hNr (by positivity) hBle (Wσ_nonneg σ c) hW (hlow.trans hup)
  have ha1 := soma_abs_le a (by positivity) hsa
  calc ∑ k, |c k| ≤ (N : ℝ) ^ σ * ∑ k, |a k| := soma_c_le c hσ0.le
    _ ≤ (N : ℝ) ^ σ * (C * 5 ^ η * q ^ 2 * Real.sqrt (50 * π + 8) * ((N : ℝ) * Real.sqrt N)) :=
        mul_le_mul_of_nonneg_left ha1 (by positivity)
    _ = C * 5 ^ η * Real.sqrt (50 * π + 8) * (N : ℝ) ^ (σ + 3 / 2 + 2 * η) := expoentes hN0

end ATK.ZeroClasses.BDNormaL1

#print axioms ATK.ZeroClasses.BDNormaL1.integrable_mellin_meio
#print axioms ATK.ZeroClasses.BDNormaL1.integrable_espectro
#print axioms ATK.ZeroClasses.BDNormaL1.int_espectro_le
#print axioms ATK.ZeroClasses.BDNormaL1.int_cos_abs
#print axioms ATK.ZeroClasses.BDNormaL1.norm_sq_soma
#print axioms ATK.ZeroClasses.BDNormaL1.cpow_neg_I
#print axioms ATK.ZeroClasses.BDNormaL1.media_inf
#print axioms ATK.ZeroClasses.BDNormaL1.soma_sigma
#print axioms ATK.ZeroClasses.BDNormaL1.norm_P_sq_le
#print axioms ATK.ZeroClasses.BDNormaL1.media_sup
#print axioms ATK.ZeroClasses.BDNormaL1.arit_X
#print axioms ATK.ZeroClasses.BDNormaL1.soma_abs_le
#print axioms ATK.ZeroClasses.BDNormaL1.soma_c_le
#print axioms ATK.ZeroClasses.BDNormaL1.expoentes
#print axioms ATK.ZeroClasses.BDNormaL1.norma_l1_le
