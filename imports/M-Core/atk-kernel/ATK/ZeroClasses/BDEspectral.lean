import ATK.ZeroClasses.BDPonderado
import ATK.EspectralDN

/-!
# Báez-Duarte ponderado: a forma espectral de `D_N(σ)` (rodada 73)

Primeira peça da questão Q2(ii) de `fronteira/RH_frontier.md` (necessidade com taxa). Para `0 < σ < 1`:

* **Plancherel de Mellin ponderado** (`plancherel_σ`): se `∫_0^∞ |f(t)| t^{σ−1} dt < ∞` e
  `∫_0^∞ |f(t)|² t^{2σ−1} dt < ∞`, então
  `∫_0^∞ |f(t)|² t^{2σ−1} dt = (1/2π) ∫_ℝ |𝓜f(σ + iτ)|² dτ`;
  reduz-se ao caso `σ = ½` (`ATK.MellinPlancherel`) trocando `f` por `t^{σ−½} f(t)` (`mellin_cpow_smul` da Mathlib);
* **a forma espectral** (`Wσ_espectral`): `‖χ − Σ c_k ρ_{k+1}‖²_σ = (1/2π) ∫ |1 + ζ(s) Σ_k c_k (k+1)^{−s}|²/|s|² dτ`,
  `s = σ + iτ` (com `ATK.EspectralDN.mellin_res_geral`);
* `DNσ_le` e `iInf_DNσ_le`: qualquer vetor de coeficientes dá uma cota superior para `D_N(σ)` e para `inf_N D_N(σ)`;
* **o núcleo de Riesz** `w(u) = (1 − u)²₊` (`wR`): `𝓜w(z) = 2/(z(z + 1)(z + 2))` em `Re z > 0` (`hasMellin_wR`, de
  `hasMellin_cpow_Ioc` da Mathlib), `‖W(c + iy)‖ ≤ (8/c)(1 + |y|)^{−2}` (`norm_WR_le`) e a **inversão de Mellin**
  `w(u) = (1/2π) ∫ u^{−(c+iy)} W(c + iy) dy` (`wR_inv`, de `mellinInv_mellin_eq`);
* **o molificador** `A_N(s) = Σ_{k<N} μ(k)(1 − k/N)² k^{−s}` (`aN`, `LSeries_aN_soma`) e a sua **representação
  integral** `A_N(s) = (1/2π) ∫ W(c + iy) N^{c+iy} F(s + c + iy) dy`, `F = 1/ζ`, para `Re s + c > 1`
  (`LSeries_aN_int`: inversão termo a termo e `integral_tsum_of_summable_integral_norm`);
* **`DNσ_le_molif`**: com `c_k = −μ(k + 1) w((k + 1)/N)` (`cN`, `soma_cN`),
  `D_N(σ) ≤ (1/2π) ∫ |1 − ζ(s)A_N(s)|²/|s|² dτ`.

Com isso, a necessidade com taxa reduz-se a deslocar a integral de `A_N` para `Re z = −δ` sob `SemZeros θ`
(o resíduo em `z = 0` é `F(s) = 1/ζ(s)`, e o resto é `O(N^{−δ})`).

Classificação (rodada 73): **ferramenta**. RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace ATK.ZeroClasses.BDEspectral

open ATK.BaezDuarteBridge (res)
open ATK.ZeroClasses.BDPonderado (Wσ DNσ Wσ_nonneg integrable_w)
open ATK.RHLogZeta (F)
open ATK.ZeroClasses.LittlewoodMu (mu norm_mu_le LSeries_mu)

/-- **Plancherel de Mellin na reta `Re s = σ`**. -/
theorem plancherel_σ {f : ℝ → ℂ} {σ : ℝ} (h1 : MellinConvergent f (σ : ℂ))
    (h2 : IntegrableOn (fun t => ‖f t‖ ^ 2 * t ^ (2 * σ - 1)) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 * t ^ (2 * σ - 1) =
      (2 * π)⁻¹ * ∫ τ : ℝ, ‖mellin f ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (((σ - 1 / 2 : ℝ)) : ℂ) • f t with hg
  have hg1 : MellinConvergent g ((1 / 2 : ℝ) : ℂ) := by
    rw [hg, MellinConvergent.cpow_smul]
    have e : ((1 / 2 : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
    rw [e]
    exact h1
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
  have hP := ATK.MellinPlancherel.integral_norm_sq_eq_mellin hg1 hg2
  have e1 : ∫ t in Ioi (0 : ℝ), ‖g t‖ ^ 2 = ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 * t ^ (2 * σ - 1) :=
    setIntegral_congr_fun measurableSet_Ioi hnorm
  have e2 : ∀ τ : ℝ, mellin g (1 / 2 + (τ : ℂ) * I) = mellin f ((σ : ℂ) + (τ : ℂ) * I) := by
    intro τ
    rw [hg, mellin_cpow_smul]
    congr 1
    push_cast
    ring
  rw [e1] at hP
  rw [hP]
  simp_rw [e2]

/-- O integrando espectral em `s = σ + iτ`. -/
noncomputable def espectroσ (σ : ℝ) {N : ℕ} (c : Fin N → ℝ) (τ : ℝ) : ℝ :=
  ‖(1 + riemannZeta ((σ : ℂ) + (τ : ℂ) * I) *
      ∑ k : Fin N, (c k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * I))) /
    ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2

/-- **A forma espectral de `‖res‖²_σ`**: `Wσ σ c = (1/2π) ∫ |1 + ζ(s)P_c(s)|²/|s|² dτ`. -/
theorem Wσ_espectral {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) :
    Wσ σ c = (2 * π)⁻¹ * ∫ τ : ℝ, espectroσ σ c τ := by
  have hM := (ATK.EspectralDN.mellin_res_geral c (s := (σ : ℂ)) (by simpa using hσ0)
    (by simpa using hσ1)).1
  have h2 : IntegrableOn (fun t => ‖((res c t : ℝ) : ℂ)‖ ^ 2 * t ^ (2 * σ - 1)) (Ioi 0) := by
    refine (integrable_w c hσ0 hσ1).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Complex.norm_real, sq_abs]
  have hP := plancherel_σ hM h2
  have e1 : Wσ σ c = ∫ t in Ioi (0 : ℝ), ‖((res c t : ℝ) : ℂ)‖ ^ 2 * t ^ (2 * σ - 1) := by
    unfold Wσ
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp [Complex.norm_real, sq_abs]
  rw [e1, hP]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  have hre : ((σ : ℂ) + (τ : ℂ) * I).re = σ := by simp
  simp only
  rw [(ATK.EspectralDN.mellin_res_geral c (by rw [hre]; exact hσ0) (by rw [hre]; exact hσ1)).2]
  rfl

/-- `D_N(σ) ≤ (1/2π) ∫ |1 + ζ(s)P_c(s)|²/|s|² dτ` para todo `c`. -/
theorem DNσ_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) :
    DNσ σ N ≤ (2 * π)⁻¹ * ∫ τ : ℝ, espectroσ σ c τ := by
  rw [← Wσ_espectral hσ0 hσ1 c]
  exact ciInf_le ⟨0, fun _ ⟨c', hc'⟩ => hc' ▸ Wσ_nonneg σ c'⟩ c

/-- `inf_N D_N(σ) ≤ (1/2π) ∫ |1 + ζ(s)P_c(s)|²/|s|² dτ` para todo `N` e todo `c`. -/
theorem iInf_DNσ_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (c : Fin N → ℝ) :
    ⨅ M, DNσ σ M ≤ (2 * π)⁻¹ * ∫ τ : ℝ, espectroσ σ c τ :=
  (ciInf_le ⟨0, fun _ ⟨M, hM⟩ => hM ▸ ATK.ZeroClasses.BDPonderado.DNσ_nonneg σ M⟩ N).trans
    (DNσ_le hσ0 hσ1 c)


/-! ## 2. O núcleo de Riesz `w(u) = (1 − u)²₊` -/

/-- `w(u) = max(1 − u, 0)²`. -/
noncomputable def wR (u : ℝ) : ℝ := max (1 - u) 0 ^ 2

theorem continuous_wR : Continuous wR := by unfold wR; fun_prop

theorem wR_nonneg (u : ℝ) : 0 ≤ wR u := by unfold wR; positivity

theorem wR_eq_zero {u : ℝ} (hu : 1 ≤ u) : wR u = 0 := by
  unfold wR
  rw [max_eq_right (by linarith)]
  norm_num

/-- `W(z) = 2/(z(z + 1)(z + 2))`, a transformada de Mellin de `w`. -/
noncomputable def WR (z : ℂ) : ℂ := 2 / (z * (z + 1) * (z + 2))

theorem hasMellin_congr {f g : ℝ → ℂ} {s m : ℂ} (h : HasMellin f s m)
    (hfg : ∀ t ∈ Ioi (0 : ℝ), f t = g t) : HasMellin g s m := by
  refine ⟨h.1.congr_fun (fun t ht => by simp only [hfg t ht]) measurableSet_Ioi, ?_⟩
  rw [← h.2]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by simp only [hfg t ht]

/-- **`𝓜w(z) = 2/(z(z + 1)(z + 2))`** para `Re z > 0`. -/
theorem hasMellin_wR {z : ℂ} (hz : 0 < z.re) : HasMellin (fun t => ((wR t : ℝ) : ℂ)) z (WR z) := by
  have h0 := hasMellin_cpow_Ioc (0 : ℂ) (s := z) (by simpa using hz)
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := z) (by simp; linarith)
  have h2 := hasMellin_cpow_Ioc (2 : ℂ) (s := z) (by simp; linarith)
  have h1' := hasMellin_const_smul h1.1 (2 : ℂ)
  have hA := hasMellin_sub h0.1 h1'.1
  have hB := hasMellin_add hA.1 h2.1
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; exact lt_irrefl 0 hz
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz2 : z + 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hval : mellin (fun t => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (0 : ℂ)) t -
      (2 : ℂ) • indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (1 : ℂ)) t) z +
      mellin (indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (2 : ℂ))) z = WR z := by
    rw [hA.2, h1'.2, h0.2, h1.2, h2.2]
    unfold WR
    simp only [add_zero, smul_eq_mul]
    field_simp
    ring
  refine hasMellin_congr ⟨hB.1, hB.2.trans hval⟩ fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  by_cases h1t : t ≤ 1
  · have hmem : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, h1t⟩
    simp only [indicator_of_mem hmem, cpow_zero, cpow_one, smul_eq_mul]
    rw [show ((t : ℂ) ^ (2 : ℂ)) = (t : ℂ) ^ 2 by norm_cast]
    unfold wR
    rw [max_eq_left (by linarith)]
    push_cast
    ring
  · have hmem : t ∉ Ioc (0 : ℝ) 1 := fun h => h1t h.2
    simp only [indicator_of_notMem hmem, smul_zero, sub_zero, add_zero]
    rw [wR_eq_zero (by linarith)]
    simp

theorem WR_cont {c : ℝ} (hc : 0 < c) : Continuous (fun y : ℝ => WR ((c : ℂ) + y * I)) := by
  unfold WR
  refine Continuous.div continuous_const (by fun_prop) fun y => ?_
  have hne : ∀ a : ℝ, 0 < a → ((c : ℂ) + y * I + a) ≠ 0 := by
    intro a ha h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h0 : ((c : ℂ) + y * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  refine mul_ne_zero (mul_ne_zero h0 ?_) ?_
  · have := hne 1 one_pos
    push_cast at this
    exact this
  · have := hne 2 two_pos
    push_cast at this
    exact this

/-- **`‖W(c + iy)‖ ≤ (8/c)(1 + |y|)^{−2}`**. -/
theorem norm_WR_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖WR ((c : ℂ) + y * I)‖ ≤ 8 / c * (1 + ‖y‖) ^ (-2 : ℝ) := by
  set z : ℂ := (c : ℂ) + y * I with hzdef
  have hre : z.re = c := by simp [hzdef]
  have him : z.im = y := by simp [hzdef]
  have h0 : c ≤ ‖z‖ := by
    have := abs_re_le_norm z
    rw [hre, abs_of_pos hc] at this
    exact this
  have hlow : ∀ a : ℝ, 1 ≤ a → (1 + |y|) / 2 ≤ ‖z + a‖ := by
    intro a ha
    have h1 := abs_re_le_norm (z + a)
    have h2 := abs_im_le_norm (z + a)
    have e1 : (z + a).re = c + a := by simp [hre]
    have e2 : (z + a).im = y := by simp [him]
    rw [e1, abs_of_pos (by linarith)] at h1
    rw [e2] at h2
    linarith
  have h1 := hlow 1 le_rfl
  have h2 := hlow 2 (by norm_num)
  push_cast at h1 h2
  have hy : 0 < (1 + |y|) / 2 := by positivity
  unfold WR
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, norm_mul, norm_mul, hn2, Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
  have hden : c * ((1 + |y|) / 2) * ((1 + |y|) / 2) ≤ ‖z‖ * ‖z + 1‖ * ‖z + 2‖ :=
    mul_le_mul (mul_le_mul h0 h1 hy.le (norm_nonneg _)) h2 hy.le (by positivity)
  calc 2 / (‖z‖ * ‖z + 1‖ * ‖z + 2‖) ≤ 2 / (c * ((1 + |y|) / 2) * ((1 + |y|) / 2)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 8 / c * ((1 + |y|) ^ 2)⁻¹ := by field_simp; norm_num

theorem integrable_WR {c : ℝ} (hc : 0 < c) : Integrable (fun y : ℝ => WR ((c : ℂ) + y * I)) := by
  have hI : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-2 : ℝ)) :=
    integrable_one_add_norm (by simp)
  exact Integrable.mono' (hI.const_mul (8 / c)) (WR_cont hc).aestronglyMeasurable
    (ae_of_all _ (norm_WR_le hc))

/-- **Inversão de Mellin para `w`**: `w(u) = (1/2π) ∫ u^{−(c+iy)} W(c + iy) dy`, `u > 0`, `c > 0`. -/
theorem wR_inv {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : 0 < u) :
    ((wR u : ℝ) : ℂ) = (1 / (2 * π)) • ∫ y : ℝ, (u : ℂ) ^ (-((c : ℂ) + y * I)) • WR ((c : ℂ) + y * I) := by
  have hcre : ∀ y : ℝ, 0 < ((c : ℂ) + y * I).re := fun y => by simpa using hc
  have hM : MellinConvergent (fun t => ((wR t : ℝ) : ℂ)) (c : ℂ) := (hasMellin_wR (by simpa using hc)).1
  have hV : VerticalIntegrable (mellin (fun t => ((wR t : ℝ) : ℂ))) c := by
    refine (integrable_WR hc).congr (ae_of_all _ fun y => ?_)
    exact ((hasMellin_wR (hcre y)).2).symm
  have hcont : ContinuousAt (fun t => ((wR t : ℝ) : ℂ)) u :=
    (continuous_ofReal.comp continuous_wR).continuousAt
  have h := mellinInv_mellin_eq c (fun t => ((wR t : ℝ) : ℂ)) hu hM hV hcont
  rw [← h]
  unfold mellinInv
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [(hasMellin_wR (hcre y)).2]

/-! ## 3. O molificador de Riesz `A_N(s) = Σ_{k<N} μ(k) (1 − k/N)² k^{−s}` -/

/-- Os coeficientes `μ(k) w(k/N)`. -/
noncomputable def aN (N : ℕ) (k : ℕ) : ℂ := mu k * ((wR ((k : ℝ) / N) : ℝ) : ℂ)

theorem aN_eq_zero {N k : ℕ} (hN : 1 ≤ N) (hk : N ≤ k) : aN N k = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (1 : ℝ) ≤ (k : ℝ) / N := by
    rw [le_div_iff₀ hN0, one_mul]
    exact_mod_cast hk
  simp [aN, wR_eq_zero h1]

/-- `A_N(s)` é a soma finita `Σ_{k<N}`. -/
theorem LSeries_aN_soma {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    LSeries (aN N) s = ∑ k ∈ Finset.range N, LSeries.term (aN N) s k := by
  unfold LSeries
  refine tsum_eq_sum fun k hk => ?_
  have hkN : N ≤ k := by simpa using hk
  have hk0 : k ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hk0, aN_eq_zero hN hkN, zero_div]

theorem norm_term_mu_le {w : ℂ} (k : ℕ) : ‖LSeries.term mu w k‖ ≤ ((k : ℝ) ^ w.re)⁻¹ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [LSeries.term_zero, norm_zero]
    positivity
  · rw [LSeries.term_of_ne_zero hk.ne', norm_div, norm_natCast_cpow_of_pos hk, div_eq_mul_inv]
    have := norm_mu_le k
    have hpos : 0 ≤ ((k : ℝ) ^ w.re)⁻¹ := by positivity
    calc ‖mu k‖ * ((k : ℝ) ^ w.re)⁻¹ ≤ 1 * ((k : ℝ) ^ w.re)⁻¹ := mul_le_mul_of_nonneg_right this hpos
      _ = ((k : ℝ) ^ w.re)⁻¹ := one_mul _

/-- **A representação integral**: para `Re s + c > 1`,
`A_N(s) = (1/2π) ∫ W(c + iy) N^{c+iy} F(s + c + iy) dy`, `F = 1/ζ`. -/
theorem LSeries_aN_int {N : ℕ} (hN : 1 ≤ N) {s : ℂ} {c : ℝ} (hc : 0 < c) (hsc : 1 < s.re + c) :
    LSeries (aN N) s = (1 / (2 * π)) • ∫ y : ℝ, WR ((c : ℂ) + y * I) * (N : ℂ) ^ ((c : ℂ) + y * I) *
      F (s + ((c : ℂ) + y * I)) := by
  have hN0 : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  set g : ℕ → ℝ → ℂ := fun k y => WR ((c : ℂ) + y * I) * (N : ℂ) ^ ((c : ℂ) + y * I) *
    LSeries.term mu (s + ((c : ℂ) + y * I)) k with hg
  have hzc : Continuous (fun y : ℝ => (c : ℂ) + y * I) := by fun_prop
  -- continuidade de cada `g k`
  have hgc : ∀ k, Continuous (g k) := by
    intro k
    have h1 : Continuous (fun y : ℝ => WR ((c : ℂ) + y * I)) := WR_cont hc
    have h2 : Continuous (fun y : ℝ => (N : ℂ) ^ ((c : ℂ) + y * I)) := hzc.const_cpow (Or.inl hNne)
    have h3 : Continuous (fun y : ℝ => LSeries.term mu (s + ((c : ℂ) + y * I)) k) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [LSeries.term_zero]
        exact continuous_const
      · simp only [LSeries.term_of_ne_zero hk.ne']
        have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        exact continuous_const.div ((continuous_const.add hzc).const_cpow (Or.inl hkne))
          fun y h => hkne ((cpow_eq_zero_iff _ _).mp h).1
    exact (h1.mul h2).mul h3
  -- a cota de cada `g k`
  have hgb : ∀ k y, ‖g k y‖ ≤ ‖WR ((c : ℂ) + y * I)‖ * ((N : ℝ) ^ c * ((k : ℝ) ^ (s.re + c))⁻¹) := by
    intro k y
    simp only [hg]
    rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hN0, mul_assoc]
    have hre : ((c : ℂ) + y * I).re = c := by simp
    have hre2 : (s + ((c : ℂ) + y * I)).re = s.re + c := by simp
    rw [hre]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := norm_term_mu_le (w := s + ((c : ℂ) + y * I)) k
    rwa [hre2] at this
  have hWi := (integrable_WR hc).norm
  have hgi : ∀ k, Integrable (g k) := fun k =>
    Integrable.mono' (hWi.mul_const _) (hgc k).aestronglyMeasurable (ae_of_all _ (hgb k))
  have hsum : Summable (fun k => ∫ y : ℝ, ‖g k y‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _) (fun k => ?_)
      ((Real.summable_nat_rpow_inv.mpr hsc).mul_left ((∫ y : ℝ, ‖WR ((c : ℂ) + y * I)‖) * (N : ℝ) ^ c))
    calc ∫ y : ℝ, ‖g k y‖ ≤ ∫ y : ℝ, ‖WR ((c : ℂ) + y * I)‖ * ((N : ℝ) ^ c * ((k : ℝ) ^ (s.re + c))⁻¹) :=
          integral_mono (hgi k).norm (hWi.mul_const _) (hgb k)
      _ = (∫ y : ℝ, ‖WR ((c : ℂ) + y * I)‖) * (N : ℝ) ^ c * ((k : ℝ) ^ (s.re + c))⁻¹ := by
          rw [integral_mul_const]
          ring
  -- cada termo
  have hterm : ∀ k : ℕ, LSeries.term (aN N) s k = (1 / (2 * π)) • ∫ y : ℝ, g k y := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hg, LSeries.term_zero]
    · have hk0 : k ≠ 0 := hk.ne'
      have hkr : (0 : ℝ) < k := by exact_mod_cast hk
      have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
      have hpt : ∀ y : ℝ, g k y = mu k / (k : ℂ) ^ s *
          ((((k : ℝ) / N : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) • WR ((c : ℂ) + y * I)) := by
        intro y
        have e1 : (((k : ℝ) / N : ℝ) : ℂ) = ((k : ℝ) : ℂ) * (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
        have e2 : (((N : ℝ)⁻¹ : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) = (N : ℂ) ^ ((c : ℂ) + y * I) := by
          rw [ofReal_inv, ofReal_natCast, inv_cpow _ _ (by rw [natCast_arg]; exact Real.pi_ne_zero.symm),
            cpow_neg, inv_inv]
        rw [e1, mul_cpow_ofReal_nonneg (by positivity) (by positivity), e2, ofReal_natCast]
        simp only [hg, smul_eq_mul]
        rw [LSeries.term_of_ne_zero hk0, cpow_add _ _ hkne, cpow_neg]
        have h1 : (k : ℂ) ^ s ≠ 0 := fun h => hkne ((cpow_eq_zero_iff _ _).mp h).1
        have h2 : (k : ℂ) ^ ((c : ℂ) + y * I) ≠ 0 := fun h => hkne ((cpow_eq_zero_iff _ _).mp h).1
        field_simp
      rw [LSeries.term_of_ne_zero hk0, aN, wR_inv hc (div_pos hkr hNr)]
      simp_rw [hpt]
      rw [integral_const_mul, Complex.real_smul, Complex.real_smul]
      ring
  -- a soma
  have hlim : ∀ y : ℝ, ∑' k, g k y = WR ((c : ℂ) + y * I) * (N : ℂ) ^ ((c : ℂ) + y * I) *
      F (s + ((c : ℂ) + y * I)) := by
    intro y
    simp only [hg]
    rw [tsum_mul_left]
    congr 1
    exact LSeries_mu (by simp; linarith)
  unfold LSeries
  simp_rw [hterm, Complex.real_smul]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hgi hsum]
  simp_rw [hlim]


/-! ## 4. O molificador no critério -/

/-- Os coeficientes reais `c_k = −μ(k + 1) w((k + 1)/N)`, `k < N`. -/
noncomputable def cN (N : ℕ) (k : Fin N) : ℝ :=
  -((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ) * wR (((k.val + 1 : ℕ) : ℝ) / N)

/-- `Σ_k c_k (k + 1)^{−s} = −A_N(s)`. -/
theorem soma_cN {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    ∑ k : Fin N, ((cN N k : ℝ) : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-s) = -LSeries (aN N) s := by
  set h : ℕ → ℂ := fun j => -(LSeries.term (aN N) s (j + 1)) with hh
  have hpt : ∀ k : Fin N, ((cN N k : ℝ) : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-s) = h k.val := by
    intro k
    simp only [hh]
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero _), cpow_neg, div_eq_mul_inv]
    simp only [cN, aN, mu]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ => hpt k, Fin.sum_univ_eq_sum_range h N, LSeries_aN_soma hN]
  have e1 := Finset.sum_range_succ' (fun k => LSeries.term (aN N) s k) N
  have e2 := Finset.sum_range_succ (fun k => LSeries.term (aN N) s k) N
  have hN0 : LSeries.term (aN N) s N = 0 := by
    rw [LSeries.term_of_ne_zero (by omega), aN_eq_zero hN le_rfl, zero_div]
  rw [LSeries.term_zero, add_zero] at e1
  rw [hN0, add_zero] at e2
  rw [← e2, e1]
  simp only [hh, Finset.sum_neg_distrib]

/-- **`D_N(σ) ≤ (1/2π) ∫ |1 − ζ(s)A_N(s)|²/|s|² dτ`**, `A_N` o molificador de Riesz. -/
theorem DNσ_le_molif {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    DNσ σ N ≤ (2 * π)⁻¹ * ∫ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) *
      LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) / ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
  refine (DNσ_le hσ0 hσ1 (cN N)).trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [espectroσ]
  rw [soma_cN hN]
  ring_nf

end ATK.ZeroClasses.BDEspectral

#print axioms ATK.ZeroClasses.BDEspectral.plancherel_σ
#print axioms ATK.ZeroClasses.BDEspectral.Wσ_espectral
#print axioms ATK.ZeroClasses.BDEspectral.DNσ_le
#print axioms ATK.ZeroClasses.BDEspectral.iInf_DNσ_le
#print axioms ATK.ZeroClasses.BDEspectral.continuous_wR
#print axioms ATK.ZeroClasses.BDEspectral.wR_nonneg
#print axioms ATK.ZeroClasses.BDEspectral.wR_eq_zero
#print axioms ATK.ZeroClasses.BDEspectral.hasMellin_congr
#print axioms ATK.ZeroClasses.BDEspectral.hasMellin_wR
#print axioms ATK.ZeroClasses.BDEspectral.WR_cont
#print axioms ATK.ZeroClasses.BDEspectral.norm_WR_le
#print axioms ATK.ZeroClasses.BDEspectral.integrable_WR
#print axioms ATK.ZeroClasses.BDEspectral.wR_inv
#print axioms ATK.ZeroClasses.BDEspectral.aN_eq_zero
#print axioms ATK.ZeroClasses.BDEspectral.LSeries_aN_soma
#print axioms ATK.ZeroClasses.BDEspectral.norm_term_mu_le
#print axioms ATK.ZeroClasses.BDEspectral.LSeries_aN_int
#print axioms ATK.ZeroClasses.BDEspectral.soma_cN
#print axioms ATK.ZeroClasses.BDEspectral.DNσ_le_molif
