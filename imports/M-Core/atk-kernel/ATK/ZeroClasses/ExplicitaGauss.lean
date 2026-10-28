import ATK.ZeroClasses.ExplicitaT

/-!
# A fórmula explícita com peso gaussiano (rodada 89)

A fórmula explícita das rodadas 70–78 tem o peso `x^s/s`, e a soma sobre os zeros só converge condicionalmente. Aqui
o peso é **gaussiano**, `W(s) = exp((s − ½)u + τ(s − ½)²)`, `τ > 0`. Em `Re s` limitada, `|W(s)|` decai como
`e^{−τ(Im s)²}`. A soma em `ρ` converge absolutamente, e o lado aritmético é `e^{−u/2}ψ(e^u)` suavizado:

* **`bordo_peso`**: o retângulo largo da rodada 70 com um peso inteiro `W` qualquer,
  `∮ W(s)(−ζ′/ζ)(s)/s ds = 2πi (W(1) − Σ_ρ m_ρ W(ρ)/ρ + Σ_{n<K} W(−2(n+1))/(2(n+1)) − W(0) log 2π)`;
* **`integral_linha`**: `∫ exp((a + iy)Y + τ(a + iy)²) dy = 2π k_τ(Y)`, `k_τ(v) = (4πτ)^{−1/2}e^{−v²/(4τ)}`
  (`integral_cexp_quadratic` da Mathlib);
* **`linha_x`**: `∫ e^{−sL}W(s)/s dy = 2π e^{−L/2} Φ_τ(u − L)` na reta `Re s = c > 0`, com
  `Φ_τ(Y) = ∫_0^∞ e^{−w/2} k_τ(Y − w) dw`. A prova usa `1/s = ∫_0^∞ e^{−sw} dw` (`inv_eq_integral`) e Fubini no
  produto (`integral_integral_swap`);
* **`lado_aritmetico`**: `∫ F_W(2 + iy) dy = 2π A_τ(u)`, com `A_τ(u) = Σ_n Λ(n) n^{−1/2} Φ_τ(u − log n)` (`Aτ`).
  A troca entre soma e integral é `integral_tsum_of_summable_integral_norm`;
* **as cotas**:
  * horizontais em alturas boas, `‖F_W(x ± iT)‖ ≤ e^{3|u| + 9τ − τT²}A(T)/T` (`hor_bound`), que tende a `0`
    (`hor_tendsto`);
  * as retas `Re s = 2` e `Re s = −5/2` são integráveis (`integrable_dir`, `integrable_esq`);
  * a reta esquerda é `O(e^{−3u})`, uniformemente em `u` (`esq_le`);
* **`formula_gauss`** (sem hipóteses): ao longo de alturas boas `T_k ∈ [k + 6, k + 7]`,
  `Σ_{|γ| ≤ T_k} m_ρ W(ρ)/ρ → W(1) + W(−2)/2 − W(0) log 2π − A_τ(u) + (1/2π) ∫ F_W(−5/2 + iy) dy`.

Sob RH, `W(ρ) = e^{iγu − τγ²}`. Esta é a forma que se usa nas provas de oscilação: Littlewood,
`ψ(x) − x = Ω±(√x log log log x)`, continua BUILD_PENDING.

Classificação (rodada 89): **ferramenta**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.ExplicitaGauss

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_sum bordo_cauchy bordo_inv
  bordo_const_mul)
open ATK.ZeroClasses.FormulaExplicita (principio_polo zeta1_eq zeta1_an zeta1_eq_zero_iff zeta1_zero
  ordem_zeta1 ordem_zeta1_ne_top logDeriv_zeta1 logDeriv_zeta1_zero triv_re triv_im ordem_trivial)

/-! ## 1. O retângulo largo com um peso inteiro `W` -/

/-- `F_W(s) = W(s)(−ζ′/ζ)(s)/s`. -/
noncomputable def Fw (W : ℂ → ℂ) (s : ℂ) : ℂ := W s * (-logDeriv riemannZeta s) / s

/-- `W(s)/s`. -/
noncomputable def pw (W : ℂ → ℂ) (s : ℂ) : ℂ := W s / s

theorem dslope_diffW {W : ℂ → ℂ} (hW : Differentiable ℂ W) (a : ℂ) : Differentiable ℂ (dslope W a) := by
  rw [← differentiableOn_univ, differentiableOn_dslope univ_mem]
  exact hW.differentiableOn

theorem dslope_add_inv {W : ℂ → ℂ} (_hW : Differentiable ℂ W) {u : ℂ} (hu : u ≠ 0) :
    dslope W 0 u + W 0 * (u - 0)⁻¹ = pw W u := by
  unfold pw
  rw [dslope_of_ne _ hu, slope_def_field, sub_zero]
  field_simp
  ring

/-- **O retângulo largo com peso**: para `W` inteira, em `[−(2K + ½), c] × [−T, T]` sem zeros nas horizontais,
`∮ W(s)(−ζ′/ζ)(s)/s ds = 2πi (W(1) − Σ_ρ m_ρ W(ρ)/ρ + Σ_{n<K} W(−2(n+1))/(2(n+1)) − W(0) log 2π)`
(a rodada 70 é o caso `W(s) = x^s`). -/
theorem bordo_peso {W : ℂ → ℂ} (hW : Differentiable ℂ W) {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (K : ℕ)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re < 1 → (s.im = -T ∨ s.im = T) → riemannZeta s ≠ 0) :
    ∃ S : Finset ℂ,
      (∀ u, u ∈ S ↔ u ∈ Ret ⟨-(2 * K + 1 / 2), -T⟩ ⟨c, T⟩ ∧ riemannZeta u = 0 ∧ 0 < u.re) ∧
      bordo (Fw W) ⟨-(2 * K + 1 / 2), -T⟩ ⟨c, T⟩ =
        2 * π * I * (W 1 - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * pw W u +
          ∑ n ∈ Finset.range K, W (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1)) -
          W 0 * (Real.log (2 * π) : ℂ)) := by
  classical
  set z : ℂ := ⟨-(2 * (K : ℝ) + 1 / 2), -T⟩ with hz
  set w : ℂ := ⟨c, T⟩ with hw
  have hzre : z.re = -(2 * (K : ℝ) + 1 / 2) := rfl
  have hzim : z.im = -T := rfl
  have hwre : w.re = c := rfl
  have hwim : w.im = T := rfl
  have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
  have hzc : -(2 * (K : ℝ) + 1 / 2) ≤ c := by linarith
  have hTT : -T ≤ T := by linarith
  have hmemR : ∀ p : ℂ, p ∈ Ret z w ↔
      (-(2 * (K : ℝ) + 1 / 2) ≤ p.re ∧ p.re ≤ c) ∧ (-T ≤ p.im ∧ p.im ≤ T) := by
    intro p
    rw [Ret, mem_reProdIm, hzre, hwre, hzim, hwim, uIcc_of_le hzc, uIcc_of_le hTT]
    rfl
  -- nenhum zero de `ζ₁` no bordo
  have hbd1 : ∀ p ∈ Bordo z w, riemannZeta₁ p ≠ 0 := by
    rintro p ⟨_, hside⟩ hp0
    obtain ⟨_, hζ⟩ := zeta1_eq_zero_iff.mp hp0
    rw [hzre, hwre, hzim, hwim] at hside
    by_cases hre : 0 < p.re
    · have hre1 : p.re < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
      rcases hside with h | h | h | h
      · linarith
      · linarith
      · exact hbd p hre hre1 (Or.inl h) hζ
      · exact hbd p hre hre1 (Or.inr h) hζ
    · obtain ⟨n, hn⟩ := ATK.ZetaSimetria.zero_trivial_de_re_nao_pos hζ (not_lt.mp hre)
      have hr : p.re = -2 * ((n : ℝ) + 1) := by rw [hn, triv_re]
      have hi : p.im = 0 := by rw [hn, triv_im]
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      rcases hside with h | h | h | h
      · rw [hr] at h
        have h4 : ((4 * (n + 1) : ℕ) : ℝ) = ((4 * K + 1 : ℕ) : ℝ) := by push_cast; linarith
        have h5 : 4 * (n + 1) = 4 * K + 1 := by exact_mod_cast h4
        omega
      · rw [hr] at h; linarith
      · rw [hi] at h; linarith
      · rw [hi] at h; linarith
  have htop : ∀ p ∈ Ret z w, analyticOrderAt riemannZeta₁ p ≠ ⊤ := fun p _ => ordem_zeta1_ne_top p
  have hψan : AnalyticOnNhd ℂ (dslope W 0) univ := fun s _ => (dslope_diffW hW 0).analyticAt s
  have h0int : z.re < (0 : ℂ).re ∧ (0 : ℂ).re < w.re ∧ z.im < (0 : ℂ).im ∧ (0 : ℂ).im < w.im := by
    simp only [zero_re, zero_im, hzre, hwre, hzim, hwim]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hz10 : riemannZeta₁ 0 ≠ 0 := by rw [zeta1_zero]; norm_num
  obtain ⟨S₀, hS₀, hpol⟩ := principio_polo isOpen_univ zeta1_an hψan (z := z) (w := w)
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) (subset_univ _) htop hbd1
    (p := 0) (c := W 0) h0int hz10
  -- a decomposição de `F` no bordo
  have hne0 : ∀ p ∈ Bordo z w, p ≠ 0 := by
    rintro p ⟨_, h⟩ rfl
    rw [hzre, hwre, hzim, hwim, zero_re, zero_im] at h
    rcases h with h | h | h | h <;> linarith
  have hne1 : ∀ p ∈ Bordo z w, p ≠ 1 := by
    rintro p ⟨_, h⟩ rfl
    rw [hzre, hwre, hzim, hwim, one_re, one_im] at h
    rcases h with h | h | h | h <;> linarith
  have hζbd : ∀ p ∈ Bordo z w, riemannZeta p ≠ 0 := fun p hp h =>
    hbd1 p hp (zeta1_eq_zero_iff.mpr ⟨hne1 p hp, h⟩)
  have heq : EqOn (Fw W) (fun s => (-1 : ℂ) * (logDeriv riemannZeta₁ s * (dslope W 0 s + W 0 * (s - 0)⁻¹)) +
      ((dslope W 1 s - dslope W 0 s) +
        (W 1 * (s - 1)⁻¹ + (-W 0) * (s - 0)⁻¹))) (Bordo z w) := by
    intro s hs
    have hs0 := hne0 s hs
    have hs1 := hne1 s hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp only [Fw]
    rw [logDeriv_zeta1 hs1 (hζbd s hs), dslope_of_ne _ hs1, dslope_of_ne _ hs0, slope_def_field,
      slope_def_field]
    simp only [sub_zero]
    field_simp
    ring
  have hψc : Continuous (dslope W 0) := (dslope_diffW hW 0).continuous
  have hd1c : Continuous (dslope W 1) := (dslope_diffW hW 1).continuous
  have hinv0 : ContinuousOn (fun s : ℂ => (s - 0)⁻¹) (Bordo z w) := fun p hp =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hne0 p hp))).continuousWithinAt
  have hinv1 : ContinuousOn (fun s : ℂ => (s - 1)⁻¹) (Bordo z w) := fun p hp =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hne1 p hp))).continuousWithinAt
  have hlogc : ContinuousOn (logDeriv riemannZeta₁) (Bordo z w) := by
    intro p hp
    have e : logDeriv riemannZeta₁ = fun z => deriv riemannZeta₁ z / riemannZeta₁ z :=
      funext fun z => logDeriv_apply _ z
    rw [e]
    exact ((zeta1_an p (mem_univ _)).deriv.continuousAt.div (zeta1_an p (mem_univ _)).continuousAt
      (hbd1 p hp)).continuousWithinAt
  have hP : ContinuousOn (fun s => logDeriv riemannZeta₁ s * (dslope W 0 s + W 0 * (s - 0)⁻¹))
      (Bordo z w) :=
    hlogc.mul (hψc.continuousOn.add (continuousOn_const.mul hinv0))
  have hc1 : ContinuousOn (fun s => (-1 : ℂ) * (logDeriv riemannZeta₁ s * (dslope W 0 s + W 0 * (s - 0)⁻¹)))
      (Bordo z w) := continuousOn_const.mul hP
  have hQ1 : ContinuousOn (fun s => dslope W 1 s - dslope W 0 s) (Bordo z w) :=
    (hd1c.sub hψc).continuousOn
  have hQ2a : ContinuousOn (fun s : ℂ => W 1 * (s - 1)⁻¹) (Bordo z w) :=
    continuousOn_const.mul hinv1
  have hQ2b : ContinuousOn (fun s : ℂ => (-W 0) * (s - 0)⁻¹) (Bordo z w) :=
    continuousOn_const.mul hinv0
  have hQ2 : ContinuousOn (fun s : ℂ => W 1 * (s - 1)⁻¹ + (-W 0) * (s - 0)⁻¹) (Bordo z w) :=
    hQ2a.add hQ2b
  have hQ : ContinuousOn (fun s => (dslope W 1 s - dslope W 0 s) +
      (W 1 * (s - 1)⁻¹ + (-W 0) * (s - 0)⁻¹)) (Bordo z w) := hQ1.add hQ2
  have hQd : DifferentiableOn ℂ (fun s => dslope W 1 s - dslope W 0 s)
      (Ret z w) :=
    ((dslope_diffW hW 1).sub (dslope_diffW hW 0)).differentiableOn
  have hb1 : bordo (fun s => (s - 1)⁻¹) z w = 2 * π * I :=
    bordo_inv (by rw [hzre, one_re]; linarith) (by rw [hwre, one_re]; linarith)
      (by rw [hzim, one_im]; linarith) (by rw [hwim, one_im]; linarith)
  have hb0 : bordo (fun s => (s - 0)⁻¹) z w = 2 * π * I :=
    bordo_inv h0int.1 h0int.2.1 h0int.2.2.1 h0int.2.2.2
  -- a soma sobre os zeros: não triviais + triviais
  set S : Finset ℂ := S₀.filter (fun u => 0 < u.re) with hSdef
  have hsplit : ∑ u ∈ S₀, (analyticOrderNatAt riemannZeta₁ u : ℂ) * (dslope W 0 u + W 0 * (u - 0)⁻¹) =
      ∑ u ∈ S, (analyticOrderNatAt riemannZeta₁ u : ℂ) * (dslope W 0 u + W 0 * (u - 0)⁻¹) +
      ∑ u ∈ S₀.filter (fun u => ¬ 0 < u.re),
        (analyticOrderNatAt riemannZeta₁ u : ℂ) * (dslope W 0 u + W 0 * (u - 0)⁻¹) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hT2 : S₀.filter (fun u => ¬ 0 < u.re) =
      (Finset.range K).image (fun n : ℕ => -2 * ((n : ℂ) + 1)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, hS₀, hmemR, zeta1_eq_zero_iff]
    constructor
    · rintro ⟨⟨⟨⟨hr1, _⟩, _⟩, _, hζ⟩, hre⟩
      obtain ⟨n, hn⟩ := ATK.ZetaSimetria.zero_trivial_de_re_nao_pos hζ (not_lt.mp hre)
      refine ⟨n, ?_, hn.symm⟩
      rw [hn, triv_re] at hr1
      have h4 : ((4 * (n + 1) : ℕ) : ℝ) ≤ ((4 * K + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h5 : 4 * (n + 1) ≤ 4 * K + 1 := by exact_mod_cast h4
      omega
    · rintro ⟨n, hn, rfl⟩
      have hn' : ((n : ℝ) + 1) ≤ K := by
        have : n + 1 ≤ K := hn
        exact_mod_cast this
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      simp only [triv_re, triv_im]
      refine ⟨⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_,
        riemannZeta_neg_two_mul_nat_add_one n⟩, by linarith⟩
      intro h
      have := congrArg Complex.re h
      rw [triv_re, one_re] at this
      linarith
  have hinj : ∀ a ∈ Finset.range K, ∀ b ∈ Finset.range K,
      -2 * ((a : ℂ) + 1) = -2 * ((b : ℂ) + 1) → a = b := by
    intro a _ b _ hab
    have h := congrArg Complex.re hab
    rw [triv_re, triv_re] at h
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  have hsum2 : ∑ u ∈ S₀.filter (fun u => ¬ 0 < u.re),
      (analyticOrderNatAt riemannZeta₁ u : ℂ) * (dslope W 0 u + W 0 * (u - 0)⁻¹) =
      ∑ n ∈ Finset.range K, -(W (-2 * ((n : ℂ) + 1)) / (2 * ((n : ℂ) + 1))) := by
    rw [hT2, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hn1 : (-2 * ((n : ℂ) + 1)) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [triv_re, one_re] at this
      linarith
    have hn0' : (-2 * ((n : ℂ) + 1)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      rw [triv_re, zero_re] at this
      linarith
    rw [dslope_add_inv hW hn0']
    have hm : analyticOrderNatAt riemannZeta₁ (-2 * ((n : ℂ) + 1)) = 1 := by
      simp only [analyticOrderNatAt, ordem_zeta1 hn1, ordem_trivial n, ENat.toNat_one]
    rw [hm, Nat.cast_one, one_mul, pw, neg_mul, div_neg]
  have hsum1 : ∑ u ∈ S, (analyticOrderNatAt riemannZeta₁ u : ℂ) * (dslope W 0 u + W 0 * (u - 0)⁻¹) =
      ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * pw W u := by
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨hu0', hre⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, hz1⟩ := (hS₀ u).mp hu0'
    have hu1 := (zeta1_eq_zero_iff.mp hz1).1
    have hu0 : u ≠ 0 := fun h => by rw [h, zero_re] at hre; exact lt_irrefl 0 hre
    rw [dslope_add_inv hW hu0]
    simp only [analyticOrderNatAt, ordem_zeta1 hu1]
  refine ⟨S, fun u => ?_, ?_⟩
  · rw [hSdef, Finset.mem_filter, hS₀, zeta1_eq_zero_iff]
    constructor
    · rintro ⟨⟨hR, _, hζ⟩, hre⟩
      exact ⟨hR, hζ, hre⟩
    · rintro ⟨hR, hζ, hre⟩
      refine ⟨⟨hR, ?_, hζ⟩, hre⟩
      rintro rfl
      exact riemannZeta_one_ne_zero hζ
  · rw [bordo_congr heq, bordo_add hc1 hQ, bordo_const_mul, hpol, bordo_add hQ1 hQ2,
      bordo_cauchy hQd, bordo_add hQ2a hQ2b, bordo_const_mul, bordo_const_mul, hb1, hb0, hsplit,
      hsum1, hsum2, logDeriv_zeta1_zero, Finset.sum_neg_distrib]
    ring


/-! ## 2. O peso gaussiano e o lado aritmético -/

/-- O peso gaussiano `W(s) = exp((s − ½)u + τ(s − ½)²)`. -/
noncomputable def Wg (u τ : ℝ) (s : ℂ) : ℂ := cexp ((s - 1 / 2) * u + τ * (s - 1 / 2) ^ 2)

theorem Wg_diff (u τ : ℝ) : Differentiable ℂ (Wg u τ) := by
  unfold Wg; fun_prop

theorem norm_Wg (u τ : ℝ) (s : ℂ) :
    ‖Wg u τ s‖ = Real.exp ((s.re - 1 / 2) * u + τ * ((s.re - 1 / 2) ^ 2 - s.im ^ 2)) := by
  unfold Wg
  rw [Complex.norm_exp]
  congr 1
  simp only [sq, add_re, mul_re, sub_re, ofReal_re, ofReal_im, sub_im, mul_im, one_re, one_im,
    div_ofNat_re, div_ofNat_im]
  ring

/-- O núcleo do calor `k_τ(v) = (4πτ)^{−1/2} e^{−v²/(4τ)}`. -/
noncomputable def kg (τ v : ℝ) : ℝ := (4 * π * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(v ^ 2 / (4 * τ)))

theorem kg_nonneg (τ v : ℝ) (hτ : 0 < τ) : 0 ≤ kg τ v := by
  unfold kg; positivity

theorem dois_pi_kg {τ : ℝ} (hτ : 0 < τ) (Y : ℝ) :
    2 * π * kg τ Y = Real.sqrt (π / τ) * Real.exp (-(Y ^ 2 / (4 * τ))) := by
  unfold kg
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have h2 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h4 : Real.sqrt (4 * π * τ) = 2 * Real.sqrt π * Real.sqrt τ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), h2]
  rw [h4, Real.sqrt_div' π hτ.le]
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hτ' : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsq : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  field_simp
  nlinarith [hsq]

/-- **A integral gaussiana na reta vertical**: `∫ exp((a + iy)Y + τ(a + iy)²) dy = 2π k_τ(Y)`. -/
theorem integral_linha {τ : ℝ} (hτ : 0 < τ) (a Y : ℝ) :
    ∫ y : ℝ, cexp (((a : ℂ) + y * I) * Y + τ * ((a : ℂ) + y * I) ^ 2) = ((2 * π * kg τ Y : ℝ) : ℂ) := by
  have h : ∀ y : ℝ, ((a : ℂ) + y * I) * Y + τ * ((a : ℂ) + y * I) ^ 2 =
      (-(τ : ℂ)) * (y : ℂ) ^ 2 + (I * (2 * τ * a + Y)) * y + (τ * a ^ 2 + a * Y) := by
    intro y
    have hI : I ^ 2 = -1 := I_sq
    linear_combination (τ : ℂ) * (y : ℂ) ^ 2 * hI
  simp_rw [h]
  rw [integral_cexp_quadratic (by simpa using hτ) _ _, dois_pi_kg hτ Y]
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have e1 : (π : ℂ) / -(-(τ : ℂ)) = ((π / τ : ℝ) : ℂ) := by push_cast; ring
  have e2 : (τ : ℂ) * a ^ 2 + a * Y - (I * (2 * τ * a + Y)) ^ 2 / (4 * -(τ : ℂ)) = ((-(Y ^ 2 / (4 * τ)) : ℝ) : ℂ) := by
    push_cast
    have hI : I ^ 2 = -1 := I_sq
    field_simp
    linear_combination (2 * τ * a + Y) ^ 2 * hI
  rw [e1, e2, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_exp, ← Real.sqrt_eq_rpow]
  push_cast
  ring

theorem norm_exp_linha (L c y w : ℝ) : ‖cexp (-((c : ℂ) + y * I) * L) * cexp (-((c : ℂ) + y * I) * w)‖ =
    Real.exp (-(c * L)) * Real.exp (-(c * w)) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp

/-- `1/s = ∫_0^∞ e^{−sw} dw` (`Re s > 0`). -/
theorem inv_eq_integral {s : ℂ} (hs : 0 < s.re) : 1 / s = ∫ w in Ioi (0 : ℝ), cexp (-s * w) := by
  rw [integral_exp_mul_complex_Ioi (by simpa using hs) 0]
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

/-- `Φ_τ(Y) = ∫_0^∞ e^{−w/2} k_τ(Y − w) dw`: o degrau suavizado. -/
noncomputable def Phi (τ Y : ℝ) : ℝ := ∫ w in Ioi (0 : ℝ), Real.exp (-(w / 2)) * kg τ (Y - w)

/-- **O termo `n` do lado aritmético**: `∫ e^{−sL} W(s)/s dy = 2π e^{−L/2} Φ_τ(u − L)` na reta `Re s = c > 0`
(`1/s = ∫_0^∞ e^{−sw} dw`, Fubini e a integral gaussiana). -/
theorem linha_x {τ : ℝ} (hτ : 0 < τ) (u L : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, cexp (-((c : ℂ) + y * I) * L) * Wg u τ ((c : ℂ) + y * I) / ((c : ℂ) + y * I) =
      ((2 * π * (Real.exp (-(L / 2)) * Phi τ (u - L)) : ℝ) : ℂ) := by
  set f : ℝ → ℝ → ℂ := fun y w => cexp (-((c : ℂ) + y * I) * L) * Wg u τ ((c : ℂ) + y * I) *
    cexp (-((c : ℂ) + y * I) * w) with hf
  have hre : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := fun y => by simp
  have step1 : ∀ y : ℝ, cexp (-((c : ℂ) + y * I) * L) * Wg u τ ((c : ℂ) + y * I) / ((c : ℂ) + y * I) =
      ∫ w in Ioi (0 : ℝ), f y w := fun y => by
    rw [div_eq_mul_one_div, inv_eq_integral (by rw [hre]; exact hc), ← integral_const_mul]
  simp_rw [step1]
  -- integrabilidade no produto
  set K : ℝ := Real.exp (-(c * L) + (c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) with hK
  have hg : Integrable (fun z : ℝ × ℝ => (K * Real.exp (-τ * z.1 ^ 2)) * Real.exp (-c * z.2))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ((integrable_exp_neg_mul_sq hτ).const_mul K).mul_prod (exp_neg_integrableOn_Ioi 0 hc)
  have hcont : Continuous (Function.uncurry f) := by
    have hW := (Wg_diff u τ).continuous
    simp only [hf]
    fun_prop
  have hnorm : ∀ z : ℝ × ℝ, ‖Function.uncurry f z‖ = (K * Real.exp (-τ * z.1 ^ 2)) * Real.exp (-c * z.2) := by
    intro z
    simp only [Function.uncurry, hf]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, norm_Wg, hK]
    simp only [neg_re, mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, add_im, mul_im]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hint : Integrable (Function.uncurry f) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hg.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun z => le_of_eq (hnorm z))
  rw [integral_integral_swap hint]
  -- a integral em `y`, para cada `w`
  have step3 : ∀ w : ℝ, ∫ y : ℝ, f y w = ((2 * π * (Real.exp (-((L + w) / 2)) * kg τ (u - L - w)) : ℝ) : ℂ) := by
    intro w
    have hpt : ∀ y : ℝ, f y w = cexp (-((L + w) / 2 : ℝ)) *
        cexp ((((c - 1 / 2 : ℝ) : ℂ) + y * I) * ((u - L - w : ℝ) : ℂ) +
          τ * (((c - 1 / 2 : ℝ) : ℂ) + y * I) ^ 2) := by
      intro y
      simp only [hf, Wg]
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_linha hτ]
    push_cast
    ring
  simp_rw [step3]
  rw [integral_complex_ofReal]
  congr 1
  rw [integral_const_mul]
  congr 1
  unfold Phi
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
  rw [show -((L + w) / 2) = -(L / 2) + -(w / 2) by ring, Real.exp_add, show u - L - w = (u - L) - w by ring]
  ring

open ATK.ZeroClasses.PNT (vM LSeries_vM)

theorem term_vM_eq {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    LSeries.term vM s n = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * cexp (-s * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, vM, div_eq_mul_inv]
  congr 1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_neg, ← Complex.natCast_log]
  congr 1
  ring

/-- O termo `n` do lado aritmético, como função da ordenada `y`. -/
noncomputable def Fn (u τ c : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  LSeries.term vM ((c : ℂ) + y * I) n * Wg u τ ((c : ℂ) + y * I) / ((c : ℂ) + y * I)

theorem norm_Fn_le {u τ c : ℝ} (hc : 0 < c) (n : ℕ) (y : ℝ) :
    ‖Fn u τ c n y‖ ≤ ‖LSeries.term vM (c : ℂ) n‖ *
      (Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) / c * Real.exp (-τ * y ^ 2)) := by
  unfold Fn
  rw [norm_div, norm_mul, norm_Wg]
  have hre : ((c : ℂ) + y * I).re = c := by simp
  have him : ((c : ℂ) + y * I).im = y := by simp
  rw [hre, him]
  have ht : ‖LSeries.term vM ((c : ℂ) + y * I) n‖ = ‖LSeries.term vM (c : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  rw [ht]
  have hs : c ≤ ‖(c : ℂ) + y * I‖ := by
    have := abs_re_le_norm ((c : ℂ) + y * I)
    rw [hre, abs_of_pos hc] at this
    exact this
  have he : Real.exp ((c - 1 / 2) * u + τ * ((c - 1 / 2) ^ 2 - y ^ 2)) =
      Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) * Real.exp (-τ * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) * Real.exp (-τ * y ^ 2) * ‖(c : ℂ) + y * I‖⁻¹
      ≤ Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) * Real.exp (-τ * y ^ 2) * c⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact inv_anti₀ hc hs
    _ = Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) * c⁻¹ * Real.exp (-τ * y ^ 2) := by ring

theorem Fn_eq {u τ c : ℝ} {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    Fn u τ c n y = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (cexp (-((c : ℂ) + y * I) * Real.log n) * Wg u τ ((c : ℂ) + y * I) / ((c : ℂ) + y * I)) := by
  unfold Fn
  rw [term_vM_eq hn]
  ring

theorem integrable_Fn {u τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) (n : ℕ) : Integrable (Fn u τ c n) := by
  have hcont : Continuous (Fn u τ c n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : Fn u τ c 0 = fun _ => 0 := by funext y; simp [Fn]
      rw [this]; exact continuous_const
    · have hW := (Wg_diff u τ).continuous
      have e : Fn u τ c n = fun y : ℝ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (cexp (-((c : ℂ) + y * I) * Real.log n) * Wg u τ ((c : ℂ) + y * I) / ((c : ℂ) + y * I)) :=
        funext fun y => Fn_eq hn.ne' y
      rw [e]
      have hne : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := fun y h => by
        have := congrArg Complex.re h
        simp at this
        linarith
      exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) hne)
  refine ((integrable_exp_neg_mul_sq hτ).const_mul (‖LSeries.term vM (c : ℂ) n‖ *
    (Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) / c))).mono' hcont.aestronglyMeasurable ?_
  exact Eventually.of_forall fun y => (norm_Fn_le hc n y).trans (le_of_eq (by ring))

/-- **O lado aritmético**: `∫ F_W(c + iy) dy = 2π Σ_n Λ(n) n^{−1/2} Φ_τ(u − log n)` (`c > 1`). -/
theorem lado_aritmetico {τ : ℝ} (hτ : 0 < τ) (u : ℝ) {c : ℝ} (hc : 1 < c) :
    ∫ y : ℝ, Fw (Wg u τ) ((c : ℂ) + y * I) =
      ((2 * π * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) *
        Phi τ (u - Real.log n) : ℝ) : ℂ) := by
  have hc0 : 0 < c := by linarith
  have hre : ∀ y : ℝ, 1 < ((c : ℂ) + y * I).re := fun y => by simpa using hc
  have hF : ∀ y : ℝ, Fw (Wg u τ) ((c : ℂ) + y * I) = ∑' n : ℕ, Fn u τ c n y := by
    intro y
    unfold Fw Fn
    rw [← LSeries_vM (hre y), LSeries, mul_comm, mul_div_assoc, ← tsum_mul_right]
    congr 1
    funext n
    ring
  simp_rw [hF]
  have hsum : Summable fun n : ℕ => ∫ y : ℝ, ‖Fn u τ c n y‖ := by
    have hL : LSeriesSummable vM (c : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_)
      (hL.norm.mul_right (Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) / c *
        ∫ y : ℝ, Real.exp (-τ * y ^ 2)))
    calc ∫ y : ℝ, ‖Fn u τ c n y‖
        ≤ ∫ y : ℝ, ‖LSeries.term vM (c : ℂ) n‖ *
            (Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) / c * Real.exp (-τ * y ^ 2)) :=
          integral_mono (integrable_Fn hτ hc0 n).norm
            (((integrable_exp_neg_mul_sq hτ).const_mul _).const_mul _) (fun y => norm_Fn_le hc0 n y)
      _ = ‖LSeries.term vM (c : ℂ) n‖ *
            (Real.exp ((c - 1 / 2) * u + τ * (c - 1 / 2) ^ 2) / c * ∫ y : ℝ, Real.exp (-τ * y ^ 2)) := by
          rw [integral_const_mul, integral_const_mul]
  rw [← integral_tsum_of_summable_integral_norm (fun n => integrable_Fn hτ hc0 n) hsum]
  have hval : ∀ n : ℕ, ∫ y : ℝ, Fn u τ c n y = ((2 * π * (ArithmeticFunction.vonMangoldt n *
      Real.exp (-(Real.log n / 2)) * Phi τ (u - Real.log n)) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Fn]
    · simp_rw [Fn_eq hn.ne']
      rw [integral_const_mul, linha_x hτ u (Real.log n) hc0]
      push_cast
      ring
  simp_rw [hval]
  rw [← Complex.ofReal_tsum, tsum_mul_left]

/-! ## 3. As cotas no retângulo -/

theorem norm_Fw (W : ℂ → ℂ) (s : ℂ) : ‖Fw W s‖ = ‖W s‖ * ‖logDeriv riemannZeta s‖ / ‖s‖ := by
  unfold Fw
  rw [norm_div, norm_mul, norm_neg]

/-- **As horizontais**: em alturas boas, `‖F_W(x ± iT)‖ ≤ e^{3|u| + 9τ − τT²} A(T)/T` em `−5/2 ≤ x ≤ 2`. -/
theorem hor_bound {u τ T C₁ c₀ : ℝ} (hτ : 0 < τ) (hT : 6 ≤ T) (hC₁ : 0 ≤ C₁)
    (hc₀ : ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv riemannZeta s‖ ≤ c₀)
    (hgood : ∀ σ : ℝ, 0 < σ → σ ≤ 2 → ∀ τ : ℝ, (τ = T ∨ τ = -T) →
      riemannZeta ((σ : ℂ) + τ * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + τ * I)‖ ≤ C₁ * Real.log (2 + T) ^ 2)
    {x t : ℝ} (hx1 : -5 / 2 ≤ x) (hx2 : x ≤ 2) (ht : t = T ∨ t = -T) :
    ‖Fw (Wg u τ) ((x : ℂ) + t * I)‖ ≤
      Real.exp (3 * |u| + 9 * τ - τ * T ^ 2) * (C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23) / T := by
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  have hl0 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hT0 : 0 < T := by linarith
  have ht2 : t ^ 2 = T ^ 2 := by rcases ht with h | h <;> rw [h]; ring
  have htabs : |t| = T := by
    rcases ht with h | h <;> rw [h]
    · exact abs_of_pos hT0
    · rw [abs_neg]; exact abs_of_pos hT0
  rw [norm_Fw, norm_Wg]
  have hre : ((x : ℂ) + t * I).re = x := by simp
  have him : ((x : ℂ) + t * I).im = t := by simp
  rw [hre, him, ht2]
  have hL := ATK.ZeroClasses.ExplicitaLimite.logDeriv_hor hC₁ hT hc₀ hgood hx2 ht
  have hL' : ‖logDeriv riemannZeta ((x : ℂ) + t * I)‖ ≤
      C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23 := by linarith
  have hs : T ≤ ‖(x : ℂ) + t * I‖ := by
    have := abs_im_le_norm ((x : ℂ) + t * I)
    rwa [him, htabs] at this
  have hE : Real.exp ((x - 1 / 2) * u + τ * ((x - 1 / 2) ^ 2 - T ^ 2)) ≤ Real.exp (3 * |u| + 9 * τ - τ * T ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h1 : (x - 1 / 2) * u ≤ 3 * |u| := by
      have : |x - 1 / 2| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc (x - 1 / 2) * u ≤ |(x - 1 / 2) * u| := le_abs_self _
        _ = |x - 1 / 2| * |u| := abs_mul _ _
        _ ≤ 3 * |u| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h2 : (x - 1 / 2) ^ 2 ≤ 9 := by nlinarith
    nlinarith
  have hA0 : 0 ≤ C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23 := by positivity
  calc Real.exp ((x - 1 / 2) * u + τ * ((x - 1 / 2) ^ 2 - T ^ 2)) *
        ‖logDeriv riemannZeta ((x : ℂ) + t * I)‖ / ‖(x : ℂ) + t * I‖
      ≤ Real.exp (3 * |u| + 9 * τ - τ * T ^ 2) *
          (C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23) / ‖(x : ℂ) + t * I‖ := by
        gcongr
    _ ≤ Real.exp (3 * |u| + 9 * τ - τ * T ^ 2) *
          (C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23) / T := by
        gcongr

/-- O majorante das horizontais tende a zero. -/
theorem hor_tendsto {u τ C₁ c₀ : ℝ} (hτ : 0 < τ) (hC₁ : 0 ≤ C₁) (hc₀ : 0 ≤ c₀) :
    Tendsto (fun T : ℝ => 9 / 2 * (Real.exp (3 * |u| + 9 * τ - τ * T ^ 2) *
      (C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23) / T)) atTop (𝓝 0) := by
  set M : ℝ := 9 / 2 * Real.exp (3 * |u| + 9 * τ) * (9 * C₁ + c₀ + 26) / τ with hM
  have hlim : Tendsto (fun T : ℝ => M * ((τ * T ^ 2) ^ 1 * Real.exp (-(τ * T ^ 2)))) atTop (𝓝 (M * 0)) := by
    have h1 : Tendsto (fun T : ℝ => τ * T ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop hτ
    exact ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1).const_mul M
  rw [mul_zero] at hlim
  have hl : ∀ T : ℝ, 1 ≤ T → 0 ≤ Real.log (2 + T) ∧ Real.log (2 + T) ≤ 3 * T := fun T hT =>
    ⟨Real.log_nonneg (by linarith), by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + T by linarith); linarith⟩
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have := (hl T hT).1
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    obtain ⟨hl0, hl3⟩ := hl T hT
    have hT0 : 0 < T := by linarith
    have hA : C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23 ≤ (9 * C₁ + c₀ + 26) * T ^ 2 := by
      have h1 : Real.log (2 + T) ^ 2 ≤ 9 * T ^ 2 := by nlinarith
      have h2 : c₀ ≤ c₀ * T ^ 2 := le_mul_of_one_le_right hc₀ (by nlinarith)
      nlinarith
    have hE : Real.exp (3 * |u| + 9 * τ - τ * T ^ 2) = Real.exp (3 * |u| + 9 * τ) * Real.exp (-(τ * T ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    have hE1 : 0 < Real.exp (3 * |u| + 9 * τ) := Real.exp_pos _
    have hE2 : 0 < Real.exp (-(τ * T ^ 2)) := Real.exp_pos _
    rw [hE, hM, pow_one]
    calc 9 / 2 * (Real.exp (3 * |u| + 9 * τ) * Real.exp (-(τ * T ^ 2)) *
          (C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23) / T)
        ≤ 9 / 2 * (Real.exp (3 * |u| + 9 * τ) * Real.exp (-(τ * T ^ 2)) * ((9 * C₁ + c₀ + 26) * T ^ 2) / T) := by
          gcongr
      _ = 9 / 2 * Real.exp (3 * |u| + 9 * τ) * (9 * C₁ + c₀ + 26) * Real.exp (-(τ * T ^ 2)) * T := by
          field_simp
      _ ≤ 9 / 2 * Real.exp (3 * |u| + 9 * τ) * (9 * C₁ + c₀ + 26) * Real.exp (-(τ * T ^ 2)) * T ^ 2 := by
          gcongr
          nlinarith
      _ = 9 / 2 * Real.exp (3 * |u| + 9 * τ) * (9 * C₁ + c₀ + 26) / τ * (τ * T ^ 2 * Real.exp (-(τ * T ^ 2))) := by
          field_simp

/-! ## 4. As retas verticais `Re s = 2` e `Re s = −5/2` -/

theorem continuousAt_Fw {u τ : ℝ} {s : ℂ} (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) (h0 : s ≠ 0) :
    ContinuousAt (Fw (Wg u τ)) s := by
  have hA := ATK.ZeroClasses.Explicita.zeta_analytic h1
  have hL : ContinuousAt (logDeriv riemannZeta) s := by
    have e : logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z :=
      funext fun z => logDeriv_apply _ z
    rw [e]
    exact hA.deriv.continuousAt.div hA.continuousAt hz
  unfold Fw
  exact (((Wg_diff u τ).continuous.continuousAt).mul hL.neg).div continuousAt_id h0

theorem continuous_linha {u τ σ : ℝ} (hne : ∀ y : ℝ, (σ : ℂ) + y * I ≠ 1 ∧
    riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧ (σ : ℂ) + y * I ≠ 0) :
    Continuous fun y : ℝ => Fw (Wg u τ) ((σ : ℂ) + y * I) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  obtain ⟨h1, hz, h0⟩ := hne y
  have hc : Continuous fun y : ℝ => (σ : ℂ) + y * I := by fun_prop
  exact ContinuousAt.comp (g := Fw (Wg u τ)) (continuousAt_Fw h1 hz h0) hc.continuousAt

theorem integrable_dir (u : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable fun y : ℝ => Fw (Wg u τ) (((2 : ℝ) : ℂ) + y * I) := by
  obtain ⟨c₀, hc₀⟩ := ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  have hne : ∀ y : ℝ, ((2 : ℝ) : ℂ) + y * I ≠ 1 ∧ riemannZeta (((2 : ℝ) : ℂ) + y * I) ≠ 0 ∧
      ((2 : ℝ) : ℂ) + y * I ≠ 0 := by
    intro y
    have hre : (((2 : ℝ) : ℂ) + y * I).re = 2 := by simp
    refine ⟨fun h => ?_, riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; norm_num), fun h => ?_⟩
    · have := congrArg Complex.re h; rw [hre, one_re] at this; norm_num at this
    · have := congrArg Complex.re h; rw [hre, zero_re] at this; norm_num at this
  refine ((integrable_exp_neg_mul_sq hτ).const_mul (Real.exp (3 / 2 * u + τ * (9 / 4)) * c₀ / 2)).mono'
    (continuous_linha hne).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_Fw, norm_Wg]
  have hre : (((2 : ℝ) : ℂ) + y * I).re = 2 := by simp
  have him : (((2 : ℝ) : ℂ) + y * I).im = y := by simp
  rw [hre, him]
  have hL := hc₀ (((2 : ℝ) : ℂ) + y * I) (by rw [hre])
  have hs : 2 ≤ ‖((2 : ℝ) : ℂ) + y * I‖ := by
    have := abs_re_le_norm (((2 : ℝ) : ℂ) + y * I)
    rwa [hre, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
  have he : Real.exp ((2 - 1 / 2) * u + τ * ((2 - 1 / 2) ^ 2 - y ^ 2)) =
      Real.exp (3 / 2 * u + τ * (9 / 4)) * Real.exp (-τ * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  calc Real.exp (3 / 2 * u + τ * (9 / 4)) * Real.exp (-τ * y ^ 2) *
        ‖logDeriv riemannZeta (((2 : ℝ) : ℂ) + y * I)‖ / ‖((2 : ℝ) : ℂ) + y * I‖
      ≤ Real.exp (3 / 2 * u + τ * (9 / 4)) * Real.exp (-τ * y ^ 2) * c₀ / 2 := by
        gcongr
    _ = Real.exp (3 / 2 * u + τ * (9 / 4)) * c₀ / 2 * Real.exp (-τ * y ^ 2) := by ring

/-- A abscissa da reta esquerda, `−(2·1 + ½) = −5/2`. -/
theorem sigmaL_eq : (-(2 * ((1 : ℕ) : ℝ) + 1 / 2)) = -5 / 2 := by norm_num

theorem ne_esq (y : ℝ) : ((-5 / 2 : ℝ) : ℂ) + y * I ≠ 1 ∧ riemannZeta (((-5 / 2 : ℝ) : ℂ) + y * I) ≠ 0 ∧
    ((-5 / 2 : ℝ) : ℂ) + y * I ≠ 0 := by
  have hre : (((-5 / 2 : ℝ) : ℂ) + y * I).re = -5 / 2 := by simp
  refine ⟨fun h => ?_, fun hz => ?_, fun h => ?_⟩
  · have := congrArg Complex.re h; rw [hre, one_re] at this; norm_num at this
  · obtain ⟨n, hn⟩ := ATK.ZetaSimetria.zero_trivial_de_re_nao_pos hz (by rw [hre]; norm_num)
    have h2 := congrArg Complex.re hn
    rw [hre, triv_re] at h2
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have h4 : ((4 * (n + 1) : ℕ) : ℝ) = ((5 : ℕ) : ℝ) := by push_cast; linarith
    have h5 : 4 * (n + 1) = 5 := by exact_mod_cast h4
    omega
  · have := congrArg Complex.re h; rw [hre, zero_re] at this; norm_num at this

/-- A cota pontual na reta esquerda: `‖F_W(−5/2 + iy)‖ ≤ e^{−3u + 9τ}(2/5)((c₀ + B + 13) + |y|) e^{−τy²}`. -/
theorem norm_esq_pt {c₀ B : ℝ} (hc₀ : ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv riemannZeta s‖ ≤ c₀)
    (hB : ∀ (n : ℕ) (y : ℝ), ‖digamma ((1 / 2 : ℂ) + y * I + n)‖ ≤ B + Real.log (2 + |y|) + 2 * n)
    (u τ y : ℝ) : ‖Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      Real.exp (-3 * u + 9 * τ) * (2 / 5) * ((c₀ + B + 13) * Real.exp (-τ * y ^ 2) +
        |y| * Real.exp (-τ * y ^ 2)) := by
  rw [norm_Fw, norm_Wg]
  have hre : (((-5 / 2 : ℝ) : ℂ) + y * I).re = -5 / 2 := by simp
  have him : (((-5 / 2 : ℝ) : ℂ) + y * I).im = y := by simp
  rw [hre, him]
  have hL := ATK.ZeroClasses.ExplicitaLimite.logDeriv_esq_reta hc₀ hB (K := 1) le_rfl y
  rw [sigmaL_eq] at hL
  have hlog : Real.log (2 + |y|) ≤ 1 + |y| := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + |y| by positivity); linarith
  have hL' : ‖logDeriv riemannZeta (((-5 / 2 : ℝ) : ℂ) + y * I)‖ ≤ c₀ + B + 13 + |y| := by
    push_cast at hL ⊢; linarith
  have hs : 5 / 2 ≤ ‖((-5 / 2 : ℝ) : ℂ) + y * I‖ := by
    have := abs_re_le_norm (((-5 / 2 : ℝ) : ℂ) + y * I)
    rw [hre] at this
    norm_num at this ⊢
    linarith
  have he : Real.exp ((-5 / 2 - 1 / 2) * u + τ * ((-5 / 2 - 1 / 2) ^ 2 - y ^ 2)) =
      Real.exp (-3 * u + 9 * τ) * Real.exp (-τ * y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  have hx : 0 < Real.exp (-τ * y ^ 2) := Real.exp_pos _
  have hx3 : 0 < Real.exp (-3 * u + 9 * τ) := Real.exp_pos _
  have hp : 0 ≤ c₀ + B + 13 + |y| := (norm_nonneg _).trans hL'
  calc Real.exp (-3 * u + 9 * τ) * Real.exp (-τ * y ^ 2) *
        ‖logDeriv riemannZeta (((-5 / 2 : ℝ) : ℂ) + y * I)‖ / ‖((-5 / 2 : ℝ) : ℂ) + y * I‖
      ≤ Real.exp (-3 * u + 9 * τ) * Real.exp (-τ * y ^ 2) * (c₀ + B + 13 + |y|) / (5 / 2) := by
        gcongr
    _ = Real.exp (-3 * u + 9 * τ) * (2 / 5) * ((c₀ + B + 13) * Real.exp (-τ * y ^ 2) +
          |y| * Real.exp (-τ * y ^ 2)) := by ring

theorem integrable_G {τ : ℝ} (hτ : 0 < τ) (A : ℝ) :
    Integrable fun y : ℝ => A * Real.exp (-τ * y ^ 2) + |y| * Real.exp (-τ * y ^ 2) := by
  refine ((integrable_exp_neg_mul_sq hτ).const_mul A).add ((integrable_mul_exp_neg_mul_sq hτ).norm.congr ?_)
  exact Eventually.of_forall fun y => by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

theorem integrable_esq (u : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable fun y : ℝ => Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I) := by
  obtain ⟨c₀, hc₀⟩ := ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
  obtain ⟨B, hB0, hB⟩ := ATK.ZeroClasses.ExplicitaLimite.digamma_esq
  exact ((integrable_G hτ (c₀ + B + 13)).const_mul (Real.exp (-3 * u + 9 * τ) * (2 / 5))).mono'
    (continuous_linha (ne_esq)).aestronglyMeasurable (Eventually.of_forall fun y => norm_esq_pt hc₀ hB u τ y)

/-- **A reta esquerda é `O(e^{−3u})`**, uniformemente em `u`. -/
theorem esq_le {τ : ℝ} (hτ : 0 < τ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ,
    ‖∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)‖ ≤ M * Real.exp (-3 * u) := by
  obtain ⟨c₀, hc₀⟩ := ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
  obtain ⟨B, hB0, hB⟩ := ATK.ZeroClasses.ExplicitaLimite.digamma_esq
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  set G : ℝ → ℝ := fun y => (c₀ + B + 13) * Real.exp (-τ * y ^ 2) + |y| * Real.exp (-τ * y ^ 2) with hG
  have hGi : Integrable G := integrable_G hτ (c₀ + B + 13)
  have hG0 : 0 ≤ ∫ y : ℝ, G y := integral_nonneg fun y => by
    simp only [hG]; positivity
  refine ⟨Real.exp (9 * τ) * (2 / 5) * ∫ y : ℝ, G y, by positivity, fun u => ?_⟩
  calc ‖∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)‖
      ≤ ∫ y : ℝ, Real.exp (-3 * u + 9 * τ) * (2 / 5) * G y :=
        norm_integral_le_of_norm_le (hGi.const_mul _) (Eventually.of_forall fun y => norm_esq_pt hc₀ hB u τ y)
    _ = Real.exp (9 * τ) * (2 / 5) * (∫ y : ℝ, G y) * Real.exp (-3 * u) := by
        rw [integral_const_mul, show -3 * u + 9 * τ = 9 * τ + -3 * u by ring, Real.exp_add]
        ring

/-! ## 5. A fórmula explícita gaussiana -/

open ATK.ZeroClasses.ExplicitaT (Zfin mem_Zfin)

/-- `A_τ(u) = Σ_n Λ(n) n^{−1/2} Φ_τ(u − log n)`: `e^{−u/2}ψ(e^u)` suavizado na escala `√τ`. -/
noncomputable def Aτ (τ u : ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) * Phi τ (u - Real.log n)

/-- **A fórmula explícita gaussiana** (sem hipóteses). Para `τ > 0` e `u ∈ ℝ`, ao longo de alturas boas
`T_k ∈ [k + 6, k + 7]`,

  `Σ_{|γ| ≤ T_k} m_ρ W(ρ)/ρ → W(1) + W(−2)/2 − W(0) log 2π − A_τ(u) + (1/2π) ∫ F_W(−5/2 + iy) dy`,

`W(s) = exp((s − ½)u + τ(s − ½)²)`, `ρ` sobre os zeros não triviais. -/
theorem formula_gauss {τ : ℝ} (hτ : 0 < τ) (u : ℝ) : ∃ T : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 6 ≤ T k ∧ T k ≤ k + 7) ∧
    Tendsto (fun k => ∑ ρ ∈ Zfin (T k), (analyticOrderNatAt riemannZeta ρ : ℂ) * pw (Wg u τ) ρ) atTop
      (𝓝 (Wg u τ 1 + Wg u τ (-2) / 2 - Wg u τ 0 * (Real.log (2 * π) : ℂ) - (Aτ τ u : ℂ) +
        (1 / (2 * π : ℂ)) * ∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I))) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := ATK.ZeroClasses.Explicita.altura_boa
  obtain ⟨c₀, hc₀⟩ := ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 2 (by norm_num))
  have hex : ∀ k : ℕ, ∃ T : ℝ, (k : ℝ) + 6 ≤ T ∧ T ≤ k + 7 ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ 2 → ∀ t : ℝ, (t = T ∨ t = -T) →
        riemannZeta ((σ : ℂ) + t * I) ≠ 0 ∧
        ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ C₁ * Real.log (2 + T) ^ 2 := fun k => by
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    obtain ⟨T, h1, h2, h3⟩ := hC₁ ((k : ℝ) + 6) (by linarith)
    exact ⟨T, h1, by linarith, h3⟩
  choose T hT1 hT2 hgood using hex
  refine ⟨T, fun k => ⟨hT1 k, hT2 k⟩, ?_⟩
  have hT6 : ∀ k, 6 ≤ T k := fun k => le_trans (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) (hT1 k)
  have hTlim : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => hT1 k) (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  -- as quatro partes do bordo
  set H : ℕ → ℂ := fun k => (∫ x : ℝ in (-5 / 2 : ℝ)..2, Fw (Wg u τ) ((x : ℂ) + ((-T k : ℝ) : ℂ) * I)) -
    ∫ x : ℝ in (-5 / 2 : ℝ)..2, Fw (Wg u τ) ((x : ℂ) + ((T k : ℝ) : ℂ) * I) with hH
  set VR : ℕ → ℂ := fun k => ∫ y : ℝ in (-T k)..(T k), Fw (Wg u τ) (((2 : ℝ) : ℂ) + y * I) with hVR
  set VL : ℕ → ℂ := fun k => ∫ y : ℝ in (-T k)..(T k), Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I) with hVL
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have hk : ∀ k : ℕ, ∑ ρ ∈ Zfin (T k), (analyticOrderNatAt riemannZeta ρ : ℂ) * pw (Wg u τ) ρ =
      Wg u τ 1 + Wg u τ (-2) / 2 - Wg u τ 0 * (Real.log (2 * π) : ℂ) - (H k / (2 * π * I) + (VR k - VL k) / (2 * π)) := by
    intro k
    have hT0 : 0 < T k := by linarith [hT6 k]
    have hbd : ∀ s : ℂ, 0 < s.re → s.re < 1 → (s.im = -T k ∨ s.im = T k) → riemannZeta s ≠ 0 := by
      intro s h0 h1 him
      have := (hgood k s.re h0 (by linarith) s.im him.symm).1
      rwa [Complex.re_add_im] at this
    obtain ⟨S, hS, hbordo⟩ := bordo_peso (Wg_diff u τ) (c := 2) (by norm_num) hT0 1 hbd
    have hSZ : S = Zfin (T k) := by
      ext ρ
      rw [hS, mem_Zfin]
      constructor
      · rintro ⟨hR, hz, hre⟩
        have him := (mem_reProdIm.mp hR).2
        change ρ.im ∈ [[-T k, T k]] at him
        rw [uIcc_of_le (by linarith)] at him
        exact ⟨hz, hre, abs_le.mpr ⟨him.1, him.2⟩⟩
      · rintro ⟨hz, hre, him⟩
        have hρ1 : ρ.re < 1 := by
          by_contra h
          exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
        refine ⟨mem_reProdIm.mpr ⟨?_, ?_⟩, hz, hre⟩
        · change ρ.re ∈ [[-(2 * ((1 : ℕ) : ℝ) + 1 / 2), 2]]
          rw [uIcc_of_le (by norm_num)]
          exact ⟨by norm_num; linarith, by linarith⟩
        · change ρ.im ∈ [[-T k, T k]]
          rw [uIcc_of_le (by linarith)]
          exact ⟨(abs_le.mp him).1, (abs_le.mp him).2⟩
    rw [hSZ] at hbordo
    have hb : ATK.ZeroClasses.ArgRetangulo.bordo (Fw (Wg u τ)) ⟨-(2 * ((1 : ℕ) : ℝ) + 1 / 2), -T k⟩ ⟨2, T k⟩ =
        H k + I * VR k - I * VL k := by
      simp only [hH, hVR, hVL]
      show (∫ x : ℝ in (-(2 * ((1 : ℕ) : ℝ) + 1 / 2))..2, Fw (Wg u τ) ((x : ℂ) + ((-T k : ℝ) : ℂ) * I)) -
          (∫ x : ℝ in (-(2 * ((1 : ℕ) : ℝ) + 1 / 2))..2, Fw (Wg u τ) ((x : ℂ) + ((T k : ℝ) : ℂ) * I)) +
          I • (∫ y : ℝ in (-T k)..(T k), Fw (Wg u τ) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) -
          I • (∫ y : ℝ in (-T k)..(T k),
            Fw (Wg u τ) (((-(2 * ((1 : ℕ) : ℝ) + 1 / 2) : ℝ) : ℂ) + (y : ℂ) * I)) = _
      rw [sigmaL_eq]
      simp only [smul_eq_mul]
    rw [hb, Finset.sum_range_one] at hbordo
    have e2 : Wg u τ (-2 * (((0 : ℕ) : ℂ) + 1)) / (2 * (((0 : ℕ) : ℂ) + 1)) = Wg u τ (-2) / 2 := by norm_num
    rw [e2] at hbordo
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    linear_combination hbordo
  -- os limites das quatro partes
  have hR : Tendsto VR atTop (𝓝 (∫ y : ℝ, Fw (Wg u τ) (((2 : ℝ) : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral (integrable_dir u hτ) (tendsto_neg_atTop_atBot.comp hTlim) hTlim
  have hL : Tendsto VL atTop (𝓝 (∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral (integrable_esq u hτ) (tendsto_neg_atTop_atBot.comp hTlim) hTlim
  set bd : ℝ → ℝ := fun T => Real.exp (3 * |u| + 9 * τ - τ * T ^ 2) *
    (C₁ * Real.log (2 + T) ^ 2 + c₀ + Real.log (2 + T) + 23) / T with hbd
  have hhor : ∀ k : ℕ, ∀ t : ℝ, (t = T k ∨ t = -T k) →
      ‖∫ x : ℝ in (-5 / 2 : ℝ)..2, Fw (Wg u τ) ((x : ℂ) + (t : ℂ) * I)‖ ≤ bd (T k) * |2 - (-5 / 2 : ℝ)| := by
    intro k t ht
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le (by norm_num)] at hx
    exact hor_bound hτ (hT6 k) hC₁0 hc₀ (hgood k) hx.1.le hx.2 ht
  have hHlim : Tendsto H atTop (𝓝 0) := by
    have hb' : Tendsto (fun k => 2 * (9 / 2 * bd (T k))) atTop (𝓝 (2 * 0)) :=
      ((hor_tendsto (u := u) hτ hC₁0 hc₀0).comp hTlim).const_mul 2
    rw [mul_zero] at hb'
    refine squeeze_zero_norm (fun k => ?_) hb'
    have h1 := hhor k (-T k) (Or.inr rfl)
    have h2 := hhor k (T k) (Or.inl rfl)
    have e : |2 - (-5 / 2 : ℝ)| = 9 / 2 := by norm_num [abs_of_pos]
    rw [e] at h1 h2
    calc ‖H k‖ ≤ ‖∫ x : ℝ in (-5 / 2 : ℝ)..2, Fw (Wg u τ) ((x : ℂ) + ((-T k : ℝ) : ℂ) * I)‖ +
          ‖∫ x : ℝ in (-5 / 2 : ℝ)..2, Fw (Wg u τ) ((x : ℂ) + ((T k : ℝ) : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ bd (T k) * (9 / 2) + bd (T k) * (9 / 2) := add_le_add h1 h2
      _ = 2 * (9 / 2 * bd (T k)) := by ring
  have hfin := (tendsto_const_nhds (x := Wg u τ 1 + Wg u τ (-2) / 2 - Wg u τ 0 * (Real.log (2 * π) : ℂ))).sub
    ((hHlim.div_const (2 * π * I)).add ((hR.sub hL).div_const (2 * π)))
  rw [lado_aritmetico hτ u (c := 2) (by norm_num)] at hfin
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hval : Wg u τ 1 + Wg u τ (-2) / 2 - Wg u τ 0 * (Real.log (2 * π) : ℂ) -
      (0 / (2 * π * I) + (((2 * π * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) *
        Phi τ (u - Real.log n) : ℝ) : ℂ) - ∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)) / (2 * π)) =
      Wg u τ 1 + Wg u τ (-2) / 2 - Wg u τ 0 * (Real.log (2 * π) : ℂ) - (Aτ τ u : ℂ) +
        (1 / (2 * π : ℂ)) * ∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I) := by
    unfold Aτ
    push_cast
    field_simp
    ring
  rw [hval] at hfin
  exact hfin.congr fun k => (hk k).symm

end ATK.ZeroClasses.ExplicitaGauss

#print axioms ATK.ZeroClasses.ExplicitaGauss.dslope_diffW
#print axioms ATK.ZeroClasses.ExplicitaGauss.dslope_add_inv
#print axioms ATK.ZeroClasses.ExplicitaGauss.bordo_peso
#print axioms ATK.ZeroClasses.ExplicitaGauss.Wg_diff
#print axioms ATK.ZeroClasses.ExplicitaGauss.norm_Wg
#print axioms ATK.ZeroClasses.ExplicitaGauss.kg_nonneg
#print axioms ATK.ZeroClasses.ExplicitaGauss.dois_pi_kg
#print axioms ATK.ZeroClasses.ExplicitaGauss.integral_linha
#print axioms ATK.ZeroClasses.ExplicitaGauss.norm_exp_linha
#print axioms ATK.ZeroClasses.ExplicitaGauss.inv_eq_integral
#print axioms ATK.ZeroClasses.ExplicitaGauss.linha_x
#print axioms ATK.ZeroClasses.ExplicitaGauss.term_vM_eq
#print axioms ATK.ZeroClasses.ExplicitaGauss.norm_Fn_le
#print axioms ATK.ZeroClasses.ExplicitaGauss.Fn_eq
#print axioms ATK.ZeroClasses.ExplicitaGauss.integrable_Fn
#print axioms ATK.ZeroClasses.ExplicitaGauss.lado_aritmetico
#print axioms ATK.ZeroClasses.ExplicitaGauss.norm_Fw
#print axioms ATK.ZeroClasses.ExplicitaGauss.hor_bound
#print axioms ATK.ZeroClasses.ExplicitaGauss.hor_tendsto
#print axioms ATK.ZeroClasses.ExplicitaGauss.continuousAt_Fw
#print axioms ATK.ZeroClasses.ExplicitaGauss.continuous_linha
#print axioms ATK.ZeroClasses.ExplicitaGauss.integrable_dir
#print axioms ATK.ZeroClasses.ExplicitaGauss.sigmaL_eq
#print axioms ATK.ZeroClasses.ExplicitaGauss.ne_esq
#print axioms ATK.ZeroClasses.ExplicitaGauss.norm_esq_pt
#print axioms ATK.ZeroClasses.ExplicitaGauss.integrable_G
#print axioms ATK.ZeroClasses.ExplicitaGauss.integrable_esq
#print axioms ATK.ZeroClasses.ExplicitaGauss.esq_le
#print axioms ATK.ZeroClasses.ExplicitaGauss.formula_gauss
