import ATK.ZeroClasses.BDEspectral

/-!
# Báez-Duarte ponderado: o deslocamento do molificador (rodada 74)

Segunda peça da questão Q2(ii) de `fronteira/RH_frontier.md`. Sob `SemZeros θ` (`ζ ≠ 0` em `Re s > θ`,
`½ ≤ θ < 1`), para `θ + δ < Re s < 1`, `0 < δ < 1`:

  **`A_N(s) = 1/ζ(s) + (1/2π) ∫ W(−δ + iy) N^{−δ+iy} ζ(s − δ + iy)^{−1} dy`**   (`desloc`),

com `A_N(s) = Σ_{k<N} μ(k)(1 − k/N)² k^{−s}` e `W(z) = 2/(z(z + 1)(z + 2))` (rodada 73). Daí

  **`|A_N(σ + iτ) − 1/ζ(σ + iτ)| ≤ K N^{−δ} (1 + |τ|)^η`**   (`molif_cota`),

uniforme em `N` e `τ`. As peças:

* `bordo_Gs`: no retângulo `[−δ, 1] × [−Y, Y]`, `∮ W(z)N^z F(s + z) dz = 2πi F(s)` — o único polo é `z = 0`
  (resíduo `W ~ 1/z`), pois `F(s + z) = 1/ζ(s + z)` é holomorfa em `Re(s + z) > θ` (`QuasiRH.differentiableAt_F`);
* `norm_WR_esq`, `norm_WR_hor`: `‖W(−δ + iy)‖ ≤ 8/(δ(1 − δ)) (1 + |y|)^{−2}` e `‖W(x ± iY)‖ ≤ 2/|Y|³`;
* `|1/ζ(s)| ≤ C(1 + |Im s|)^η` em `Re s ≥ θ + δ′` (`QuasiRH.norm_F_le`, Borel–Carathéodory e três círculos);
* `Y → ∞`: as horizontais somem como `Y^{−2}` e as verticais convergem (`intervalIntegral_tendsto_integral`).

Classificação (rodada 74): **ferramenta**. RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real Interval

namespace ATK.ZeroClasses.BDDesloc

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_cauchy bordo_inv
  bordo_const_mul)
open ATK.ZeroClasses.BDEspectral (WR aN LSeries_aN_int)
open ATK.ZeroClasses.QuasiRH (SemZeros differentiableAt_F norm_F_le)
open ATK.RHLogZeta (F)

/-! ## 1. Cotas elementares -/

theorem um_add_le (a b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (1 + |a + b|) ^ η ≤ (1 + |a|) ^ η * (1 + |b|) ^ η := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hη
  have h1 := abs_add_le a b
  have h2 := mul_nonneg (abs_nonneg a) (abs_nonneg b)
  nlinarith

theorem WR_cont' {a : ℝ} (h0 : a ≠ 0) (h1 : a + 1 ≠ 0) (h2 : a + 2 ≠ 0) :
    Continuous (fun y : ℝ => WR ((a : ℂ) + y * I)) := by
  unfold WR
  refine Continuous.div continuous_const (by fun_prop) fun y => ?_
  have hne : ∀ b : ℝ, a + b ≠ 0 → ((a : ℂ) + y * I + b) ≠ 0 := by
    intro b hb h
    have := congrArg Complex.re h
    simp at this
    exact hb this
  have e0 : ((a : ℂ) + y * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact h0 this
  refine mul_ne_zero (mul_ne_zero e0 ?_) ?_
  · have := hne 1 h1
    push_cast at this
    exact this
  · have := hne 2 h2
    push_cast at this
    exact this

/-- **`‖W(−δ + iy)‖ ≤ 8/(δ(1 − δ)) (1 + |y|)^{−2}`**. -/
theorem norm_WR_esq {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (y : ℝ) :
    ‖WR (((-δ : ℝ) : ℂ) + y * I)‖ ≤ 8 / (δ * (1 - δ)) * (1 + ‖y‖) ^ (-2 : ℝ) := by
  set z : ℂ := ((-δ : ℝ) : ℂ) + y * I with hzdef
  have hre : z.re = -δ := by simp [hzdef]
  have him : z.im = y := by simp [hzdef]
  have h0 : δ ≤ ‖z‖ := by
    have := abs_re_le_norm z
    rw [hre, abs_neg, abs_of_pos hδ0] at this
    exact this
  have h1 : (1 - δ) * (1 + |y|) / 2 ≤ ‖z + 1‖ := by
    have a1 := abs_re_le_norm (z + 1)
    have a2 := abs_im_le_norm (z + 1)
    have e1 : (z + 1).re = 1 - δ := by simp [hre]; ring
    have e2 : (z + 1).im = y := by simp [him]
    rw [e1, abs_of_pos (by linarith)] at a1
    rw [e2] at a2
    have : (1 - δ) * |y| ≤ |y| := by nlinarith [abs_nonneg y]
    nlinarith
  have h2 : (1 + |y|) / 2 ≤ ‖z + 2‖ := by
    have a1 := abs_re_le_norm (z + 2)
    have a2 := abs_im_le_norm (z + 2)
    have e1 : (z + 2).re = 2 - δ := by simp [hre]; ring
    have e2 : (z + 2).im = y := by simp [him]
    rw [e1, abs_of_pos (by linarith)] at a1
    rw [e2] at a2
    linarith
  have hy : 0 < (1 + |y|) / 2 := by positivity
  have hy' : 0 < (1 - δ) * (1 + |y|) / 2 := by
    have : 0 < 1 - δ := by linarith
    positivity
  unfold WR
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, norm_mul, norm_mul, hn2, Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
  have hden : δ * ((1 - δ) * (1 + |y|) / 2) * ((1 + |y|) / 2) ≤ ‖z‖ * ‖z + 1‖ * ‖z + 2‖ :=
    mul_le_mul (mul_le_mul h0 h1 hy'.le (norm_nonneg _)) h2 hy.le (by positivity)
  have hδ' : 0 < 1 - δ := by linarith
  calc 2 / (‖z‖ * ‖z + 1‖ * ‖z + 2‖) ≤ 2 / (δ * ((1 - δ) * (1 + |y|) / 2) * ((1 + |y|) / 2)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 8 / (δ * (1 - δ)) * ((1 + |y|) ^ 2)⁻¹ := by field_simp; norm_num

/-- **`‖W(x + iY)‖ ≤ 2/|Y|³`** para `|Y| ≥ 1`. -/
theorem norm_WR_hor {x Y : ℝ} (hY : 1 ≤ |Y|) : ‖WR ((x : ℂ) + Y * I)‖ ≤ 2 / |Y| ^ 3 := by
  set z : ℂ := (x : ℂ) + Y * I with hzdef
  have hlow : ∀ b : ℝ, |Y| ≤ ‖z + b‖ := by
    intro b
    have := abs_im_le_norm (z + b)
    have e : (z + b).im = Y := by simp [hzdef]
    rw [e] at this
    exact this
  have h0 : |Y| ≤ ‖z‖ := by simpa using hlow 0
  have h1 : |Y| ≤ ‖z + 1‖ := by simpa using hlow 1
  have h2 : |Y| ≤ ‖z + 2‖ := by simpa using hlow 2
  have hYp : 0 < |Y| := by linarith
  unfold WR
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, norm_mul, norm_mul, hn2]
  have hden : |Y| * |Y| * |Y| ≤ ‖z‖ * ‖z + 1‖ * ‖z + 2‖ :=
    mul_le_mul (mul_le_mul h0 h1 hYp.le (norm_nonneg _)) h2 hYp.le (by positivity)
  calc 2 / (‖z‖ * ‖z + 1‖ * ‖z + 2‖) ≤ 2 / (|Y| * |Y| * |Y|) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 2 / |Y| ^ 3 := by ring

/-! ## 2. O resíduo no retângulo `[−δ, 1] × [−Y, Y]` -/

/-- O integrando `G(z) = W(z) N^z F(s + z)`. -/
noncomputable def Gs (N : ℕ) (s z : ℂ) : ℂ := WR z * (N : ℂ) ^ z * F (s + z)

/-- **`∮ W(z)N^z F(s + z) dz = 2πi F(s)`** em `[−δ, 1] × [−Y, Y]`, sob `SemZeros θ` e `θ + δ < Re s`. -/
theorem bordo_Gs {θ δ Y : ℝ} (hZ : SemZeros θ) (hδ0 : 0 < δ) (hδ1 : δ < 1) {s : ℂ} (hs : θ + δ < s.re)
    (hY : 0 < Y) {N : ℕ} (hN : 1 ≤ N) :
    bordo (Gs N s) ⟨-δ, -Y⟩ ⟨1, Y⟩ = 2 * π * I * F s := by
  set z₀ : ℂ := ⟨-δ, -Y⟩ with hz₀
  set w₀ : ℂ := ⟨1, Y⟩ with hw₀
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set U : Set ℂ := {z : ℂ | -1 < z.re ∧ θ - s.re < z.re} with hUdef
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_re)
  set H : ℂ → ℂ := fun z => 2 * (N : ℂ) ^ z * F (s + z) / ((z + 1) * (z + 2)) with hHdef
  have hHd : DifferentiableOn ℂ H U := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    have hF : DifferentiableAt ℂ (fun z => F (s + z)) z :=
      (differentiableAt_F hZ (by simp; linarith)).comp z (differentiableAt_const _ |>.add differentiableAt_id)
    have hP : DifferentiableAt ℂ (fun z : ℂ => (N : ℂ) ^ z) z := differentiableAt_id.const_cpow (Or.inl hNne)
    have hz1 : z + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    have hz2 : z + 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    exact (((differentiableAt_const _).mul hP).mul hF).div
      ((differentiableAt_id.add_const _).mul (differentiableAt_id.add_const _)) (mul_ne_zero hz1 hz2)
      |>.differentiableWithinAt
  have hRU : Ret z₀ w₀ ⊆ U := by
    intro z hz
    have hr := (mem_reProdIm.mp hz).1
    change z.re ∈ [[-δ, 1]] at hr
    rw [uIcc_of_le (by linarith)] at hr
    exact ⟨by linarith [hr.1], by linarith [hr.1]⟩
  have h0U : (0 : ℂ) ∈ U := ⟨by simp, by simp; linarith⟩
  have hD : DifferentiableOn ℂ (dslope H 0) U := (differentiableOn_dslope (hU.mem_nhds h0U)).mpr hHd
  have hne0 : ∀ z ∈ Bordo z₀ w₀, z ≠ 0 := by
    rintro z ⟨_, h⟩ rfl
    change (0 : ℂ).re = -δ ∨ (0 : ℂ).re = 1 ∨ (0 : ℂ).im = -Y ∨ (0 : ℂ).im = Y at h
    simp only [zero_re, zero_im] at h
    rcases h with h | h | h | h <;> linarith
  have heq : EqOn (Gs N s) (fun z => dslope H 0 z + H 0 * (z - 0)⁻¹) (Bordo z₀ w₀) := by
    intro z hz
    have hz0 := hne0 z hz
    have hzU := hRU hz.1
    have hz1 : z + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith [hzU.1]
    have hz2 : z + 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith [hzU.1]
    show Gs N s z = dslope H 0 z + H 0 * (z - 0)⁻¹
    rw [dslope_of_ne _ hz0, slope_def_field, sub_zero]
    simp only [Gs, WR, hHdef]
    field_simp
    ring
  have hBR : Bordo z₀ w₀ ⊆ Ret z₀ w₀ := fun z hz => hz.1
  have hc1 : ContinuousOn (dslope H 0) (Bordo z₀ w₀) := (hD.mono (hBR.trans hRU)).continuousOn
  have hc2 : ContinuousOn (fun z : ℂ => H 0 * (z - 0)⁻¹) (Bordo z₀ w₀) := fun z hz =>
    (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr (hne0 z hz)))).continuousWithinAt
  rw [bordo_congr heq, bordo_add hc1 hc2, bordo_cauchy (hD.mono hRU), zero_add, bordo_const_mul,
    bordo_inv (by simp [hz₀]; linarith) (by simp [hw₀]) (by simp [hz₀]; linarith) (by simp [hw₀]; linarith)]
  have hH0 : H 0 = F s := by
    simp only [hHdef, cpow_zero, add_zero]
    ring
  rw [hH0]
  ring

/-! ## 3. As retas e o limite `Y → ∞` -/

theorem cont_Gs {θ : ℝ} (hZ : SemZeros θ) {s : ℂ} {a : ℝ} (ha : θ < s.re + a) {N : ℕ} (hN : 1 ≤ N)
    (hW : Continuous (fun y : ℝ => WR ((a : ℂ) + y * I))) :
    Continuous (fun y : ℝ => Gs N s ((a : ℂ) + y * I)) := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hl : Continuous (fun y : ℝ => (a : ℂ) + y * I) := by fun_prop
  have hP : Continuous (fun y : ℝ => (N : ℂ) ^ ((a : ℂ) + y * I)) := hl.const_cpow (Or.inl hNne)
  have hF : Continuous (fun y : ℝ => F (s + ((a : ℂ) + y * I))) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : θ < (s + ((a : ℂ) + y * I)).re := by simp; linarith
    have hc : Continuous (fun y : ℝ => s + ((a : ℂ) + y * I)) := by fun_prop
    exact ContinuousAt.comp (g := F) (f := fun y : ℝ => s + ((a : ℂ) + y * I))
      (differentiableAt_F hZ hre).continuousAt hc.continuousAt
  exact (hW.mul hP).mul hF

/-- A cota de `G` numa reta vertical `Re z = a`, `−δ ≤ a ≤ 1`. -/
theorem norm_Gs_le {θ δ C η : ℝ} {s : ℂ} (hη : 0 ≤ η)
    (hC : ∀ w : ℂ, θ + (s.re - δ - θ) ≤ w.re → ‖F w‖ ≤ C * (1 + |w.im|) ^ η) (hC0 : 0 ≤ C)
    {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : -δ ≤ a) (y : ℝ) :
    ‖Gs N s ((a : ℂ) + y * I)‖ ≤
      ‖WR ((a : ℂ) + y * I)‖ * ((N : ℝ) ^ a * (C * (1 + |s.im|) ^ η * (1 + |y|) ^ η)) := by
  have hN0 : 0 < N := hN
  unfold Gs
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hN0, mul_assoc]
  have hre : ((a : ℂ) + y * I).re = a := by simp
  rw [hre]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hw := hC (s + ((a : ℂ) + y * I)) (by simp; linarith)
  have him : (s + ((a : ℂ) + y * I)).im = s.im + y := by simp
  rw [him] at hw
  calc ‖F (s + ((a : ℂ) + y * I))‖ ≤ C * (1 + |s.im + y|) ^ η := hw
    _ ≤ C * ((1 + |s.im|) ^ η * (1 + |y|) ^ η) := mul_le_mul_of_nonneg_left (um_add_le _ _ hη) hC0
    _ = C * (1 + |s.im|) ^ η * (1 + |y|) ^ η := by ring

theorem integrable_Gs {θ δ C η B : ℝ} {s : ℂ} (hZ : SemZeros θ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hC : ∀ w : ℂ, θ + (s.re - δ - θ) ≤ w.re → ‖F w‖ ≤ C * (1 + |w.im|) ^ η) (hC0 : 0 ≤ C)
    {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : -δ ≤ a) (ha' : θ < s.re + a)
    (hW : ∀ y : ℝ, ‖WR ((a : ℂ) + y * I)‖ ≤ B * (1 + ‖y‖) ^ (-2 : ℝ))
    (hWc : Continuous (fun y : ℝ => WR ((a : ℂ) + y * I))) :
    Integrable (fun y : ℝ => Gs N s ((a : ℂ) + y * I)) := by
  have hI : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 - η))) :=
    integrable_one_add_norm (by simp; linarith)
  refine Integrable.mono' (hI.const_mul (B * ((N : ℝ) ^ a * (C * (1 + |s.im|) ^ η))))
    (cont_Gs hZ ha' hN hWc).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have h1 := norm_Gs_le hη0 hC hC0 hN ha y
  have h2 := hW y
  have hpos : 0 ≤ (N : ℝ) ^ a * (C * (1 + |s.im|) ^ η * (1 + |y|) ^ η) := by positivity
  have hy : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have hpow : (1 + ‖y‖) ^ (-2 : ℝ) * (1 + |y|) ^ η = (1 + ‖y‖) ^ (-(2 - η)) := by
    rw [Real.norm_eq_abs] at hy ⊢
    rw [← Real.rpow_add hy]
    ring_nf
  calc ‖Gs N s ((a : ℂ) + y * I)‖
      ≤ ‖WR ((a : ℂ) + y * I)‖ * ((N : ℝ) ^ a * (C * (1 + |s.im|) ^ η * (1 + |y|) ^ η)) := h1
    _ ≤ B * (1 + ‖y‖) ^ (-2 : ℝ) * ((N : ℝ) ^ a * (C * (1 + |s.im|) ^ η * (1 + |y|) ^ η)) :=
        mul_le_mul_of_nonneg_right h2 hpos
    _ = B * ((N : ℝ) ^ a * (C * (1 + |s.im|) ^ η)) * ((1 + ‖y‖) ^ (-2 : ℝ) * (1 + |y|) ^ η) := by ring
    _ = B * ((N : ℝ) ^ a * (C * (1 + |s.im|) ^ η)) * (1 + ‖y‖) ^ (-(2 - η)) := by rw [hpow]

/-- **O deslocamento**: `A_N(s) = F(s) + (1/2π) ∫ W(−δ + iy) N^{−δ+iy} F(s − δ + iy) dy`. -/
theorem desloc {θ δ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {s : ℂ} (hs : θ + δ < s.re) (hs1 : s.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    LSeries (aN N) s = F s + (1 / (2 * π)) • ∫ y : ℝ, Gs N s (((-δ : ℝ) : ℂ) + y * I) := by
  have hN0 : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨C, hC0, hC⟩ := norm_F_le hZ hθ hθ1 (δ := s.re - δ - θ) (η := 1 / 2) (by linarith) (by linarith)
    (by norm_num)
  -- as retas
  have hI1 : Integrable (fun y : ℝ => Gs N s (((1 : ℝ) : ℂ) + y * I)) :=
    integrable_Gs hZ (by norm_num) (by norm_num) hC hC0.le hN (by linarith) (by linarith)
      (fun y => by simpa using ATK.ZeroClasses.BDEspectral.norm_WR_le (c := 1) one_pos y)
      (ATK.ZeroClasses.BDEspectral.WR_cont one_pos)
  have hIm : Integrable (fun y : ℝ => Gs N s (((-δ : ℝ) : ℂ) + y * I)) :=
    integrable_Gs hZ (by norm_num) (by norm_num) hC hC0.le hN le_rfl (by linarith)
      (norm_WR_esq hδ0 hδ1) (WR_cont' (by linarith) (by linarith) (by linarith))
  set V₁ := ∫ y : ℝ, Gs N s (((1 : ℝ) : ℂ) + y * I) with hV₁
  set Vm := ∫ y : ℝ, Gs N s (((-δ : ℝ) : ℂ) + y * I) with hVm
  have hl1 : Tendsto (fun Y : ℝ => ∫ y in (-Y)..Y, Gs N s (((1 : ℝ) : ℂ) + y * I)) atTop (𝓝 V₁) :=
    intervalIntegral_tendsto_integral hI1 tendsto_neg_atTop_atBot tendsto_id
  have hlm : Tendsto (fun Y : ℝ => ∫ y in (-Y)..Y, Gs N s (((-δ : ℝ) : ℂ) + y * I)) atTop (𝓝 Vm) :=
    intervalIntegral_tendsto_integral hIm tendsto_neg_atTop_atBot tendsto_id
  -- as horizontais
  set K₀ : ℝ := (1 + δ) * (4 * N * (C * (1 + |s.im|) ^ (1 / 2 : ℝ))) with hK₀
  have hhor : ∀ Y : ℝ, 1 ≤ Y → ∀ τ : ℝ, |τ| = Y →
      ‖∫ x in (-δ)..1, Gs N s ((x : ℂ) + τ * I)‖ ≤ K₀ / Y ^ 2 := by
    intro Y hY τ hτ
    have hb : ∀ x ∈ Ι (-δ) 1, ‖Gs N s ((x : ℂ) + τ * I)‖ ≤ 4 * N * (C * (1 + |s.im|) ^ (1 / 2 : ℝ)) / Y ^ 2 := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hYp : 0 < Y := by linarith
      have hW := norm_WR_hor (x := x) (Y := τ) (by rw [hτ]; exact hY)
      rw [hτ] at hW
      unfold Gs
      rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hN0]
      have hre : ((x : ℂ) + τ * I).re = x := by simp
      rw [hre]
      have hF := hC (s + ((x : ℂ) + τ * I)) (by simp; linarith [hx.1])
      have him : (s + ((x : ℂ) + τ * I)).im = s.im + τ := by simp
      rw [him] at hF
      have hF2 : ‖F (s + ((x : ℂ) + τ * I))‖ ≤ C * (1 + |s.im|) ^ (1 / 2 : ℝ) * (2 * Y) := by
        have h1 := um_add_le s.im τ (η := 1 / 2) (by norm_num)
        have h2 : (1 + |τ|) ^ (1 / 2 : ℝ) ≤ 2 * Y := by
          rw [hτ]
          calc (1 + Y) ^ (1 / 2 : ℝ) ≤ (1 + Y) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ ≤ 2 * Y := by rw [Real.rpow_one]; linarith
        calc ‖F (s + ((x : ℂ) + τ * I))‖ ≤ C * (1 + |s.im + τ|) ^ (1 / 2 : ℝ) := hF
          _ ≤ C * ((1 + |s.im|) ^ (1 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left h1 hC0.le
          _ ≤ C * ((1 + |s.im|) ^ (1 / 2 : ℝ) * (2 * Y)) := by gcongr
          _ = C * (1 + |s.im|) ^ (1 / 2 : ℝ) * (2 * Y) := by ring
      have hNx : (N : ℝ) ^ x ≤ N := by
        calc (N : ℝ) ^ x ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hx.2
          _ = N := Real.rpow_one _
      have hA : 0 ≤ C * (1 + |s.im|) ^ (1 / 2 : ℝ) := by positivity
      calc ‖WR ((x : ℂ) + τ * I)‖ * (N : ℝ) ^ x * ‖F (s + ((x : ℂ) + τ * I))‖
          ≤ 2 / Y ^ 3 * N * (C * (1 + |s.im|) ^ (1 / 2 : ℝ) * (2 * Y)) := by
            apply mul_le_mul (mul_le_mul hW hNx (by positivity) (by positivity)) hF2 (norm_nonneg _)
              (by positivity)
        _ = 4 * N * (C * (1 + |s.im|) ^ (1 / 2 : ℝ)) / Y ^ 2 := by
            field_simp
            ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [show (1 : ℝ) - -δ = 1 + δ by ring, abs_of_pos (show (0 : ℝ) < 1 + δ by linarith)] at h
    calc ‖∫ x in (-δ)..1, Gs N s ((x : ℂ) + τ * I)‖
        ≤ 4 * N * (C * (1 + |s.im|) ^ (1 / 2 : ℝ)) / Y ^ 2 * (1 + δ) := h
      _ = K₀ / Y ^ 2 := by rw [hK₀]; ring
  have hK : Tendsto (fun Y : ℝ => K₀ / Y ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have hBh : Tendsto (fun Y : ℝ => ∫ x in (-δ)..1, Gs N s ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [eventually_ge_atTop 1] with Y hY
    exact hhor Y hY (-Y) (by rw [abs_neg, abs_of_pos (by linarith)])
  have hTp : Tendsto (fun Y : ℝ => ∫ x in (-δ)..1, Gs N s ((x : ℂ) + (Y : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [eventually_ge_atTop 1] with Y hY
    exact hhor Y hY Y (abs_of_pos (by linarith))
  -- o bordo
  have hunf : ∀ Y : ℝ, bordo (Gs N s) ⟨-δ, -Y⟩ ⟨1, Y⟩ =
      (∫ x in (-δ)..1, Gs N s ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)) -
        (∫ x in (-δ)..1, Gs N s ((x : ℂ) + (Y : ℂ) * I)) +
        I • (∫ y in (-Y)..Y, Gs N s (((1 : ℝ) : ℂ) + y * I)) -
        I • (∫ y in (-Y)..Y, Gs N s (((-δ : ℝ) : ℂ) + y * I)) := fun Y => rfl
  have hT1 : Tendsto (fun Y : ℝ => bordo (Gs N s) ⟨-δ, -Y⟩ ⟨1, Y⟩) atTop
      (𝓝 (0 - 0 + I • V₁ - I • Vm)) := by
    simp_rw [hunf]
    exact ((hBh.sub hTp).add (hl1.const_smul I)).sub (hlm.const_smul I)
  have hT2 : Tendsto (fun Y : ℝ => bordo (Gs N s) ⟨-δ, -Y⟩ ⟨1, Y⟩) atTop (𝓝 (2 * π * I * F s)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Y hY
    exact (bordo_Gs hZ hδ0 hδ1 hs hY hN).symm
  have hEq := tendsto_nhds_unique hT1 hT2
  simp only [sub_zero, zero_add, smul_eq_mul] at hEq
  have hV : V₁ = 2 * π * F s + Vm := by
    have h2 : I * (V₁ - Vm - 2 * π * F s) = 0 := by linear_combination hEq
    have h3 := (mul_eq_zero.mp h2).resolve_left I_ne_zero
    linear_combination h3
  have hA := LSeries_aN_int hN (s := s) (c := 1) one_pos (by linarith)
  have hA' : LSeries (aN N) s = (1 / (2 * π)) • V₁ := hA
  rw [hA', hV, Complex.real_smul, Complex.real_smul]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- **`|A_N(σ + iτ) − 1/ζ(σ + iτ)| ≤ K N^{−δ}(1 + |τ|)^η`**, uniforme em `N ≥ 1` e `τ`. -/
theorem molif_cota {θ σ δ η : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hσ : θ + δ < σ) (hσ1 : σ < 1) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ τ : ℝ,
      ‖LSeries (aN N) ((σ : ℂ) + τ * I) - F ((σ : ℂ) + τ * I)‖ ≤ K * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ η := by
  obtain ⟨C, hC0, hC⟩ := norm_F_le hZ hθ hθ1 (δ := σ - δ - θ) (η := η) (by linarith) (by linarith) hη0
  set I₀ : ℝ := ∫ y : ℝ, (1 + ‖y‖) ^ (-(2 - η)) with hI₀
  have hI : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 - η))) :=
    integrable_one_add_norm (by simp; linarith)
  have hI0 : 0 ≤ I₀ := integral_nonneg fun y => by positivity
  have hδ' : 0 < 1 - δ := by linarith
  refine ⟨(1 / (2 * π)) * (8 / (δ * (1 - δ))) * C * I₀, by positivity, fun N hN τ => ?_⟩
  set s : ℂ := (σ : ℂ) + τ * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = τ := by simp [hsdef]
  have hC' : ∀ w : ℂ, θ + (s.re - δ - θ) ≤ w.re → ‖F w‖ ≤ C * (1 + |w.im|) ^ η := by
    rw [hsre]; exact hC
  rw [desloc hZ hθ hθ1 hδ0 hδ1 (by rw [hsre]; exact hσ) (by rw [hsre]; exact hσ1) hN, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hb : ∀ y : ℝ, ‖Gs N s (((-δ : ℝ) : ℂ) + y * I)‖ ≤
      (8 / (δ * (1 - δ)) * ((N : ℝ) ^ (-δ) * (C * (1 + |τ|) ^ η))) * (1 + ‖y‖) ^ (-(2 - η)) := by
    intro y
    have h1 := norm_Gs_le hη0.le hC' hC0.le hN le_rfl y
    rw [hsim] at h1
    have h2 := norm_WR_esq hδ0 hδ1 y
    have hpos : 0 ≤ (N : ℝ) ^ (-δ) * (C * (1 + |τ|) ^ η * (1 + |y|) ^ η) := by positivity
    have hy : (0 : ℝ) < 1 + |y| := by positivity
    have hpow : (1 + ‖y‖) ^ (-2 : ℝ) * (1 + |y|) ^ η = (1 + ‖y‖) ^ (-(2 - η)) := by
      rw [Real.norm_eq_abs, ← Real.rpow_add hy]
      ring_nf
    calc ‖Gs N s (((-δ : ℝ) : ℂ) + y * I)‖
        ≤ ‖WR (((-δ : ℝ) : ℂ) + y * I)‖ * ((N : ℝ) ^ (-δ) * (C * (1 + |τ|) ^ η * (1 + |y|) ^ η)) := h1
      _ ≤ 8 / (δ * (1 - δ)) * (1 + ‖y‖) ^ (-2 : ℝ) *
            ((N : ℝ) ^ (-δ) * (C * (1 + |τ|) ^ η * (1 + |y|) ^ η)) := mul_le_mul_of_nonneg_right h2 hpos
      _ = (8 / (δ * (1 - δ)) * ((N : ℝ) ^ (-δ) * (C * (1 + |τ|) ^ η))) *
            ((1 + ‖y‖) ^ (-2 : ℝ) * (1 + |y|) ^ η) := by ring
      _ = (8 / (δ * (1 - δ)) * ((N : ℝ) ^ (-δ) * (C * (1 + |τ|) ^ η))) * (1 + ‖y‖) ^ (-(2 - η)) := by
          rw [hpow]
  have hint := norm_integral_le_of_norm_le (hI.const_mul _) (ae_of_all _ hb)
  rw [integral_const_mul, ← hI₀] at hint
  calc 1 / (2 * π) * ‖∫ y : ℝ, Gs N s (((-δ : ℝ) : ℂ) + y * I)‖
      ≤ 1 / (2 * π) * ((8 / (δ * (1 - δ)) * ((N : ℝ) ^ (-δ) * (C * (1 + |τ|) ^ η))) * I₀) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 1 / (2 * π) * (8 / (δ * (1 - δ))) * C * I₀ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ η := by ring

end ATK.ZeroClasses.BDDesloc

#print axioms ATK.ZeroClasses.BDDesloc.um_add_le
#print axioms ATK.ZeroClasses.BDDesloc.WR_cont'
#print axioms ATK.ZeroClasses.BDDesloc.norm_WR_esq
#print axioms ATK.ZeroClasses.BDDesloc.norm_WR_hor
#print axioms ATK.ZeroClasses.BDDesloc.bordo_Gs
#print axioms ATK.ZeroClasses.BDDesloc.cont_Gs
#print axioms ATK.ZeroClasses.BDDesloc.norm_Gs_le
#print axioms ATK.ZeroClasses.BDDesloc.integrable_Gs
#print axioms ATK.ZeroClasses.BDDesloc.desloc
#print axioms ATK.ZeroClasses.BDDesloc.molif_cota
