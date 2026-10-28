import ATK.ZeroClasses.VariacaoArg

/-!
# Riemann–von Mangoldt (rodada 42)

**Teorema** (`riemannVonMangoldt : ATK.FechamentoO1.RiemannVonMangoldt`). Existe `C` tal que, para todo `T ≥ 2`,

  `|N(T) − ((T/2π) log(T/2π) − T/2π)| ≤ C log T`,

com `N(T)` o número de zeros não triviais de `ζ` com `0 < Im ρ ≤ T`, contados com multiplicidade. A Mathlib não
tem a fórmula. A prova junta as três rodadas anteriores:

1. **o princípio do argumento** (rodada 40) para `ξ` no retângulo `[−1, 2] × [1, T]`. A altura `1` está abaixo do
   primeiro zero (rodada 29), e `T` não pode ser ordenada de zero. A conta dá `2πi N(T) = ∮ ξ′/ξ`
   (`bordo_eq_N`);
2. **as simetrias** `ξ′/ξ(1 − s) = −ξ′/ξ(s)` e `ξ′/ξ(s̄) = conj ξ′/ξ(s)` (`g_one_sub`, `g_conj`) dobram o contorno
   sobre a metade direita (`lado_horizontal`, `lado_esquerdo`): `πN(T) = Im K₁ − Im K_T + Re R_T` (`identidade`);
3. **as primitivas** `E(s) = log s + log(s − 1) − (s/2) log π + log Γ(s/2)` (Stirling, rodada 39) e
   `Λ = E + log ζ` em `Re s = 2` (`hasDerivAt_E`, `hasDerivAt_Λ`) dão
   `πN(T) = Im E(½ + iT) + arg ζ(2 + iT) − Im ∫_{1/2}^{2} ζ′/ζ + C₁` (`formula_N`);
4. **as estimativas**: `Im E(½ + iT) = (T/2) log(T/2π) − T/2 + 7π/8 + O(1/T)` (`im_ell_quarto`),
   `|arg ζ(2 + iT)| ≤ π/2` e `|Im ∫ ζ′/ζ| = O(log T)` (`variacao_log`, rodada 41) dão `rvm_nao_ordenada`; para
   `T` ordenada, a monotonia de `N` entre duas alturas vizinhas que não são ordenadas dá `riemannVonMangoldt`.

Com isso, `NecessidadeRH` reduz-se à dedução de Báez-Duarte (`necessidade_iff_deducao`).

Classificação (rodada 42): **alavanca** — fecha `RiemannVonMangoldt`, que estava BUILD_PENDING. `CrescimentoN`
(zeros *distintos*, B10) não segue daqui sem uma cota de multiplicidade melhor que `O(log T)` e segue
BUILD_PENDING. RH continua OPEN_MATH.
-/

open Complex ComplexConjugate Set Filter Topology Metric
open scoped Real Interval

namespace ATK.ZeroClasses.RvM

open ATK.BaseRiemannXi (riemannXi differentiable_riemannXi riemannXi_one_sub riemannXi_conj)
open ATK.ZeroClasses.ArgRetangulo (bordo Ret Bordo principio_argumento)
open ATK.ZeroClasses.StirlingComplexo (ell hasDerivAt_ell im_ell_quarto ell_diff)

/-- `g = ξ′/ξ`. -/
noncomputable abbrev g : ℂ → ℂ := logDeriv riemannXi

/-! ## 1. As simetrias de `ξ′/ξ` -/

theorem deriv_xi_one_sub (s : ℂ) : deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have h1 : HasDerivAt (fun s => riemannXi (1 - s)) (deriv riemannXi (1 - s) * (-1)) s :=
    (differentiable_riemannXi (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
  have h2 : (fun s => riemannXi (1 - s)) = riemannXi := funext riemannXi_one_sub
  rw [h2] at h1
  rw [h1.deriv]
  ring

theorem deriv_xi_conj (s : ℂ) : deriv riemannXi (conj s) = conj (deriv riemannXi s) := by
  have h1 := ((differentiable_riemannXi (conj s)).hasDerivAt).conj_conj
  have h2 : (conj ∘ riemannXi ∘ conj : ℂ → ℂ) = riemannXi := by
    funext x
    simp [riemannXi_conj]
  rw [h2, Complex.conj_conj] at h1
  rw [h1.deriv, Complex.conj_conj]

theorem g_one_sub (s : ℂ) : g (1 - s) = -g s := by
  simp only [g, logDeriv_apply, deriv_xi_one_sub, riemannXi_one_sub, neg_div]

theorem g_conj (s : ℂ) : g (conj s) = conj (g s) := by
  simp only [g, logDeriv_apply, deriv_xi_conj, riemannXi_conj, map_div₀]

theorem integral_conj' {a b : ℝ} (f : ℝ → ℂ) :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-! ## 2. Onde `ξ` não se anula -/

theorem xi_ne_zero_fora {s : ℂ} (h : s.re ≤ 0 ∨ 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases h with h | h
  · exact ATK.BaseRiemannXi.riemannXi_ne_zero_of_re_le_zero h
  · exact ATK.BaseRiemannXi.riemannXi_ne_zero_of_one_le_re h

theorem xi_ne_zero_baixo {s : ℂ} (h : |s.im| ≤ 13) : riemannXi s ≠ 0 := by
  intro hx
  obtain ⟨h0, h1⟩ := ATK.BaseRiemannXi.riemannXi_zero_mem_strip hx
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at h1
  exact ATK.ZeroClasses.Faixa.faixa_sem_zeros h0 h1 h
    ((ATK.BaseRiemannXi.riemannXi_eq_zero_iff h0 hs1).mp hx)

/-- `T` não é ordenada de zero no segmento `[½, 2] + iT`. -/
def NaoOrdenada (T : ℝ) : Prop := ∀ σ ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0

/-- Se `T` não é ordenada, `ξ ≠ 0` em toda a reta `Im s = T`. -/
theorem xi_ne_zero_topo {T : ℝ} (hT : 0 < T) (hno : NaoOrdenada T) (x : ℝ) :
    riemannXi (x + T * I) ≠ 0 := by
  intro hx
  obtain ⟨h0, h1⟩ := ATK.BaseRiemannXi.riemannXi_zero_mem_strip hx
  have hre : ((x : ℂ) + T * I).re = x := by simp
  rw [hre] at h0 h1
  have hs1 : ∀ y : ℝ, (y : ℂ) + T * I ≠ 1 := fun y h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  rcases le_or_gt (1 / 2) x with hx2 | hx2
  · exact hno x ⟨hx2, by linarith⟩
      ((ATK.BaseRiemannXi.riemannXi_eq_zero_iff (by rw [hre]; exact h0) (hs1 x)).mp hx)
  · have e : riemannXi ((1 - x : ℝ) + T * I) = conj (riemannXi (x + T * I)) := by
      rw [← riemannXi_conj, ← riemannXi_one_sub]
      congr 1
      apply Complex.ext <;> simp
    have hx' : riemannXi ((1 - x : ℝ) + T * I) = 0 := by rw [e, hx, map_zero]
    have hre' : (((1 - x : ℝ) : ℂ) + T * I).re = 1 - x := by simp
    exact hno (1 - x) ⟨by linarith, by linarith⟩
      ((ATK.BaseRiemannXi.riemannXi_eq_zero_iff (by rw [hre']; linarith) (hs1 _)).mp hx')

theorem continuousAt_g {s : ℂ} (h : riemannXi s ≠ 0) : ContinuousAt g s := by
  have ha : AnalyticAt ℂ riemannXi s := differentiable_riemannXi.analyticAt s
  exact ha.deriv.continuousAt.div ha.continuousAt h

theorem integrable_horizontal {T a b : ℝ} (h : ∀ x : ℝ, riemannXi (x + T * I) ≠ 0) :
    IntervalIntegrable (fun x : ℝ => g (x + T * I)) MeasureTheory.volume a b := by
  have hc : Continuous fun x : ℝ => g (x + T * I) := continuous_iff_continuousAt.mpr fun x =>
    (continuousAt_g (h x)).comp (f := fun x : ℝ => (x : ℂ) + T * I) (by fun_prop)
  exact hc.intervalIntegrable a b

theorem integrable_vertical {c a b : ℝ} (h : ∀ y : ℝ, riemannXi (c + y * I) ≠ 0) :
    IntervalIntegrable (fun y : ℝ => g (c + y * I)) MeasureTheory.volume a b := by
  have hc : Continuous fun y : ℝ => g (c + y * I) := continuous_iff_continuousAt.mpr fun y =>
    (continuousAt_g (h y)).comp (f := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop)
  exact hc.intervalIntegrable a b

/-! ## 3. Dobrando o contorno -/

/-- **O lado horizontal** `[−1, 2] + iT` é `K − K̄`, `K = ∫_{1/2}^{2} ξ′/ξ(x + iT) dx`. -/
theorem lado_horizontal {T : ℝ} (h : ∀ x : ℝ, riemannXi (x + T * I) ≠ 0) :
    ∫ x in (-1 : ℝ)..2, g (x + T * I) =
      (∫ x in (1 / 2 : ℝ)..2, g (x + T * I)) - conj (∫ x in (1 / 2 : ℝ)..2, g (x + T * I)) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (integrable_horizontal h)
    (integrable_horizontal h)]
  have hsym : ∀ x : ℝ, g (x + T * I) = -conj (g (((1 - x : ℝ) : ℂ) + T * I)) := by
    intro x
    have e : (x : ℂ) + T * I = 1 - conj (((1 - x : ℝ) : ℂ) + T * I) := by
      apply Complex.ext <;> simp
    rw [e, g_one_sub, g_conj]
  have h1 : ∫ x in (-1 : ℝ)..(1 / 2), g (x + T * I) =
      ∫ x in (-1 : ℝ)..(1 / 2), -conj (g (((1 - x : ℝ) : ℂ) + T * I)) :=
    intervalIntegral.integral_congr fun x _ => hsym x
  have h2 : ∫ x in (-1 : ℝ)..(1 / 2), g (((1 - x : ℝ) : ℂ) + T * I) =
      ∫ x in (1 / 2 : ℝ)..2, g (x + T * I) := by
    have := intervalIntegral.integral_comp_sub_left (fun u : ℝ => g (u + T * I)) (a := -1) (b := 1 / 2) 1
    norm_num at this
    push_cast
    exact this
  rw [h1, intervalIntegral.integral_neg, integral_conj', h2]
  ring

/-- **O lado esquerdo** é `−conj` do direito. -/
theorem lado_esquerdo {T : ℝ} :
    ∫ y in (1 : ℝ)..T, g (((-1 : ℝ) : ℂ) + y * I) = -conj (∫ y in (1 : ℝ)..T, g ((2 : ℝ) + y * I)) := by
  have hsym : ∀ y : ℝ, g (((-1 : ℝ) : ℂ) + y * I) = -conj (g ((2 : ℝ) + y * I)) := by
    intro y
    have e : ((-1 : ℝ) : ℂ) + y * I = 1 - conj (((2 : ℝ) : ℂ) + y * I) := by
      apply Complex.ext <;> simp <;> norm_num
    rw [e, g_one_sub, g_conj]
  rw [intervalIntegral.integral_congr fun y _ => hsym y, intervalIntegral.integral_neg, integral_conj']

/-- **O princípio do argumento para `ξ`**: `∮ ξ′/ξ = 2πi N(T)` no retângulo `[−1, 2] × [1, T]`. -/
theorem bordo_eq_N {T : ℝ} (hT : 4 ≤ T) (hno : NaoOrdenada T) :
    bordo g ⟨-1, 1⟩ ⟨2, T⟩ = 2 * π * I * (ATK.FechamentoO1.N T : ℂ) := by
  classical
  have hf : AnalyticOnNhd ℂ riemannXi univ := fun s _ => differentiable_riemannXi.analyticAt s
  have hξ2 : riemannXi 2 ≠ 0 := xi_ne_zero_fora (Or.inr (by norm_num))
  have hzr : (⟨-1, 1⟩ : ℂ).re = -1 := rfl
  have hzi : (⟨-1, 1⟩ : ℂ).im = 1 := rfl
  have hwr : (⟨2, T⟩ : ℂ).re = 2 := rfl
  have hwi : (⟨2, T⟩ : ℂ).im = T := rfl
  have hbd : ∀ p ∈ Bordo ⟨-1, 1⟩ ⟨2, T⟩, riemannXi p ≠ 0 := by
    rintro p ⟨_, hc⟩
    rw [hzr, hwr, hzi, hwi] at hc
    rcases hc with h | h | h | h
    · exact xi_ne_zero_fora (Or.inl (by rw [h]; norm_num))
    · exact xi_ne_zero_fora (Or.inr (by rw [h]; norm_num))
    · exact xi_ne_zero_baixo (by rw [h]; norm_num)
    · have e : p = (p.re : ℂ) + T * I := by
        apply Complex.ext <;> simp [h]
      rw [e]
      exact xi_ne_zero_topo (by linarith) hno p.re
  obtain ⟨S, hS, hbord⟩ := principio_argumento isOpen_univ hf (z := ⟨-1, 1⟩) (w := ⟨2, T⟩)
    (by rw [hzr, hwr]; norm_num) (by rw [hzi, hwi]; linarith) (subset_univ _)
    (fun p _ => ATK.ArgPrincipio.ordem_finita hf isPreconnected_univ (mem_univ 2) hξ2 (mem_univ p)) hbd
  rw [hbord]
  congr 1
  unfold ATK.FechamentoO1.N
  push_cast
  have hne1 : ∀ u : ℂ, 0 < u.re → u.re < 1 → u ≠ 1 := fun u _ h1 h => by
    rw [h, one_re] at h1
    exact lt_irrefl 1 h1
  have hSeq : S = (ATK.FechamentoO1.zerosAte_finito T).toFinset := by
    ext u
    rw [hS, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hu, hξu⟩
      obtain ⟨h0, h1⟩ := ATK.BaseRiemannXi.riemannXi_zero_mem_strip hξu
      have hz := (ATK.BaseRiemannXi.riemannXi_eq_zero_iff h0 (hne1 u h0 h1)).mp hξu
      have him := (mem_reProdIm.mp hu).2
      rw [hzi, hwi, uIcc_of_le (by linarith : (1 : ℝ) ≤ T)] at him
      exact ⟨⟨hz, h0, h1⟩, by linarith [him.1], him.2⟩
    · rintro ⟨hZ, hpos, hle⟩
      have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 u hZ
      rw [abs_of_pos hpos] at h13
      refine ⟨mem_reProdIm.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [hzr, hwr, uIcc_of_le (by norm_num)]
        exact ⟨by linarith [hZ.2.1], by linarith [hZ.2.2]⟩
      · rw [hzi, hwi, uIcc_of_le (by linarith)]
        exact ⟨by linarith, hle⟩
      · exact (ATK.BaseRiemannXi.riemannXi_eq_zero_iff hZ.2.1 (hne1 u hZ.2.1 hZ.2.2)).mpr hZ.1
  rw [hSeq]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' := (Set.Finite.mem_toFinset _).mp hu
  rw [ATK.ZeroClasses.Jensen.ordemNat_zeta_eq_xi hu'.1.2.1 (hne1 u hu'.1.2.1 hu'.1.2.2)]

/-- **A identidade**: `πN(T) = Im K₁ − Im K_T + Re R_T`. -/
theorem identidade {T : ℝ} (hT : 4 ≤ T) (hno : NaoOrdenada T) :
    π * (ATK.FechamentoO1.N T : ℝ) = (∫ x in (1 / 2 : ℝ)..2, g (x + (1 : ℝ) * I)).im -
      (∫ x in (1 / 2 : ℝ)..2, g (x + T * I)).im + (∫ y in (1 : ℝ)..T, g ((2 : ℝ) + y * I)).re := by
  have hb := bordo_eq_N hT hno
  have e : bordo g ⟨-1, 1⟩ ⟨2, T⟩ = (∫ x in (-1 : ℝ)..2, g (x + (1 : ℝ) * I)) -
      (∫ x in (-1 : ℝ)..2, g (x + T * I)) + I * (∫ y in (1 : ℝ)..T, g ((2 : ℝ) + y * I)) -
      I * ∫ y in (1 : ℝ)..T, g (((-1 : ℝ) : ℂ) + y * I) := rfl
  rw [e, lado_horizontal (T := 1) (fun x => xi_ne_zero_baixo (by simp)),
    lado_horizontal (fun x => xi_ne_zero_topo (by linarith) hno x), lado_esquerdo] at hb
  have him := congrArg Complex.im hb
  simp only [sub_im, add_im, mul_im, mul_re, conj_im, conj_re, neg_im, neg_re, I_re, I_im, zero_mul,
    one_mul, zero_add, sub_zero, ofReal_re, ofReal_im, mul_zero, natCast_re, natCast_im,
    re_ofNat, im_ofNat, mul_one, add_zero] at him
  linarith

/-! ## 4. As primitivas -/

/-- `E(s) = log s + log(s − 1) − (s/2) log π + log Γ(s/2)`. -/
noncomputable def E (s : ℂ) : ℂ := log s + log (s - 1) - (Real.log π / 2 : ℂ) * s + ell (s / 2)

/-- `E′(s) = 1/s + 1/(s − 1) − ½ log π + ½ ψ(s/2)`. -/
noncomputable def E' (s : ℂ) : ℂ := 1 / s + 1 / (s - 1) - (Real.log π : ℂ) / 2 + digamma (s / 2) / 2

/-- `Λ = E + log ζ`. -/
noncomputable def Λ (s : ℂ) : ℂ := E s + log (riemannZeta s)

theorem hasDerivAt_E {s : ℂ} (h0 : s ∈ slitPlane) (h1 : s - 1 ∈ slitPlane) (hre : 0 < s.re) :
    HasDerivAt E (E' s) s := by
  have a := Complex.hasDerivAt_log h0
  have b := ((hasDerivAt_id s).sub_const 1).clog h1
  have c := (hasDerivAt_id s).const_mul ((Real.log π / 2 : ℂ))
  have hre2 : 0 < (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  have d := (hasDerivAt_ell hre2).comp s ((hasDerivAt_id s).div_const 2)
  have := ((a.add b).sub c).add d
  convert this using 1
  · funext x
    simp [E]
  · simp only [E', id]
    ring

theorem E'_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    g s = E' s + logDeriv riemannZeta s := by
  have := ATK.XiAnalitica.logDeriv_xiE hre hs1 hz
  rw [ATK.XiAnalitica.xiE_eq_riemannXi] at this
  rw [g, this, E']

theorem hasDerivAt_Λ {s : ℂ} (hre : 2 ≤ s.re) : HasDerivAt Λ (g s) s := by
  have hpos : 0 < s.re := by linarith
  have h0 : s ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hpos)
  have h1 : s - 1 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by rw [sub_re, one_re]; linarith))
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hre
  have hzr := ATK.ZeroClasses.VariacaoArg.re_zeta_dois hre
  have hb := ATK.BLProva.dois_menos_pos
  have hz0 : riemannZeta s ≠ 0 := by
    intro h
    rw [h, zero_re] at hzr
    linarith
  have hzs : riemannZeta s ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have e := (differentiableAt_riemannZeta hs1).hasDerivAt.clog hzs
  have := (hasDerivAt_E h0 h1 hpos).add e
  rw [E'_eq hpos hs1 hz0, logDeriv_apply]
  exact this

/-- **O lado direito**: `i ∫_1^T ξ′/ξ(2 + iy) dy = Λ(2 + iT) − Λ(2 + i)`. -/
theorem lado_direito (T : ℝ) :
    I * ∫ y in (1 : ℝ)..T, g ((2 : ℝ) + y * I) = Λ ((2 : ℝ) + T * I) - Λ ((2 : ℝ) + (1 : ℝ) * I) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Λ ((2 : ℝ) + y * I))
    (f' := fun y : ℝ => I * g ((2 : ℝ) + y * I))
  · intro y _
    have hre : 2 ≤ (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h1 := hasDerivAt_Λ hre
    have h2 : HasDerivAt (fun w : ℂ => ((2 : ℝ) : ℂ) + w * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add ((2 : ℝ) : ℂ)
    have h3 := (h1.comp (y : ℂ) h2).comp_ofReal
    exact h3.congr_deriv (mul_comm _ _)
  · have hc : Continuous fun y : ℝ => g ((2 : ℝ) + y * I) := continuous_iff_continuousAt.mpr fun y =>
      (continuousAt_g (xi_ne_zero_fora (Or.inr (by simp)))).comp
        (f := fun y : ℝ => ((2 : ℝ) : ℂ) + y * I) (by fun_prop)
    exact (continuous_const.mul hc).intervalIntegrable _ _

theorem continuousAt_digamma {z : ℂ} (hz : 0 < z.re) : ContinuousAt digamma z := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hd := (ell_diff.deriv hU).continuousOn.continuousAt (hU.mem_nhds hz)
  refine hd.congr ?_
  filter_upwards [hU.mem_nhds hz] with w hw
  exact (hasDerivAt_ell hw).deriv

/-- **O topo**: `∫_{1/2}^{2} ξ′/ξ(x + iT) dx = E(2 + iT) − E(½ + iT) + ∫_{1/2}^{2} ζ′/ζ(x + iT) dx`. -/
theorem topo {T : ℝ} (hT : 4 ≤ T) (hno : NaoOrdenada T) :
    ∫ x in (1 / 2 : ℝ)..2, g (x + T * I) = E ((2 : ℝ) + T * I) - E (((1 / 2 : ℝ) : ℂ) + T * I) +
      ∫ x in (1 / 2 : ℝ)..2, logDeriv riemannZeta (x + T * I) := by
  have hT1 : 1 ≤ |T| := by rw [abs_of_pos (by linarith)]; linarith
  have him : ∀ x : ℝ, ((x : ℂ) + T * I).im = T := fun x => by simp
  have hslit : ∀ x : ℝ, (x : ℂ) + T * I ∈ slitPlane := fun x =>
    mem_slitPlane_iff.mpr (Or.inr (by rw [him]; linarith))
  have hslit1 : ∀ x : ℝ, (x : ℂ) + T * I - 1 ∈ slitPlane := fun x =>
    mem_slitPlane_iff.mpr (Or.inr (by simp; linarith))
  have hpt : ∀ x ∈ Icc (1 / 2 : ℝ) 2, g (x + T * I) = E' (x + T * I) + logDeriv riemannZeta (x + T * I) :=
    fun x hx => E'_eq (by simp; linarith [hx.1]) (ATK.ZeroClasses.VariacaoArg.ne_um hT1 x) (hno x hx)
  have hE'c : ContinuousOn (fun x : ℝ => E' (x + T * I)) (Icc (1 / 2 : ℝ) 2) := by
    intro x hx
    have hre : 0 < ((x : ℂ) + T * I).re := by simp; linarith [hx.1]
    have hne0 : (x : ℂ) + T * I ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [him, zero_im] at this
      linarith
    have hne1 : (x : ℂ) + T * I - 1 ≠ 0 := sub_ne_zero.mpr (ATK.ZeroClasses.VariacaoArg.ne_um hT1 x)
    have hc : ContinuousAt (fun x : ℝ => (x : ℂ) + T * I) x := by fun_prop
    have hdig : ContinuousAt (fun x : ℝ => digamma (((x : ℂ) + T * I) / 2)) x :=
      (continuousAt_digamma (by rw [div_ofNat_re]; linarith)).comp
        (f := fun x : ℝ => ((x : ℂ) + T * I) / 2) (by fun_prop)
    have : ContinuousAt (fun x : ℝ => E' (x + T * I)) x := by
      unfold E'
      exact ((((continuousAt_const.div hc hne0).add (continuousAt_const.div (hc.sub continuousAt_const)
        hne1)).sub continuousAt_const).add (hdig.div_const 2))
    exact this.continuousWithinAt
  have hint1 : IntervalIntegrable (fun x : ℝ => E' (x + T * I)) MeasureTheory.volume (1 / 2) 2 :=
    hE'c.intervalIntegrable_of_Icc (by norm_num)
  have hint2 := ATK.ZeroClasses.VariacaoArg.integrable_logDeriv_horiz hT1 (by norm_num : (1 / 2 : ℝ) ≤ 2) hno
  have hFTC : ∫ x in (1 / 2 : ℝ)..2, E' (x + T * I) = E ((2 : ℝ) + T * I) - E (((1 / 2 : ℝ) : ℂ) + T * I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => E (x + T * I))
      (f' := fun x : ℝ => E' (x + T * I))
    · intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      have h1 := hasDerivAt_E (hslit x) (hslit1 x) (by simp; linarith [hx.1])
      exact (h1.comp_add_const (x : ℂ) ((T : ℂ) * I)).comp_ofReal
    · exact hint1
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => E' (x + T * I) + logDeriv riemannZeta (x + T * I))
    (fun x hx => by rw [uIcc_of_le (by norm_num)] at hx; exact hpt x hx),
    intervalIntegral.integral_add hint1 hint2, hFTC]

/-! ## 5. A fórmula de `N(T)` -/

/-- A constante da base do retângulo. -/
noncomputable def C₁ : ℝ := (∫ x in (1 / 2 : ℝ)..2, g (x + (1 : ℝ) * I)).im - (Λ ((2 : ℝ) + (1 : ℝ) * I)).im

/-- **A fórmula**: `πN(T) = Im E(½ + iT) + arg ζ(2 + iT) − Im ∫_{1/2}^{2} ζ′/ζ(x + iT) dx + C₁`. -/
theorem formula_N {T : ℝ} (hT : 4 ≤ T) (hno : NaoOrdenada T) :
    π * (ATK.FechamentoO1.N T : ℝ) = (E (((1 / 2 : ℝ) : ℂ) + T * I)).im + arg (riemannZeta ((2 : ℝ) + T * I)) -
      (∫ x in (1 / 2 : ℝ)..2, logDeriv riemannZeta (x + T * I)).im + C₁ := by
  rw [identidade hT hno, topo hT hno]
  have hR : (∫ y in (1 : ℝ)..T, g ((2 : ℝ) + y * I)).re =
      (Λ ((2 : ℝ) + T * I) - Λ ((2 : ℝ) + (1 : ℝ) * I)).im := by
    rw [← lado_direito T, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  rw [hR]
  have hΛ : (Λ ((2 : ℝ) + T * I)).im = (E ((2 : ℝ) + T * I)).im + arg (riemannZeta ((2 : ℝ) + T * I)) := by
    rw [Λ, add_im, log_im]
  simp only [sub_im, add_im] at *
  rw [hΛ, C₁]
  ring

/-! ## 6. As estimativas -/

theorem arg_meio {T : ℝ} (hT : 0 < T) :
    arg (((1 / 2 : ℝ) : ℂ) + T * I) + arg (((1 / 2 : ℝ) : ℂ) + T * I - 1) = π := by
  set w : ℂ := ((1 / 2 : ℝ) : ℂ) + T * I with hw
  have e : w - 1 = -conj w := by
    rw [hw]
    apply Complex.ext <;> simp <;> norm_num
  have hc : (conj w).im < 0 := by rw [conj_im, hw]; simp; linarith
  rw [e, arg_neg_eq_arg_add_pi_of_im_neg hc, arg_conj]
  have hne : arg w ≠ π := by
    intro h
    have := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (show 0 < w.re by rw [hw]; simp))
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  rw [if_neg hne]
  ring

/-- **`Im E(½ + iT) = (T/2) log(T/2π) − T/2 + 7π/8 + O(1/T)`**. -/
theorem im_E_meio {T : ℝ} (hT : 4 ≤ T) :
    |(E (((1 / 2 : ℝ) : ℂ) + T * I)).im - (T / 2 * Real.log (T / (2 * π)) - T / 2 + 7 * π / 8)| ≤ 18 / T := by
  have hTpos : 0 < T := by linarith
  have hq := im_ell_quarto (τ := T / 2) (by linarith)
  have e1 : (((1 / 2 : ℝ) : ℂ) + T * I) / 2 = 1 / 4 + ((T / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have hE : (E (((1 / 2 : ℝ) : ℂ) + T * I)).im = π - Real.log π / 2 * T +
      (ell (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im := by
    rw [E, add_im, sub_im, add_im, log_im, log_im, e1, ← arg_meio hTpos]
    simp only [mul_im, ofReal_re, ofReal_im, add_re, add_im, I_re, I_im]
    norm_num
  rw [hE]
  have hlog : Real.log (T / (2 * π)) = Real.log (T / 2) - Real.log π := by
    rw [show T / (2 * π) = (T / 2) / π by ring, Real.log_div (by positivity) Real.pi_pos.ne']
  rw [hlog]
  have h18 : 9 / (T / 2) = 18 / T := by field_simp; ring
  rw [h18] at hq
  have e2 : π - Real.log π / 2 * T + (ell (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im -
      (T / 2 * (Real.log (T / 2) - Real.log π) - T / 2 + 7 * π / 8) =
      (ell (1 / 4 + ((T / 2 : ℝ) : ℂ) * I)).im - (T / 2 * Real.log (T / 2) - T / 2 - π / 8) := by ring
  rw [e2]
  exact hq

/-- O termo principal `m(T) = (T/2π) log(T/2π) − T/2π`. -/
noncomputable def m (T : ℝ) : ℝ := T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π)

/-- **Riemann–von Mangoldt nas alturas que não são ordenadas.** -/
theorem rvm_nao_ordenada : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T → NaoOrdenada T →
    |(ATK.FechamentoO1.N T : ℝ) - m T| ≤ C * Real.log T := by
  obtain ⟨Cv, hCv⟩ := ATK.ZeroClasses.VariacaoArg.variacao_log
  set Cv' := max Cv 0
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set K := (7 * π / 8 + 18 / 4 + π / 2 + |C₁|) / Real.log 4
  have hK : 0 ≤ K := by positivity
  refine ⟨(Cv' + K) / π, by positivity, fun T hT hno => ?_⟩
  have hTpos : 0 < T := by linarith
  have hlogT : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hf := formula_N hT hno
  have hE := im_E_meio hT
  have hv := (hCv T hT hno).trans (mul_le_mul_of_nonneg_right (le_max_left Cv 0)
    (Real.log_nonneg (by linarith)))
  have harg : |arg (riemannZeta ((2 : ℝ) + T * I))| ≤ π / 2 := by
    apply abs_arg_le_pi_div_two_iff.mpr
    have := ATK.ZeroClasses.VariacaoArg.re_zeta_dois (s := ((2 : ℝ) : ℂ) + T * I) (by simp)
    linarith [ATK.BLProva.dois_menos_pos]
  have hm : π * m T = T / 2 * Real.log (T / (2 * π)) - T / 2 := by
    unfold m
    field_simp
  have h18 : 18 / T ≤ 18 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  have hKT : 7 * π / 8 + 18 / 4 + π / 2 + |C₁| ≤ K * Real.log T := by
    calc 7 * π / 8 + 18 / 4 + π / 2 + |C₁| = K * Real.log 4 := by
          simp only [K]
          field_simp
      _ ≤ K * Real.log T := mul_le_mul_of_nonneg_left hlogT hK
  have key : |π * ((ATK.FechamentoO1.N T : ℝ) - m T)| ≤ (Cv' + K) * Real.log T := by
    rw [mul_sub, hm, hf]
    rw [abs_le] at hE hv harg ⊢
    have hC1 := abs_le.mp (le_refl |C₁|)
    constructor <;> nlinarith [neg_abs_le C₁, le_abs_self C₁]
  rw [abs_mul, abs_of_pos Real.pi_pos] at key
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  linarith

/-! ## 7. Todas as alturas -/

theorem existe_nao_ordenada {a b : ℝ} (ha : 0 < a) (hab : a < b) : ∃ T ∈ Ioo a b, NaoOrdenada T := by
  classical
  set O := (fun ρ : ℂ => ρ.im) '' (ATK.FechamentoO1.zerosAte b) with hO
  have hOf : O.Finite := (ATK.FechamentoO1.zerosAte_finito b).image _
  obtain ⟨T, hT, hTO⟩ := ((Set.Ioo_infinite hab).sdiff hOf).nonempty
  refine ⟨T, hT, fun σ hσ hz => hTO ?_⟩
  have hσ1 : σ < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith) hz
  have hZ : (σ : ℂ) + T * I ∈ ZetaSimetria.Z :=
    ⟨hz, by simp; linarith [hσ.1], by simp; exact hσ1⟩
  have hmem : (σ : ℂ) + T * I ∈ ATK.FechamentoO1.zerosAte b :=
    ⟨hZ, by simp; linarith [hT.1], by simp; exact hT.2.le⟩
  exact ⟨(σ : ℂ) + T * I, hmem, by simp⟩

theorem xlogx_sup {u v : ℝ} (hv : 0 < v) (huv : v ≤ u) :
    u * Real.log u - v * Real.log v ≤ (u - v) * (1 + Real.log u) := by
  have hu : 0 < u := lt_of_lt_of_le hv huv
  have h := Real.log_le_sub_one_of_pos (div_pos hu hv)
  rw [Real.log_div hu.ne' hv.ne'] at h
  have : v * (Real.log u - Real.log v) ≤ v * (u / v - 1) := mul_le_mul_of_nonneg_left h hv.le
  have e : v * (u / v - 1) = u - v := by field_simp
  rw [e] at this
  nlinarith

theorem xlogx_inf {u v : ℝ} (hv : 0 < v) (huv : v ≤ u) :
    (u - v) * (1 + Real.log v) ≤ u * Real.log u - v * Real.log v := by
  have hu : 0 < u := lt_of_lt_of_le hv huv
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
  rw [Real.log_div hu.ne' hv.ne', inv_div] at h
  have : u * (1 - v / u) ≤ u * (Real.log u - Real.log v) := mul_le_mul_of_nonneg_left h hu.le
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hu.ne'] at this
  nlinarith

/-- `0 ≤ m(x) − m(y) ≤ log x` para `2π ≤ y ≤ x ≤ y + 1`. -/
theorem m_lip {x y : ℝ} (hy : 2 * π ≤ y) (hxy : y ≤ x) (hx1 : x ≤ y + 1) :
    0 ≤ m x - m y ∧ m x - m y ≤ Real.log x := by
  have hpi := Real.pi_pos
  set u := x / (2 * π)
  set v := y / (2 * π)
  have hv1 : 1 ≤ v := by rw [le_div_iff₀ (by positivity)]; linarith
  have hvu : v ≤ u := div_le_div_of_nonneg_right hxy (by positivity)
  have hu1 : u - v ≤ 1 := by
    rw [← sub_div, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hmd : m x - m y = (u * Real.log u - v * Real.log v) - (u - v) := by
    unfold m
    ring
  have hlu : Real.log u ≤ Real.log x := Real.log_le_log (lt_of_lt_of_le one_pos (hv1.trans hvu))
    (div_le_self (by linarith) (by nlinarith [Real.pi_gt_three]))
  have hlv : 0 ≤ Real.log v := Real.log_nonneg hv1
  have hlu0 : 0 ≤ Real.log u := Real.log_nonneg (hv1.trans hvu)
  have hs := xlogx_sup (by linarith) hvu
  have hi := xlogx_inf (by linarith) hvu
  constructor
  · rw [hmd]
    nlinarith
  · rw [hmd]
    have : (u - v) * Real.log u ≤ 1 * Real.log u := mul_le_mul_of_nonneg_right hu1 hlu0
    nlinarith

/-- **Riemann–von Mangoldt** (`ATK.FechamentoO1.RiemannVonMangoldt`). -/
theorem riemannVonMangoldt : ATK.FechamentoO1.RiemannVonMangoldt := by
  obtain ⟨C, hC0, hC⟩ := rvm_nao_ordenada
  have hpi := Real.pi_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * (C + 1) + 20 / Real.log 2, fun T hT => ?_⟩
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlT0 : 0 < Real.log T := lt_of_lt_of_le hl2 hlogT
  change |(ATK.FechamentoO1.N T : ℝ) - m T| ≤ _
  rcases le_or_gt T 13 with h13 | h13
  · -- não há zeros até a altura 13
    have hN : ATK.FechamentoO1.N T = 0 := by
      unfold ATK.FechamentoO1.N
      apply Finset.sum_eq_zero
      intro ρ hρ
      have hρ' := (Set.Finite.mem_toFinset _).mp hρ
      have := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hρ'.1
      rw [abs_of_pos hρ'.2.1] at this
      linarith [hρ'.2.2]
    rw [hN, Nat.cast_zero, zero_sub, abs_neg]
    have hu0 : 0 < T / (2 * π) := by positivity
    have hu1 : T / (2 * π) ≤ 3 := by rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
    have hla : Real.log (T / (2 * π)) ≤ T / (2 * π) := (Real.log_le_sub_one_of_pos hu0).trans (by linarith)
    have hlb : -Real.log (T / (2 * π)) ≤ (T / (2 * π))⁻¹ := by
      rw [← Real.log_inv]
      exact (Real.log_le_sub_one_of_pos (inv_pos.mpr hu0)).trans (by linarith)
    have hinv : (T / (2 * π))⁻¹ * (T / (2 * π)) = 1 := inv_mul_cancel₀ hu0.ne'
    have hm10 : |m T| ≤ 20 := by
      unfold m
      rw [abs_le]
      constructor <;> nlinarith
    calc |m T| ≤ 20 := hm10
      _ = 20 / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ 20 / Real.log 2 * Real.log T := mul_le_mul_of_nonneg_left hlogT (by positivity)
      _ ≤ (2 * (C + 1) + 20 / Real.log 2) * Real.log T := by nlinarith
  · obtain ⟨T₁, hT₁, hno₁⟩ := existe_nao_ordenada (by linarith : (0 : ℝ) < T - 1) (by linarith : T - 1 < T)
    obtain ⟨T₂, hT₂, hno₂⟩ := existe_nao_ordenada (by linarith : (0 : ℝ) < T) (by linarith : T < T + 1)
    have h1 := hC T₁ (by linarith [hT₁.1]) hno₁
    have h2 := hC T₂ (by linarith [hT₂.1]) hno₂
    have hN1 : (ATK.FechamentoO1.N T₁ : ℝ) ≤ ATK.FechamentoO1.N T := by
      exact_mod_cast ATK.FechamentoO1.N_mono hT₁.2.le
    have hN2 : (ATK.FechamentoO1.N T : ℝ) ≤ ATK.FechamentoO1.N T₂ := by
      exact_mod_cast ATK.FechamentoO1.N_mono hT₂.1.le
    have hpi6 : 2 * π ≤ 7 := by nlinarith [Real.pi_lt_d2]
    obtain ⟨m1a, m1b⟩ := m_lip (x := T) (y := T₁) (by linarith [hT₁.1]) hT₁.2.le (by linarith [hT₁.1])
    obtain ⟨m2a, m2b⟩ := m_lip (x := T₂) (y := T) (by linarith) hT₂.1.le (by linarith [hT₂.2])
    have hl1 : Real.log T₁ ≤ Real.log T := Real.log_le_log (by linarith [hT₁.1]) hT₁.2.le
    have hl2' : Real.log T₂ ≤ 2 * Real.log T := by
      rw [← Real.log_rpow (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact Real.log_le_log (by linarith [hT₂.1]) (by nlinarith [hT₂.2])
    have hc1 := mul_le_mul_of_nonneg_left hl1 hC0
    have hc2 := mul_le_mul_of_nonneg_left hl2' hC0
    have h20 : 0 ≤ 20 / Real.log 2 * Real.log T := by positivity
    have hClT : 0 ≤ C * Real.log T := mul_nonneg hC0 hlT0.le
    rw [abs_le] at h1 h2 ⊢
    have expand : (2 * (C + 1) + 20 / Real.log 2) * Real.log T =
        2 * (C * Real.log T) + 2 * Real.log T + 20 / Real.log 2 * Real.log T := by ring
    rw [expand]
    constructor
    · linarith [h1.1, hN1, m1b, hc1]
    · linarith [h2.2, hN2, m2b, hc2]

/-- **`NecessidadeRH` reduz-se à dedução de Báez-Duarte**: `RiemannVonMangoldt`, `HadamardXi` e `LittlewoodSobRH`
são teoremas. -/
theorem necessidade_iff_deducao : ATK.FechamentoO1.NecessidadeRH ↔
    (ATK.FechamentoO1.RiemannVonMangoldt → ATK.FechamentoO1.HadamardXi →
      ATK.FechamentoO1.LittlewoodSobRH → RiemannHypothesis → ATK.NecessidadeBD.EntradasNecessidade) := by
  rw [ATK.ZeroClasses.LittlewoodRH.necessidade_iff_rvm]
  exact ⟨fun h => h.2, fun h => ⟨riemannVonMangoldt, h⟩⟩

end ATK.ZeroClasses.RvM

#print axioms ATK.ZeroClasses.RvM.deriv_xi_one_sub
#print axioms ATK.ZeroClasses.RvM.deriv_xi_conj
#print axioms ATK.ZeroClasses.RvM.g_one_sub
#print axioms ATK.ZeroClasses.RvM.g_conj
#print axioms ATK.ZeroClasses.RvM.integral_conj'
#print axioms ATK.ZeroClasses.RvM.xi_ne_zero_fora
#print axioms ATK.ZeroClasses.RvM.xi_ne_zero_baixo
#print axioms ATK.ZeroClasses.RvM.xi_ne_zero_topo
#print axioms ATK.ZeroClasses.RvM.continuousAt_g
#print axioms ATK.ZeroClasses.RvM.integrable_horizontal
#print axioms ATK.ZeroClasses.RvM.integrable_vertical
#print axioms ATK.ZeroClasses.RvM.lado_horizontal
#print axioms ATK.ZeroClasses.RvM.lado_esquerdo
#print axioms ATK.ZeroClasses.RvM.bordo_eq_N
#print axioms ATK.ZeroClasses.RvM.identidade
#print axioms ATK.ZeroClasses.RvM.hasDerivAt_E
#print axioms ATK.ZeroClasses.RvM.E'_eq
#print axioms ATK.ZeroClasses.RvM.hasDerivAt_Λ
#print axioms ATK.ZeroClasses.RvM.lado_direito
#print axioms ATK.ZeroClasses.RvM.continuousAt_digamma
#print axioms ATK.ZeroClasses.RvM.topo
#print axioms ATK.ZeroClasses.RvM.formula_N
#print axioms ATK.ZeroClasses.RvM.arg_meio
#print axioms ATK.ZeroClasses.RvM.im_E_meio
#print axioms ATK.ZeroClasses.RvM.rvm_nao_ordenada
#print axioms ATK.ZeroClasses.RvM.existe_nao_ordenada
#print axioms ATK.ZeroClasses.RvM.xlogx_sup
#print axioms ATK.ZeroClasses.RvM.xlogx_inf
#print axioms ATK.ZeroClasses.RvM.m_lip
#print axioms ATK.ZeroClasses.RvM.riemannVonMangoldt
#print axioms ATK.ZeroClasses.RvM.necessidade_iff_deducao
