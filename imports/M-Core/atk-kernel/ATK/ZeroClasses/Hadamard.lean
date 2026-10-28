import ATK.ZeroClasses.CanonicoInteira
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# O teorema de Hadamard para `ξ` (rodada 33)

**`hadamardXi : ATK.FechamentoO1.HadamardXi`**: existem `A, B` com
`ξ(s) = e^{A + Bs} ∏_ρ ((1 − s/ρ)e^{s/ρ})^{m_ρ}` (produtos parciais simétricos `|Im ρ| ≤ T`, com
multiplicidade), sem hipóteses.

A prova:

1. **o quociente** (`existe_quociente`): `ξ` e `P` (o produto canônico, rodadas 31–32) são inteiras com a mesma
   ordem em todo ponto, logo `ξ = P · F` com `F` inteira e sem zeros;
2. **o logaritmo** (`existe_log`): `F = e^g` com `g` inteira (primitiva de `F′/F`, Morera da Mathlib);
3. **a média de `log⁺|F|`** (`media_posLog_exp_le`): em `|z| = R`,
   `média log⁺|F| ≤ média log⁺|ξ| + média log⁺|P| − média log|P| ≤ K R^{3/2}`
   (`log⁺(ab) ≤ log⁺a + log⁺b` fora dos zeros de `P`, que são finitos no círculo; Jensen da Mathlib dá
   `média log|P| ≥ log|P(0)| = 0`; as cotas de `ξ` (rodada 30) e de `P` (rodada 32));
4. **Poisson** (`re_g_le`): `Re g(w) ≤ 3 · média log⁺|F|` em `|w| ≤ R/2` (fórmula de Poisson da Mathlib, núcleo
   `≤ (R + |w|)/(R − |w|) ≤ 3`);
5. **Borel–Carathéodory** (`norm_g_le`, da Mathlib): `|g| ≤ 2(3K R^{3/2} + 1) + 3|g(0)|` em `|z| ≤ R/4`;
6. **Cauchy duas vezes** (`norm_g2_le`): `|g″(z₀)| ≤ 1024·(6K R^{3/2} + 2 + 3|g(0)|)/R² → 0`, logo `g″ ≡ 0` e
   `g(z) = g(0) + g′(0)z` (`g_afim`);
7. **conclusão**: `ξ = e^{A + Bs} · P` e, pela redução `hadamardXi_iff` da rodada 31, `HadamardXi`.

Classificação (rodada 33): **ferramenta / alavanca** — fecha uma das três peças ausentes da Mathlib em
`NecessidadeRH` (`ATK.FechamentoO1`). Não diz nada sobre a posição dos zeros: RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric Real
open scoped Real

namespace ATK.ZeroClasses.Hadamard

open ATK.BaseRiemannXi ATK.ZeroClasses.Canonico ATK.ZeroClasses.CanonicoInteira

/-! ## 1. Ferramentas gerais -/

/-- Monotonia da média no círculo, fora de um conjunto enumerável. -/
theorem media_mono_fora {f₁ f₂ : ℂ → ℝ} {R : ℝ} (hR : R ≠ 0) (h₁ : CircleIntegrable f₁ 0 R)
    (h₂ : CircleIntegrable f₂ 0 R) {S : Set ℂ} (hS : S.Countable)
    (h : ∀ z ∈ sphere (0 : ℂ) |R|, z ∉ S → f₁ z ≤ f₂ z) :
    circleAverage f₁ 0 R ≤ circleAverage f₂ 0 R := by
  rw [circleAverage_def, circleAverage_def, smul_eq_mul, smul_eq_mul]
  have hnull : MeasureTheory.volume (circleMap 0 R ⁻¹' S) = 0 :=
    (hS.preimage_circleMap 0 hR).measure_zero _
  have hae : ∀ᵐ θ ∂MeasureTheory.volume, f₁ (circleMap 0 R θ) ≤ f₂ (circleMap 0 R θ) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (fun θ hθ => ?_) hnull
    by_contra hc
    exact hθ (h _ (circleMap_mem_sphere' 0 R θ) hc)
  have := intervalIntegral.integral_mono_ae (le_of_lt Real.two_pi_pos) h₁ h₂ hae
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **O quociente**: duas funções inteiras com a mesma ordem (finita) em todo ponto diferem por um fator inteiro
sem zeros. -/
theorem existe_quociente {f₁ f₂ : ℂ → ℂ} (h₁ : Differentiable ℂ f₁) (h₂ : Differentiable ℂ f₂)
    (hord : ∀ z, analyticOrderAt f₁ z = analyticOrderAt f₂ z)
    (htop : ∀ z, analyticOrderAt f₂ z ≠ ⊤) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ z, F z ≠ 0) ∧ ∀ z, f₁ z = f₂ z * F z := by
  classical
  have ex : ∀ z, ∃ g₁ g₂ : ℂ → ℂ, AnalyticAt ℂ g₁ z ∧ g₁ z ≠ 0 ∧ AnalyticAt ℂ g₂ z ∧ g₂ z ≠ 0 ∧
      ∃ n : ℕ, (∀ᶠ w in 𝓝 z, f₁ w = (w - z) ^ n • g₁ w) ∧ (∀ᶠ w in 𝓝 z, f₂ w = (w - z) ^ n • g₂ w) := by
    intro z
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (htop z)
    obtain ⟨g₂, hg₂a, hg₂0, hg₂e⟩ := ((h₂.analyticAt z).analyticOrderAt_eq_natCast).mp hn.symm
    obtain ⟨g₁, hg₁a, hg₁0, hg₁e⟩ :=
      ((h₁.analyticAt z).analyticOrderAt_eq_natCast).mp (by rw [hord z]; exact hn.symm)
    exact ⟨g₁, g₂, hg₁a, hg₁0, hg₂a, hg₂0, n, hg₁e, hg₂e⟩
  choose g₁ g₂ hg₁a hg₁0 hg₂a hg₂0 n he₁ he₂ using ex
  have hval : ∀ w, f₂ w ≠ 0 → g₁ w w / g₂ w w = f₁ w / f₂ w := by
    intro w hw
    have e1 := (he₁ w).self_of_nhds
    have e2 := (he₂ w).self_of_nhds
    have hn0 : n w = 0 := by
      by_contra h
      apply hw
      rw [e2, sub_self, zero_pow h, zero_smul]
    rw [hn0, pow_zero, one_smul] at e1 e2
    rw [e1, e2]
  refine ⟨fun z => g₁ z z / g₂ z z, ?_, fun z => div_ne_zero (hg₁0 z) (hg₂0 z), ?_⟩
  · intro z₀
    have hne : ∀ᶠ w in 𝓝[≠] z₀, f₂ w ≠ 0 :=
      ((h₂.analyticAt z₀).eventually_eq_zero_or_eventually_ne_zero).resolve_left
        (fun h => htop z₀ (analyticOrderAt_eq_top.mpr h))
    have hg2ne : ∀ᶠ w in 𝓝 z₀, g₂ z₀ w ≠ 0 := (hg₂a z₀).continuousAt.eventually_ne (hg₂0 z₀)
    have hF : (fun w => g₁ z₀ w / g₂ z₀ w) =ᶠ[𝓝 z₀] (fun z => g₁ z z / g₂ z z) := by
      rw [eventually_nhdsWithin_iff] at hne
      filter_upwards [hne, he₁ z₀, he₂ z₀, hg2ne] with w hw1 hw2 hw3 hw4
      by_cases hw : w = z₀
      · subst hw
        rfl
      · rw [hval w (hw1 hw), hw2, hw3, smul_eq_mul, smul_eq_mul]
        have hp : (w - z₀) ^ n z₀ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
        field_simp
    have han : AnalyticAt ℂ (fun w => g₁ z₀ w / g₂ z₀ w) z₀ := (hg₁a z₀).div (hg₂a z₀) (hg₂0 z₀)
    exact (han.congr hF).differentiableAt
  · intro z
    by_cases hz : f₂ z = 0
    · have e1 := (he₁ z).self_of_nhds
      have e2 := (he₂ z).self_of_nhds
      have hn : n z ≠ 0 := by
        intro h
        rw [h, pow_zero, one_smul] at e2
        exact hg₂0 z (e2 ▸ hz)
      rw [e1, sub_self, zero_pow hn, zero_smul, hz, zero_mul]
    · show f₁ z = f₂ z * (g₁ z z / g₂ z z)
      rw [hval z hz]
      field_simp

/-- **O logaritmo**: uma função inteira sem zeros é `e^g` com `g` inteira. -/
theorem existe_log {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : ∀ z, F z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, F z = cexp (g z) := by
  have hd : Differentiable ℂ (fun z => deriv F z / F z) := by
    intro z
    have : DifferentiableAt ℂ (deriv F) z := ((hF.analyticAt z).deriv).differentiableAt
    exact this.div (hF z) (h0 z)
  obtain ⟨G, hG0, hG⟩ := (hd.isExactOn_univ).with_val_at 0 (Complex.log (F 0))
  have hGd : Differentiable ℂ G := fun z => (hG z (mem_univ z)).differentiableAt
  have hH : ∀ z, HasDerivAt (fun z => F z * cexp (-G z)) 0 z := by
    intro z
    have h1 := (hF z).hasDerivAt
    have h2 := ((hG z (mem_univ z)).neg).cexp
    convert h1.mul h2 using 1
    field_simp [h0 z]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun z => (hH z).differentiableAt)
    (fun z => (hH z).deriv)
  refine ⟨G, hGd, fun z => ?_⟩
  have h := hconst z 0
  simp only [hG0, Complex.exp_neg, Complex.exp_log (h0 0), mul_inv_cancel₀ (h0 0)] at h
  have hz : cexp (G z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at h
  exact h

/-! ## 2. `ξ = P · e^g` -/

theorem xi_eq : ATK.FechamentoO1.xi = riemannXi := by
  funext s
  rfl

theorem ordem_Pcan_finita (z : ℂ) : analyticOrderAt Pcan z ≠ ⊤ := by
  rw [ordem_Pcan_eq_xi]
  exact ATK.ZeroClasses.Lagarias.ordem_xi_finita z

theorem existe_g : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, riemannXi z = Pcan z * cexp (g z) := by
  obtain ⟨F, hF, hF0, hξ⟩ := existe_quociente differentiable_riemannXi Pcan_differentiable
    (fun z => (ordem_Pcan_eq_xi z).symm) ordem_Pcan_finita
  obtain ⟨g, hg, hFg⟩ := existe_log hF hF0
  exact ⟨g, hg, fun z => by rw [hξ z, hFg z]⟩

theorem Pcan_zero : Pcan 0 = 1 := by
  unfold Pcan E1
  simp

/-! ## 3. A média de `log⁺|e^g|` -/

/-- A constante `S = Σ_{(ρ,j)} 1/|ρ|^{3/2}`. -/
noncomputable def S32 : ℝ := ∑' q : ZM, 1 / ‖((q.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ (3 / 2 : ℝ)

theorem S32_nonneg : 0 ≤ S32 := by
  unfold S32
  refine tsum_nonneg fun q => ?_
  have := Real.rpow_nonneg (norm_nonneg (((q.1 : ATK.ZetaSimetria.Z) : ℂ))) (3 / 2 : ℝ)
  positivity

theorem posLog_Pcan_le (z : ℂ) : log⁺ ‖Pcan z‖ ≤ 3 * ‖z‖ ^ (3 / 2 : ℝ) * S32 := by
  have h := Pcan_norm_le z
  have h0 : 0 ≤ 3 * ‖z‖ ^ (3 / 2 : ℝ) * S32 := by
    have := Real.rpow_nonneg (norm_nonneg z) (3 / 2 : ℝ)
    have := S32_nonneg
    positivity
  rw [Real.posLog_def]
  refine max_le h0 ?_
  beta_reduce
  rcases (norm_nonneg (Pcan z)).eq_or_lt with h1 | h1
  · rw [← h1, Real.log_zero]
    exact h0
  · calc Real.log ‖Pcan z‖ ≤ Real.log (Real.exp (3 * ‖z‖ ^ (3 / 2 : ℝ) * S32)) :=
          Real.log_le_log h1 (by unfold S32; exact h)
      _ = _ := Real.log_exp _

theorem posLog_xi_le {R : ℝ} (hR : 2 ≤ R) {z : ℂ} (hz : ‖z‖ = R) :
    log⁺ ‖riemannXi z‖ ≤ 34 * R ^ (3 / 2 : ℝ) := by
  have hR0 : 0 ≤ R := by linarith
  have hb := ATK.ZeroClasses.Jensen.cota_xi (s := z) (R := 2 * (R + 1)) (n := ⌈R⌉₊ + 1)
    (by omega) (by linarith) (by have := Nat.le_ceil R; push_cast; linarith) (by
      calc ‖z - 1 / 2‖ ≤ ‖z‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 * (R + 1) := by rw [hz]; norm_num; linarith)
  have hc := Nat.ceil_lt_add_one hR0
  have hX := ATK.ZeroClasses.Jensen.log_Bx_le hR (n := ⌈R⌉₊ + 1) (by push_cast; linarith)
    (by push_cast; linarith)
  have hB2 := ATK.ZeroClasses.Jensen.Bx_ge (R := 2 * (R + 1)) (by linarith) (⌈R⌉₊ + 1)
  have hlogR : Real.log R ≤ 2 * R ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hR0 (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hpow : R * R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have hr1 : 1 ≤ R ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlx : log⁺ ‖riemannXi z‖ ≤ Real.log (ATK.ZeroClasses.Jensen.Bx (2 * (R + 1)) (⌈R⌉₊ + 1)) := by
    rw [Real.posLog_def]
    refine max_le (Real.log_nonneg (by linarith)) ?_
    beta_reduce
    rcases (norm_nonneg (riemannXi z)).eq_or_lt with h1 | h1
    · rw [← h1, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log h1 hb
  calc log⁺ ‖riemannXi z‖ ≤ 13 * Real.log R + 4 * R * Real.log R := hlx.trans hX
    _ ≤ 17 * R * Real.log R := by nlinarith
    _ ≤ 17 * R * (2 * R ^ (1 / 2 : ℝ)) := by gcongr
    _ = 34 * (R * R ^ (1 / 2 : ℝ)) := by ring
    _ = 34 * R ^ (3 / 2 : ℝ) := by rw [hpow]

/-! ## 4. O expoente `g` -/

/-- O expoente: `ξ = P · e^{gH}`. -/
noncomputable def gH : ℂ → ℂ := Classical.choose existe_g

theorem gH_diff : Differentiable ℂ gH := (Classical.choose_spec existe_g).1

theorem xi_eq_P_exp (z : ℂ) : riemannXi z = Pcan z * cexp (gH z) :=
  (Classical.choose_spec existe_g).2 z

theorem deriv_gH_diff : Differentiable ℂ (deriv gH) :=
  fun z => ((gH_diff.analyticAt z).deriv).differentiableAt

/-- **`média log⁺|e^g| ≤ (34 + 3S) R^{3/2}`** em `|z| = R ≥ 2`. -/
theorem media_posLog_exp_le {R : ℝ} (hR : 2 ≤ R) :
    circleAverage (fun z => log⁺ ‖cexp (gH z)‖) 0 R ≤ (34 + 3 * S32) * R ^ (3 / 2 : ℝ) := by
  have hR0 : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR0
  have hS0 := S32_nonneg
  have hcF : Continuous (fun z => log⁺ ‖cexp (gH z)‖) := by
    have := gH_diff.continuous
    fun_prop
  have hcX : Continuous (fun z => log⁺ ‖riemannXi z‖) := by
    have := continuous_riemannXi
    fun_prop
  have hcP : Continuous (fun z => log⁺ ‖Pcan z‖) := by
    have := Pcan_differentiable.continuous
    fun_prop
  have hFi : CircleIntegrable (fun z => log⁺ ‖cexp (gH z)‖) 0 R := hcF.continuousOn.circleIntegrable'
  have hXi : CircleIntegrable (fun z => log⁺ ‖riemannXi z‖) 0 R := hcX.continuousOn.circleIntegrable'
  have hPi : CircleIntegrable (fun z => log⁺ ‖Pcan z‖) 0 R := hcP.continuousOn.circleIntegrable'
  have hLi : CircleIntegrable (fun z => Real.log ‖Pcan z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm (fun z _ => (Pcan_differentiable.analyticAt z).meromorphicAt)
  have eInv : (fun z => log⁺ ‖(Pcan z)⁻¹‖) = (fun z => log⁺ ‖Pcan z‖) - (fun z => Real.log ‖Pcan z‖) := by
    funext z
    simp only [Pi.sub_apply, norm_inv]
    linarith [Real.posLog_sub_posLog_inv (x := ‖Pcan z‖)]
  have hIi : CircleIntegrable (fun z => log⁺ ‖(Pcan z)⁻¹‖) 0 R := by
    rw [eInv]
    exact hPi.sub hLi
  -- passo a: fora dos zeros, log⁺|e^g| ≤ log⁺|ξ| + log⁺|1/P|
  have hfin : (closedBall (0 : ℂ) |R| ∩ riemannZetaZeros).Finite :=
    (isCompact_closedBall _ _).inter_riemannZetaZeros_finite
  have ha : circleAverage (fun z => log⁺ ‖cexp (gH z)‖) 0 R ≤
      circleAverage ((fun z => log⁺ ‖riemannXi z‖) + (fun z => log⁺ ‖(Pcan z)⁻¹‖)) 0 R := by
    refine media_mono_fora hR0.ne' hFi (hXi.add hIi) hfin.countable (fun z hz hzS => ?_)
    have hz0 : riemannZeta z ≠ 0 := fun h => hzS ⟨sphere_subset_closedBall hz, h⟩
    have hP : Pcan z ≠ 0 := Pcan_ne_zero (fun hZ => hz0 hZ.1)
    have he : cexp (gH z) = riemannXi z * (Pcan z)⁻¹ := by
      rw [xi_eq_P_exp z]
      field_simp
    simp only [Pi.add_apply]
    rw [he, norm_mul]
    exact Real.posLog_mul
  -- passo b–d
  have hb : circleAverage ((fun z => log⁺ ‖riemannXi z‖) + (fun z => log⁺ ‖(Pcan z)⁻¹‖)) 0 R =
      circleAverage (fun z => log⁺ ‖riemannXi z‖) 0 R + circleAverage (fun z => log⁺ ‖Pcan z‖) 0 R -
        circleAverage (fun z => Real.log ‖Pcan z‖) 0 R := by
    rw [circleAverage_add hXi hIi, eInv, circleAverage_sub hPi hLi]
    ring
  have hd : 0 ≤ circleAverage (fun z => Real.log ‖Pcan z‖) 0 R := by
    have han : AnalyticOnNhd ℂ Pcan (closedBall 0 |R|) := fun z _ => Pcan_differentiable.analyticAt z
    have hJ := han.circleAverage_log_norm hR0.ne' (by rw [Pcan_zero]; norm_num)
    rw [hJ, Pcan_zero, norm_one, Real.log_one, add_zero]
    refine finsum_nonneg fun u => ?_
    by_cases hu : u ∈ closedBall (0 : ℂ) |R|
    · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u) ?_
      rw [mem_closedBall_zero_iff, habs] at hu
      rcases (norm_nonneg u).eq_or_lt with h0 | h0
      · have : u = 0 := norm_eq_zero.mp h0.symm
        rw [this, sub_zero, norm_zero, inv_zero, mul_zero, Real.log_zero]
      · apply Real.log_nonneg
        rw [zero_sub, norm_neg, ← div_eq_mul_inv, le_div_iff₀ h0, one_mul]
        exact hu
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  have he : circleAverage (fun z => log⁺ ‖riemannXi z‖) 0 R ≤ 34 * R ^ (3 / 2 : ℝ) :=
    circleAverage_mono_on_of_le_circle hXi (fun z hz => posLog_xi_le hR (by
      rw [mem_sphere_zero_iff_norm, habs] at hz
      exact hz))
  have hf : circleAverage (fun z => log⁺ ‖Pcan z‖) 0 R ≤ 3 * R ^ (3 / 2 : ℝ) * S32 :=
    circleAverage_mono_on_of_le_circle hPi (fun z hz => by
      rw [mem_sphere_zero_iff_norm, habs] at hz
      have := posLog_Pcan_le z
      rw [hz] at this
      exact this)
  calc circleAverage (fun z => log⁺ ‖cexp (gH z)‖) 0 R
      ≤ _ := ha
    _ = _ := hb
    _ ≤ 34 * R ^ (3 / 2 : ℝ) + 3 * R ^ (3 / 2 : ℝ) * S32 - 0 := by linarith
    _ = (34 + 3 * S32) * R ^ (3 / 2 : ℝ) := by ring

/-! ## 5. Poisson e Borel–Carathéodory -/

theorem nucleo_cotas {R : ℝ} (hR0 : 0 < R) {w z : ℂ} (hw : ‖w‖ ≤ R / 2) (hz : z ∈ sphere (0 : ℂ) R) :
    0 ≤ poissonKernel 0 w z ∧ poissonKernel 0 w z ≤ 3 := by
  have hwb : w ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  have e : poissonKernel 0 w z = ((z - 0 + (w - 0)) / ((z - 0) - (w - 0))).re := by
    rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
  have h1 := le_re_herglotzRieszKernel hz hwb
  have h2 := re_herglotzRieszKernel_le hz hwb
  simp only [sub_zero] at h1 h2 e
  rw [e]
  have hd : 0 < R - ‖w‖ := by linarith
  have hd2 : (0 : ℝ) ≤ R + ‖w‖ := by linarith [norm_nonneg w]
  refine ⟨le_trans (div_nonneg hd.le hd2) h1, h2.trans ?_⟩
  rw [div_le_iff₀ hd]
  linarith

/-- **Poisson**: `Re g(w) ≤ 3 · média log⁺|e^g|` em `|w| ≤ R/2`. -/
theorem re_g_le {R : ℝ} (hR : 2 ≤ R) {w : ℂ} (hw : ‖w‖ ≤ R / 2) :
    (gH w).re ≤ 3 * ((34 + 3 * S32) * R ^ (3 / 2 : ℝ)) := by
  have hR0 : 0 < R := by linarith
  have habs : |R| = R := abs_of_pos hR0
  have hwb : w ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  have hP := (gH_diff.diffContOnCl (s := ball 0 R)).circleAverage_poissonKernel_smul hwb
  have hkc : ContinuousOn (poissonKernel 0 w) (sphere 0 |R|) := by
    rw [habs]
    intro z hz
    have hzw : z - 0 - (w - 0) ≠ 0 := by
      intro h
      have : z = w := by linear_combination h
      rw [mem_sphere_zero_iff_norm] at hz
      rw [this] at hz
      linarith
    unfold poissonKernel
    refine ContinuousAt.continuousWithinAt ?_
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hzw)
  have hint : CircleIntegrable (poissonKernel 0 w • gH) 0 R :=
    ContinuousOn.circleIntegrable' (hkc.smul gH_diff.continuous.continuousOn)
  have hre := Complex.reCLM.circleAverage_comp_comm hint
  rw [hP] at hre
  have e : (Complex.reCLM ∘ (poissonKernel 0 w • gH)) = fun z => poissonKernel 0 w z * (gH z).re := by
    funext z
    simp
  rw [e] at hre
  have hcF : Continuous (fun z => log⁺ ‖cexp (gH z)‖) := by
    have := gH_diff.continuous
    fun_prop
  have hint1 : CircleIntegrable (fun z => poissonKernel 0 w z * (gH z).re) 0 R := by
    have := (hkc.mul ((Complex.continuous_re.comp gH_diff.continuous).continuousOn))
    exact this.circleIntegrable'
  have hint2 : CircleIntegrable ((3 : ℝ) • fun z => log⁺ ‖cexp (gH z)‖) 0 R :=
    (hcF.continuousOn.circleIntegrable').smul _
  have hmono := circleAverage_mono hint1 hint2 (fun z hz => by
    rw [habs] at hz
    obtain ⟨k0, k3⟩ := nucleo_cotas hR0 hw hz
    simp only [Pi.smul_apply, smul_eq_mul]
    have hl : log⁺ ‖cexp (gH z)‖ = max 0 (gH z).re := by
      rw [show log⁺ ‖cexp (gH z)‖ = max 0 (Real.log ‖cexp (gH z)‖) from rfl, Complex.norm_exp,
        Real.log_exp]
    rw [hl]
    have hm0 : 0 ≤ max 0 (gH z).re := le_max_left _ _
    calc poissonKernel 0 w z * (gH z).re ≤ poissonKernel 0 w z * max 0 (gH z).re :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) k0
      _ ≤ 3 * max 0 (gH z).re := mul_le_mul_of_nonneg_right k3 hm0)
  rw [circleAverage_smul, smul_eq_mul] at hmono
  have hA := media_posLog_exp_le hR
  have : (gH w).re = circleAverage (fun z => poissonKernel 0 w z * (gH z).re) 0 R := by
    rw [hre]
    rfl
  rw [this]
  linarith

/-- **Borel–Carathéodory**: `|g| ≤ 2(3K R^{3/2} + 1) + 3|g(0)|` em `|z| ≤ R/4`. -/
theorem norm_g_le {R : ℝ} (hR : 2 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R / 4) :
    ‖gH z‖ ≤ 2 * (3 * ((34 + 3 * S32) * R ^ (3 / 2 : ℝ)) + 1) + 3 * ‖gH 0‖ := by
  have hS0 := S32_nonneg
  have hR0 : 0 < R := by linarith
  set M := 3 * ((34 + 3 * S32) * R ^ (3 / 2 : ℝ)) + 1 with hMdef
  have hM : 0 < M := by
    have := Real.rpow_nonneg hR0.le (3 / 2 : ℝ)
    positivity
  have hmaps : MapsTo gH (ball 0 (R / 2)) {z | z.re ≤ M} := fun w hw => by
    show (gH w).re ≤ M
    have := re_g_le hR (w := w) (by rw [mem_ball_zero_iff] at hw; linarith)
    linarith
  have hzb : z ∈ ball (0 : ℂ) (R / 2) := mem_ball_zero_iff.mpr (by linarith)
  have hBC := Complex.borelCaratheodory hM gH_diff.differentiableOn hmaps (by linarith) hzb
  have hd : 0 < R / 2 - ‖z‖ := by linarith
  have h1 : 2 * M * ‖z‖ / (R / 2 - ‖z‖) ≤ 2 * M := by
    rw [div_le_iff₀ hd]
    nlinarith [norm_nonneg z]
  have h2 : ‖gH 0‖ * (R / 2 + ‖z‖) / (R / 2 - ‖z‖) ≤ 3 * ‖gH 0‖ := by
    rw [div_le_iff₀ hd]
    nlinarith [norm_nonneg (gH 0), norm_nonneg z]
  linarith

/-! ## 6. Cauchy: `g″ ≡ 0` -/

theorem norm_g2_le {R : ℝ} (hR : 2 ≤ R) {z₀ : ℂ} (hz₀ : ‖z₀‖ ≤ R / 8) :
    ‖deriv (deriv gH) z₀‖ ≤
      1024 * (2 * (3 * ((34 + 3 * S32) * R ^ (3 / 2 : ℝ)) + 1) + 3 * ‖gH 0‖) / R ^ 2 := by
  set B := 2 * (3 * ((34 + 3 * S32) * R ^ (3 / 2 : ℝ)) + 1) + 3 * ‖gH 0‖ with hB
  have hR0 : 0 < R := by linarith
  have h1 : ∀ w ∈ sphere z₀ (R / 32), ‖deriv gH w‖ ≤ B / (R / 32) := by
    intro w hw
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) gH_diff.diffContOnCl ?_
    intro u hu
    apply norm_g_le hR
    rw [mem_sphere_iff_norm] at hu hw
    calc ‖u‖ = ‖(u - w) + ((w - z₀) + z₀)‖ := by ring_nf
      _ ≤ ‖u - w‖ + (‖w - z₀‖ + ‖z₀‖) := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ R / 4 := by linarith
  have h2 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < R / 32)
    deriv_gH_diff.diffContOnCl h1
  calc ‖deriv (deriv gH) z₀‖ ≤ B / (R / 32) / (R / 32) := h2
    _ = 1024 * B / R ^ 2 := by field_simp; ring

theorem g2_zero (z₀ : ℂ) : deriv (deriv gH) z₀ = 0 := by
  set K := 34 + 3 * S32 with hK
  set c := 2 + 3 * ‖gH 0‖ with hc
  have hlim : Tendsto (fun R : ℝ => 1024 * (2 * (3 * (K * R ^ (3 / 2 : ℝ)) + 1) + 3 * ‖gH 0‖) / R ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
    have h2 : Tendsto (fun R : ℝ => R ^ (-(2 : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
    have h3 := (h1.const_mul (6144 * K)).add (h2.const_mul (1024 * c))
    simp only [mul_zero, add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have e1 : R ^ (-(1 / 2 : ℝ)) = R ^ (3 / 2 : ℝ) / R ^ 2 := by
      rw [show (-(1 / 2 : ℝ)) = 3 / 2 - 2 by norm_num, Real.rpow_sub hR, Real.rpow_two]
    have e2 : R ^ (-(2 : ℝ)) = 1 / R ^ 2 := by
      rw [Real.rpow_neg hR.le, Real.rpow_two, one_div]
    rw [e1, e2, hc]
    field_simp
    ring
  have hev : ∀ᶠ R in atTop, ‖deriv (deriv gH) z₀‖ ≤
      1024 * (2 * (3 * (K * R ^ (3 / 2 : ℝ)) + 1) + 3 * ‖gH 0‖) / R ^ 2 := by
    filter_upwards [eventually_ge_atTop (max 2 (8 * ‖z₀‖))] with R hR
    exact norm_g2_le (le_of_max_le_left hR) (by have := le_of_max_le_right hR; linarith)
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)

/-- **`g` é afim**: `g(z) = g(0) + g′(0)·z`. -/
theorem g_afim (z : ℂ) : gH z = gH 0 + deriv gH 0 * z := by
  have hc := is_const_of_deriv_eq_zero deriv_gH_diff g2_zero
  set B := deriv gH 0 with hB
  have hh : ∀ x, HasDerivAt (fun z => gH z - B * z) 0 x := by
    intro x
    have := ((gH_diff x).hasDerivAt).sub ((hasDerivAt_id' x).const_mul B)
    convert this using 1
    rw [hc x 0]
    ring
  have h := is_const_of_deriv_eq_zero (fun x => (hh x).differentiableAt) (fun x => (hh x).deriv) z 0
  simp only [mul_zero, sub_zero] at h
  linear_combination h

/-! ## 7. O teorema de Hadamard para `ξ` -/

/-- **Hadamard para `ξ`**: `ξ(s) = e^{A + Bs} · P(s)`. -/
theorem xi_hadamard : ∃ A B : ℂ, ∀ s, riemannXi s = cexp (A + B * s) * Pcan s :=
  ⟨gH 0, deriv gH 0, fun s => by rw [xi_eq_P_exp s, g_afim s]; ring⟩

/-- **`HadamardXi`** (`ATK.FechamentoO1`), sem hipóteses: os produtos parciais simétricos
`e^{A+Bs} ∏_{|Im ρ| ≤ T} ((1 − s/ρ)e^{s/ρ})^{m_ρ}` convergem para `ξ(s)`. -/
theorem hadamardXi : ATK.FechamentoO1.HadamardXi := by
  rw [ATK.ZeroClasses.Canonico.hadamardXi_iff]
  obtain ⟨A, B, h⟩ := xi_hadamard
  exact ⟨A, B, fun s => by rw [xi_eq]; exact h s⟩

/-- **O que resta da necessidade de Báez-Duarte**: com `HadamardXi` provado, `NecessidadeRH` equivale a
Riemann–von Mangoldt, Littlewood sob RH e a dedução clássica. -/
theorem necessidade_iff : ATK.FechamentoO1.NecessidadeRH ↔
    ATK.FechamentoO1.RiemannVonMangoldt ∧ ATK.FechamentoO1.LittlewoodSobRH ∧
      (ATK.FechamentoO1.RiemannVonMangoldt → ATK.FechamentoO1.HadamardXi →
        ATK.FechamentoO1.LittlewoodSobRH → RiemannHypothesis → ATK.NecessidadeBD.EntradasNecessidade) :=
  ⟨fun h => ⟨h.rvm, h.littlewood, h.deducao⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, hadamardXi, h2, h3⟩⟩

end ATK.ZeroClasses.Hadamard

#print axioms ATK.ZeroClasses.Hadamard.media_mono_fora
#print axioms ATK.ZeroClasses.Hadamard.existe_quociente
#print axioms ATK.ZeroClasses.Hadamard.existe_log
#print axioms ATK.ZeroClasses.Hadamard.xi_eq
#print axioms ATK.ZeroClasses.Hadamard.ordem_Pcan_finita
#print axioms ATK.ZeroClasses.Hadamard.existe_g
#print axioms ATK.ZeroClasses.Hadamard.Pcan_zero
#print axioms ATK.ZeroClasses.Hadamard.S32_nonneg
#print axioms ATK.ZeroClasses.Hadamard.posLog_Pcan_le
#print axioms ATK.ZeroClasses.Hadamard.posLog_xi_le
#print axioms ATK.ZeroClasses.Hadamard.gH_diff
#print axioms ATK.ZeroClasses.Hadamard.xi_eq_P_exp
#print axioms ATK.ZeroClasses.Hadamard.deriv_gH_diff
#print axioms ATK.ZeroClasses.Hadamard.media_posLog_exp_le
#print axioms ATK.ZeroClasses.Hadamard.nucleo_cotas
#print axioms ATK.ZeroClasses.Hadamard.re_g_le
#print axioms ATK.ZeroClasses.Hadamard.norm_g_le
#print axioms ATK.ZeroClasses.Hadamard.norm_g2_le
#print axioms ATK.ZeroClasses.Hadamard.g2_zero
#print axioms ATK.ZeroClasses.Hadamard.g_afim
#print axioms ATK.ZeroClasses.Hadamard.xi_hadamard
#print axioms ATK.ZeroClasses.Hadamard.hadamardXi
#print axioms ATK.ZeroClasses.Hadamard.necessidade_iff
