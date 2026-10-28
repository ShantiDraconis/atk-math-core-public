import ATK.ZeroClasses.LittlewoodMontagem

/-!
# As médias de `F` sob RH (rodada 94)

Sob RH, as médias de `F(y) = (ψ(e^y) − e^y)e^{−y/2}` são pequenas (`integral_F_log`):

  `|∫ₐᵇ F(u) du| ≤ C(1 + log b)`   para `1 ≤ a ≤ b`.

É o substituto da fórmula explícita integrada (`∫ (ψ(t) − t) dt/t = O(√x)` a menos de `log`) e o passo que falta
para `π(x) − Li(x) = Ω±(√x log log log x/log x)`. A prova integra em `u` a fórmula gaussiana das rodadas 89–92 e faz
`τ → 0` só nas pontas do intervalo.

* §1 `summable_gz`, `tsum_gz`: sob RH, a soma sobre os zeros converge absolutamente para todo `τ > 0`
  (`|ρ|e^{−τγ²} ≤ 2/τ`) e vale `−(k_τ * F)(u) + R(u, τ)`.
* §2 `integral_re_pw_le`: `|∫ₐᵇ Re(W_u(ρ)/ρ) du| ≤ 3/|ρ|²` (primitiva explícita); daí, por convergência dominada,
  `|∫ₐᵇ Σ_ρ m_ρ Re(W_u(ρ)/ρ) du| ≤ 3Σ m_ρ/|ρ|²` uniformemente em `τ`, `a`, `b` (`integral_tsum_le`).
* §3 `fubini_kF` e `aprox_le`: `∫ₐᵇ (k_τ * F) = ∫ k_τ(v) ∫ₐᵇ F(u − v) du dv`, e a diferença para `∫ₐᵇ F` só vê as
  pontas: `≤ 2B ∫ k_τ(v)|v|(1 + (c + |v|)²) dv`, que vai a `0` com `τ` (`momento_le`, via
  `e^v + e^{−v} − 2 ≥ v²/2 + |v|³/6`, `H_ge`).
* §4 `integral_F_diadico`: `|∫ₐᵇ F| ≤ C` para `1 ≤ a ≤ b ≤ 2a`, com `τ ≍ a^{−4}` (o resto `R = O(e^{−u/2}/τ)` da
  rodada 92 custa `a⁵e^{−a/2} ≤ 46080`, `pot_exp_le`).
* §5 `integral_F_pot`, **`integral_F_log`**: somando `O(log b)` intervalos diádicos.

Classificação: **ferramenta** (sob RH). `π(x) − Li(x) = Ω±(…)` continua BUILD_PENDING (falta a montagem com
`primeCounting_eq_theta_div_log_add_integral` da Mathlib). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

namespace ATK.ZeroClasses.LittlewoodMedia

open ATK.ZeroClasses.ExplicitaGauss (Wg pw kg kg_nonneg norm_Wg)
open ATK.ZeroClasses.ExplicitaT (Zfin mem_Zfin)
open ATK.ZeroClasses.LittlewoodBase (Fpsi)
open ATK.ZeroClasses.LittlewoodMontagem (Resto)

local notation "Zs" => ATK.ZetaSimetria.Z

/-! ## 1. A soma sobre os zeros é absolutamente convergente sob RH -/

theorem norm_pw_RH {ρ : ℂ} (hρ : ρ.re = 1 / 2) (u τ : ℝ) :
    ‖pw (Wg u τ) ρ‖ = Real.exp (-(τ * ρ.im ^ 2)) / ‖ρ‖ := by
  unfold pw
  rw [norm_div, norm_Wg, hρ]
  congr 2
  ring

/-- `|ρ| e^{−τγ²} ≤ 2/τ` para os zeros da faixa. -/
theorem norm_mul_exp_le {ρ : ℂ} (hZ : ρ ∈ Zs) {τ : ℝ} (hτ : 0 < τ) :
    ‖ρ‖ * Real.exp (-(τ * ρ.im ^ 2)) ≤ 2 / τ := by
  have hsq := ATK.ZeroClasses.LittlewoodSoma.norm_sq_le hZ
  have hn := ATK.ZeroClasses.LittlewoodSoma.norm_pos_Z hZ
  have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hZ
  have hn1 : 1 ≤ ‖ρ‖ := by linarith [Complex.abs_im_le_norm ρ]
  have he : 1 + τ * ρ.im ^ 2 ≤ Real.exp (τ * ρ.im ^ 2) := by linarith [Real.add_one_le_exp (τ * ρ.im ^ 2)]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hτ]
  have h1 : ‖ρ‖ ≤ ‖ρ‖ ^ 2 := by nlinarith
  have h2 : τ * ‖ρ‖ ≤ τ * ‖ρ‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hτ.le
  have h3 : τ * ‖ρ‖ ^ 2 ≤ 2 * (τ * ρ.im ^ 2) := by nlinarith
  nlinarith

theorem summable_gauss {τ : ℝ} (hτ : 0 < τ) :
    Summable fun ρ : Zs => (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
      Real.exp (-(τ * (ρ : ℂ).im ^ 2)) / ‖(ρ : ℂ)‖ := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    (ATK.ZeroClasses.JensenLocal.soma_ordem_inv_quadrado.mul_left (2 / τ))
  have hn := ATK.ZeroClasses.LittlewoodSoma.norm_pos_Z ρ.2
  have h := norm_mul_exp_le ρ.2 hτ
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hn]
  calc (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * Real.exp (-(τ * (ρ : ℂ).im ^ 2))
      = (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 *
          (‖(ρ : ℂ)‖ * Real.exp (-(τ * (ρ : ℂ).im ^ 2))) * ‖(ρ : ℂ)‖ := by
        field_simp
    _ ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 * (2 / τ) * ‖(ρ : ℂ)‖ := by
        gcongr
    _ = 2 / τ * ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) * ‖(ρ : ℂ)‖ := by ring

/-- O termo `m_ρ Re(W(ρ)/ρ)` como função na faixa. -/
noncomputable def gz (u τ : ℝ) (ρ : Zs) : ℝ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (pw (Wg u τ) (ρ : ℂ)).re

theorem abs_gz_le (hRH : RiemannHypothesis) (u τ : ℝ) (ρ : Zs) :
    |gz u τ ρ| ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
      Real.exp (-(τ * (ρ : ℂ).im ^ 2)) / ‖(ρ : ℂ)‖ := by
  unfold gz
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hm, mul_div_assoc,
    ← norm_pw_RH (ATK.ZeroClasses.LagariasHadamard.re_de_RH hRH ρ.2) u τ]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hm

theorem summable_gz (hRH : RiemannHypothesis) {τ : ℝ} (hτ : 0 < τ) (u : ℝ) : Summable (gz u τ) :=
  Summable.of_norm_bounded (summable_gauss hτ) (fun ρ => by
    rw [Real.norm_eq_abs]; exact abs_gz_le hRH u τ ρ)

/-- As somas sobre `Zfin T` tendem à soma total quando `T → ∞`. -/
theorem tendsto_Zfin {f : ℂ → ℝ} (hs : Summable fun ρ : Zs => f ρ) {ι : Type*} {l : Filter ι}
    {T : ι → ℝ} (hT : Tendsto T l atTop) :
    Tendsto (fun i => ∑ ρ ∈ Zfin (T i), f ρ) l (𝓝 (∑' ρ : Zs, f ρ)) := by
  classical
  have e : ∀ i, ∑ ρ ∈ Zfin (T i), f ρ = ∑ ρ ∈ (Zfin (T i)).subtype (· ∈ Zs), f ρ := fun i =>
    (Finset.sum_subtype_of_mem f fun ρ hρ => (ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin hρ).1).symm
  simp_rw [e]
  refine hs.hasSum.comp (tendsto_atTop.mpr fun s => ?_)
  filter_upwards [hT.eventually_ge_atTop (∑ ρ ∈ s, |(ρ : ℂ).im|)] with i hi
  intro ρ hρ
  rw [Finset.mem_subtype, mem_Zfin]
  have hle : |(ρ : ℂ).im| ≤ ∑ ρ ∈ s, |(ρ : ℂ).im| :=
    Finset.single_le_sum (f := fun ρ : Zs => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
  exact ⟨ρ.2.1, ρ.2.2.1, hle.trans hi⟩

/-- **A soma total é o lado de `F` da fórmula gaussiana** (sob RH). -/
theorem tsum_gz (hRH : RiemannHypothesis) {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    ∑' ρ : Zs, gz u τ ρ = -(∫ v, kg τ v * Fpsi (u - v)) + Resto u τ := by
  obtain ⟨T, hT, hlim⟩ := ATK.ZeroClasses.LittlewoodMontagem.formula_psi_resto hτ u
  have hT' : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => (hT k).1) (tendsto_atTop_add_const_right _ 6 tendsto_natCast_atTop_atTop)
  have h := tendsto_Zfin (f := fun ρ : ℂ => (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg u τ) ρ).re)
    (summable_gz hRH hτ u) hT'
  exact tendsto_nhds_unique h hlim

/-! ## 2. A integral em `u` da soma sobre os zeros é limitada -/

theorem sum_Zfin_le_tsum {f : ℂ → ℝ} (hs : Summable fun ρ : Zs => f ρ) (hf : ∀ ρ ∈ Zs, 0 ≤ f ρ) (T : ℝ) :
    ∑ ρ ∈ Zfin T, f ρ ≤ ∑' ρ : Zs, f ρ := by
  classical
  rw [← Finset.sum_subtype_of_mem f fun ρ hρ => (ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin hρ).1]
  exact hs.sum_le_tsum _ (fun ρ _ => hf ρ ρ.2)

theorem continuous_re_pw (τ : ℝ) (ρ : ℂ) : Continuous fun u : ℝ => (pw (Wg u τ) ρ).re := by
  unfold pw Wg
  fun_prop

/-- **Sob RH, `|∫ₐᵇ Re(W_u(ρ)/ρ) du| ≤ 3/|ρ|²`**: a primitiva é
`e^{−τγ²}(sen(γu)/(2γ) − cos(γu))/|ρ|²`. -/
theorem integral_re_pw_le (hRH : RiemannHypothesis) {ρ : ℂ} (hZ : ρ ∈ Zs) {τ : ℝ} (hτ : 0 ≤ τ) (a b : ℝ) :
    |∫ u in a..b, (pw (Wg u τ) ρ).re| ≤ 3 / ‖ρ‖ ^ 2 := by
  have hre := ATK.ZeroClasses.LagariasHadamard.re_de_RH hRH hZ
  have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hZ
  have hn := ATK.ZeroClasses.LittlewoodSoma.norm_pos_Z hZ
  set γ := ρ.im with hγ
  have hγ0 : γ ≠ 0 := by intro h; rw [h, abs_zero] at h13; linarith
  set c := Real.exp (-(τ * γ ^ 2)) / ‖ρ‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 / ‖ρ‖ ^ 2 := by
    rw [hc]
    gcongr
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hfun : (fun u : ℝ => (pw (Wg u τ) ρ).re) = fun u => c * (Real.cos (γ * u) / 2 + γ * Real.sin (γ * u)) := by
    funext u
    rw [ATK.ZeroClasses.LittlewoodBase.re_pw_RH hre u τ, hc]
    ring
  have hd : ∀ u : ℝ, HasDerivAt (fun u => c * (Real.sin (γ * u) / (2 * γ) - Real.cos (γ * u)))
      (c * (Real.cos (γ * u) / 2 + γ * Real.sin (γ * u))) u := by
    intro u
    have h1 : HasDerivAt (fun u => Real.sin (γ * u)) (Real.cos (γ * u) * γ) u := by
      have := ((hasDerivAt_id u).const_mul γ).sin
      simpa using this
    have h2 : HasDerivAt (fun u => Real.cos (γ * u)) (-Real.sin (γ * u) * γ) u := by
      have := ((hasDerivAt_id u).const_mul γ).cos
      simpa using this
    have h3 := ((h1.div_const (2 * γ)).sub h2).const_mul c
    convert h3 using 1
    field_simp
    ring
  rw [hfun, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous fun u : ℝ => c * (Real.cos (γ * u) / 2 + γ * Real.sin (γ * u))).intervalIntegrable _ _)]
  have hGb : ∀ u : ℝ, |c * (Real.sin (γ * u) / (2 * γ) - Real.cos (γ * u))| ≤ 3 / 2 * (1 / ‖ρ‖ ^ 2) := by
    intro u
    rw [abs_mul, abs_of_nonneg hc0]
    have hs := Real.abs_sin_le_one (γ * u)
    have hco := Real.abs_cos_le_one (γ * u)
    have hg1 : 1 ≤ |γ| := by linarith
    have h2 : |Real.sin (γ * u) / (2 * γ) - Real.cos (γ * u)| ≤ 3 / 2 := by
      calc |Real.sin (γ * u) / (2 * γ) - Real.cos (γ * u)|
          ≤ |Real.sin (γ * u) / (2 * γ)| + |Real.cos (γ * u)| := abs_sub _ _
        _ ≤ 1 / 2 + 1 := by
          gcongr
          rw [abs_div, abs_mul, abs_two, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        _ = 3 / 2 := by norm_num
    calc c * |Real.sin (γ * u) / (2 * γ) - Real.cos (γ * u)| ≤ (1 / ‖ρ‖ ^ 2) * (3 / 2) :=
          mul_le_mul hc1 h2 (abs_nonneg _) (by positivity)
      _ = 3 / 2 * (1 / ‖ρ‖ ^ 2) := by ring
  calc |c * (Real.sin (γ * b) / (2 * γ) - Real.cos (γ * b)) - c * (Real.sin (γ * a) / (2 * γ) - Real.cos (γ * a))|
      ≤ |c * (Real.sin (γ * b) / (2 * γ) - Real.cos (γ * b))| +
        |c * (Real.sin (γ * a) / (2 * γ) - Real.cos (γ * a))| := abs_sub _ _
    _ ≤ 3 / 2 * (1 / ‖ρ‖ ^ 2) + 3 / 2 * (1 / ‖ρ‖ ^ 2) := add_le_add (hGb b) (hGb a)
    _ = 3 / ‖ρ‖ ^ 2 := by ring

/-- As somas parciais `S_T(u) = Σ_{|γ| ≤ T} m_ρ Re(W_u(ρ)/ρ)`. -/
noncomputable def Sn (τ T u : ℝ) : ℝ := ∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg u τ) ρ).re

theorem continuous_Sn (τ T : ℝ) : Continuous (Sn τ T) := by
  unfold Sn
  exact continuous_finsetSum _ fun ρ _ => continuous_const.mul (continuous_re_pw τ ρ)

/-- **`|∫ₐᵇ S_T(u) du| ≤ 3C₀`** sob RH, uniformemente em `T`, `τ ≥ 0`, `a`, `b`. -/
theorem integral_Sn_le (hRH : RiemannHypothesis) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ T a b : ℝ, 0 ≤ τ →
    |∫ u in a..b, Sn τ T u| ≤ 3 * C₀ := by
  obtain ⟨C₀, hC₀, hC⟩ := ATK.ZeroClasses.LittlewoodSoma.soma_inv_sq_le
  refine ⟨C₀, hC₀, fun τ T a b hτ => ?_⟩
  unfold Sn
  rw [intervalIntegral.integral_finsetSum (f := fun ρ u => (analyticOrderNatAt riemannZeta ρ : ℝ) *
    (pw (Wg u τ) ρ).re) (fun ρ _ => (continuous_const.mul (continuous_re_pw τ ρ)).intervalIntegrable _ _)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h := hC (Zfin T) (fun ρ hρ => (ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin hρ).1)
  calc ∑ ρ ∈ Zfin T, |∫ u in a..b, (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg u τ) ρ).re|
      ≤ ∑ ρ ∈ Zfin T, 3 * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2) := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have hZ := (ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin hρ).1
        have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
        rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hm]
        calc (analyticOrderNatAt riemannZeta ρ : ℝ) * |∫ u in a..b, (pw (Wg u τ) ρ).re|
            ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (3 / ‖ρ‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (integral_re_pw_le hRH hZ hτ a b) hm
          _ = 3 * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2) := by ring
    _ ≤ 3 * C₀ := by rw [← Finset.mul_sum]; linarith

/-- **`|∫ₐᵇ Σ_ρ m_ρ Re(W_u(ρ)/ρ) du| ≤ 3C₀`** sob RH, para todo `τ > 0` (convergência dominada). -/
theorem integral_tsum_le (hRH : RiemannHypothesis) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ a b : ℝ, 0 < τ →
    IntervalIntegrable (fun u => ∑' ρ : Zs, gz u τ ρ) volume a b ∧
      |∫ u in a..b, ∑' ρ : Zs, gz u τ ρ| ≤ 3 * C₀ := by
  obtain ⟨C₀, hC₀, hC⟩ := integral_Sn_le hRH
  refine ⟨C₀, hC₀, fun τ a b hτ => ?_⟩
  set M := ∑' ρ : Zs, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
    Real.exp (-(τ * (ρ : ℂ).im ^ 2)) / ‖(ρ : ℂ)‖ with hM
  have hbound : ∀ (T u : ℝ), ‖Sn τ T u‖ ≤ M := by
    intro T u
    rw [Real.norm_eq_abs]
    unfold Sn
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun ρ hρ => ?_) (sum_Zfin_le_tsum (f := fun ρ : ℂ =>
      (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) / ‖ρ‖) (summable_gauss hτ)
      (fun ρ _ => by positivity) T)
    exact abs_gz_le hRH u τ ⟨ρ, (ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin hρ).1⟩
  have hlim : ∀ u : ℝ, Tendsto (fun n : ℕ => Sn τ n u) atTop (𝓝 (∑' ρ : Zs, gz u τ ρ)) := fun u =>
    tendsto_Zfin (f := fun ρ : ℂ => (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg u τ) ρ).re)
      (summable_gz hRH hτ u) tendsto_natCast_atTop_atTop
  have hmeas : AEStronglyMeasurable (fun u => ∑' ρ : Zs, gz u τ ρ) (volume.restrict (Ι a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n : ℕ => (continuous_Sn τ (n : ℝ)).aestronglyMeasurable) (Eventually.of_forall hlim)
  have hint : IntervalIntegrable (fun u => ∑' ρ : Zs, gz u τ ρ) volume a b :=
    IntervalIntegrable.mono_fun' (g := fun _ => M) intervalIntegrable_const hmeas
      (Eventually.of_forall fun u => le_of_tendsto' ((hlim u).norm) fun n => hbound n u)
  refine ⟨hint, ?_⟩
  have hdct : Tendsto (fun n : ℕ => ∫ u in a..b, Sn τ n u) atTop
      (𝓝 (∫ u in a..b, ∑' ρ : Zs, gz u τ ρ)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun n => (continuous_Sn τ n).aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun u _ => hbound n u)
      intervalIntegrable_const (Eventually.of_forall fun u _ => hlim u)
  exact le_of_tendsto' hdct.abs fun n => hC τ n a b hτ.le

/-! ## 3. Da média gaussiana à integral de `F` -/

/-- `H(v) = e^v + e^{−v} − 2 ≥ v²/2 + |v|³/6`. -/
theorem H_ge (v : ℝ) : v ^ 2 / 2 + |v| ^ 3 / 6 ≤ Real.exp v + Real.exp (-v) - 2 := by
  have h1 := Real.sum_le_exp_of_nonneg (abs_nonneg v) 4
  have h2 := Real.add_one_le_exp (-|v|)
  have e : ∑ i ∈ Finset.range 4, |v| ^ i / (i.factorial : ℝ) = 1 + |v| + |v| ^ 2 / 2 + |v| ^ 3 / 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [e] at h1
  have hsym : Real.exp v + Real.exp (-v) = Real.exp |v| + Real.exp (-|v|) := by
    rcases le_total 0 v with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_neg]
      ring
  rw [hsym, ← sq_abs v]
  linarith

theorem integrable_kg_H {τ : ℝ} (hτ : 0 < τ) :
    Integrable fun v => kg τ v * (Real.exp v + Real.exp (-v) - 2) := by
  have i1 := ATK.ZeroClasses.LittlewoodBase.integrable_kg_exp hτ 1
  have i2 := ATK.ZeroClasses.LittlewoodBase.integrable_kg_exp hτ (-1)
  have i3 := ATK.ZeroClasses.LittlewoodBase.integrable_kg hτ
  have e : (fun v => kg τ v * (Real.exp v + Real.exp (-v) - 2)) =
      fun v => kg τ v * Real.exp (1 * v) + kg τ v * Real.exp (-1 * v) - 2 * kg τ v := by
    funext v
    simp only [one_mul, neg_mul]
    ring
  rw [e]
  exact (i1.add i2).sub (i3.const_mul 2)

theorem integral_kg_H {τ : ℝ} (hτ : 0 < τ) :
    ∫ v, kg τ v * (Real.exp v + Real.exp (-v) - 2) = 2 * Real.exp τ - 2 := by
  have i1 := ATK.ZeroClasses.LittlewoodBase.integrable_kg_exp hτ 1
  have i2 := ATK.ZeroClasses.LittlewoodBase.integrable_kg_exp hτ (-1)
  have i3 := ATK.ZeroClasses.LittlewoodBase.integrable_kg hτ
  have i12 : Integrable (fun v => kg τ v * Real.exp (1 * v) + kg τ v * Real.exp (-1 * v)) := i1.add i2
  have e : (fun v => kg τ v * (Real.exp v + Real.exp (-v) - 2)) =
      fun v => (kg τ v * Real.exp (1 * v) + kg τ v * Real.exp (-1 * v)) - 2 * kg τ v := by
    funext v
    simp only [one_mul, neg_mul]
    ring
  rw [e, integral_sub i12 (i3.const_mul 2), integral_add i1 i2, integral_const_mul,
    ATK.ZeroClasses.LittlewoodBase.integral_kg_exp hτ 1, ATK.ZeroClasses.LittlewoodBase.integral_kg_exp hτ (-1),
    ATK.ZeroClasses.LittlewoodBase.integral_kg hτ]
  norm_num
  ring

/-- O momento `∫ k_τ(v)|v|(1 + (c + |v|)²) dv ≤ (1 + 2c²)δ + ((1 + 2c²)2/δ + 12)(2e^τ − 2)`. -/
theorem momento_le {τ : ℝ} (hτ : 0 < τ) {c δ : ℝ} (_hc : 0 ≤ c) (hδ : 0 < δ) :
    Integrable (fun v => kg τ v * (|v| * (1 + (c + |v|) ^ 2))) ∧
    ∫ v, kg τ v * (|v| * (1 + (c + |v|) ^ 2)) ≤
      (1 + 2 * c ^ 2) * δ + ((1 + 2 * c ^ 2) * 2 / δ + 12) * (2 * Real.exp τ - 2) := by
  have iH := integrable_kg_H hτ
  have i3 := ATK.ZeroClasses.LittlewoodBase.integrable_kg hτ
  have hpt : ∀ v : ℝ, |v| * (1 + (c + |v|) ^ 2) ≤
      (1 + 2 * c ^ 2) * δ + ((1 + 2 * c ^ 2) * 2 / δ + 12) * (Real.exp v + Real.exp (-v) - 2) := by
    intro v
    have hH := H_ge v
    have hv0 := abs_nonneg v
    have hsq : (c + |v|) ^ 2 ≤ 2 * c ^ 2 + 2 * |v| ^ 2 := by nlinarith [sq_nonneg (c - |v|)]
    have h1 : |v| ≤ δ + |v| ^ 2 / δ := by
      rcases le_total |v| δ with h | h
      · have : 0 ≤ |v| ^ 2 / δ := by positivity
        linarith
      · have : |v| ≤ |v| ^ 2 / δ := by
          rw [le_div_iff₀ hδ]; nlinarith
        linarith
    have hv2 : |v| ^ 2 ≤ 2 * (Real.exp v + Real.exp (-v) - 2) := by
      rw [sq_abs]; nlinarith [pow_nonneg hv0 3]
    have hv3 : |v| ^ 3 ≤ 6 * (Real.exp v + Real.exp (-v) - 2) := by nlinarith [sq_nonneg v]
    have hHn : 0 ≤ Real.exp v + Real.exp (-v) - 2 := by nlinarith [sq_nonneg v, pow_nonneg hv0 3]
    have hc2 : 0 ≤ 1 + 2 * c ^ 2 := by positivity
    calc |v| * (1 + (c + |v|) ^ 2) ≤ |v| * (1 + (2 * c ^ 2 + 2 * |v| ^ 2)) := by gcongr
      _ = (1 + 2 * c ^ 2) * |v| + 2 * |v| ^ 3 := by ring
      _ ≤ (1 + 2 * c ^ 2) * (δ + |v| ^ 2 / δ) + 2 * (6 * (Real.exp v + Real.exp (-v) - 2)) := by gcongr
      _ = (1 + 2 * c ^ 2) * δ + (1 + 2 * c ^ 2) / δ * |v| ^ 2 + 12 * (Real.exp v + Real.exp (-v) - 2) := by
          ring
      _ ≤ (1 + 2 * c ^ 2) * δ + (1 + 2 * c ^ 2) / δ * (2 * (Real.exp v + Real.exp (-v) - 2)) +
            12 * (Real.exp v + Real.exp (-v) - 2) := by gcongr
      _ = (1 + 2 * c ^ 2) * δ + ((1 + 2 * c ^ 2) * 2 / δ + 12) * (Real.exp v + Real.exp (-v) - 2) := by
          ring
  have imaj : Integrable fun v => kg τ v * ((1 + 2 * c ^ 2) * δ +
      ((1 + 2 * c ^ 2) * 2 / δ + 12) * (Real.exp v + Real.exp (-v) - 2)) := by
    have := (i3.const_mul ((1 + 2 * c ^ 2) * δ)).add (iH.const_mul ((1 + 2 * c ^ 2) * 2 / δ + 12))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply]
    ring
  have hint : Integrable (fun v => kg τ v * (|v| * (1 + (c + |v|) ^ 2))) := by
    refine imaj.mono' (by unfold kg; fun_prop) (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kg_nonneg τ v hτ) (by positivity))]
    exact mul_le_mul_of_nonneg_left (hpt v) (kg_nonneg τ v hτ)
  refine ⟨hint, ?_⟩
  calc ∫ v, kg τ v * (|v| * (1 + (c + |v|) ^ 2))
      ≤ ∫ v, kg τ v * ((1 + 2 * c ^ 2) * δ + ((1 + 2 * c ^ 2) * 2 / δ + 12) *
          (Real.exp v + Real.exp (-v) - 2)) :=
        integral_mono hint imaj fun v => mul_le_mul_of_nonneg_left (hpt v) (kg_nonneg τ v hτ)
    _ = (1 + 2 * c ^ 2) * δ * (∫ v, kg τ v) +
          ((1 + 2 * c ^ 2) * 2 / δ + 12) * ∫ v, kg τ v * (Real.exp v + Real.exp (-v) - 2) := by
        have e : (fun v => kg τ v * ((1 + 2 * c ^ 2) * δ + ((1 + 2 * c ^ 2) * 2 / δ + 12) *
            (Real.exp v + Real.exp (-v) - 2))) = fun v => (1 + 2 * c ^ 2) * δ * kg τ v +
            ((1 + 2 * c ^ 2) * 2 / δ + 12) * (kg τ v * (Real.exp v + Real.exp (-v) - 2)) := by
          funext v
          ring
        rw [e, integral_add (i3.const_mul _) (iH.const_mul _), integral_const_mul, integral_const_mul]
    _ = (1 + 2 * c ^ 2) * δ + ((1 + 2 * c ^ 2) * 2 / δ + 12) * (2 * Real.exp τ - 2) := by
        rw [ATK.ZeroClasses.LittlewoodBase.integral_kg hτ, integral_kg_H hτ, mul_one]

theorem continuous_kg (τ : ℝ) : Continuous (kg τ) := by
  unfold kg
  fun_prop

theorem integrable_sq_kg {τ : ℝ} (hτ : 0 < τ) : Integrable fun v => v ^ 2 * kg τ v := by
  refine ((integrable_kg_H hτ).const_mul 2).mono' (by have := continuous_kg τ; fun_prop)
    (Eventually.of_forall fun v => ?_)
  have hH := H_ge v
  have hk := kg_nonneg τ v hτ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : v ^ 2 ≤ 2 * (Real.exp v + Real.exp (-v) - 2) := by nlinarith [pow_nonneg (abs_nonneg v) 3]
  nlinarith

theorem intervalIntegrable_F {B : ℝ} (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2)) (a b : ℝ) :
    IntervalIntegrable Fpsi volume a b :=
  IntervalIntegrable.mono_fun' (g := fun y => B * (1 + y ^ 2))
    ((by fun_prop : Continuous fun y : ℝ => B * (1 + y ^ 2)).intervalIntegrable _ _)
    ATK.ZeroClasses.LittlewoodBase.measurable_Fpsi.aestronglyMeasurable
    (Eventually.of_forall fun y => by show ‖Fpsi y‖ ≤ B * (1 + y ^ 2); rw [Real.norm_eq_abs]; exact hB y)

theorem abs_le_of_mem_uIoc {p q x : ℝ} (h : x ∈ Ι p q) : |x| ≤ max |p| |q| := by
  rcases Set.mem_uIoc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · rw [abs_le]
    constructor <;> linarith [le_abs_self p, neg_abs_le p, le_abs_self q, neg_abs_le q,
      le_max_left |p| |q|, le_max_right |p| |q|]

/-- `|∫ₐᵇ F − ∫ₐᵇ F(u − v) du| ≤ 2B|v|(1 + (c + |v|)²)` se `|a|, |b| ≤ c`. -/
theorem dif_desloc_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2)) {a b c : ℝ}
    (ha : |a| ≤ c) (hb : |b| ≤ c) (v : ℝ) :
    |(∫ u in a..b, Fpsi u) - ∫ u in a..b, Fpsi (u - v)| ≤ 2 * B * (|v| * (1 + (c + |v|) ^ 2)) := by
  have hI := intervalIntegrable_F hB
  rw [intervalIntegral.integral_comp_sub_right (fun u => Fpsi u) v,
    intervalIntegral.integral_interval_sub_interval_comm (hI a b) (hI (a - v) (b - v)) (hI a (a - v))]
  have hK : ∀ p : ℝ, |p| ≤ c → ∀ x ∈ Ι p (p - v), ‖Fpsi x‖ ≤ B * (1 + (c + |v|) ^ 2) := by
    intro p hp x hx
    have h1 := abs_le_of_mem_uIoc hx
    have h2 : |p - v| ≤ c + |v| := (abs_sub _ _).trans (by linarith)
    have h3 : |x| ≤ c + |v| := h1.trans (max_le (by linarith [abs_nonneg v]) h2)
    have h4 : x ^ 2 ≤ (c + |v|) ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg x) h3 2
    rw [Real.norm_eq_abs]
    calc |Fpsi x| ≤ B * (1 + x ^ 2) := hB x
      _ ≤ B * (1 + (c + |v|) ^ 2) := by gcongr
  have e1 := intervalIntegral.norm_integral_le_of_norm_le_const (hK a ha)
  have e2 := intervalIntegral.norm_integral_le_of_norm_le_const (hK b hb)
  rw [Real.norm_eq_abs] at e1 e2
  have ha' : |a - v - a| = |v| := by rw [sub_sub_cancel_left, abs_neg]
  have hb' : |b - v - b| = |v| := by rw [sub_sub_cancel_left, abs_neg]
  rw [ha'] at e1
  rw [hb'] at e2
  calc |(∫ x in a..a - v, Fpsi x) - ∫ x in b..b - v, Fpsi x|
      ≤ |∫ x in a..a - v, Fpsi x| + |∫ x in b..b - v, Fpsi x| := abs_sub _ _
    _ ≤ B * (1 + (c + |v|) ^ 2) * |v| + B * (1 + (c + |v|) ^ 2) * |v| := add_le_add e1 e2
    _ = 2 * B * (|v| * (1 + (c + |v|) ^ 2)) := by ring

/-- **Fubini para a média gaussiana**: `∫ₐᵇ (k_τ * F) = ∫ k_τ(v) ∫ₐᵇ F(u − v) du dv`. -/
theorem fubini_kF {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2)) {τ : ℝ} (hτ : 0 < τ)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun u => ∫ v, kg τ v * Fpsi (u - v)) volume a b ∧
    (∫ u in a..b, ∫ v, kg τ v * Fpsi (u - v)) = ∫ v, kg τ v * ∫ u in a..b, Fpsi (u - v) ∧
    Integrable (fun v => kg τ v * ∫ u in a..b, Fpsi (u - v)) := by
  have : IsFiniteMeasure (volume.restrict (Ι a b)) := by rw [Set.uIoc_of_le hab]; infer_instance
  have i3 := ATK.ZeroClasses.LittlewoodBase.integrable_kg hτ
  have h1 : Integrable (fun x : ℝ => 1 + 2 * x ^ 2) (volume.restrict (Ι a b)) := by
    have : IntegrableOn (fun x : ℝ => 1 + 2 * x ^ 2) (Set.uIcc a b) :=
      (by fun_prop : Continuous fun x : ℝ => 1 + 2 * x ^ 2).integrableOn_uIcc
    exact this.mono_set Set.uIoc_subset_uIcc
  have I1 := h1.mul_prod i3
  have I2 := (integrable_const (1 : ℝ) (μ := volume.restrict (Ι a b))).mul_prod (integrable_sq_kg hτ)
  have hmeas : Measurable fun p : ℝ × ℝ => kg τ p.2 * Fpsi (p.1 - p.2) :=
    ((continuous_kg τ).measurable.comp measurable_snd).mul
      (ATK.ZeroClasses.LittlewoodBase.measurable_Fpsi.comp (measurable_fst.sub measurable_snd))
  have hint : Integrable (Function.uncurry fun u v => kg τ v * Fpsi (u - v))
      ((volume.restrict (Ι a b)).prod volume) := by
    refine ((I1.const_mul B).add (I2.const_mul (2 * B))).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    show ‖kg τ p.2 * Fpsi (p.1 - p.2)‖ ≤
      B * ((1 + 2 * p.1 ^ 2) * kg τ p.2) + 2 * B * (1 * (p.2 ^ 2 * kg τ p.2))
    rw [Real.norm_eq_abs]
    have hk := kg_nonneg τ p.2 hτ
    rw [abs_mul, abs_of_nonneg hk]
    have hF := hB (p.1 - p.2)
    have hsq : (p.1 - p.2) ^ 2 ≤ 2 * p.1 ^ 2 + 2 * p.2 ^ 2 := by nlinarith [sq_nonneg (p.1 + p.2)]
    calc kg τ p.2 * |Fpsi (p.1 - p.2)| ≤ kg τ p.2 * (B * (1 + (p.1 - p.2) ^ 2)) :=
          mul_le_mul_of_nonneg_left hF hk
      _ ≤ kg τ p.2 * (B * (1 + (2 * p.1 ^ 2 + 2 * p.2 ^ 2))) := by gcongr
      _ = B * ((1 + 2 * p.1 ^ 2) * kg τ p.2) + 2 * B * (1 * (p.2 ^ 2 * kg τ p.2)) := by ring
  have hswap := MeasureTheory.intervalIntegral_integral_swap hint
  refine ⟨?_, ?_, ?_⟩
  · rw [intervalIntegrable_iff]
    exact hint.integral_prod_left
  · rw [hswap]
    congr 1
    funext v
    rw [intervalIntegral.integral_const_mul]
  · have h := hint.integral_prod_right
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [Set.uIoc_of_le hab, integral_const_mul, intervalIntegral.integral_of_le hab]

/-- **A aproximação**: `|∫ₐᵇ F − ∫ₐᵇ (k_τ * F)| ≤ 2B ∫ k_τ(v)|v|(1 + (c + |v|)²) dv` se `|a|, |b| ≤ c`. -/
theorem aprox_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2)) {τ : ℝ} (hτ : 0 < τ)
    {a b c : ℝ} (hab : a ≤ b) (ha : |a| ≤ c) (hb : |b| ≤ c) :
    |(∫ u in a..b, Fpsi u) - ∫ u in a..b, ∫ v, kg τ v * Fpsi (u - v)| ≤
      2 * B * ∫ v, kg τ v * (|v| * (1 + (c + |v|) ^ 2)) := by
  obtain ⟨-, hfub, hintI⟩ := fubini_kF hB0 hB hτ hab
  have hc : 0 ≤ c := (abs_nonneg a).trans ha
  obtain ⟨hmom, -⟩ := momento_le hτ hc one_pos
  have i3 := ATK.ZeroClasses.LittlewoodBase.integrable_kg hτ
  have e0 : ∫ u in a..b, Fpsi u = ∫ v, kg τ v * ∫ u in a..b, Fpsi u := by
    rw [integral_mul_const, ATK.ZeroClasses.LittlewoodBase.integral_kg hτ, one_mul]
  have i0 : Integrable fun v => kg τ v * ∫ u in a..b, Fpsi u := i3.mul_const _
  rw [hfub, e0, ← integral_sub i0 hintI, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono (i0.sub hintI).norm (hmom.const_mul _) fun v => ?_
  have hk := kg_nonneg τ v hτ
  simp only [Real.norm_eq_abs]
  rw [← mul_sub, abs_mul, abs_of_nonneg hk]
  calc kg τ v * |(∫ u in a..b, Fpsi u) - ∫ u in a..b, Fpsi (u - v)|
      ≤ kg τ v * (2 * B * (|v| * (1 + (c + |v|) ^ 2))) :=
        mul_le_mul_of_nonneg_left (dif_desloc_le hB0 hB ha hb v) hk
    _ = 2 * B * (kg τ v * (|v| * (1 + (c + |v|) ^ 2))) := by ring

theorem pot_exp_le {a : ℝ} (ha : 1 ≤ a) : a ^ 5 * Real.exp (-(a / 2)) ≤ 46080 := by
  have h := Real.pow_div_factorial_le_exp (a / 2) (by positivity) 6
  norm_num [Nat.factorial] at h
  have he : 0 < Real.exp (a / 2) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ he]
  have h6 : a ^ 6 ≤ 46080 * Real.exp (a / 2) := by
    have : (a / 2) ^ 6 = a ^ 6 / 64 := by ring
    rw [this] at h
    linarith
  nlinarith [pow_pos (by linarith : (0 : ℝ) < a) 5]

theorem cota_Xi {B a : ℝ} (hB0 : 0 ≤ B) (ha : 1 ≤ a) :
    4 * (2 * B * ((1 + 2 * (2 * a) ^ 2) * 2 / (1 / (2 * B * (1 + 2 * (2 * a) ^ 2) + 1)) + 12)) + 4 ≤
      (8 * B * (18 * (18 * B + 1) + 12) + 4) * a ^ 4 := by
  rw [div_div_eq_mul_div, div_one]
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have h4 : 1 ≤ a ^ 4 := by nlinarith
  have hc2 : 1 + 2 * (2 * a) ^ 2 ≤ 9 * a ^ 2 := by nlinarith
  have hΛ : 2 * B * (1 + 2 * (2 * a) ^ 2) + 1 ≤ (18 * B + 1) * a ^ 2 := by nlinarith
  have hm : (1 + 2 * (2 * a) ^ 2) * (2 * B * (1 + 2 * (2 * a) ^ 2) + 1) ≤ 9 * (18 * B + 1) * a ^ 4 := by
    have := mul_le_mul hc2 hΛ (by positivity) (by positivity)
    nlinarith
  have hB12 : 0 ≤ B * (a ^ 4 - 1) := mul_nonneg hB0 (by linarith)
  have hBm := mul_le_mul_of_nonneg_left hm hB0
  nlinarith

/-! ## 4. `∫ₐᵇ F = O(1)` em intervalos diádicos, sob RH -/

/-- **Sob RH, `|∫ₐᵇ F(u) du| ≤ C` para `1 ≤ a ≤ b ≤ 2a`.** -/
theorem integral_F_diadico (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 * a →
    |∫ u in a..b, Fpsi u| ≤ C := by
  obtain ⟨C₀, hC₀, hts⟩ := integral_tsum_le hRH
  obtain ⟨B, hB0, hB⟩ := ATK.ZeroClasses.LittlewoodBase.Fpsi_le_RH hRH
  obtain ⟨K, hK0, hK⟩ := ATK.ZeroClasses.LittlewoodMontagem.resto_le
  set D := 8 * B * (18 * (18 * B + 1) + 12) + 4 with hD
  refine ⟨3 * C₀ + K * D * 46080 + 2, by positivity, fun a b ha hab hb2 => ?_⟩
  have ha0 : 0 < a := by linarith
  set c := 2 * a with hc
  have hac : |a| ≤ c := by rw [abs_of_pos ha0]; linarith
  have hbc : |b| ≤ c := by rw [abs_of_pos (by linarith)]; linarith
  have hc0 : 0 ≤ c := by linarith
  set Λ := 2 * B * (1 + 2 * c ^ 2) + 1 with hΛ
  have hΛ1 : 1 ≤ Λ := by have : 0 ≤ 2 * B * (1 + 2 * c ^ 2) := by positivity
                         linarith
  set δ := 1 / Λ with hδ
  have hδ0 : 0 < δ := by positivity
  set Ξ := 2 * B * ((1 + 2 * c ^ 2) * 2 / δ + 12) with hΞ
  have hΞ0 : 0 ≤ Ξ := by positivity
  set τ := 1 / (4 * Ξ + 4) with hτd
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [hτd, div_le_one (by positivity)]; linarith
  -- o erro de aproximação é `≤ 2`
  obtain ⟨-, hmom⟩ := momento_le hτ0 hc0 hδ0
  have hexp : 2 * Real.exp τ - 2 ≤ 4 * τ := by
    have := Real.abs_exp_sub_one_le (x := τ) (by rw [abs_of_pos hτ0]; exact hτ1)
    rw [abs_of_pos hτ0] at this
    linarith [le_abs_self (Real.exp τ - 1)]
  have herr : 2 * B * ∫ v, kg τ v * (|v| * (1 + (c + |v|) ^ 2)) ≤ 2 := by
    have h1 : 2 * B * ((1 + 2 * c ^ 2) * δ) ≤ 1 := by
      rw [hδ, ← mul_div_assoc, mul_one, ← mul_div_assoc, div_le_one (by positivity)]
      linarith
    have h2 : Ξ * (2 * Real.exp τ - 2) ≤ 1 := by
      calc Ξ * (2 * Real.exp τ - 2) ≤ Ξ * (4 * τ) := mul_le_mul_of_nonneg_left hexp hΞ0
        _ = 4 * Ξ / (4 * Ξ + 4) := by rw [hτd]; ring
        _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc 2 * B * ∫ v, kg τ v * (|v| * (1 + (c + |v|) ^ 2))
        ≤ 2 * B * ((1 + 2 * c ^ 2) * δ + ((1 + 2 * c ^ 2) * 2 / δ + 12) * (2 * Real.exp τ - 2)) :=
          mul_le_mul_of_nonneg_left hmom (by positivity)
      _ = 2 * B * ((1 + 2 * c ^ 2) * δ) + Ξ * (2 * Real.exp τ - 2) := by rw [hΞ]; ring
      _ ≤ 2 := by linarith
  have hap := aprox_le hB0 hB hτ0 hab hac hbc
  -- a média gaussiana: `k_τ * F = R − Σ_ρ`
  obtain ⟨hkF, -, -⟩ := fubini_kF hB0 hB hτ0 hab
  obtain ⟨htsI, htsB⟩ := hts τ a b hτ0
  have hfun : (fun u => ∫ v, kg τ v * Fpsi (u - v)) = fun u => Resto u τ - ∑' ρ : Zs, gz u τ ρ := by
    funext u
    rw [tsum_gz hRH hτ0 u]
    ring
  have hRI : IntervalIntegrable (fun u => Resto u τ) volume a b := by
    have e : (fun u => Resto u τ) = fun u => (∫ v, kg τ v * Fpsi (u - v)) + ∑' ρ : Zs, gz u τ ρ := by
      funext u
      rw [tsum_gz hRH hτ0 u]
      ring
    rw [e]
    exact hkF.add htsI
  have hkF' : ∫ u in a..b, ∫ v, kg τ v * Fpsi (u - v) =
      (∫ u in a..b, Resto u τ) - ∫ u in a..b, ∑' ρ : Zs, gz u τ ρ := by
    rw [hfun, intervalIntegral.integral_sub hRI htsI]
  -- o resto
  have hRb : |∫ u in a..b, Resto u τ| ≤ K * D * 46080 := by
    have hpt : ∀ x ∈ Ι a b, ‖Resto x τ‖ ≤ K / τ * Real.exp (-(a / 2)) := by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      refine (hK x τ hτ0 hτ1 (by linarith [hx.1])).trans ?_
      gcongr
      linarith [hx.1]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
    have hinvτ : 1 / τ ≤ D * a ^ 4 := by
      rw [hτd, one_div_one_div]
      exact cota_Xi hB0 ha
    have hba : b - a ≤ a := by linarith
    calc |∫ u in a..b, Resto u τ| ≤ K / τ * Real.exp (-(a / 2)) * (b - a) := h
      _ ≤ K * (D * a ^ 4) * Real.exp (-(a / 2)) * a := by
          have : K / τ ≤ K * (D * a ^ 4) := by
            rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinvτ hK0
          gcongr
      _ = K * D * (a ^ 5 * Real.exp (-(a / 2))) := by ring
      _ ≤ K * D * 46080 := by
          have : 0 ≤ K * D := by positivity
          exact mul_le_mul_of_nonneg_left (pot_exp_le ha) this
  -- juntando
  rw [hkF'] at hap
  have h3 : |(∫ u in a..b, Resto u τ) - ∫ u in a..b, ∑' ρ : Zs, gz u τ ρ| ≤ K * D * 46080 + 3 * C₀ :=
    (abs_sub _ _).trans (add_le_add hRb htsB)
  have := abs_sub_abs_le_abs_sub (∫ u in a..b, Fpsi u)
    ((∫ u in a..b, Resto u τ) - ∫ u in a..b, ∑' ρ : Zs, gz u τ ρ)
  linarith

/-! ## 5. Intervalos quaisquer: `|∫ₐᵇ F| ≤ C(1 + log b)` -/

theorem integral_F_pot (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a b : ℝ), 1 ≤ a → a ≤ b →
    b ≤ 2 ^ n * a → |∫ u in a..b, Fpsi u| ≤ (n + 1) * C := by
  obtain ⟨C, hC0, hC⟩ := integral_F_diadico hRH
  obtain ⟨B, hB0, hB⟩ := ATK.ZeroClasses.LittlewoodBase.Fpsi_le_RH hRH
  refine ⟨C, hC0, fun n => ?_⟩
  induction n with
  | zero =>
    intro a b ha hab hb
    rw [pow_zero, one_mul] at hb
    have e : b = a := le_antisymm hb hab
    rw [e, intervalIntegral.integral_same, abs_zero]
    positivity
  | succ n ih =>
    intro a b ha hab hb
    rcases le_or_gt b (2 * a) with h | h
    · have h1 := hC a b ha hab h
      have : C ≤ ((n + 1 : ℕ) + 1 : ℝ) * C := by
        have : (1 : ℝ) ≤ ((n + 1 : ℕ) + 1 : ℝ) := by push_cast; linarith [n.cast_nonneg (α := ℝ)]
        nlinarith
      linarith
    · rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_F hB a (2 * a))
        (intervalIntegrable_F hB (2 * a) b)]
      have h1 := hC a (2 * a) ha (by linarith) le_rfl
      have h2 := ih (2 * a) b (by linarith) h.le (by rw [pow_succ] at hb; linarith)
      calc |(∫ u in a..2 * a, Fpsi u) + ∫ u in 2 * a..b, Fpsi u|
          ≤ |∫ u in a..2 * a, Fpsi u| + |∫ u in 2 * a..b, Fpsi u| := abs_add_le _ _
        _ ≤ C + (n + 1) * C := add_le_add h1 h2
        _ = ((n + 1 : ℕ) + 1) * C := by push_cast; ring

/-- **Sob RH, `|∫ₐᵇ F(u) du| ≤ C(1 + log b)` para `1 ≤ a ≤ b`.** -/
theorem integral_F_log (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b →
    |∫ u in a..b, Fpsi u| ≤ C * (1 + Real.log b) := by
  obtain ⟨C, hC0, hC⟩ := integral_F_pot hRH
  refine ⟨2 * C, by positivity, fun a b ha hab => ?_⟩
  have hb1 : 1 ≤ b := ha.trans hab
  have hb0 : 0 < b := by linarith
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hl0 : 0 ≤ Real.logb 2 b := Real.logb_nonneg (by norm_num) hb1
  set n := ⌈Real.logb 2 b⌉₊ with hn
  have hpow : b ≤ 2 ^ n * a := by
    have h1 : b = (2 : ℝ) ^ Real.logb 2 b := (Real.rpow_logb (by norm_num) (by norm_num) hb0).symm
    have h2 : (2 : ℝ) ^ Real.logb 2 b ≤ (2 : ℝ) ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    rw [Real.rpow_natCast] at h2
    have h3 : (2 : ℝ) ^ n ≤ 2 ^ n * a := le_mul_of_one_le_right (by positivity) ha
    linarith
  have hn1 : (n : ℝ) + 1 ≤ 2 * (1 + Real.log b) := by
    have h1 := Nat.ceil_lt_add_one hl0
    have h2 : Real.logb 2 b ≤ 2 * Real.log b := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have := Real.log_two_gt_d9
      nlinarith
    linarith
  calc |∫ u in a..b, Fpsi u| ≤ (n + 1) * C := hC n a b ha hab hpow
    _ ≤ 2 * (1 + Real.log b) * C := mul_le_mul_of_nonneg_right hn1 hC0
    _ = 2 * C * (1 + Real.log b) := by ring

end ATK.ZeroClasses.LittlewoodMedia

#print axioms ATK.ZeroClasses.LittlewoodMedia.norm_pw_RH
#print axioms ATK.ZeroClasses.LittlewoodMedia.norm_mul_exp_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.summable_gauss
#print axioms ATK.ZeroClasses.LittlewoodMedia.abs_gz_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.summable_gz
#print axioms ATK.ZeroClasses.LittlewoodMedia.tendsto_Zfin
#print axioms ATK.ZeroClasses.LittlewoodMedia.tsum_gz
#print axioms ATK.ZeroClasses.LittlewoodMedia.sum_Zfin_le_tsum
#print axioms ATK.ZeroClasses.LittlewoodMedia.continuous_re_pw
#print axioms ATK.ZeroClasses.LittlewoodMedia.integral_re_pw_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.continuous_Sn
#print axioms ATK.ZeroClasses.LittlewoodMedia.integral_Sn_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.integral_tsum_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.H_ge
#print axioms ATK.ZeroClasses.LittlewoodMedia.integrable_kg_H
#print axioms ATK.ZeroClasses.LittlewoodMedia.integral_kg_H
#print axioms ATK.ZeroClasses.LittlewoodMedia.momento_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.continuous_kg
#print axioms ATK.ZeroClasses.LittlewoodMedia.integrable_sq_kg
#print axioms ATK.ZeroClasses.LittlewoodMedia.intervalIntegrable_F
#print axioms ATK.ZeroClasses.LittlewoodMedia.abs_le_of_mem_uIoc
#print axioms ATK.ZeroClasses.LittlewoodMedia.dif_desloc_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.fubini_kF
#print axioms ATK.ZeroClasses.LittlewoodMedia.aprox_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.pot_exp_le
#print axioms ATK.ZeroClasses.LittlewoodMedia.cota_Xi
#print axioms ATK.ZeroClasses.LittlewoodMedia.integral_F_diadico
#print axioms ATK.ZeroClasses.LittlewoodMedia.integral_F_pot
#print axioms ATK.ZeroClasses.LittlewoodMedia.integral_F_log
