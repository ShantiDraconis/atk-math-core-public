import ATK.HadamardGenero0
import ATK.XiTP
import ATK.XiPhi

/-!
# ATK — **HR ⟺ PF∞ dos coeficientes de Ξ** (no kernel, as duas direções)

`Ξ(t) = Σ (−1)ⁿ aₙ t²ⁿ` e `B(w) = Σ aₙ wⁿ` (`ATK.XiTP.aXi`), com `B(−z²) = ξ(1/2 + iz)`.

**Teorema (`rh_iff_tn`)**: `RiemannHypothesis ↔ (toep aXi).IsTotallyNonneg` — HR equivale a todos os
menores de Toeplitz `det(a_{i_p − j_q})` serem `≥ 0` (`rh_iff_menores`).

* (⇐) `ATK.XiTP.rh_de_tn` (Edrei para funções inteiras, rodada 10).
* (⇒) `tn_de_rh`: sob HR, `B` só tem zeros reais negativos (`zerosNeg_of_rh`) e tem ordem `≤ 3/4`:
  `|B(w)| ≤ 320·exp(320·|w|^{3/4})` (`crescimento_B`), via a representação `ξ(1/2 + iz) = 2∫₀^∞Φ(u)cos(zu)du`
  estendida a `z` complexo (`HPhi`, holomorfia sob a integral e princípio de identidade, `gXi_eq_HPhi`) e a
  cota forte `|Φ(u)| ≤ 160·e^{u/2 − (3/2)e^{2u}}` (`Phi_cota`). Então `ATK.Hadamard.hadamard_tn` (Hadamard
  de gênero 0) dá a positividade total.

**Estado**: isto é uma **equivalência**, não uma prova de HR. A positividade total dos `aₙ` continua
**`OPEN_MATH`** — é exatamente HR.
-/

open Complex Filter Topology Metric Set MeasureTheory
open scoped Nat

namespace ATK.XiCresc

open ATK.Edrei ATK.Hadamard ATK.XiTP ATK.BaseRiemannXi
open ATK.XiPhi (Phi phiT cN hT)
open ATK.ToeplitzTN (toep)

/-! ## 1. Cota forte para `Φ` -/

theorem phiT_cota_forte (c u : ℝ) (hc : 3 / 2 ≤ c) :
    |phiT c u| ≤ 80 * Real.exp (u / 2 - c / 2 * Real.exp (2 * u)) := by
  set w := c * Real.exp (2 * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; have := Real.exp_pos (2 * u); nlinarith
  have h2 := ATK.XiPhi.pow_le_exp_half hw0 (k := 2) le_rfl
  have h1 := ATK.XiPhi.pow_le_exp_half hw0 (k := 1) (by norm_num)
  have e : phiT c u = (4 * w ^ 2 - 6 * w) * Real.exp (u / 2 - w) := by
    unfold phiT hT
    rw [hw]
  rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
  have habs : |4 * w ^ 2 - 6 * w| ≤ 80 * Real.exp (w / 2) := by
    rw [abs_le]
    constructor <;> nlinarith [Real.exp_pos (w / 2)]
  calc |4 * w ^ 2 - 6 * w| * Real.exp (u / 2 - w) ≤ 80 * Real.exp (w / 2) * Real.exp (u / 2 - w) :=
        mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ = 80 * Real.exp (u / 2 - c / 2 * Real.exp (2 * u)) := by
        rw [mul_assoc, ← Real.exp_add, hw]
        congr 2
        ring

/-- **`|Φ(u)| ≤ 160·e^{u/2 − (3/2)e^{2u}}`** para `u ≥ 0`. -/
theorem Phi_cota {u : ℝ} (hu : 0 ≤ u) :
    |Phi u| ≤ 160 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) := by
  have hE : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hq : Real.exp (-(3 / 2)) < 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    have h32 : (2 : ℝ) < Real.exp (3 / 2) := by
      have := Real.add_one_le_exp (3 / 2 : ℝ)
      linarith
    linarith
  have hb : ∀ n : ℕ, |phiT (cN n) u| ≤
      80 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) * Real.exp (-(3 / 2)) ^ n := by
    intro n
    refine (phiT_cota_forte _ u (ATK.XiPhi.cN_ge n)).trans ?_
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : (3 : ℝ) * ((n : ℝ) + 1) ≤ cN n := by
      unfold cN
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      nlinarith [Real.pi_gt_three]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith
  have hsg : Summable fun n : ℕ => 80 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) *
      Real.exp (-(3 / 2)) ^ n :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le (by linarith)).mul_left _
  have hb' : ∀ n : ℕ, ‖phiT (cN n) u‖ ≤
      80 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) * Real.exp (-(3 / 2)) ^ n := fun n => by
    rw [Real.norm_eq_abs]
    exact hb n
  have hsn : Summable fun n => ‖phiT (cN n) u‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb' hsg
  calc |Phi u| = ‖∑' n, phiT (cN n) u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖phiT (cN n) u‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, 80 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) * Real.exp (-(3 / 2)) ^ n :=
        Summable.tsum_le_tsum hb' hsn hsg
    _ = 80 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) * (1 - Real.exp (-(3 / 2)))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le (by linarith)]
    _ ≤ 160 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) := by
        have h2 : (1 - Real.exp (-(3 / 2)))⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        have := Real.exp_pos (u / 2 - 3 / 2 * Real.exp (2 * u))
        nlinarith

theorem continuousOn_Phi : ContinuousOn Phi (Ici 0) := by
  refine continuousOn_tsum (u := fun n => 80 * Real.exp (-(cN n / 2)))
    (fun n => (ATK.XiPhi.continuous_phiT _).continuousOn)
    (ATK.XiPhi.summable_exp_cN.mul_left 80) fun n u hu => ?_
  rw [Real.norm_eq_abs]
  have := ATK.XiPhi.cota_phiT (cN n) u (ATK.XiPhi.cN_ge n) hu
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ici.mp hu])
  have h2 := Real.exp_pos (-(cN n / 2))
  nlinarith

/-- `u/2 − (3/2)e^{2u} + yu ≤ y√y − u` (`y, u ≥ 0`). -/
theorem expoente_le {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) :
    u / 2 - 3 / 2 * Real.exp (2 * u) + y * u ≤ y * Real.sqrt y - u := by
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have h3 : (2 * u) ^ 3 / 6 ≤ Real.exp (2 * u) := by
    have := Real.pow_div_factorial_le_exp (2 * u) (by linarith) 3
    simpa [Nat.factorial] using this
  have hkey : y * u - u ^ 3 ≤ y * Real.sqrt y := by
    rcases le_total u (Real.sqrt y) with h | h
    · have := mul_le_mul_of_nonneg_left h hy
      nlinarith [pow_nonneg hu 3]
    · have hsq : y ≤ u ^ 2 := by
        have := Real.sq_sqrt hy
        nlinarith [Real.sqrt_nonneg y]
      have : y * u - u ^ 3 = u * (y - u ^ 2) := by ring
      rw [this]
      have : u * (y - u ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu (by linarith)
      have : 0 ≤ y * Real.sqrt y := mul_nonneg hy (Real.sqrt_nonneg y)
      linarith
  nlinarith

/-- `|Φ(u)|·e^{yu} ≤ 160·e^{y√y}·e^{−u}` (`y, u ≥ 0`). -/
theorem Phi_exp_cota {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) :
    |Phi u| * Real.exp (y * u) ≤ 160 * Real.exp (y * Real.sqrt y) * Real.exp (-u) := by
  calc |Phi u| * Real.exp (y * u) ≤ 160 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u)) *
        Real.exp (y * u) := mul_le_mul_of_nonneg_right (Phi_cota hu) (Real.exp_pos _).le
    _ = 160 * Real.exp (u / 2 - 3 / 2 * Real.exp (2 * u) + y * u) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ 160 * Real.exp (y * Real.sqrt y - u) := by
        gcongr
        exact expoente_le hy hu
    _ = 160 * Real.exp (y * Real.sqrt y) * Real.exp (-u) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

/-! ## 2. `Ξ` em `z` complexo: `HPhi(z) = 2∫₀^∞Φ(u)cos(zu)du` -/

theorem norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  have h : ∀ v : ℂ, ‖Complex.exp v‖ ≤ Real.exp ‖v‖ := fun v => by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (Complex.re_le_norm v)
  rw [Complex.cos, norm_div, Complex.norm_ofNat]
  have h1 := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  have h2 := h (w * I)
  have h3 := h (-w * I)
  rw [norm_mul, Complex.norm_I, mul_one] at h2
  rw [norm_mul, Complex.norm_I, mul_one, norm_neg] at h3
  linarith

theorem norm_sin_le (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp ‖w‖ := by
  have h : ∀ v : ℂ, ‖Complex.exp v‖ ≤ Real.exp ‖v‖ := fun v => by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (Complex.re_le_norm v)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have h1 := norm_sub_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  have h2 := h (w * I)
  have h3 := h (-w * I)
  rw [norm_mul, Complex.norm_I, mul_one] at h2
  rw [norm_mul, Complex.norm_I, mul_one, norm_neg] at h3
  linarith

/-- `HPhi(z) = 2∫₀^∞ Φ(u)cos(zu)du`. -/
noncomputable def HPhi (z : ℂ) : ℂ := 2 * ∫ u in Ioi (0 : ℝ), (Phi u : ℂ) * Complex.cos (z * u)

theorem aesm_F (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (Phi u : ℂ) * Complex.cos (z * u)) (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine (Complex.continuous_ofReal.comp_continuousOn (continuousOn_Phi.mono Ioi_subset_Ici_self)).mul ?_
  exact (by fun_prop : Continuous fun u : ℝ => Complex.cos (z * u)).continuousOn

theorem integrable_F (z : ℂ) :
    Integrable (fun u : ℝ => (Phi u : ℂ) * Complex.cos (z * u)) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' (ATK.XiPhi.integrableOn_exp_neg_mul
    (160 * Real.exp (‖z‖ * Real.sqrt ‖z‖))) (aesm_F z) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc : ‖Complex.cos (z * u)‖ ≤ Real.exp (‖z‖ * u) := by
    refine (norm_cos_le _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
  calc |Phi u| * ‖Complex.cos (z * u)‖ ≤ |Phi u| * Real.exp (‖z‖ * u) :=
        mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ ≤ 160 * Real.exp (‖z‖ * Real.sqrt ‖z‖) * Real.exp (-u) := Phi_exp_cota (norm_nonneg z) hu0

theorem hasDerivAt_HPhi (z₀ : ℂ) : HasDerivAt HPhi
    (2 * ∫ u in Ioi (0 : ℝ), (Phi u : ℂ) * (-Complex.sin (z₀ * u) * u)) z₀ := by
  set Y := ‖z₀‖ + 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z u => (Phi u : ℂ) * Complex.cos (z * u))
    (F' := fun z u => (Phi u : ℂ) * (-Complex.sin (z * u) * u))
    (bound := fun u => 160 * Real.exp (Y * Real.sqrt Y) * Real.exp (-u))
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall fun z => aesm_F z) (integrable_F z₀)
    ?_ ?_ (ATK.XiPhi.integrableOn_exp_neg_mul _) ?_
  · exact key.2.const_mul 2
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_Phi.mono Ioi_subset_Ici_self)).mul ?_
    exact (by fun_prop : Continuous fun u : ℝ => -Complex.sin (z₀ * u) * u).continuousOn
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu z hz => ?_
    have hu0 : 0 ≤ u := le_of_lt hu
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := mem_ball_iff_norm.mp hz
      have h2 := norm_le_insert' z z₀
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hu0]
    have hs : ‖Complex.sin (z * u)‖ ≤ Real.exp ((‖z₀‖ + 1) * u) := by
      refine (norm_sin_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      exact mul_le_mul_of_nonneg_right hzn hu0
    have hu1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hprod : ‖Complex.sin (z * u)‖ * u ≤ Real.exp (Y * u) := by
      calc ‖Complex.sin (z * u)‖ * u ≤ Real.exp ((‖z₀‖ + 1) * u) * Real.exp u :=
            mul_le_mul hs hu1 hu0 (Real.exp_pos _).le
        _ = Real.exp (Y * u) := by rw [← Real.exp_add, hY]; ring_nf
    calc |Phi u| * (‖Complex.sin (z * u)‖ * u) ≤ |Phi u| * Real.exp (Y * u) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ ≤ 160 * Real.exp (Y * Real.sqrt Y) * Real.exp (-u) := Phi_exp_cota hY0 hu0
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => z * u) (u : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (u : ℂ)
    have h2 := (Complex.hasDerivAt_cos (z * u)).comp z h1
    have h3 := h2.const_mul (Phi u : ℂ)
    simpa [mul_comm, mul_assoc, mul_left_comm] using h3

theorem HPhi_differentiable : Differentiable ℂ HPhi := fun z => (hasDerivAt_HPhi z).differentiableAt

theorem HPhi_ofReal (t : ℝ) : HPhi t = (Xi t : ℂ) := by
  rw [ATK.XiPhi.Xi_dois_Phi, HPhi]
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  rfl

/-- **`ξ(1/2 + iz) = 2∫₀^∞Φ(u)cos(zu)du` para todo `z ∈ ℂ`** (princípio de identidade). -/
theorem gXi_eq_HPhi : gXi = HPhi := by
  have hf : AnalyticOnNhd ℂ gXi univ := fun z _ => gXi_differentiable.analyticAt z
  have hg : AnalyticOnNhd ℂ HPhi univ := fun z _ => HPhi_differentiable.analyticAt z
  have hseq : Tendsto (fun n : ℕ => (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [Complex.ofReal_zero] at h1
      exact h1
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), gXi z = HPhi z :=
    hseq.frequently (Frequently.of_forall fun n => by rw [gXi_ofReal, HPhi_ofReal])
  funext z
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (mem_univ 0) hfreq (mem_univ z)

/-- **Ordem de `ξ`**: `|ξ(1/2 + iz)| ≤ 320·e^{|z|√|z|}`. -/
theorem norm_gXi_le (z : ℂ) : ‖gXi z‖ ≤ 320 * Real.exp (‖z‖ * Real.sqrt ‖z‖) := by
  rw [gXi_eq_HPhi, HPhi, norm_mul, Complex.norm_ofNat]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun u : ℝ => (Phi u : ℂ) * Complex.cos (z * u)) (ATK.XiPhi.integrableOn_exp_neg_mul
    (160 * Real.exp (‖z‖ * Real.sqrt ‖z‖)))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
      have hu0 : 0 ≤ u := le_of_lt hu
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc : ‖Complex.cos (z * u)‖ ≤ Real.exp (‖z‖ * u) := by
        refine (norm_cos_le _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      calc |Phi u| * ‖Complex.cos (z * u)‖ ≤ |Phi u| * Real.exp (‖z‖ * u) :=
            mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ ≤ 160 * Real.exp (‖z‖ * Real.sqrt ‖z‖) * Real.exp (-u) :=
            Phi_exp_cota (norm_nonneg z) hu0)
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at h
  linarith

/-! ## 3. `B(w) = Σaₙwⁿ`: crescimento e zeros sob HR -/

theorem existe_raiz (w : ℂ) : ∃ z : ℂ, -z ^ 2 = w := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-w) two_pos
  exact ⟨z, by rw [hz, neg_neg]⟩

/-- **`|B(w)| ≤ 320·exp(320·|w|^{3/4})`** — ordem `≤ 3/4 < 1` (a forma `A·exp(A·|w|^σ)` pedida por
`ATK.Hadamard.hadamard_tn`). -/
theorem crescimento_B (w : ℂ) : ‖ev aXi w‖ ≤ 320 * Real.exp (320 * ‖w‖ ^ (3 / 4 : ℝ)) := by
  obtain ⟨z, rfl⟩ := existe_raiz w
  rw [ev_aXi]
  refine (norm_gXi_le z).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hz : ‖-z ^ 2‖ = ‖z‖ ^ 2 := by rw [norm_neg, norm_pow]
  rw [hz]
  have e : ‖z‖ * Real.sqrt ‖z‖ = (‖z‖ ^ 2) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    norm_num
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' (norm_nonneg z) (by norm_num),
      Real.rpow_one]
  rw [e]
  have := Real.rpow_nonneg (sq_nonneg ‖z‖) (3 / 4 : ℝ)
  nlinarith

/-- Sob HR, todo zero de `B` é real negativo. -/
theorem zerosNeg_of_rh (h : RiemannHypothesis) : ZerosNeg aXi := by
  intro w hw
  obtain ⟨z, rfl⟩ := existe_raiz w
  rw [ev_aXi] at hw
  have hzim : z.im = 0 := (riemannHypothesis_iff_Xi.mp h) z hw
  have hz0 : z.re ≠ 0 := by
    intro hre
    have hz : z = ((0 : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [hzim])
    rw [hz, gXi_ofReal] at hw
    have := ATK.BaseRiemannXiSinal.Xi_zero_pos
    exact absurd (Complex.ofReal_eq_zero.mp hw) this.ne'
  constructor
  · simp [sq, Complex.mul_im, hzim]
  · simp only [Complex.neg_re, sq, Complex.mul_re, hzim, mul_zero, sub_zero]
    have := mul_self_pos.mpr hz0
    linarith

/-! ## 4. O teorema -/

/-- **HR ⇒ PF∞**: sob HR, a matriz de Toeplitz dos coeficientes de `Ξ` é totalmente não negativa. -/
theorem tn_de_rh (h : RiemannHypothesis) : (toep aXi).IsTotallyNonneg :=
  hadamard_tn inteira_aXi aXi_zero_pos (zerosNeg_of_rh h) (A := 320) (σ := 3 / 4) (by norm_num)
    (by norm_num) (by norm_num) crescimento_B

/-- **HR ⟺ PF∞ dos coeficientes de `Ξ`** (as duas direções no kernel). -/
theorem rh_iff_tn : RiemannHypothesis ↔ (toep aXi).IsTotallyNonneg := ⟨tn_de_rh, rh_de_tn⟩

/-- **HR ⟺ todos os menores de Toeplitz dos `aₙ` são `≥ 0`.** -/
theorem rh_iff_menores : RiemannHypothesis ↔ ∀ (r : ℕ) (I J : Fin r → ℕ), StrictMono I → StrictMono J →
    0 ≤ (Matrix.of fun p q => if J q ≤ I p then aXi (I p - J q) else 0).det := by
  refine ⟨fun h r I J hI hJ => ?_, rh_de_menores⟩
  have := tn_de_rh h hI hJ
  convert this using 2
  ext p q
  simp [toep, Matrix.submatrix_apply]

/-- **HR ⟺ fatoração de gênero 0**: `B(w) = a₀∏(1 + αⱼw)` coeficiente a coeficiente, `αⱼ ≥ 0`, `Σαⱼ < ∞`. -/
theorem rh_iff_genero0 : RiemannHypothesis ↔ ∃ α : ℕ → ℝ, (∀ j, 0 ≤ α j) ∧ Summable α ∧
    ∀ n, Tendsto (fun N => prodCoef (aXi 0) α N n) atTop (𝓝 (aXi n)) := by
  constructor
  · intro h
    have hB : Boa (aXi 0) aXi := ⟨inteira_aXi, rfl, zerosNeg_of_rh h⟩
    refine ⟨alphaH aXi, alphaH_nonneg aXi_zero_pos hB,
      summable_alpha aXi_zero_pos hB (A := 320) (σ := 3 / 4) (by norm_num) (by norm_num)
        (by norm_num) crescimento_B, fun n => ?_⟩
    exact coef_eq_lim inteira_aXi aXi_zero_pos (zerosNeg_of_rh h) (A := 320) (σ := 3 / 4)
      (by norm_num) (by norm_num) (by norm_num) crescimento_B n
  · rintro ⟨α, hα, _, hlim⟩
    refine rh_de_tn (tn_closed (A := fun N => toep (prodCoef (aXi 0) α N))
      (tn_prodCoef aXi_zero_pos.le hα) fun i j => ?_)
    simp only [toep]
    split_ifs
    · exact hlim _
    · exact tendsto_const_nhds

end ATK.XiCresc

#print axioms ATK.XiCresc.phiT_cota_forte
#print axioms ATK.XiCresc.Phi_cota
#print axioms ATK.XiCresc.continuousOn_Phi
#print axioms ATK.XiCresc.expoente_le
#print axioms ATK.XiCresc.Phi_exp_cota
#print axioms ATK.XiCresc.norm_cos_le
#print axioms ATK.XiCresc.norm_sin_le
#print axioms ATK.XiCresc.aesm_F
#print axioms ATK.XiCresc.integrable_F
#print axioms ATK.XiCresc.hasDerivAt_HPhi
#print axioms ATK.XiCresc.HPhi_differentiable
#print axioms ATK.XiCresc.HPhi_ofReal
#print axioms ATK.XiCresc.gXi_eq_HPhi
#print axioms ATK.XiCresc.norm_gXi_le
#print axioms ATK.XiCresc.existe_raiz
#print axioms ATK.XiCresc.crescimento_B
#print axioms ATK.XiCresc.zerosNeg_of_rh
#print axioms ATK.XiCresc.tn_de_rh
#print axioms ATK.XiCresc.rh_iff_tn
#print axioms ATK.XiCresc.rh_iff_menores
#print axioms ATK.XiCresc.rh_iff_genero0
