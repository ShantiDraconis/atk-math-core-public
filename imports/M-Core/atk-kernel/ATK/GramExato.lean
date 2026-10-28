import ATK.BaezDuarteVetorB
import ATK.DInfinito
import ATK.NecessidadeRH
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# ATK-RH — Valores exatos de Gram, `D₁`, cauda, certificado ortogonal

* **`G₁₁ = ∫_0^∞ {1/t}² dt = log(2π) − γ`** (`G_zero`): degraus `(1/(n+2), 1/(n+1)]`, soma parcial
  `2M + 1 − H_{M+1} − 2M log(M+1) + 2 log M!` (`integral_partial_sq`), Stirling (Mathlib) e
  `H_n − log n → γ`.
* **`D₁ = 1 − (1 − γ)²/(log 2π − γ)`** (`DN_um`), ≈ 0,858212.
* **Escala**: `∫ ρ_{dh} ρ_{dk} = (1/d) ∫ ρ_h ρ_k`; em particular `G_{kk} = G₁₁/k` (`G_diag`).
* **Cauda**: `Σ_{k≥0} (D_{N+k} − D_{N+k+1}) = D_N − D_∞` (`cauda`).
* **Ganhos**: para `D` antítona e `≥ 0`, `D → 0 ⟺` ganho uniforme (`tende_zero_iff_ganho`);
  o ganho só estrito não basta (`ganho_estrito_nao_basta`: `D_N = ½ + 1/(N+1)`).
* **Certificado ortogonal (Rota B)**: Cauchy–Schwarz para `SemiInner` (`cauchy_schwarz`); se `h ⊥ ρ_k`
  para todo `k ≤ N`, então `⟨χ, h⟩²/‖h‖² ≤ D_N` (`DN_ge_ortogonal`); um `h ≠ 0` ortogonal a todos os
  `ρ_k` com `⟨χ, h⟩ ≠ 0` **refutaria HR** (`refuta_rh`). Nenhum `h` desses é conhecido.
-/

open MeasureTheory Set Filter Topology Real intervalIntegral

namespace ATK.GramExato

open ATK.BaezDuarteVetorB (fr measurable_fr fr_nonneg fr_le_one fr_on_step)
open ATK.Conditional.Riemann (rho chi DN residualSq DN_nonneg)
open ATK.OmegaGramRho (SemiInner err comb)

/-! ## 1. O degrau de `{1/x}²` -/

theorem integrableOn_fr_sq (a b : ℝ) : IntegrableOn (fun x => fr x ^ 2) (Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := 1) ?_ (measurable_fr.pow_const 2).aestronglyMeasurable ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h0 := fr_nonneg x
    have h1 := fr_le_one x
    nlinarith

theorem intervalIntegrable_fr_sq {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun x => fr x ^ 2) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (integrableOn_fr_sq a b)

/-- `∫_{1/(n+2)}^{1/(n+1)} {1/x}² = 1 + (n+1)/(n+2) − 2(n+1)(log(n+2) − log(n+1))`. -/
theorem integral_step_sq (n : ℕ) :
    ∫ x in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), fr x ^ 2 =
      1 + ((n : ℝ) + 1) / ((n : ℝ) + 2) -
        2 * ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hab : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le hn1 (by linarith)
  have ha : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  set c : ℝ := (n : ℝ) + 1 with hc
  have hpt : ∀ x ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), fr x ^ 2 = (x⁻¹ - c) ^ 2 := by
    intro x hx; rw [fr_on_step n hx]
  have hpos : ∀ x ∈ uIcc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), 0 < x := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hderiv : ∀ x ∈ uIcc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)),
      HasDerivAt (fun x => -x⁻¹ - 2 * c * Real.log x + c ^ 2 * x) ((x⁻¹ - c) ^ 2) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    have h1 := (hasDerivAt_inv hx0).neg
    have h2 := (Real.hasDerivAt_log hx0).const_mul (2 * c)
    have h3 := (hasDerivAt_id x).const_mul (c ^ 2)
    have := (h1.sub h2).add h3
    convert this using 1
    · funext y; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id]
    · field_simp
      ring
  have hcont : ContinuousOn (fun x : ℝ => (x⁻¹ - c) ^ 2) (uIcc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) := by
    refine ((continuousOn_inv₀.mono ?_).sub continuousOn_const).pow 2
    intro x hx; exact (hpos x hx).ne'
  rw [intervalIntegral.integral_of_le hab, setIntegral_congr_fun measurableSet_Ioc hpt,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have e1 : Real.log (1 / ((n : ℝ) + 1)) = -Real.log ((n : ℝ) + 1) := by rw [one_div, Real.log_inv]
  have e2 : Real.log (1 / ((n : ℝ) + 2)) = -Real.log ((n : ℝ) + 2) := by rw [one_div, Real.log_inv]
  simp only [e1, e2]
  rw [hc]
  field_simp
  ring

/-! ## 2. Somas parciais -/

/-- `∫_{1/(M+1)}^1 {1/x}² = 2M + 1 − H_{M+1} − 2M log(M+1) + 2 log M!`. -/
theorem integral_partial_sq (M : ℕ) :
    ∫ x in (1 / ((M : ℝ) + 1))..1, fr x ^ 2 =
      2 * M + 1 - (harmonic (M + 1) : ℝ) - 2 * M * Real.log ((M : ℝ) + 1) +
        2 * Real.log (M.factorial : ℝ) := by
  induction M with
  | zero => simp [harmonic]
  | succ M ih =>
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have e1 : (1 : ℝ) / (((M + 1 : ℕ) : ℝ) + 1) = 1 / ((M : ℝ) + 2) := by push_cast; ring
    have hab : 1 / ((M : ℝ) + 2) ≤ 1 / ((M : ℝ) + 1) := one_div_le_one_div_of_le hM1 (by linarith)
    have hb1 : 1 / ((M : ℝ) + 1) ≤ 1 := by rw [div_le_one hM1]; linarith [M.cast_nonneg (α := ℝ)]
    rw [e1, ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_fr_sq hab)
      (intervalIntegrable_fr_sq hb1), ih, integral_step_sq M, harmonic_succ (M + 1),
      Nat.factorial_succ]
    push_cast
    have hf : (0 : ℝ) < (M.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos M
    rw [Real.log_mul hM1.ne' hf.ne']
    have e3 : ((M : ℝ) + 1 + 1) = (M : ℝ) + 2 := by ring
    rw [e3]
    field_simp
    ring

/-- Forma de Stirling da soma parcial (para `M ≥ 1`). -/
theorem partial_stirling {M : ℕ} (hM : 1 ≤ M) :
    2 * M + 1 - (harmonic (M + 1) : ℝ) - 2 * M * Real.log ((M : ℝ) + 1) + 2 * Real.log (M.factorial : ℝ) =
      1 - ((harmonic (M + 1) : ℝ) - Real.log (((M + 1 : ℕ) : ℝ))) -
        (Real.log ((M : ℝ) + 1) - Real.log M) - 2 * ((M : ℝ) * Real.log (1 + 1 / (M : ℝ))) +
        2 * Real.log (Stirling.stirlingSeq M) + Real.log 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Stirling.log_stirlingSeq_formula]
  have e1 : Real.log (1 + 1 / (M : ℝ)) = Real.log ((M : ℝ) + 1) - Real.log M := by
    rw [show 1 + 1 / (M : ℝ) = ((M : ℝ) + 1) / M by field_simp, Real.log_div (by positivity) hM0.ne']
  have e2 : Real.log (2 * (M : ℝ)) = Real.log 2 + Real.log M := Real.log_mul (by norm_num) hM0.ne'
  have e3 : Real.log ((M : ℝ) / Real.exp 1) = Real.log M - 1 := by
    rw [Real.log_div hM0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  rw [e1, e2, e3]
  push_cast
  ring

theorem tendsto_partial_sq :
    Tendsto (fun M : ℕ => ∫ x in (1 / ((M : ℝ) + 1))..1, fr x ^ 2) atTop
      (𝓝 (Real.log (2 * π) - eulerMascheroniConstant - 1)) := by
  have hH : Tendsto (fun M : ℕ => (harmonic (M + 1) : ℝ) - Real.log (((M + 1 : ℕ) : ℝ))) atTop
      (𝓝 eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hL : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 1) - Real.log M) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop
  have hX : Tendsto (fun M : ℕ => (M : ℝ) * Real.log (1 + 1 / (M : ℝ))) atTop (𝓝 1) :=
    (Real.tendsto_mul_log_one_add_div_atTop 1).comp tendsto_natCast_atTop_atTop
  have hS : Tendsto (fun M : ℕ => Real.log (Stirling.stirlingSeq M)) atTop (𝓝 (Real.log (√π))) :=
    ((Real.continuousAt_log (by positivity)).tendsto).comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlim := (((((tendsto_const_nhds (x := (1 : ℝ))).sub hH).sub hL).sub (hX.const_mul 2)).add
    (hS.const_mul 2)).add_const (Real.log 2)
  have hval : 1 - eulerMascheroniConstant - 0 - 2 * 1 + 2 * Real.log (√π) + Real.log 2 =
      Real.log (2 * π) - eulerMascheroniConstant - 1 := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [integral_partial_sq, partial_stirling hM]

/-! ## 3. `G₁₁ = log 2π − γ` -/

theorem integral_Ioc_fr_sq : ∫ x in Ioc (0 : ℝ) 1, fr x ^ 2 = Real.log (2 * π) - eulerMascheroniConstant - 1 := by
  let s : ℕ → Set ℝ := fun M => Ioc (1 / ((M : ℝ) + 1)) 1
  have hmono : Monotone s := by
    intro M M' h
    have hM : (M : ℝ) ≤ M' := by exact_mod_cast h
    exact Set.Ioc_subset_Ioc_left (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hU : (⋃ M, s M) = Ioc 0 1 := by
    ext x
    simp only [s, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨M, h1, h2⟩
      exact ⟨lt_trans (by positivity) h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt h1
      exact ⟨M, hM, h2⟩
  have hlim := tendsto_setIntegral_of_monotone (μ := volume) (f := fun x => fr x ^ 2)
    (fun M => measurableSet_Ioc) hmono (by rw [hU]; exact integrableOn_fr_sq 0 1)
  rw [hU] at hlim
  have hlim2 : Tendsto (fun M : ℕ => ∫ x in s M, fr x ^ 2) atTop
      (𝓝 (Real.log (2 * π) - eulerMascheroniConstant - 1)) := by
    refine tendsto_partial_sq.congr fun M => ?_
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hb1 : 1 / ((M : ℝ) + 1) ≤ 1 := by rw [div_le_one hM1]; linarith [M.cast_nonneg (α := ℝ)]
    exact intervalIntegral.integral_of_le hb1
  exact tendsto_nhds_unique hlim hlim2

theorem fr_of_gt_one {x : ℝ} (hx : 1 < x) : fr x = x⁻¹ := by
  have hx0 : 0 < x := by linarith
  unfold fr
  rw [Int.fract_eq_self.mpr ⟨by positivity, by rw [div_lt_one hx0]; exact hx⟩, one_div]

theorem integral_Ioi_fr_sq : ∫ x in Ioi (1 : ℝ), fr x ^ 2 = 1 := by
  have hpt : ∀ x ∈ Ioi (1 : ℝ), fr x ^ 2 = x ^ (-2 : ℝ) := by
    intro x hx
    have hx0 : 0 < x := lt_trans one_pos hx
    rw [fr_of_gt_one hx, Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_pow]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

theorem rho_one (t : ℝ) : rho 1 t = fr t := by
  simp [rho, fr]

theorem integral_Ioi_zero_fr_sq : ∫ t in Ioi (0 : ℝ), fr t ^ 2 = Real.log (2 * π) - eulerMascheroniConstant := by
  have hint : IntegrableOn (fun t => fr t ^ 2) (Ioi 0) := by
    have := ATK.GramBaezDuarte.integrable_rho_sq (k := 1) le_rfl
    simpa [rho_one] using this
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Set.Ioc_disjoint_Ioi_same) measurableSet_Ioi (integrableOn_fr_sq 0 1)
      (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)),
    integral_Ioc_fr_sq, integral_Ioi_fr_sq]
  ring

/-- **`G₁₁ = ∫_0^∞ {1/t}² dt = log(2π) − γ`.** -/
theorem G_zero (N : ℕ) (hN : 0 < N) :
    ATK.GramBaezDuarte.G N ⟨0, hN⟩ ⟨0, hN⟩ = Real.log (2 * π) - eulerMascheroniConstant := by
  unfold ATK.GramBaezDuarte.G
  simp only [Nat.zero_add]
  simp_rw [rho_one, ← sq]
  exact integral_Ioi_zero_fr_sq

theorem log_two_pi_sub_gamma_pos : 0 < Real.log (2 * π) - eulerMascheroniConstant := by
  have h1 : 1 < Real.log (2 * π) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    have := Real.pi_gt_three
    linarith
  have := eulerMascheroniConstant_lt_two_thirds
  linarith

/-! ## 4. `D₁` exato -/

/-- **`D₁ = 1 − (1 − γ)²/(log 2π − γ)`** (≈ 0,858212). -/
theorem DN_um : DN 1 = 1 - (1 - eulerMascheroniConstant) ^ 2 / (Real.log (2 * π) - eulerMascheroniConstant) := by
  rw [ATK.GramBaezDuarte.DN_eq_gram]
  have hG : ATK.GramBaezDuarte.G 1 0 0 = Real.log (2 * π) - eulerMascheroniConstant := G_zero 1 one_pos
  have hb : ATK.GramBaezDuarte.b 1 0 = 1 - eulerMascheroniConstant := ATK.BaezDuarteVetorB.b_zero 1 one_pos
  have hinv : (ATK.GramBaezDuarte.G 1)⁻¹ = (ATK.GramBaezDuarte.G 1 0 0)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [Matrix.inv_def, Matrix.det_fin_one, Matrix.adjugate_fin_one, Ring.inverse_eq_inv']
  rw [hinv]
  simp only [dotProduct, Fin.sum_univ_one, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
    smul_eq_mul, hG, hb]
  have := log_two_pi_sub_gamma_pos
  field_simp

/-! ## 5. Escala -/

/-- `∫ ρ_{dh} ρ_{dk} = (1/d) ∫ ρ_h ρ_k`. -/
theorem escala (d h k : ℕ) (hd : 1 ≤ d) :
    ∫ t in Ioi (0 : ℝ), rho (d * h) t * rho (d * k) t =
      (d : ℝ)⁻¹ * ∫ t in Ioi (0 : ℝ), rho h t * rho k t := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (fun t => rho (d * h) t * rho (d * k) t) = fun t => (fun u => rho h u * rho k u) ((d : ℝ) * t) := by
    funext t
    simp only [rho]
    push_cast
    ring_nf
  rw [e, integral_comp_mul_left_Ioi (fun u => rho h u * rho k u) 0 hd0, mul_zero, smul_eq_mul]

/-- **`G_{kk} = G₁₁/k`** (índice `k = j + 1`). -/
theorem G_diag (N : ℕ) (j : Fin N) :
    ATK.GramBaezDuarte.G N j j = (Real.log (2 * π) - eulerMascheroniConstant) / ((j.val : ℝ) + 1) := by
  unfold ATK.GramBaezDuarte.G
  have := escala (j.val + 1) 1 1 (by omega)
  simp only [mul_one] at this
  rw [this]
  have h1 : ∫ t in Ioi (0 : ℝ), rho 1 t * rho 1 t = Real.log (2 * π) - eulerMascheroniConstant := by
    simp_rw [rho_one, ← sq]; exact integral_Ioi_zero_fr_sq
  rw [h1]
  push_cast
  ring

/-! ## 6. Cauda e ganhos -/

/-- **Cauda**: `Σ_{k≥0} (D_{N+k} − D_{N+k+1}) = D_N − D_∞`. -/
theorem cauda (N : ℕ) :
    HasSum (fun k => DN (N + k) - DN (N + k + 1)) (DN N - ATK.DInfinito.dInf) := by
  have hnn : ∀ k, 0 ≤ DN (N + k) - DN (N + k + 1) := fun k =>
    sub_nonneg.mpr (ATK.RiemannConcrete.DN_antitone (Nat.le_succ _))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have htel : ∀ n, ∑ k ∈ Finset.range n, (DN (N + k) - DN (N + k + 1)) = DN N - DN (N + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, ← add_assoc]; ring
  simp_rw [htel]
  have hN : Tendsto (fun k : ℕ => N + k) atTop atTop :=
    (tendsto_add_atTop_nat N).congr fun k => add_comm k N
  exact tendsto_const_nhds.sub (ATK.DInfinito.tendsto_dInf.comp hN)

theorem dInf_eq (N : ℕ) : ATK.DInfinito.dInf = DN N - ∑' k, (DN (N + k) - DN (N + k + 1)) := by
  rw [(cauda N).tsum_eq]; ring

/-- **Ganho uniforme**: para `D` antítona e `≥ 0`, `D → 0` ⟺ todo nível `ε` admite um ganho
uniforme `δ`. -/
theorem tende_zero_iff_ganho (D : ℕ → ℝ) (hD : Antitone D) (h0 : ∀ N, 0 ≤ D N) :
    Tendsto D atTop (𝓝 0) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ N, ε ≤ D N → ∃ M > N, D M ≤ D N - δ := by
  constructor
  · intro hT ε hε
    refine ⟨ε / 2, by linarith, fun N hN => ?_⟩
    obtain ⟨M0, hM0⟩ := (Metric.tendsto_atTop.mp hT) (ε / 2) (by linarith)
    refine ⟨max M0 (N + 1), by omega, ?_⟩
    have := hM0 (max M0 (N + 1)) (le_max_left _ _)
    rw [Real.dist_eq, sub_zero, abs_lt] at this
    linarith
  · intro hG
    have hlim := tendsto_atTop_ciInf hD ⟨0, by rintro _ ⟨N, rfl⟩; exact h0 N⟩
    set L := ⨅ N, D N with hL
    have hL0 : 0 ≤ L := le_ciInf h0
    have hLle : ∀ N, L ≤ D N := fun N => ciInf_le ⟨0, by rintro _ ⟨M, rfl⟩; exact h0 M⟩ N
    by_contra hne
    have hLpos : 0 < L := by
      rcases hL0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; rw [h]; exact hlim
    obtain ⟨δ, hδ, hstep⟩ := hG L hLpos
    have key : ∀ k : ℕ, ∃ M, D M ≤ D 0 - k * δ := by
      intro k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨M, hM⟩ := ih
        obtain ⟨M', -, hM'⟩ := hstep M (hLle M)
        exact ⟨M', by push_cast; linarith⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (D 0 / δ)
    obtain ⟨M, hM⟩ := key k
    have : D 0 < k * δ := by rwa [div_lt_iff₀ hδ] at hk
    linarith [h0 M]

/-- **Ganho só estrito não basta**: `D_N = ½ + 1/(N+1)` decresce estritamente e não tende a `0`. -/
theorem ganho_estrito_nao_basta :
    let D : ℕ → ℝ := fun N => 1 / 2 + 1 / ((N : ℝ) + 1)
    Antitone D ∧ (∀ N, 0 ≤ D N) ∧ (∀ ε > 0, ∀ N, ε ≤ D N → ∃ M > N, D M < D N) ∧
      ¬ Tendsto D atTop (𝓝 0) := by
  intro D
  refine ⟨?_, fun N => by simp only [D]; positivity, ?_, ?_⟩
  · intro a b hab
    simp only [D]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (a : ℝ) + 1) (by linarith : (a : ℝ) + 1 ≤ (b : ℝ) + 1)
    linarith
  · intro ε _ N _
    refine ⟨N + 1, by omega, ?_⟩
    simp only [D]
    push_cast
    have := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < (N : ℝ) + 1) (by linarith : (N : ℝ) + 1 < (N : ℝ) + 1 + 1)
    linarith
  · intro h
    have hlim : Tendsto D atTop (𝓝 (1 / 2)) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 / 2 : ℝ)
      rw [add_zero] at this
      exact this
    have := tendsto_nhds_unique h hlim
    norm_num at this

/-! ## 7. Cauchy–Schwarz e o certificado ortogonal -/

theorem cauchy_schwarz {V : Type*} [AddCommGroup V] [Module ℝ V] (ip : SemiInner V) (x y : V) :
    ip.B x y ^ 2 ≤ ip.B x x * ip.B y y := by
  have key : ∀ t : ℝ, 0 ≤ ip.B y y * (t * t) + (-2 * ip.B x y) * t + ip.B x x := by
    intro t
    have h := ip.nonneg (x - t • y)
    rw [ip.sub_left, ip.sub_right, ip.sub_right, ip.smul_left, ip.smul_left, ip.smul_right,
      ip.smul_right, ip.symm y x] at h
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem B_comb_ortogonal {V : Type*} [AddCommGroup V] [Module ℝ V] (ip : SemiInner V) {N : ℕ}
    (v : Fin N → V) (h : V) (horth : ∀ i, ip.B (v i) h = 0) (c : Fin N → ℝ) :
    ip.B (comb v c) h = 0 := by
  unfold comb
  rw [ip.sum_left]
  exact Finset.sum_eq_zero fun i _ => by rw [ip.smul_left, horth i, mul_zero]

/-- **Certificado ortogonal**: `h ⊥ v_i` ⇒ `⟨χ, h⟩²/‖h‖² ≤ err(c)` para todo `c`. -/
theorem err_ge_ortogonal {V : Type*} [AddCommGroup V] [Module ℝ V] (ip : SemiInner V) {N : ℕ}
    (v : Fin N → V) (χ h : V) (horth : ∀ i, ip.B (v i) h = 0) (hh : 0 < ip.B h h) (c : Fin N → ℝ) :
    ip.B χ h ^ 2 / ip.B h h ≤ err ip v χ c := by
  have e : ip.B (χ - comb v c) h = ip.B χ h := by
    rw [ip.sub_left, B_comb_ortogonal ip v h horth c, sub_zero]
  have cs := cauchy_schwarz ip (χ - comb v c) h
  rw [e] at cs
  rw [div_le_iff₀ hh]
  unfold err
  linarith

open ATK.GramBaezDuarte (ip chiL rhoL L2) in
/-- **`D_N ≥ ⟨χ, h⟩²/‖h‖²`** para `h ∈ L²(0,∞)` ortogonal a `ρ_1, …, ρ_N`. -/
theorem DN_ge_ortogonal (N : ℕ) (h : L2) (horth : ∀ i, ip.B (rhoL N i) h = 0) (hh : 0 < ip.B h h) :
    ip.B chiL h ^ 2 / ip.B h h ≤ DN N := by
  refine le_ciInf fun c => ?_
  rw [← ATK.GramBaezDuarte.err_eq]
  exact err_ge_ortogonal ip (rhoL N) chiL h horth hh c

open ATK.GramBaezDuarte (ip chiL rhoL L2) in
/-- **Rota B (condicional)**: um `h ≠ 0` ortogonal a todos os `ρ_k` com `⟨χ, h⟩ ≠ 0` refutaria HR. -/
theorem refuta_rh (h : L2) (horth : ∀ N i, ip.B (rhoL N i) h = 0) (hh : 0 < ip.B h h)
    (hχ : ip.B chiL h ≠ 0) : ¬ RiemannHypothesis := by
  rw [ATK.NecessidadeRH.rh_iff_iInf_DN]
  intro h0
  have hpos : 0 < ip.B chiL h ^ 2 / ip.B h h := div_pos (by positivity) hh
  have hle : ip.B chiL h ^ 2 / ip.B h h ≤ ⨅ N, DN N := le_ciInf fun N => DN_ge_ortogonal N h (horth N) hh
  rw [h0] at hle
  linarith

end ATK.GramExato

-- Auditoria de axiomas (kernel)
#print axioms ATK.GramExato.integrableOn_fr_sq
#print axioms ATK.GramExato.integral_step_sq
#print axioms ATK.GramExato.integral_partial_sq
#print axioms ATK.GramExato.partial_stirling
#print axioms ATK.GramExato.tendsto_partial_sq
#print axioms ATK.GramExato.integral_Ioc_fr_sq
#print axioms ATK.GramExato.fr_of_gt_one
#print axioms ATK.GramExato.integral_Ioi_fr_sq
#print axioms ATK.GramExato.rho_one
#print axioms ATK.GramExato.integral_Ioi_zero_fr_sq
#print axioms ATK.GramExato.G_zero
#print axioms ATK.GramExato.log_two_pi_sub_gamma_pos
#print axioms ATK.GramExato.DN_um
#print axioms ATK.GramExato.escala
#print axioms ATK.GramExato.G_diag
#print axioms ATK.GramExato.cauda
#print axioms ATK.GramExato.dInf_eq
#print axioms ATK.GramExato.tende_zero_iff_ganho
#print axioms ATK.GramExato.ganho_estrito_nao_basta
#print axioms ATK.GramExato.cauchy_schwarz
#print axioms ATK.GramExato.B_comb_ortogonal
#print axioms ATK.GramExato.err_ge_ortogonal
#print axioms ATK.GramExato.DN_ge_ortogonal
#print axioms ATK.GramExato.refuta_rh
