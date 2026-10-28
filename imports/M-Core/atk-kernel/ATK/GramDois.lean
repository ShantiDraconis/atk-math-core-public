import ATK.GramExato
import ATK.GamaCotas
import ATK.Cert.Intervalo

/-!
# ATK-RH — `G₁₂`, `D₂` exato e a primeira cota numérica incondicional `D_∞ < 0,29`

* **`G₁₂ = ∫_0^∞ {1/t}{1/(2t)} dt = ¾(log 2π − γ) − ¼ log 2`** (`G_um_dois`): degraus
  `(1/(n+2), 1/(n+1)]`, onde `{1/(2t)} = 1/(2t) − ⌊(n+1)/2⌋`; somas de pares fechadas
  (`integral_pares`) e Stirling.
* **`D₂ = 1 − (g₂₂b₁² − 2g₁₂b₁b₂ + g₁₁b₂²)/(g₁₁g₂₂ − g₁₂²)`** com `g₁₁ = log 2π − γ`, `g₂₂ = g₁₁/2`,
  `b₁ = 1 − γ`, `b₂ = (log 2 + 1 − γ)/2` (`DN_dois`).
* Aritmética intervalar (`ATK.Cert.IR`) com `γ, log 2, log π` certificados (`ATK.GamaCotas`):
  **`0,2899 < D₂ < 0,2900`** e **`0,85821 < D₁ < 0,85822`**; logo **`D_∞ ≤ D₂ < 0,29`** (`dInf_lt`) — a
  primeira cota numérica de `D_∞` provada no kernel sem hipótese (antes só havia `D_∞ ≤ D₁ < 1`).
* Cotas de Gram: `0 ≤ G_{ij}`, `G_{ij}² ≤ G_{ii}G_{jj}`, logo `G_{ij} ≤ (log 2π − γ)/√(ij) < 2/√(ij)`.
* A integral por pedaços corrigida `∫_a^b (t/i − p)(t/j − q)t⁻² = (b−a)/(ij) − (q/i + p/j)log(b/a) +
  pq(1/a − 1/b)` e o **contraexemplo** à versão com `(p/i + q/j)` (`i=1, j=2, [2,3], p=2, q=1`: daria
  `< 0` para um integrando `≥ 0`).
* Erros registrados: `G₁₁ ≠ log 2π − γ − 1`, `G₁₁ ≠ log 2`, e a fórmula `(1 − γ + log k − H_{k−1})/k` para
  `b_k` dá `b₄ < 0`, contra `b_pos`.

Nada aqui prova HR: `D_∞ = 0` é equivalente a HR, e só temos `D_∞ < 0,29`.
-/

open MeasureTheory Set Filter Topology Real intervalIntegral

namespace ATK.GramDois

open ATK.Conditional.Riemann (rho chi DN)
open ATK.BaezDuarteVetorB (fr fr_on_step)
open ATK.GramExato (rho_one fr_of_gt_one)

/-! ## 1. `ρ₂` nos degraus de `ρ₁` -/

theorem rho_two (t : ℝ) : rho 2 t = Int.fract (t⁻¹ / 2) := by
  unfold rho; congr 1; push_cast; ring

theorem rho_two_on_step (n : ℕ) {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    rho 2 t = t⁻¹ / 2 - (((n + 1) / 2 : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := ht
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have ht0 : 0 < t := lt_trans (by positivity) h1
  have hA : (n : ℝ) + 1 ≤ t⁻¹ := by
    rw [le_inv_comm₀ hn1 ht0]; simpa [one_div] using h2
  have hB : t⁻¹ < (n : ℝ) + 2 := by
    rw [inv_lt_comm₀ ht0 hn2]; simpa [one_div] using h1
  set b := (n + 1) / 2 with hb
  have hb1 : 2 * b ≤ n + 1 := by omega
  have hb2 : n ≤ 2 * b := by omega
  have hb1r : 2 * (b : ℝ) ≤ n + 1 := by exact_mod_cast hb1
  have hb2r : (n : ℝ) ≤ 2 * b := by exact_mod_cast hb2
  rw [rho_two, Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, ⟨b, by push_cast; ring⟩⟩

theorem rho12_on_step (n : ℕ) {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    rho 1 t * rho 2 t = (t⁻¹ - ((n : ℝ) + 1)) * (t⁻¹ / 2 - (((n + 1) / 2 : ℕ) : ℝ)) := by
  rw [rho_one, fr_on_step n ht, rho_two_on_step n ht]

theorem rho12_nonneg (t : ℝ) : 0 ≤ rho 1 t * rho 2 t :=
  mul_nonneg (ATK.RiemannFaithful.rho_nonneg 1 t) (ATK.RiemannFaithful.rho_nonneg 2 t)

theorem rho12_le_one (t : ℝ) : rho 1 t * rho 2 t ≤ 1 := by
  have h1 := ATK.RiemannFaithful.rho_le_one 1 t
  have h2 := ATK.RiemannFaithful.rho_le_one 2 t
  have h0 := ATK.RiemannFaithful.rho_nonneg 1 t
  have h0' := ATK.RiemannFaithful.rho_nonneg 2 t
  nlinarith

theorem integrableOn_rho12 (a b : ℝ) : IntegrableOn (fun t => rho 1 t * rho 2 t) (Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := 1) ?_
    ((ATK.RiemannFaithful.measurable_rho 1).mul (ATK.RiemannFaithful.measurable_rho 2)).aestronglyMeasurable ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (rho12_nonneg t)]
    exact rho12_le_one t

theorem intervalIntegrable_rho12 {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t => rho 1 t * rho 2 t) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (integrableOn_rho12 a b)

/-! ## 2. O degrau -/

theorem integral_step12 (n : ℕ) (b : ℝ) :
    ∫ t in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), (t⁻¹ - ((n : ℝ) + 1)) * (t⁻¹ / 2 - b) =
      1 / 2 - (b + ((n : ℝ) + 1) / 2) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) +
        b / ((n : ℝ) + 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hab : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le hn1 (by linarith)
  have ha : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  set a : ℝ := (n : ℝ) + 1 with hadef
  set c : ℝ := b + a / 2 with hc
  set d : ℝ := a * b with hd
  have hpos : ∀ x ∈ uIcc (1 / ((n : ℝ) + 2)) (1 / a), 0 < x := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hderiv : ∀ x ∈ uIcc (1 / ((n : ℝ) + 2)) (1 / a),
      HasDerivAt (fun x => -x⁻¹ / 2 - c * Real.log x + d * x) ((x⁻¹ - a) * (x⁻¹ / 2 - b)) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    have h1 := ((hasDerivAt_inv hx0).neg).div_const 2
    have h2 := (Real.hasDerivAt_log hx0).const_mul c
    have h3 := (hasDerivAt_id x).const_mul d
    have := (h1.sub h2).add h3
    convert this using 1
    · funext y; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id]
    · rw [hc, hd]; field_simp; ring
  have hcont : ContinuousOn (fun x : ℝ => (x⁻¹ - a) * (x⁻¹ / 2 - b))
      (uIcc (1 / ((n : ℝ) + 2)) (1 / a)) := by
    have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc (1 / ((n : ℝ) + 2)) (1 / a)) :=
      continuousOn_inv₀.mono fun x hx => (hpos x hx).ne'
    exact (hinv.sub continuousOn_const).mul ((hinv.div_const 2).sub continuousOn_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have e1 : Real.log (1 / a) = -Real.log a := by rw [one_div, Real.log_inv]
  have e2 : Real.log (1 / ((n : ℝ) + 2)) = -Real.log ((n : ℝ) + 2) := by rw [one_div, Real.log_inv]
  simp only [e1, e2]
  rw [hc, hd, hadef]
  field_simp
  ring

/-- `∫` de `ρ₁ρ₂` num degrau. -/
theorem integral_step_rho12 (n : ℕ) :
    ∫ t in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), rho 1 t * rho 2 t =
      1 / 2 - ((((n + 1) / 2 : ℕ) : ℝ) + ((n : ℝ) + 1) / 2) *
        (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) + (((n + 1) / 2 : ℕ) : ℝ) / ((n : ℝ) + 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hab : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le hn1 (by linarith)
  rw [intervalIntegral.integral_of_le hab,
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => rho12_on_step n ht),
    ← intervalIntegral.integral_of_le hab, integral_step12]

/-! ## 3. Somas de pares -/

/-- Forma fechada de `∫_{1/(2K+1)}^1 ρ₁ρ₂`. -/
noncomputable def Pc (K : ℕ) : ℝ :=
  2 * (K : ℝ) + 1 / 2 - 2 * (K : ℝ) * Real.log (2 * (K : ℝ) + 1) +
    1 / 2 * Real.log ((2 * K).factorial : ℝ) + (K : ℝ) * Real.log 2 + Real.log (K.factorial : ℝ) -
    1 / 4 * (harmonic K : ℝ) - 1 / 2 * (harmonic (2 * K + 1) : ℝ)

/-- Degrau `n = 2K+1` (`b = K+1`). -/
noncomputable def JA (K : ℕ) : ℝ :=
  1 / 2 - ((K : ℝ) + 1 + (2 * (K : ℝ) + 2) / 2) * (Real.log (2 * (K : ℝ) + 3) - Real.log (2 * (K : ℝ) + 2)) +
    ((K : ℝ) + 1) / (2 * (K : ℝ) + 3)

/-- Degrau `n = 2K` (`b = K`). -/
noncomputable def JB (K : ℕ) : ℝ :=
  1 / 2 - ((K : ℝ) + (2 * (K : ℝ) + 1) / 2) * (Real.log (2 * (K : ℝ) + 2) - Real.log (2 * (K : ℝ) + 1)) +
    (K : ℝ) / (2 * (K : ℝ) + 2)

theorem Pc_succ (K : ℕ) : Pc (K + 1) = Pc K + JA K + JB K := by
  have hK : (0 : ℝ) ≤ K := K.cast_nonneg
  have f1 : ((2 * (K + 1)).factorial : ℝ) = (2 * (K : ℝ) + 2) * ((2 * (K : ℝ) + 1) * ((2 * K).factorial : ℝ)) := by
    rw [show 2 * (K + 1) = (2 * K + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have f2 : ((K + 1).factorial : ℝ) = ((K : ℝ) + 1) * (K.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1 : (harmonic (K + 1) : ℝ) = (harmonic K : ℝ) + 1 / ((K : ℝ) + 1) := by
    rw [harmonic_succ]; push_cast; ring
  have h2 : (harmonic (2 * (K + 1) + 1) : ℝ) =
      (harmonic (2 * K + 1) : ℝ) + 1 / (2 * (K : ℝ) + 2) + 1 / (2 * (K : ℝ) + 3) := by
    rw [show 2 * (K + 1) + 1 = (2 * K + 1 + 1) + 1 by ring, harmonic_succ, harmonic_succ]
    push_cast; ring
  have hF2 : (0 : ℝ) < ((2 * K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hF1 : (0 : ℝ) < (K.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have l1 : Real.log ((2 * (K : ℝ) + 2) * ((2 * (K : ℝ) + 1) * ((2 * K).factorial : ℝ))) =
      Real.log 2 + Real.log ((K : ℝ) + 1) + (Real.log (2 * (K : ℝ) + 1) + Real.log ((2 * K).factorial : ℝ)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hF2.ne',
      show 2 * (K : ℝ) + 2 = 2 * ((K : ℝ) + 1) by ring, Real.log_mul two_ne_zero (by positivity)]
  have l2 : Real.log (((K : ℝ) + 1) * (K.factorial : ℝ)) = Real.log ((K : ℝ) + 1) + Real.log (K.factorial : ℝ) :=
    Real.log_mul (by positivity) hF1.ne'
  have l3 : Real.log (2 * ((K + 1 : ℕ) : ℝ) + 1) = Real.log (2 * (K : ℝ) + 3) := by
    congr 1; push_cast; ring
  have l4 : Real.log (2 * (K : ℝ) + 2) = Real.log 2 + Real.log ((K : ℝ) + 1) := by
    rw [show 2 * (K : ℝ) + 2 = 2 * ((K : ℝ) + 1) by ring, Real.log_mul two_ne_zero (by positivity)]
  unfold Pc JA JB
  rw [f1, f2, h1, h2, l1, l2, l3, l4]
  push_cast
  field_simp
  ring

/-- **`∫_{1/(2K+1)}^1 ρ₁ρ₂ = Pc K`.** -/
theorem integral_pares (K : ℕ) : ∫ t in (1 / (2 * (K : ℝ) + 1))..1, rho 1 t * rho 2 t = Pc K := by
  induction K with
  | zero => simp [Pc, harmonic]
  | succ K ih =>
    have hK : (0 : ℝ) ≤ K := K.cast_nonneg
    have sA := integral_step_rho12 (2 * K + 1)
    have sB := integral_step_rho12 (2 * K)
    rw [show (2 * K + 1 + 1) / 2 = K + 1 by omega] at sA
    rw [show (2 * K + 1) / 2 = K by omega] at sB
    have eA1 : ((2 * K + 1 : ℕ) : ℝ) + 2 = 2 * (K : ℝ) + 3 := by push_cast; ring
    have eA2 : ((2 * K + 1 : ℕ) : ℝ) + 1 = 2 * (K : ℝ) + 2 := by push_cast; ring
    have eB1 : ((2 * K : ℕ) : ℝ) + 2 = 2 * (K : ℝ) + 2 := by push_cast; ring
    have eB2 : ((2 * K : ℕ) : ℝ) + 1 = 2 * (K : ℝ) + 1 := by push_cast; ring
    rw [eA1, eA2] at sA
    rw [eB1, eB2] at sB
    push_cast at sA sB
    have hA : ∫ t in (1 / (2 * (K : ℝ) + 3))..(1 / (2 * (K : ℝ) + 2)), rho 1 t * rho 2 t = JA K := by
      rw [sA]; unfold JA; ring
    have hB : ∫ t in (1 / (2 * (K : ℝ) + 2))..(1 / (2 * (K : ℝ) + 1)), rho 1 t * rho 2 t = JB K := by
      rw [sB]; unfold JB; ring
    have p1 : 1 / (2 * (K : ℝ) + 3) ≤ 1 / (2 * (K : ℝ) + 2) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have p2 : 1 / (2 * (K : ℝ) + 2) ≤ 1 / (2 * (K : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have p3 : 1 / (2 * (K : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have e0 : (1 : ℝ) / (2 * ((K + 1 : ℕ) : ℝ) + 1) = 1 / (2 * (K : ℝ) + 3) := by push_cast; ring
    rw [e0, ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_rho12 p1)
      (intervalIntegrable_rho12 (p2.trans p3)),
      ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_rho12 p2)
      (intervalIntegrable_rho12 p3), hA, hB, ih, Pc_succ]
    ring

/-! ## 4. O limite (Stirling) -/

theorem Pc_stirling {K : ℕ} (hK : 1 ≤ K) :
    Pc K = 1 / 2 - (2 * (K : ℝ)) * Real.log (1 + 1 / (2 * (K : ℝ))) +
      1 / 2 * Real.log (Stirling.stirlingSeq (2 * K)) + Real.log (Stirling.stirlingSeq K) +
      1 / 2 * Real.log 2 - 1 / 2 * (Real.log (2 * (K : ℝ) + 1) - Real.log (2 * (K : ℝ))) -
      1 / 4 * ((harmonic K : ℝ) - Real.log K) -
      1 / 2 * ((harmonic (2 * K + 1) : ℝ) - Real.log (2 * (K : ℝ) + 1)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula]
  have c2 : ((2 * K : ℕ) : ℝ) = 2 * (K : ℝ) := by push_cast; ring
  rw [c2]
  have e1 : Real.log (1 + 1 / (2 * (K : ℝ))) = Real.log (2 * (K : ℝ) + 1) - Real.log 2 - Real.log K := by
    rw [show 1 + 1 / (2 * (K : ℝ)) = (2 * (K : ℝ) + 1) / (2 * K) by field_simp,
      Real.log_div (by positivity) (by positivity), Real.log_mul two_ne_zero hK0.ne']
    ring
  have e2 : Real.log (2 * (2 * (K : ℝ))) = 2 * Real.log 2 + Real.log K := by
    rw [← mul_assoc, Real.log_mul (by norm_num) hK0.ne', show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have e3 : Real.log (2 * (K : ℝ) / Real.exp 1) = Real.log 2 + Real.log K - 1 := by
    rw [Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp, Real.log_mul two_ne_zero hK0.ne']
  have e4 : Real.log (2 * (K : ℝ)) = Real.log 2 + Real.log K := Real.log_mul two_ne_zero hK0.ne'
  have e5 : Real.log ((K : ℝ) / Real.exp 1) = Real.log K - 1 := by
    rw [Real.log_div hK0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  rw [e1, e2, e3, e4, e5]
  unfold Pc
  ring

theorem tendsto_Pc :
    Tendsto Pc atTop (𝓝 (-1 / 2 + 3 / 4 * Real.log π + 1 / 2 * Real.log 2 - 3 / 4 * eulerMascheroniConstant)) := by
  have h2K : Tendsto (fun K : ℕ => 2 * (K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h2Kn : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    Filter.tendsto_atTop_mono (fun K => by show K ≤ 2 * K; omega) tendsto_id
  have T1 : Tendsto (fun K : ℕ => (2 * (K : ℝ)) * Real.log (1 + 1 / (2 * (K : ℝ)))) atTop (𝓝 1) :=
    (Real.tendsto_mul_log_one_add_div_atTop 1).comp h2K
  have hS : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop (𝓝 (Real.log (√π))) :=
    ((Real.continuousAt_log (by positivity)).tendsto).comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have T2 : Tendsto (fun K : ℕ => Real.log (Stirling.stirlingSeq (2 * K))) atTop (𝓝 (Real.log (√π))) :=
    hS.comp h2Kn
  have T4 : Tendsto (fun K : ℕ => Real.log (2 * (K : ℝ) + 1) - Real.log (2 * (K : ℝ))) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log 1).comp h2K
  have T5 := Real.tendsto_harmonic_sub_log
  have h2K1 : Tendsto (fun K : ℕ => 2 * K + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun K => by show K ≤ 2 * K + 1; omega) tendsto_id
  have T6 : Tendsto (fun K : ℕ => (harmonic (2 * K + 1) : ℝ) - Real.log (2 * (K : ℝ) + 1)) atTop
      (𝓝 eulerMascheroniConstant) := by
    refine (Real.tendsto_harmonic_sub_log.comp h2K1).congr fun K => ?_
    simp only [Function.comp]
    push_cast; ring_nf
  have hc1 : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => 1 / 2 * Real.log 2) atTop (𝓝 (1 / 2 * Real.log 2)) := tendsto_const_nhds
  have hlim := ((((((hc1.sub T1).add (T2.const_mul (1 / 2))).add hS).add hc2).sub
    (T4.const_mul (1 / 2))).sub (T5.const_mul (1 / 4))).sub (T6.const_mul (1 / 2))
  have hval : 1 / 2 - 1 + 1 / 2 * Real.log (√π) + Real.log (√π) + 1 / 2 * Real.log 2 - 1 / 2 * 0 -
      1 / 4 * eulerMascheroniConstant - 1 / 2 * eulerMascheroniConstant =
      -1 / 2 + 3 / 4 * Real.log π + 1 / 2 * Real.log 2 - 3 / 4 * eulerMascheroniConstant := by
    rw [Real.log_sqrt Real.pi_pos.le]; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  rw [Pc_stirling hK]

/-! ## 5. `G₁₂` -/

theorem integral_Ioc_rho12 :
    ∫ t in Ioc (0 : ℝ) 1, rho 1 t * rho 2 t =
      -1 / 2 + 3 / 4 * Real.log π + 1 / 2 * Real.log 2 - 3 / 4 * eulerMascheroniConstant := by
  let s : ℕ → Set ℝ := fun K => Ioc (1 / (2 * (K : ℝ) + 1)) 1
  have hmono : Monotone s := by
    intro K K' h
    have hK : (K : ℝ) ≤ K' := by exact_mod_cast h
    exact Set.Ioc_subset_Ioc_left (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hU : (⋃ K, s K) = Ioc 0 1 := by
    ext x
    simp only [s, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨K, h1, h2⟩
      exact ⟨lt_trans (by positivity) h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt h1
      refine ⟨K, lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hK, h2⟩
      have : (0 : ℝ) ≤ K := K.cast_nonneg
      linarith
  have hlim := tendsto_setIntegral_of_monotone (μ := volume) (f := fun t => rho 1 t * rho 2 t)
    (fun K => measurableSet_Ioc) hmono (by rw [hU]; exact integrableOn_rho12 0 1)
  rw [hU] at hlim
  have hlim2 : Tendsto (fun K : ℕ => ∫ t in s K, rho 1 t * rho 2 t) atTop
      (𝓝 (-1 / 2 + 3 / 4 * Real.log π + 1 / 2 * Real.log 2 - 3 / 4 * eulerMascheroniConstant)) := by
    refine tendsto_Pc.congr fun K => ?_
    have hb1 : 1 / (2 * (K : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [K.cast_nonneg (α := ℝ)]
    rw [← integral_pares K, intervalIntegral.integral_of_le hb1]
  exact tendsto_nhds_unique hlim hlim2

theorem rho_two_of_gt_one {t : ℝ} (ht : 1 < t) : rho 2 t = t⁻¹ / 2 := by
  have ht0 : 0 < t := by linarith
  rw [rho_two, Int.fract_eq_self.mpr ⟨by positivity, ?_⟩]
  have : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  linarith

theorem integral_Ioi_rho12 : ∫ t in Ioi (1 : ℝ), rho 1 t * rho 2 t = 1 / 2 := by
  have hpt : ∀ t ∈ Ioi (1 : ℝ), rho 1 t * rho 2 t = 1 / 2 * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [rho_one, fr_of_gt_one ht, rho_two_of_gt_one ht, Real.rpow_neg ht0.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-- **`G₁₂ = ¾(log 2π − γ) − ¼ log 2`.** -/
theorem G_um_dois :
    ATK.GramBaezDuarte.G 2 0 1 =
      3 / 4 * (Real.log (2 * π) - eulerMascheroniConstant) - 1 / 4 * Real.log 2 := by
  unfold ATK.GramBaezDuarte.G
  simp only [Fin.val_zero, Fin.val_one, Nat.zero_add]
  have hint : IntegrableOn (fun t => rho 1 t * rho 2 t) (Ioi 0) :=
    ATK.GramBaezDuarte.integrable_mul (ATK.GramBaezDuarte.memLp_rho le_rfl)
      (ATK.GramBaezDuarte.memLp_rho (by norm_num))
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Set.Ioc_disjoint_Ioi_same) measurableSet_Ioi (integrableOn_rho12 0 1)
      (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)),
    integral_Ioc_rho12, integral_Ioi_rho12, ATK.GamaCotas.log_two_pi]
  ring

/-! ## 6. `D₂` exato -/

/-- `g₁₁ = log 2π − γ`. -/
noncomputable def g11 : ℝ := Real.log (2 * π) - eulerMascheroniConstant
/-- `g₁₂ = ¾ g₁₁ − ¼ log 2`. -/
noncomputable def g12 : ℝ := 3 / 4 * g11 - 1 / 4 * Real.log 2
/-- `b₁ = 1 − γ`. -/
noncomputable def b1 : ℝ := 1 - eulerMascheroniConstant
/-- `b₂ = (log 2 + 1 − γ)/2`. -/
noncomputable def b2 : ℝ := (Real.log 2 + 1 - eulerMascheroniConstant) / 2

theorem G2_00 : ATK.GramBaezDuarte.G 2 0 0 = g11 := by
  have := ATK.GramExato.G_diag 2 0
  rw [this]; simp [g11]

theorem G2_11 : ATK.GramBaezDuarte.G 2 1 1 = g11 / 2 := by
  have := ATK.GramExato.G_diag 2 1
  rw [this]; norm_num [g11]

theorem G2_01 : ATK.GramBaezDuarte.G 2 0 1 = g12 := by rw [G_um_dois]; rfl

theorem G2_10 : ATK.GramBaezDuarte.G 2 1 0 = g12 := by
  rw [ATK.GramBaezDuarte.G_symm]; exact G2_01

theorem G2_eq : ATK.GramBaezDuarte.G 2 = !![g11, g12; g12, g11 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using G2_00
  · simpa using G2_01
  · simpa using G2_10
  · simpa using G2_11

theorem b2_eq : ATK.GramBaezDuarte.b 2 = ![b1, b2] := by
  funext j
  fin_cases j
  · simpa [b1] using ATK.BaezDuarteVetorB.b_zero 2 (by norm_num)
  · have := ATK.BaezDuarteVetorB.b_formula 2 1
    simp only [Fin.isValue, Fin.val_one] at this
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [this, b2]
    norm_num

/-- **`D₂ = 1 − (g₂₂b₁² − 2g₁₂b₁b₂ + g₁₁b₂²)/(g₁₁g₂₂ − g₁₂²)`.** -/
theorem DN_dois :
    DN 2 = 1 - (g11 / 2 * (b1 * b1) - 2 * (g12 * (b1 * b2)) + g11 * (b2 * b2)) *
      (g11 * (g11 / 2) - g12 * g12)⁻¹ := by
  rw [ATK.GramBaezDuarte.DN_eq_gram, G2_eq, b2_eq, Matrix.inv_def, Matrix.det_fin_two_of,
    Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv']
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, smul_eq_mul, Fin.isValue]
  field_simp
  ring

/-! ## 7. Aritmética intervalar: `D₁`, `D₂`, `D_∞` -/

open ATK.Cert (IR)

/-- `γ ∈ [0,5772156; 0,5772163]`. -/
def Iγ : IR := ⟨5772156 / 10 ^ 7, 5772163 / 10 ^ 7⟩
/-- `log 2 ∈ [0,6931471803; 0,6931471808]`. -/
def Il2 : IR := ⟨6931471803 / 10 ^ 10, 6931471808 / 10 ^ 10⟩
/-- `log π ∈ [1,1447295; 1,1447300]`. -/
def Ilp : IR := ⟨11447295 / 10 ^ 7, 11447300 / 10 ^ 7⟩
def Ig11 : IR := IR.sub (IR.add Il2 Ilp) Iγ
def Ig12 : IR := IR.sub (IR.mul (IR.pt (3 / 4)) Ig11) (IR.mul (IR.pt (1 / 4)) Il2)
def Ig22 : IR := IR.mul (IR.pt (1 / 2)) Ig11
def Ib1 : IR := IR.sub (IR.pt 1) Iγ
def Ib2 : IR := IR.mul (IR.pt (1 / 2)) (IR.sub (IR.add Il2 (IR.pt 1)) Iγ)
def Inum : IR :=
  IR.add (IR.sub (IR.mul Ig22 (IR.mul Ib1 Ib1)) (IR.mul (IR.pt 2) (IR.mul Ig12 (IR.mul Ib1 Ib2))))
    (IR.mul Ig11 (IR.mul Ib2 Ib2))
def Idet : IR := IR.sub (IR.mul Ig11 Ig22) (IR.mul Ig12 Ig12)
def ID2 : IR := IR.sub (IR.pt 1) (IR.mul Inum (IR.inv Idet))
def ID1 : IR := IR.sub (IR.pt 1) (IR.mul (IR.mul Ib1 Ib1) (IR.inv Ig11))

theorem Idet_pos : (0 : ℚ) < Idet.lo := by decide +kernel
theorem Ig11_pos : (0 : ℚ) < Ig11.lo := by decide +kernel
theorem ID2_lo : (2899 / 10000 : ℚ) < ID2.lo := by decide +kernel
theorem ID2_hi : ID2.hi < (29 / 100 : ℚ) := by decide +kernel
theorem ID1_lo : (85821 / 100000 : ℚ) < ID1.lo := by decide +kernel
theorem ID1_hi : ID1.hi < (85822 / 100000 : ℚ) := by decide +kernel
theorem Ig11_hi : Ig11.hi < (127 / 100 : ℚ) := by decide +kernel

theorem mem_γ : IR.mem eulerMascheroniConstant Iγ := by
  obtain ⟨h1, h2⟩ := ATK.GamaCotas.gama_cotas
  constructor <;> simp only [Iγ] <;> push_cast <;> linarith

theorem mem_l2 : IR.mem (Real.log 2) Il2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> simp only [Il2] <;> push_cast <;> norm_num at h1 h2 ⊢ <;> linarith

theorem mem_lp : IR.mem (Real.log π) Ilp := by
  obtain ⟨h1, h2⟩ := ATK.GamaCotas.log_pi_cotas
  constructor <;> simp only [Ilp] <;> push_cast <;> linarith

theorem mem_g11 : IR.mem g11 Ig11 := by
  unfold g11 Ig11
  rw [ATK.GamaCotas.log_two_pi]
  exact IR.mem_sub (IR.mem_add mem_l2 mem_lp) mem_γ

theorem mem_g12 : IR.mem g12 Ig12 := by
  have := IR.mem_sub (IR.mem_mul (IR.mem_pt (3 / 4)) mem_g11) (IR.mem_mul (IR.mem_pt (1 / 4)) mem_l2)
  convert this using 1
  · unfold g12; push_cast; ring
  · rfl

theorem mem_g22 : IR.mem (g11 / 2) Ig22 := by
  have := IR.mem_mul (IR.mem_pt (1 / 2)) mem_g11
  convert this using 1
  · push_cast; ring
  · rfl

theorem mem_b1 : IR.mem b1 Ib1 := by
  have := IR.mem_sub (IR.mem_pt 1) mem_γ
  convert this using 1
  · unfold b1; push_cast; ring
  · rfl

theorem mem_b2 : IR.mem b2 Ib2 := by
  have := IR.mem_mul (IR.mem_pt (1 / 2)) (IR.mem_sub (IR.mem_add mem_l2 (IR.mem_pt 1)) mem_γ)
  convert this using 1
  · unfold b2; push_cast; ring
  · rfl

theorem mem_num : IR.mem (g11 / 2 * (b1 * b1) - 2 * (g12 * (b1 * b2)) + g11 * (b2 * b2)) Inum := by
  have := IR.mem_add (IR.mem_sub (IR.mem_mul mem_g22 (IR.mem_mul mem_b1 mem_b1))
    (IR.mem_mul (IR.mem_pt 2) (IR.mem_mul mem_g12 (IR.mem_mul mem_b1 mem_b2))))
    (IR.mem_mul mem_g11 (IR.mem_mul mem_b2 mem_b2))
  convert this using 1
  · push_cast; ring
  · rfl

theorem mem_det : IR.mem (g11 * (g11 / 2) - g12 * g12) Idet :=
  IR.mem_sub (IR.mem_mul mem_g11 mem_g22) (IR.mem_mul mem_g12 mem_g12)

theorem det_pos : 0 < g11 * (g11 / 2) - g12 * g12 := by
  have h := mem_det.1
  have h0 : (0 : ℝ) < (Idet.lo : ℝ) := by exact_mod_cast Idet_pos
  linarith

theorem g11_pos : 0 < g11 := by
  have h := mem_g11.1
  have h0 : (0 : ℝ) < (Ig11.lo : ℝ) := by exact_mod_cast Ig11_pos
  linarith

/-- **`0,2899 < D₂ < 0,2900`.** -/
theorem D2_cotas : (2899 / 10000 : ℝ) < DN 2 ∧ DN 2 < 29 / 100 := by
  have hm := IR.mem_sub (IR.mem_pt 1) (IR.mem_mul mem_num (IR.mem_inv mem_det Idet_pos))
  rw [DN_dois]
  have hlo : ((2899 / 10000 : ℚ) : ℝ) < (ID2.lo : ℝ) := by exact_mod_cast ID2_lo
  have hhi : (ID2.hi : ℝ) < ((29 / 100 : ℚ) : ℝ) := by exact_mod_cast ID2_hi
  push_cast at hlo hhi hm
  obtain ⟨m1, m2⟩ := hm
  constructor
  · unfold ID2 at hlo; linarith
  · unfold ID2 at hhi; linarith

/-- **`0,85821 < D₁ < 0,85822`.** -/
theorem D1_cotas : (85821 / 100000 : ℝ) < DN 1 ∧ DN 1 < 85822 / 100000 := by
  have hm := IR.mem_sub (IR.mem_pt 1) (IR.mem_mul (IR.mem_mul mem_b1 mem_b1) (IR.mem_inv mem_g11 Ig11_pos))
  have hD : DN 1 = 1 - b1 * b1 * g11⁻¹ := by
    rw [ATK.GramExato.DN_um]; unfold b1 g11; rw [div_eq_mul_inv, sq]
  rw [hD]
  have hlo : ((85821 / 100000 : ℚ) : ℝ) < (ID1.lo : ℝ) := by exact_mod_cast ID1_lo
  have hhi : (ID1.hi : ℝ) < ((85822 / 100000 : ℚ) : ℝ) := by exact_mod_cast ID1_hi
  push_cast at hlo hhi hm
  obtain ⟨m1, m2⟩ := hm
  constructor
  · unfold ID1 at hlo; linarith
  · unfold ID1 at hhi; linarith

/-- **`D_∞ ≤ D₂ < 0,29`**: a primeira cota numérica incondicional de `D_∞`. -/
theorem dInf_lt : ATK.DInfinito.dInf < 29 / 100 := by
  have hle : ATK.DInfinito.dInf ≤ DN 2 :=
    ciInf_le ⟨0, by rintro _ ⟨N, rfl⟩; exact ATK.Conditional.Riemann.DN_nonneg N⟩ 2
  linarith [D2_cotas.2]

/-- Em particular a cota do texto, `D_∞ ≤ 0,29670246`, vale (mas não é ótima). -/
theorem dInf_le_texto : ATK.DInfinito.dInf ≤ 29670246 / 10 ^ 8 := by
  have := dInf_lt; linarith

/-! ## 8. Cotas de Gram -/

theorem G_nonneg (N : ℕ) (i j : Fin N) : 0 ≤ ATK.GramBaezDuarte.G N i j :=
  setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (ATK.RiemannFaithful.rho_nonneg _ t) (ATK.RiemannFaithful.rho_nonneg _ t)

theorem G_sq_le (N : ℕ) (i j : Fin N) :
    ATK.GramBaezDuarte.G N i j ^ 2 ≤ ATK.GramBaezDuarte.G N i i * ATK.GramBaezDuarte.G N j j :=
  ATK.GramExato.cauchy_schwarz ATK.GramBaezDuarte.ip (ATK.GramBaezDuarte.rhoL N i)
    (ATK.GramBaezDuarte.rhoL N j)

/-- **`G_{ij} ≤ (log 2π − γ)/√((i+1)(j+1))`** (índices `i+1`, `j+1`). -/
theorem G_le (N : ℕ) (i j : Fin N) :
    ATK.GramBaezDuarte.G N i j ≤ g11 / Real.sqrt (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
  have h := G_sq_le N i j
  rw [ATK.GramExato.G_diag, ATK.GramExato.G_diag] at h
  set p : ℝ := ((i : ℝ) + 1) * ((j : ℝ) + 1) with hp
  have hp0 : 0 < p := by positivity
  have hG := G_nonneg N i j
  have hg := g11_pos
  have hsq : (ATK.GramBaezDuarte.G N i j * Real.sqrt p) ^ 2 ≤ g11 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp0.le]
    have e : (Real.log (2 * π) - eulerMascheroniConstant) / ((i : ℝ) + 1) *
        ((Real.log (2 * π) - eulerMascheroniConstant) / ((j : ℝ) + 1)) = g11 ^ 2 / p := by
      rw [hp]; unfold g11; field_simp
    rw [e, le_div_iff₀ hp0] at h
    linarith
  have h2 : ATK.GramBaezDuarte.G N i j * Real.sqrt p ≤ g11 :=
    (pow_le_pow_iff_left₀ (by positivity) hg.le two_ne_zero).mp hsq
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hp0)]
  exact h2

/-- Em particular `G_{ij} < 2/√((i+1)(j+1))`, a cota do texto. -/
theorem G_lt_dois (N : ℕ) (i j : Fin N) :
    ATK.GramBaezDuarte.G N i j < 2 / Real.sqrt (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
  have h := G_le N i j
  have hp : 0 < Real.sqrt (((i : ℝ) + 1) * ((j : ℝ) + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hg : g11 < 2 := by
    have := mem_g11.2
    have h1 : (Ig11.hi : ℝ) < ((127 / 100 : ℚ) : ℝ) := by exact_mod_cast Ig11_hi
    push_cast at h1
    linarith
  exact lt_of_le_of_lt h (div_lt_div_of_pos_right hg hp)

/-! ## 9. A integral por pedaços corrigida e o contraexemplo -/

/-- **`∫_a^b (t/i − p)(t/j − q)/t² = (b−a)/(ij) − (q/i + p/j) log(b/a) + pq(1/a − 1/b)`.** -/
theorem integral_pedaco {i j p q a b : ℝ} (hi : i ≠ 0) (hj : j ≠ 0) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (t / i - p) * (t / j - q) / t ^ 2 =
      (b - a) / (i * j) - (q / i + p / j) * Real.log (b / a) + p * q * (1 / a - 1 / b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpos : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  set c : ℝ := q / i + p / j with hc
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun x => x / (i * j) - c * Real.log x - p * q * x⁻¹)
      ((x / i - p) * (x / j - q) / x ^ 2) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    have h1 := (hasDerivAt_id x).div_const (i * j)
    have h2 := (Real.hasDerivAt_log hx0).const_mul c
    have h3 := (hasDerivAt_inv hx0).const_mul (p * q)
    have := (h1.sub h2).sub h3
    convert this using 1
    · funext y; simp only [Pi.sub_apply, id]
    · rw [hc]; field_simp; ring
  have hcont : ContinuousOn (fun x : ℝ => (x / i - p) * (x / j - q) / x ^ 2) (uIcc a b) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx; exact pow_ne_zero 2 (hpos x hx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    Real.log_div hb.ne' ha.ne']
  field_simp
  ring

/-- **Contraexemplo** à versão com coeficiente `(p/i + q/j)`: em `i = 1, j = 2`, `[2,3]`, `p = ⌊t⌋ = 2`,
`q = ⌊t/2⌋ = 1`, o integrando `(t−2)(t/2−1)/t² = (t−2)²/(2t²)` é `≥ 0`, a fórmula correta dá
`½ − 2 log(3/2) + ⅓ > 0`, e a do texto daria `½ − (5/2) log(3/2) + ⅓ < 0`. -/
theorem contraexemplo_pedaco :
    0 ≤ ∫ t in (2 : ℝ)..3, (t / 1 - 2) * (t / 2 - 1) / t ^ 2 ∧
      ∫ t in (2 : ℝ)..3, (t / 1 - 2) * (t / 2 - 1) / t ^ 2 = 1 / 2 - 2 * Real.log (3 / 2) + 1 / 3 ∧
      0 < 1 / 2 - 2 * Real.log (3 / 2) + 1 / 3 ∧
      1 / 2 - (2 / 1 + 1 / 2) * Real.log (3 / 2) + 1 / 3 < 0 := by
  have hval := integral_pedaco (i := 1) (j := 2) (p := 2) (q := 1) (a := 2) (b := 3)
    one_ne_zero two_ne_zero two_pos (by norm_num)
  have hl : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  obtain ⟨h1, h2⟩ := ATK.GamaCotas.log3_sub_log2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
    have : (t / 1 - 2) * (t / 2 - 1) = (t - 2) ^ 2 / 2 := by ring
    rw [this]; positivity
  · rw [hval]; norm_num
  · rw [hl]; norm_num at h1 h2 ⊢; linarith
  · rw [hl]; norm_num at h1 h2 ⊢; linarith

/-! ## 10. Erros registrados -/

/-- `G₁₁ ≠ log 2π − γ − 1` (texto 963449d2: esquece `∫_1^∞ t⁻² = 1`). -/
theorem G11_ne_texto1 : ATK.GramBaezDuarte.G 1 0 0 ≠ Real.log (2 * π) - eulerMascheroniConstant - 1 := by
  rw [show (0 : Fin 1) = ⟨0, one_pos⟩ from rfl, ATK.GramExato.G_zero 1 one_pos]
  intro h; linarith

/-- `G₁₁ ≠ log 2` (texto 1fb0a5dd): `G₁₁ − log 2 = log π − γ > 0`. -/
theorem G11_ne_log2 : ATK.GramBaezDuarte.G 1 0 0 ≠ Real.log 2 := by
  rw [show (0 : Fin 1) = ⟨0, one_pos⟩ from rfl, ATK.GramExato.G_zero 1 one_pos, ATK.GamaCotas.log_two_pi]
  obtain ⟨h1, -⟩ := ATK.GamaCotas.log_pi_cotas
  obtain ⟨-, h2⟩ := ATK.GamaCotas.gama_cotas
  intro h; linarith

/-- A fórmula `b_k = (1 − γ + log k − H_{k−1})/k` (texto 9654e97e) dá `b₄ < 0`, mas `b₄ > 0`
(`b_pos`); a correta é `b_k = (log k + 1 − γ)/k`. -/
theorem b4_texto_errado :
    (1 - eulerMascheroniConstant + Real.log 4 - (1 + 1 / 2 + 1 / 3)) / 4 < 0 ∧
      0 < ATK.GramBaezDuarte.b 4 ⟨3, by norm_num⟩ ∧
      ATK.GramBaezDuarte.b 4 ⟨3, by norm_num⟩ = (Real.log 4 + 1 - eulerMascheroniConstant) / 4 := by
  refine ⟨?_, ATK.BaezDuarteVetorB.b_pos 4 _, ?_⟩
  · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    obtain ⟨h1, -⟩ := ATK.GamaCotas.gama_cotas
    have h2 := Real.log_two_lt_d9
    norm_num at h2 ⊢
    linarith
  · rw [ATK.BaezDuarteVetorB.b_formula]; norm_num

end ATK.GramDois

-- Auditoria de axiomas (kernel)
#print axioms ATK.GramDois.rho_two
#print axioms ATK.GramDois.rho_two_on_step
#print axioms ATK.GramDois.rho12_on_step
#print axioms ATK.GramDois.rho12_nonneg
#print axioms ATK.GramDois.rho12_le_one
#print axioms ATK.GramDois.integrableOn_rho12
#print axioms ATK.GramDois.intervalIntegrable_rho12
#print axioms ATK.GramDois.integral_step12
#print axioms ATK.GramDois.integral_step_rho12
#print axioms ATK.GramDois.Pc_succ
#print axioms ATK.GramDois.integral_pares
#print axioms ATK.GramDois.Pc_stirling
#print axioms ATK.GramDois.tendsto_Pc
#print axioms ATK.GramDois.integral_Ioc_rho12
#print axioms ATK.GramDois.rho_two_of_gt_one
#print axioms ATK.GramDois.integral_Ioi_rho12
#print axioms ATK.GramDois.G_um_dois
#print axioms ATK.GramDois.G2_00
#print axioms ATK.GramDois.G2_11
#print axioms ATK.GramDois.G2_01
#print axioms ATK.GramDois.G2_10
#print axioms ATK.GramDois.G2_eq
#print axioms ATK.GramDois.b2_eq
#print axioms ATK.GramDois.DN_dois
#print axioms ATK.GramDois.Idet_pos
#print axioms ATK.GramDois.Ig11_pos
#print axioms ATK.GramDois.ID2_lo
#print axioms ATK.GramDois.ID2_hi
#print axioms ATK.GramDois.ID1_lo
#print axioms ATK.GramDois.ID1_hi
#print axioms ATK.GramDois.Ig11_hi
#print axioms ATK.GramDois.mem_γ
#print axioms ATK.GramDois.mem_l2
#print axioms ATK.GramDois.mem_lp
#print axioms ATK.GramDois.mem_g11
#print axioms ATK.GramDois.mem_g12
#print axioms ATK.GramDois.mem_g22
#print axioms ATK.GramDois.mem_b1
#print axioms ATK.GramDois.mem_b2
#print axioms ATK.GramDois.mem_num
#print axioms ATK.GramDois.mem_det
#print axioms ATK.GramDois.det_pos
#print axioms ATK.GramDois.g11_pos
#print axioms ATK.GramDois.D2_cotas
#print axioms ATK.GramDois.D1_cotas
#print axioms ATK.GramDois.dInf_lt
#print axioms ATK.GramDois.dInf_le_texto
#print axioms ATK.GramDois.G_nonneg
#print axioms ATK.GramDois.G_sq_le
#print axioms ATK.GramDois.G_le
#print axioms ATK.GramDois.G_lt_dois
#print axioms ATK.GramDois.integral_pedaco
#print axioms ATK.GramDois.contraexemplo_pedaco
#print axioms ATK.GramDois.G11_ne_texto1
#print axioms ATK.GramDois.G11_ne_log2
#print axioms ATK.GramDois.b4_texto_errado
