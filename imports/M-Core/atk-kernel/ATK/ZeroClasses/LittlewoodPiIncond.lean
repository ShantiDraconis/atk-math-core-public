import ATK.ZeroClasses.LittlewoodPi

/-!
# Littlewood para `π(x) − Li(x)` sem hipóteses (rodada 96)

A rodada 95 (`LittlewoodPi`) deu `π(x) − Li(x) = Ω±(√x log log log x/log x)` **sob RH**. Aqui sai o caso
`¬RH`, e com ele o teorema de Littlewood (1914) para `π` sem hipóteses.

* §1–2. A série `b(n) = (Λ(n) − 1)/log n` tem `Σ b(n) n^{−s} = log ζ(s) + ∫ζ − s` a menos de constante: sua
  derivada é `ζ′/ζ + ζ − 1` (`hasDerivAt_LSeries_bP`, via `logMul_bP`). Uma primitiva holomorfa no disco
  `|s − 2| < 2` (`primitiva`) cola com a transformada de Mellin `GA a(s)` das somas parciais
  `a(N) = Σ_{n ≤ N} b(n)`; o passo de Landau da rodada 87 (`Unilateral.extensao`) dá:
  **`a(N) ≤ A(N + 1)^θ + K` ⟹ `SemZeros θ`** (`semZeros_of_aPi_le`), e o mesmo por baixo
  (`semZeros_of_aPi_ge`).
* §3. `a(N) = (π(N) − Li(N)) + (Π(N) − π(N)) − (λ(N) − Li(N))`, com `Π(N) = Σ Λ(n)/log n` e
  `λ(N) = Σ_{2 ≤ n ≤ N} 1/log n`: `0 ≤ Π − π ≤ (ψ − θ)/log 2` (`Pi_sub_pi`) e
  `1/log N ≤ λ(N) − Li(N) ≤ 1/log 2` (`lam_sub_Li`), logo `a(N) = π(N) − Li(N) + O(√N)` (`aPi_bounds`).
* §4. **`π(x) − Li(x) = Ω±(x^θ)` para `½ ≤ θ < Θ`** (`pi_omega_mais`, `pi_omega_menos`).
* §5. **`pi_littlewood`**: `π(x) − Li(x) = Ω±(√x log log log x/log x)`, sem hipóteses (RH: rodada 95;
  `¬RH`: `Θ > ½` e §4 com `θ = (½ + Θ)/2`). **`pi_troca_sinal`**: `π(x) − Li(x)` troca de sinal infinitas
  vezes — em particular `π(x) > Li(x)` para `x` arbitrariamente grande.

Classificação: **consequência** (fecha o BUILD_PENDING da rodada 95). Nada aqui dá um `x` explícito com
`π(x) > Li(x)` (número de Skewes) nem diz algo sobre a posição dos zeros: RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.LittlewoodPiIncond

open ATK.ZeroClasses.VonKoch (GA cL LSeriesSummable_cL LSeries_cL)
open ATK.ZeroClasses.VonKochRH (Hf Hf_eq)
open ATK.ZeroClasses.QuasiRH (SemZeros)

/-! ## 1. A série `Σ (Λ(n) − 1) n^{−s}/log n`, primitiva de `−ζ′/ζ − ζ` -/

/-- `b(n) = (Λ(n) − 1)/log n` (`= 0` para `n ≤ 1`). -/
noncomputable def bR (n : ℕ) : ℝ := ((ArithmeticFunction.vonMangoldt n : ℝ) - 1) / Real.log n

noncomputable def bP (n : ℕ) : ℂ := (bR n : ℂ)

/-- `a(N) = Σ_{2 ≤ n ≤ N} (Λ(n) − 1)/log n = Π(N) − Σ_{2 ≤ n ≤ N} 1/log n`. -/
noncomputable def aPi (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, bR (k + 1)

theorem abs_bR_le (n : ℕ) : |bR n| ≤ 3 := by
  unfold bR
  rcases lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
    have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
    have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlpos : 0 < Real.log n := by linarith
    have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have h1 := ArithmeticFunction.vonMangoldt_le_log (n := n)
    rw [abs_div, abs_of_pos hlpos, div_le_iff₀ hlpos]
    have : |(ArithmeticFunction.vonMangoldt n : ℝ) - 1| ≤ Real.log n + 1 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith

theorem abs_aPi_le (N : ℕ) : |aPi N| ≤ 3 * ((N : ℝ) + 1) := by
  unfold aPi
  calc |∑ k ∈ Finset.range N, bR (k + 1)| ≤ ∑ k ∈ Finset.range N, |bR (k + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, (3 : ℝ) := Finset.sum_le_sum fun k _ => abs_bR_le _
    _ = 3 * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 3 * ((N : ℝ) + 1) := by linarith

theorem aPi_succ (n : ℕ) : ((aPi (n + 1) : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), bP (k + 1) := by
  unfold aPi bP
  push_cast
  rfl

theorem norm_bP_le (n : ℕ) : ‖bP n‖ ≤ 3 := by
  unfold bP
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_bR_le n

theorem abscissa_bP : LSeries.abscissaOfAbsConv bP ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨3, fun n _ => norm_bP_le n⟩

theorem LSeriesSummable_bP {s : ℂ} (hs : 1 < s.re) : LSeriesSummable bP s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt abscissa_bP (by exact_mod_cast hs))

theorem GA_aPi_eq {s : ℂ} (hs : 1 < s.re) : GA aPi s = LSeries bP s :=
  ATK.ZeroClasses.Unilateral.GA_eq_LSeries' (θ := 1) (C := 3) zero_le_one
    (fun N => by rw [Real.rpow_one]; exact abs_aPi_le N) aPi_succ hs (LSeriesSummable_bP hs)

theorem logMul_bP {n : ℕ} (hn : n ≠ 0) : LSeries.logMul bP n = cL n + LSeries.delta n := by
  unfold LSeries.logMul bP bR cL
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    simp [LSeries.delta]
  · have hn1 : n ≠ 1 := by omega
    have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast h)).ne'
    simp only [LSeries.delta, hn1, ite_false, add_zero]
    have e : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    have hm : Real.log n * (((ArithmeticFunction.vonMangoldt n : ℝ) - 1) / Real.log n) =
        (ArithmeticFunction.vonMangoldt n : ℝ) - 1 := by field_simp
    rw [e, ← Complex.ofReal_mul, hm]
    push_cast
    ring

/-- **`(Σ b(n) n^{−s})′ = −(Hf(s) + 1) = ζ′/ζ(s) + ζ(s) − 1`** em `Re s > 1`. -/
theorem hasDerivAt_LSeries_bP {s : ℂ} (hs : 1 < s.re) : HasDerivAt (LSeries bP) (-(Hf s + 1)) s := by
  have h := LSeries_hasDerivAt (f := bP) (lt_of_le_of_lt abscissa_bP (by exact_mod_cast hs))
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl 1 hs
  have hδ : LSeriesSummable LSeries.delta s := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt
      (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => ?_⟩) (by exact_mod_cast hs))
    unfold LSeries.delta
    split_ifs <;> simp
  have e : LSeries (LSeries.logMul bP) s = Hf s + 1 := by
    rw [LSeries_congr (g := cL + LSeries.delta) (fun hn => logMul_bP hn) s,
      LSeries_add (LSeriesSummable_cL hs) hδ, LSeries_cL hs,
      LSeries_delta, Hf_eq hs1 (riemannZeta_ne_zero_of_one_lt_re hs)]
    simp
  rw [e] at h
  exact h

/-! ## 2. A extensão ao disco e o passo de Landau -/

/-- **A primitiva no disco**: existe `P` holomorfa em `|s − 2| < 2` com `P = Σ b(n) n^{−s}` em `Re s > 1`. -/
theorem primitiva : ∃ P : ℂ → ℂ, DifferentiableOn ℂ P (ball (2 : ℂ) 2) ∧
    ∀ s ∈ ball (2 : ℂ) 2, 1 < s.re → P s = LSeries bP s := by
  have hD : DifferentiableOn ℂ (fun s => -(Hf s + 1)) (ball (2 : ℂ) 2) := by
    have := ATK.ZeroClasses.Unilateral.differentiableOn_Hf (θ := 0) le_rfl
    rw [sub_zero] at this
    exact (this.add_const 1).neg
  obtain ⟨P, hP2, hP⟩ := hD.isExactOn_ball.with_val_at 2 (LSeries bP 2)
  refine ⟨P, fun s hs => (hP s hs).differentiableAt.differentiableWithinAt, fun s hs hs1 => ?_⟩
  set U := ball (2 : ℂ) 2 ∩ {w : ℂ | 1 < w.re} with hU
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hUc : IsPreconnected U := ((convex_ball _ _).inter (convex_halfSpace_re_gt 1)).isPreconnected
  have h2U : (2 : ℂ) ∈ U := ⟨mem_ball_self (by norm_num), by show (1 : ℝ) < (2 : ℂ).re; norm_num⟩
  have hPd : DifferentiableOn ℂ P U := fun w hw => (hP w hw.1).differentiableAt.differentiableWithinAt
  have hLd : DifferentiableOn ℂ (LSeries bP) U := fun w hw =>
    (hasDerivAt_LSeries_bP hw.2).differentiableAt.differentiableWithinAt
  have hder : U.EqOn (deriv P) (deriv (LSeries bP)) := fun w hw => by
    rw [(hP w hw.1).deriv, (hasDerivAt_LSeries_bP hw.2).deriv]
  exact hUo.eqOn_of_deriv_eq hUc hPd hLd hder h2U hP2 ⟨hs, hs1⟩

/-- **Uma cota de um lado para `a(N)` dá `ζ ≠ 0` em `Re s > θ`.** -/
theorem semZeros_of_aPi_le {θ A K : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, aPi N ≤ A * ((N : ℝ) + 1) ^ θ + K) : SemZeros θ := by
  classical
  obtain ⟨P, hPd, hP⟩ := primitiva
  set H : ℂ → ℂ := fun s => if s ∈ ball (2 : ℂ) 2 then P s else GA aPi s with hH
  have hHd : DifferentiableOn ℂ H (ball (2 : ℂ) (2 - θ)) := by
    intro s hs
    have hs2 : s ∈ ball (2 : ℂ) 2 := ball_subset_ball (by linarith) hs
    refine ((hPd s hs2).differentiableAt (isOpen_ball.mem_nhds hs2)).congr_of_eventuallyEq ?_
      |>.differentiableWithinAt
    filter_upwards [isOpen_ball.mem_nhds hs2] with w hw
    simp only [hH]
    rw [ite_eq_left hw]
  have hHG : ∀ s : ℂ, 1 < s.re → GA aPi s = H s := by
    intro s hs
    by_cases hb : s ∈ ball (2 : ℂ) 2
    · simp only [hH]
      rw [ite_eq_left hb, hP s hb hs, GA_aPi_eq hs]
    · simp only [hH]
      rw [ite_eq_right hb]
  obtain ⟨G, hG, hGA⟩ := ATK.ZeroClasses.Unilateral.extensao (a := aPi) (C := 3) hθ hθ1 abs_aPi_le h hHd hHG
  -- `−G′ − 1` estende `Hf`
  have hV : IsOpen {w : ℂ | θ < w.re} := isOpen_lt continuous_const continuous_re
  have hGan : ∀ s : ℂ, θ < s.re → AnalyticAt ℂ G s := fun s hs =>
    DifferentiableOn.analyticAt (fun w hw => (hG w hw).differentiableWithinAt) (hV.mem_nhds hs)
  refine ATK.ZeroClasses.Unilateral.semZeros_of_ext_psi (G := fun s => -deriv G s - 1)
    (fun s hs => ((hGan s hs).deriv.differentiableAt.neg).sub_const 1) (fun s hs => ?_)
  have hV1 : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
  have hev : G =ᶠ[𝓝 s] LSeries bP := by
    filter_upwards [hV1.mem_nhds hs] with w hw
    rw [hGA w hw, GA_aPi_eq hw]
  rw [hev.deriv_eq, (hasDerivAt_LSeries_bP hs).deriv]
  ring

theorem semZeros_of_aPi_ge {θ A K : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ θ) - K ≤ aPi N) : SemZeros θ := by
  classical
  obtain ⟨P, hPd, hP⟩ := primitiva
  set H : ℂ → ℂ := fun s => if s ∈ ball (2 : ℂ) 2 then -P s else -GA aPi s with hH
  have hHd : DifferentiableOn ℂ H (ball (2 : ℂ) (2 - θ)) := by
    intro s hs
    have hs2 : s ∈ ball (2 : ℂ) 2 := ball_subset_ball (by linarith) hs
    refine ((hPd s hs2).differentiableAt (isOpen_ball.mem_nhds hs2)).neg.congr_of_eventuallyEq ?_
      |>.differentiableWithinAt
    filter_upwards [isOpen_ball.mem_nhds hs2] with w hw
    simp only [hH]
    rw [ite_eq_left hw]
    rfl
  have hHG : ∀ s : ℂ, 1 < s.re → GA (fun N => -aPi N) s = H s := by
    intro s hs
    rw [ATK.ZeroClasses.Unilateral.GA_neg]
    by_cases hb : s ∈ ball (2 : ℂ) 2
    · simp only [hH]
      rw [ite_eq_left hb, hP s hb hs, GA_aPi_eq hs]
    · simp only [hH]
      rw [ite_eq_right hb]
  obtain ⟨G, hG, hGA⟩ := ATK.ZeroClasses.Unilateral.extensao (a := fun N => -aPi N) (C := 3) (A := A) (K := K)
    hθ hθ1 (fun N => by rw [abs_neg]; exact abs_aPi_le N) (fun N => by have := h N; linarith) hHd hHG
  have hV : IsOpen {w : ℂ | θ < w.re} := isOpen_lt continuous_const continuous_re
  have hGan : ∀ s : ℂ, θ < s.re → AnalyticAt ℂ G s := fun s hs =>
    DifferentiableOn.analyticAt (fun w hw => (hG w hw).differentiableWithinAt) (hV.mem_nhds hs)
  refine ATK.ZeroClasses.Unilateral.semZeros_of_ext_psi (G := fun s => deriv G s - 1)
    (fun s hs => (hGan s hs).deriv.differentiableAt.sub_const 1) (fun s hs => ?_)
  have hV1 : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
  have hev : G =ᶠ[𝓝 s] fun w => -LSeries bP w := by
    filter_upwards [hV1.mem_nhds hs] with w hw
    rw [hGA w hw, ATK.ZeroClasses.Unilateral.GA_neg, GA_aPi_eq hw]
  have hd : HasDerivAt (fun w => -LSeries bP w) (-(-(Hf s + 1))) s := (hasDerivAt_LSeries_bP hs).neg
  rw [hev.deriv_eq, hd.deriv]
  ring

/-! ## 3. De `a(N)` a `π(N) − Li(N)` -/

open ATK.ZeroClasses.PiLi (Li)

/-- O indicador de primo. -/
noncomputable def ip (n : ℕ) : ℝ := if n.Prime then 1 else 0

theorem psi_nat (N : ℕ) : Chebyshev.psi N = ∑ k ∈ Finset.range N, (ArithmeticFunction.vonMangoldt (k + 1) : ℝ) := by
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Finset.sum_range_succ]

theorem theta_nat (N : ℕ) : Chebyshev.theta N = ∑ k ∈ Finset.range N, ip (k + 1) * Real.log (k + 1) := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, Finset.sum_filter]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Finset.sum_range_succ]
    congr 1
    unfold ip
    split_ifs <;> push_cast <;> ring

theorem pi_nat (N : ℕ) : (Nat.primeCounting N : ℝ) = ∑ k ∈ Finset.range N, ip (k + 1) := by
  induction N with
  | zero => simp [Nat.primeCounting, Nat.primeCounting', ip, Nat.count_succ, Nat.not_prime_zero]
  | succ N ih =>
    have h : Nat.primeCounting (N + 1) = Nat.primeCounting N + if (N + 1).Prime then 1 else 0 := by
      unfold Nat.primeCounting Nat.primeCounting'
      rw [Nat.count_succ]
    rw [h, Finset.sum_range_succ, ← ih]
    unfold ip
    split_ifs <;> push_cast <;> ring

/-- `0 ≤ Λ(n)/log n − [n primo] ≤ (Λ(n) − [n primo] log n)/log 2` para `n ≥ 1`. -/
theorem termo_Pi {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n - ip n ∧
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n - ip n ≤
        ((ArithmeticFunction.vonMangoldt n : ℝ) - ip n * Real.log n) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  unfold ip
  by_cases hp : n.Prime
  · have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hp.one_lt)
    simp only [hp, ↓reduceIte]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hl.ne']
    simp
  · simp only [hp, ↓reduceIte]
    rcases eq_or_lt_of_le hn with h1 | h2
    · subst h1
      simp
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
      have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
      simp only [sub_zero, zero_mul]
      exact ⟨by positivity, div_le_div_of_nonneg_left h0 hl2 hl⟩

/-- **`0 ≤ Π(N) − π(N) ≤ (ψ(N) − θ(N))/log 2`**, com `Π(N) = Σ_{n ≤ N} Λ(n)/log n`. -/
theorem Pi_sub_pi (N : ℕ) :
    0 ≤ (∑ k ∈ Finset.range N, (ArithmeticFunction.vonMangoldt (k + 1) : ℝ) / Real.log (k + 1)) -
        Nat.primeCounting N ∧
    (∑ k ∈ Finset.range N, (ArithmeticFunction.vonMangoldt (k + 1) : ℝ) / Real.log (k + 1)) -
        Nat.primeCounting N ≤ (Chebyshev.psi N - Chebyshev.theta N) / Real.log 2 := by
  rw [pi_nat, psi_nat, theta_nat, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  have h := fun k : ℕ => termo_Pi (n := k + 1) (Nat.le_add_left 1 k)
  push_cast at h
  exact ⟨Finset.sum_nonneg fun k _ => (h k).1, Finset.sum_le_sum fun k _ => (h k).2⟩

/-- `λ(N) = Σ_{n ≤ N} 1/log n` (o termo `n = 1` é `0`). -/
noncomputable def lam (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, 1 / Real.log (k + 1)

theorem aPi_eq (N : ℕ) : aPi N =
    (∑ k ∈ Finset.range N, (ArithmeticFunction.vonMangoldt (k + 1) : ℝ) / Real.log (k + 1)) - lam N := by
  unfold aPi lam bR
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem integral_inv_log_bounds {N : ℕ} (hN : 2 ≤ N) :
    1 / Real.log ((N : ℝ) + 1) ≤ ∫ t in (N : ℝ)..((N : ℝ) + 1), 1 / Real.log t ∧
      ∫ t in (N : ℝ)..((N : ℝ) + 1), 1 / Real.log t ≤ 1 / Real.log N := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc (N : ℝ) ((N : ℝ) + 1)) := by
    have := ATK.ZeroClasses.LittlewoodPi.continuousOn_inv_log_pow 1 (x := (N : ℝ) + 1) (by linarith)
    simp only [pow_one] at this
    exact this.mono (by
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc hN2 le_rfl)
  have hI := hc.intervalIntegrable (μ := MeasureTheory.volume)
  constructor
  · have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hI (fun t ht => by
      have h1 : Real.log t ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by linarith [ht.1]) ht.2
      have h0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      exact one_div_le_one_div_of_le h0 h1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    simpa using this
  · have := intervalIntegral.integral_mono_on (by linarith) hI intervalIntegrable_const (fun t ht => by
      have h1 : Real.log N ≤ Real.log t := Real.log_le_log (by linarith) ht.1
      have h0 : 0 < Real.log N := Real.log_pos (by linarith)
      exact one_div_le_one_div_of_le h0 h1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    simpa using this

/-- **`1/log N ≤ λ(N) − Li(N) ≤ 1/log 2`** para `N ≥ 2`. -/
theorem lam_sub_Li {N : ℕ} (hN : 2 ≤ N) :
    1 / Real.log N ≤ lam N - Li N ∧ lam N - Li N ≤ 1 / Real.log 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    unfold lam Li
    norm_num [Finset.sum_range_succ]
  | succ N hN ih =>
    have hb := integral_inv_log_bounds hN
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hint : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
      intro a b ha hab
      have := ATK.ZeroClasses.LittlewoodPi.continuousOn_inv_log_pow 1 (x := b) (by linarith)
      simp only [pow_one] at this
      refine (this.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc ha le_rfl
    have hLi : Li ((N + 1 : ℕ) : ℝ) = Li N + ∫ t in (N : ℝ)..((N : ℝ) + 1), 1 / Real.log t := by
      unfold Li
      push_cast
      rw [intervalIntegral.integral_add_adjacent_intervals (hint 2 N le_rfl hN2) (hint N (N + 1) hN2 (by linarith))]
    have hlam : lam (N + 1) = lam N + 1 / Real.log ((N : ℝ) + 1) := by
      unfold lam
      rw [Finset.sum_range_succ]
    rw [hLi, hlam]
    have hlN : 0 < Real.log N := Real.log_pos (by linarith)
    push_cast
    constructor <;> linarith [ih.1, ih.2, hb.1, hb.2]

/-- `a(N) = (π(N) − Li(N)) + (Π(N) − π(N)) − (λ(N) − Li(N))`, logo
`π(N) − Li(N) − 1/log 2 ≤ a(N) ≤ π(N) − Li(N) + C√N` para `N ≥ 2`. -/
theorem aPi_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    aPi N ≤ ((Nat.primeCounting N : ℝ) - Li N) + C * √(N : ℝ) ∧
      ((Nat.primeCounting N : ℝ) - Li N) - 1 / Real.log 2 ≤ aPi N := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C 0 / Real.log 2, by positivity, fun N hN => ?_⟩
  have hP := Pi_sub_pi N
  have hL := lam_sub_Li hN
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast hN
  have hlN : 0 < 1 / Real.log N := one_div_pos.mpr (Real.log_pos hN1)
  have hψ : (Chebyshev.psi N - Chebyshev.theta N) / Real.log 2 ≤ max C 0 / Real.log 2 * √(N : ℝ) := by
    rw [div_mul_eq_mul_div]
    gcongr
    exact (hC N).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  rw [aPi_eq]
  constructor <;> linarith [hP.1, hP.2, hL.1, hL.2]

theorem sqrt_le_rpow {θ : ℝ} (hθ : 1 / 2 ≤ θ) (N : ℕ) : √(N : ℝ) ≤ ((N : ℝ) + 1) ^ θ := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  calc √(N : ℝ) ≤ √((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    _ = ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    _ ≤ ((N : ℝ) + 1) ^ θ := Real.rpow_le_rpow_of_exponent_le h1 hθ

theorem aPi_pequeno {N : ℕ} (hN : N < 2) : -6 ≤ aPi N ∧ aPi N ≤ 6 := by
  have h := abs_aPi_le N
  have hN1 : (N : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hN
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-! ## 4. `π(x) − Li(x) = Ω±(x^θ)` para `θ < Θ` -/

open ATK.ZeroClasses.BDTheta (Teta Teta_le_um meio_le_Teta rh_iff_Teta)

/-- **`π(x) − Li(x) = Ω₊(x^θ)` para `½ ≤ θ < Θ`**: nenhuma cota `A(N + 1)^θ + K` vale por cima. -/
theorem pi_omega_mais {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ A * ((N : ℝ) + 1) ^ θ + K < (Nat.primeCounting N : ℝ) - Li N := by
  by_contra hne
  push Not at hne
  obtain ⟨C, hC0, hC⟩ := aPi_bounds
  refine ATK.ZeroClasses.Unilateral.nao_semZeros hlt
    (semZeros_of_aPi_le (A := max A 0 + C) (K := max K 0 + 6) (by linarith) (hlt.trans_le Teta_le_um) fun N => ?_)
  have hp : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
  have hA : A * ((N : ℝ) + 1) ^ θ ≤ max A 0 * ((N : ℝ) + 1) ^ θ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  have hA0 : 0 ≤ max A 0 * ((N : ℝ) + 1) ^ θ := mul_nonneg (le_max_right _ _) hp
  have hK := le_max_left K 0
  have hK0 := le_max_right K 0
  have hCp : 0 ≤ C * ((N : ℝ) + 1) ^ θ := mul_nonneg hC0 hp
  rw [add_mul]
  rcases lt_or_ge N 2 with h | h
  · linarith [(aPi_pequeno h).2]
  · have hs : C * √(N : ℝ) ≤ C * ((N : ℝ) + 1) ^ θ := mul_le_mul_of_nonneg_left (sqrt_le_rpow hθ N) hC0
    linarith [(hC N h).1, hne N h]

/-- **`π(x) − Li(x) = Ω₋(x^θ)` para `½ ≤ θ < Θ`**. -/
theorem pi_omega_menos {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ (Nat.primeCounting N : ℝ) - Li N < -(A * ((N : ℝ) + 1) ^ θ) - K := by
  by_contra hne
  push Not at hne
  obtain ⟨C, hC0, hC⟩ := aPi_bounds
  have hl2 : 0 < 1 / Real.log 2 := one_div_pos.mpr (Real.log_pos (by norm_num))
  refine ATK.ZeroClasses.Unilateral.nao_semZeros hlt
    (semZeros_of_aPi_ge (A := max A 0) (K := max K 0 + 1 / Real.log 2 + 6) (by linarith)
      (hlt.trans_le Teta_le_um) fun N => ?_)
  have hp : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
  have hA : A * ((N : ℝ) + 1) ^ θ ≤ max A 0 * ((N : ℝ) + 1) ^ θ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  have hA0 : 0 ≤ max A 0 * ((N : ℝ) + 1) ^ θ := mul_nonneg (le_max_right _ _) hp
  have hK := le_max_left K 0
  have hK0 := le_max_right K 0
  rcases lt_or_ge N 2 with h | h
  · linarith [(aPi_pequeno h).1]
  · linarith [(hC N h).2, hne N h]

/-! ## 5. Littlewood para `π(x) − Li(x)` -/

theorem tres_le_eee : (3 : ℝ) ≤ Real.exp (Real.exp (Real.exp 0)) := by
  rw [Real.exp_zero]
  have e1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  linarith [Real.add_one_le_exp (Real.exp 1)]

theorem um_le_log_eee {x : ℝ} (hx : Real.exp (Real.exp (Real.exp 0)) ≤ x) : 1 ≤ Real.log x := by
  have h3 := tres_le_eee
  rw [Real.le_log_iff_exp_le (by linarith)]
  refine le_trans ?_ hx
  rw [Real.exp_zero, Real.exp_le_exp]
  linarith [Real.add_one_le_exp (1 : ℝ)]

/-- **Littlewood para `π` sem RH**: se RH falha, `π(x) − Li(x) = Ω±(√x log log log x/log x)` com
constante `1` (de `π(x) − Li(x) = Ω±(x^θ)`, `½ < θ < Θ`). -/
theorem pi_littlewood_nao_RH (h : ¬ RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x ≤
      -(1 * √x * Real.log (Real.log (Real.log x)) / Real.log x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      1 * √x * Real.log (Real.log (Real.log x)) / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) := by
  have hT : 1 / 2 < Teta := lt_of_le_of_ne meio_le_Teta (fun he => h (rh_iff_Teta.mpr he.symm))
  set θ := (1 / 2 + Teta) / 2 with hθ
  have hθ1 : 1 / 2 < θ := by rw [hθ]; linarith
  have hθ2 : θ < Teta := by rw [hθ]; linarith
  set ε := θ - 1 / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hθε : θ = 1 / 2 + ε := by rw [hε]; ring
  -- a conta comum: para `N ≥ e^e`, `√N lll N/log N ≤ (1/ε)(N + 1)^θ`
  have hcota : ∀ N : ℕ, Real.exp (Real.exp (Real.exp 0)) ≤ (N : ℝ) →
      1 * √(N : ℝ) * Real.log (Real.log (Real.log N)) / Real.log N ≤ 1 / ε * ((N : ℝ) + 1) ^ θ := by
    intro N hx
    have hl := ATK.ZeroClasses.LittlewoodTeta.lll_ge hx
    have hr := ATK.ZeroClasses.LittlewoodMontagem.raiz_le_pot (tres_le_eee.trans hx) hε0
    rw [← hθε] at hr
    rw [one_mul]
    exact (div_le_self (mul_nonneg (Real.sqrt_nonneg _) hl) (um_le_log_eee hx)).trans hr
  have hcota0 : ∀ N : ℕ, Real.exp (Real.exp (Real.exp 0)) ≤ (N : ℝ) →
      0 ≤ 1 * √(N : ℝ) * Real.log (Real.log (Real.log N)) / Real.log N := by
    intro N hx
    have hl := ATK.ZeroClasses.LittlewoodTeta.lll_ge hx
    have := um_le_log_eee hx
    have := Real.sqrt_nonneg (N : ℝ)
    positivity
  refine ⟨fun X => ?_, fun X => ?_⟩ <;>
  · set X' := max X (Real.exp (Real.exp (Real.exp 0))) with hX'
    set K := ∑ n ∈ Finset.range (⌈X'⌉₊ + 1), |(Nat.primeCounting n : ℝ) - Li n| with hKdef
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hKn : ∀ n : ℕ, (n : ℝ) ≤ X' → |(Nat.primeCounting n : ℝ) - Li n| ≤ K := by
      intro n hn
      have hn' : n ≤ ⌈X'⌉₊ := by
        have := hn.trans (Nat.le_ceil X')
        exact_mod_cast this
      exact Finset.single_le_sum (f := fun n : ℕ => |(Nat.primeCounting n : ℝ) - Li n|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn'))
    first
    | obtain ⟨N, -, hN⟩ := pi_omega_menos hθ1.le hθ2 (1 / ε) K
      have hp : 0 ≤ 1 / ε * ((N : ℝ) + 1) ^ θ := by positivity
      have hNX : X' < (N : ℝ) := by
        by_contra hle
        push Not at hle
        have := neg_abs_le ((Nat.primeCounting N : ℝ) - Li N)
        linarith [hKn N hle]
      have hx : Real.exp (Real.exp (Real.exp 0)) ≤ (N : ℝ) := (le_max_right _ _).trans hNX.le
      refine ⟨N, (le_max_left _ _).trans hNX.le, ?_⟩
      rw [Nat.floor_natCast]
      linarith [hcota N hx]
    | obtain ⟨N, -, hN⟩ := pi_omega_mais hθ1.le hθ2 (1 / ε) K
      have hp : 0 ≤ 1 / ε * ((N : ℝ) + 1) ^ θ := by positivity
      have hNX : X' < (N : ℝ) := by
        by_contra hle
        push Not at hle
        have := le_abs_self ((Nat.primeCounting N : ℝ) - Li N)
        linarith [hKn N hle]
      have hx : Real.exp (Real.exp (Real.exp 0)) ≤ (N : ℝ) := (le_max_right _ _).trans hNX.le
      refine ⟨N, (le_max_left _ _).trans hNX.le, ?_⟩
      rw [Nat.floor_natCast]
      linarith [hcota N hx]

/-- **Littlewood para `π(x) − Li(x)`, sem hipóteses**:
`π(x) − Li(x) = Ω±(√x log log log x/log x)`. -/
theorem pi_littlewood : ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x ≤
      -(c * √x * Real.log (Real.log (Real.log x)) / Real.log x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * √x * Real.log (Real.log (Real.log x)) / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) := by
  by_cases hRH : RiemannHypothesis
  · exact ATK.ZeroClasses.LittlewoodPi.pi_littlewood_RH hRH
  · exact ⟨1, one_pos, pi_littlewood_nao_RH hRH⟩

/-- **`π(x) − Li(x)` troca de sinal infinitas vezes** (Littlewood 1914), sem hipóteses. -/
theorem pi_troca_sinal (X : ℝ) :
    (∃ x : ℝ, X ≤ x ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x < 0) ∧
    (∃ x : ℝ, X ≤ x ∧ 0 < (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x) := by
  obtain ⟨c, hc, h1, h2⟩ := pi_littlewood
  have hpos : ∀ x : ℝ, Real.exp (Real.exp (Real.exp 1)) ≤ x →
      0 < c * √x * Real.log (Real.log (Real.log x)) / Real.log x := by
    intro x hx
    have hl := ATK.ZeroClasses.LittlewoodTeta.lll_ge hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hx1 : 1 < x := lt_of_lt_of_le (by
      have := Real.add_one_le_exp (Real.exp (Real.exp 1))
      have := Real.exp_pos (Real.exp 1)
      linarith) hx
    have := Real.sqrt_pos.mpr hx0
    have := Real.log_pos hx1
    positivity
  constructor
  · obtain ⟨x, hx, hπ⟩ := h1 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩
  · obtain ⟨x, hx, hπ⟩ := h2 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩

end ATK.ZeroClasses.LittlewoodPiIncond

#print axioms ATK.ZeroClasses.LittlewoodPiIncond.abs_bR_le
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.abs_aPi_le
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.aPi_succ
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.norm_bP_le
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.abscissa_bP
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.LSeriesSummable_bP
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.GA_aPi_eq
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.logMul_bP
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.hasDerivAt_LSeries_bP
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.primitiva
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.semZeros_of_aPi_le
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.semZeros_of_aPi_ge
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.psi_nat
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.theta_nat
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.pi_nat
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.termo_Pi
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.Pi_sub_pi
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.aPi_eq
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.integral_inv_log_bounds
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.lam_sub_Li
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.aPi_bounds
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.sqrt_le_rpow
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.aPi_pequeno
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.pi_omega_mais
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.pi_omega_menos
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.tres_le_eee
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.um_le_log_eee
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.pi_littlewood_nao_RH
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.pi_littlewood
#print axioms ATK.ZeroClasses.LittlewoodPiIncond.pi_troca_sinal
