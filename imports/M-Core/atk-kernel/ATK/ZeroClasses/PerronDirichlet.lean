import ATK.ZeroClasses.Perron

/-!
# A fórmula de Perron truncada para séries de Dirichlet (rodada 45)

Para coeficientes `|f(n)| ≤ 1`, `x = N + ½`, `c > 0`, `σ + c > 1` (`σ = Re s`) e `T > 0`:

  `|Σ_{n ≤ N} f(n) n^{−s} − (1/2π) ∫_{−T}^{T} F(s + c + it) x^{c+it}/(c + it) dt| ≤ x^c (4x + 2) ζ(σ + c)/(πT)`,

com `F = LSeries f` (`perron_LSeries`). A prova:

1. **o termo** (`termo`): `f(n) n^{−s} e^{z log(x/n)} = f(n) n^{−(s+z)} x^z`;
2. **a troca de soma e integral** (`soma_perron`): convergência dominada com `|f(n) n^{−s−z} x^z/z| ≤ n^{−σ−c} x^c/c`
   dá `Σ_n f(n) n^{−s} perron(log(x/n), c, T) = (1/2π) ∫ F(s + c + it) x^{c+it}/(c + it) dt`;
3. **o degrau** (`perron_degrau`, rodada 44) em cada `n`, com `|log(x/n)| ≥ 1/(4x + 2)` (`abs_log_ge`) porque
   `x` é meio-inteiro.

É a segunda peça da entrada de Littlewood. Classificação (rodada 45): **ferramenta**. Não é RH.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

namespace ATK.ZeroClasses.PerronD

open ATK.ZeroClasses.Perron (perron perron_degrau)

/-- O meio-inteiro `x = N + ½`. -/
noncomputable abbrev xN (N : ℕ) : ℝ := N + 1 / 2

theorem xN_pos (N : ℕ) : 0 < xN N := by unfold xN; positivity

/-- **`|log(x/n)| ≥ 1/(4x + 2)`** para `x = N + ½` e `n ≥ 1`. -/
theorem abs_log_ge (N : ℕ) {n : ℕ} (hn : n ≠ 0) : 1 / (4 * xN N + 2) ≤ |Real.log (xN N / n)| := by
  have hx := xN_pos N
  have hm : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  have hm0 : (0 : ℝ) < n := by linarith
  have hk : 1 / (4 * xN N + 2) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    unfold xN
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  rcases le_or_gt n N with h | h
  · have hnN : (n : ℝ) + 1 / 2 ≤ xN N := by
      unfold xN
      have : (n : ℝ) ≤ N := by exact_mod_cast h
      linarith
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx hm0)
    rw [inv_div] at hl
    have h2 : 1 / (2 * xN N) ≤ 1 - n / xN N := by
      rw [show 1 - (n : ℝ) / xN N = (xN N - n) / xN N by field_simp, div_le_div_iff₀ (by positivity) hx]
      nlinarith
    have h3 : 1 / (4 * xN N + 2) ≤ 1 / (2 * xN N) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hpos : 0 ≤ Real.log (xN N / n) := by
      have : 0 < 1 / (2 * xN N) := by positivity
      linarith
    rw [abs_of_nonneg hpos]
    linarith
  · have hnN : xN N + 1 / 2 ≤ (n : ℝ) := by
      unfold xN
      have : (N : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith
    have e : Real.log (xN N / n) = -Real.log (n / xN N) := by rw [← Real.log_inv, inv_div]
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hm0 hx)
    rw [inv_div] at hl
    have key : 1 / (4 * xN N + 2) ≤ Real.log (n / xN N) := by
      rcases le_or_gt (n : ℝ) (2 * xN N) with h2 | h2
      · have h4 : 1 / (4 * xN N) ≤ 1 - xN N / n := by
          rw [show 1 - xN N / (n : ℝ) = (n - xN N) / n by field_simp, div_le_div_iff₀ (by positivity) hm0]
          nlinarith
        have h5 : 1 / (4 * xN N + 2) ≤ 1 / (4 * xN N) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
      · have h6 : Real.log 2 ≤ Real.log (n / xN N) :=
          Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hx]; linarith)
        have h7 := Real.log_two_gt_d9
        linarith
    have hk0 : 0 < 1 / (4 * xN N + 2) := by positivity
    rw [e, abs_neg, abs_of_nonneg (by linarith)]
    exact key

theorem log_ne_zero (N : ℕ) {n : ℕ} (hn : n ≠ 0) : Real.log (xN N / n) ≠ 0 := by
  intro h
  have := abs_log_ge N hn
  rw [h, abs_zero] at this
  have : 0 < 1 / (4 * xN N + 2) := by have := xN_pos N; positivity
  linarith

theorem inv_abs_log_le (N : ℕ) {n : ℕ} (hn : n ≠ 0) : 1 / |Real.log (xN N / n)| ≤ 4 * xN N + 2 := by
  have hx := xN_pos N
  rw [one_div_le (abs_pos.mpr (log_ne_zero N hn)) (by positivity)]
  exact abs_log_ge N hn

/-- **O termo**: `f(n) n^{−s} e^{z log(x/n)} = f(n) n^{−(s+z)} x^z`. -/
theorem termo (f : ℕ → ℂ) (s z : ℂ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    LSeries.term f s n * cexp (z * (Real.log (x / n) : ℂ)) = LSeries.term f (s + z) n * (x : ℂ) ^ z := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, cpow_add _ _ hn',
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), cpow_def_of_ne_zero hn' s, cpow_def_of_ne_zero hn' z,
    Real.log_div hx.ne' hnr.ne', ← ofReal_log hx.le, ← natCast_log]
  have e1 : cexp (z * ((Real.log x - Real.log n : ℝ) : ℂ)) =
      cexp ((Real.log x : ℂ) * z) / cexp ((Real.log n : ℂ) * z) := by
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [e1]
  have h1 : cexp ((Real.log n : ℂ) * s) ≠ 0 := Complex.exp_ne_zero _
  have h2 : cexp ((Real.log n : ℂ) * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- `|f(n) n^{−s}| ≤ n^{−Re s}` para `|f| ≤ 1`. -/
theorem norm_term_le_um {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (s : ℂ) (n : ℕ) :
    ‖LSeries.term f s n‖ ≤ ‖LSeries.term (fun _ => (1 : ℂ)) (s.re : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp only [norm_one, ofReal_re]
  split_ifs
  · exact le_rfl
  · exact div_le_div_of_nonneg_right (hf n) (by positivity)

/-- `ζ(σ)` como `Σ ‖n^{−σ}‖`. -/
theorem summable_um {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖LSeries.term (fun _ => (1 : ℂ)) (σ : ℂ) n‖ :=
  (LSeriesSummable_of_bounded_of_one_lt_real (m := 1) (fun n _ => by simp) hσ).norm

/-- O núcleo de Perron com o termo dentro: `f(n) n^{−s} e^{zL}/z = f(n) n^{−(s+z)} x^z/z`. -/
theorem termo_div (f : ℕ → ℂ) (s : ℂ) {x : ℝ} (hx : 0 < x) (c t : ℝ) (n : ℕ) :
    LSeries.term f s n * (cexp (((c : ℂ) + t * I) * (Real.log (x / n) : ℂ)) / ((c : ℂ) + t * I)) =
      LSeries.term f (s + ((c : ℂ) + t * I)) n * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
  rw [← mul_div_assoc, termo f s _ hx n]

theorem ne_zero_ct {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- **A troca**: `Σ_n f(n) n^{−s} perron(log(x/n), c, T) = (1/2π) ∫ F(s + c + it) x^{c+it}/(c + it) dt`. -/
theorem soma_perron {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} {x c T : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc : 1 < s.re + c) :
    HasSum (fun n => LSeries.term f s n * perron (Real.log (x / n)) c T)
      ((2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I)) := by
  have hZ := summable_um (σ := s.re + c) hsc
  have hint : HasSum (fun n => ∫ t in (-T)..T, LSeries.term f s n *
      (cexp (((c : ℂ) + t * I) * (Real.log (x / n) : ℂ)) / ((c : ℂ) + t * I)))
      (∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c / c) (fun n => ?_)
      (fun n => ae_of_all _ fun t _ => ?_) (ae_of_all _ fun t _ => ?_) ?_ (ae_of_all _ fun t _ => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) fun t => ne_zero_ct hc t)
    · rw [termo_div f s hx c t n, norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
      have hre : (s + ((c : ℂ) + t * I)).re = s.re + c := by simp
      have h1 := norm_term_le_um hf (s + ((c : ℂ) + t * I)) n
      rw [hre] at h1
      have h3 : ((c : ℂ) + t * I).re = c := by simp
      have h2 : c ≤ ‖(c : ℂ) + t * I‖ := by
        have := Complex.abs_re_le_norm ((c : ℂ) + t * I)
        rw [h3] at this
        linarith [le_abs_self c]
      rw [h3]
      have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx c
      calc ‖LSeries.term f (s + ((c : ℂ) + t * I)) n‖ * x ^ c / ‖(c : ℂ) + t * I‖
          ≤ ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c / ‖(c : ℂ) + t * I‖ :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hxc.le) (norm_nonneg _)
        _ ≤ ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * x ^ c / c :=
            div_le_div_of_nonneg_left (by positivity) hc h2
    · exact (hZ.mul_right (x ^ c)).div_const c
    · exact intervalIntegrable_const
    · have hs : LSeriesSummable f (s + ((c : ℂ) + t * I)) :=
        LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => hf n) (by simp; linarith)
      have := (hs.LSeriesHasSum.mul_right ((x : ℂ) ^ ((c : ℂ) + t * I))).div_const ((c : ℂ) + t * I)
      convert this using 1
      funext n
      exact termo_div f s hx c t n
  have := hint.mul_left (2 * π : ℂ)⁻¹
  convert this using 1
  funext n
  simp only [perron, intervalIntegral.integral_const_mul]
  ring

/-- **Perron truncada para séries de Dirichlet** com `|f| ≤ 1`, `x = N + ½`:
`|Σ_{n ≤ N} f(n) n^{−s} − (1/2π) ∫_{−T}^{T} F(s + c + it) x^{c+it}/(c + it) dt| ≤ x^c (4x + 2) ζ(σ + c)/(πT)`. -/
theorem perron_LSeries {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {s : ℂ} {c T : ℝ} (hc : 0 < c)
    (hsc : 1 < s.re + c) (hT : 0 < T) :
    ‖∑ n ∈ Finset.range (N + 1), LSeries.term f s n -
      (2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (xN N : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I)‖ ≤
      xN N ^ c * (4 * xN N + 2) / (π * T) *
        ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ := by
  have hx := xN_pos N
  have hZ := summable_um (σ := s.re + c) hsc
  have hA := soma_perron (T := T) hf hx hc hsc
  -- o degrau como série finita
  have hB : HasSum (fun n => LSeries.term f s n * (if 0 < Real.log (xN N / n) then (1 : ℂ) else 0))
      (∑ n ∈ Finset.range (N + 1), LSeries.term f s n) := by
    have h0 : ∀ n ∉ Finset.range (N + 1),
        LSeries.term f s n * (if 0 < Real.log (xN N / n) then (1 : ℂ) else 0) = 0 := by
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      have hn0 : n ≠ 0 := by omega
      have hm0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have hneg : Real.log (xN N / n) < 0 := by
        apply Real.log_neg (div_pos hx hm0)
        rw [div_lt_one hm0]
        unfold xN
        have : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
        linarith
      simp [not_lt.mpr hneg.le]
    have hsum : ∑ n ∈ Finset.range (N + 1),
        LSeries.term f s n * (if 0 < Real.log (xN N / n) then (1 : ℂ) else 0) =
        ∑ n ∈ Finset.range (N + 1), LSeries.term f s n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have hm0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        have hpos : 0 < Real.log (xN N / n) := by
          rw [Finset.mem_range] at hn
          apply Real.log_pos
          rw [one_lt_div hm0]
          unfold xN
          have : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp hn
          linarith
        simp [hpos]
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero h0
  have hE : HasSum (fun n => LSeries.term f s n *
      ((if 0 < Real.log (xN N / n) then (1 : ℂ) else 0) - perron (Real.log (xN N / n)) c T))
      (∑ n ∈ Finset.range (N + 1), LSeries.term f s n -
        (2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, LSeries f (s + ((c : ℂ) + t * I)) * (xN N : ℂ) ^ ((c : ℂ) + t * I) /
          ((c : ℂ) + t * I)) := by
    convert hB.sub hA using 1
    funext n
    ring
  refine hE.norm_le_of_bounded (hZ.hasSum.mul_left (xN N ^ c * (4 * xN N + 2) / (π * T))) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hL := log_ne_zero N hn
  have h1 := perron_degrau hL hc hT
  have h2 : ‖LSeries.term f s n‖ * Real.exp (c * Real.log (xN N / n)) ≤
      ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * xN N ^ c := by
    have e := termo f s (c : ℂ) hx n
    have := congrArg norm e
    rw [norm_mul, norm_mul, ← ofReal_mul, norm_exp_ofReal, norm_cpow_eq_rpow_re_of_pos hx, ofReal_re] at this
    rw [this]
    have h := norm_term_le_um hf (s + c) n
    have hre : (s + (c : ℂ)).re = s.re + c := by simp
    rw [hre] at h
    exact mul_le_mul_of_nonneg_right h (Real.rpow_pos_of_pos hx c).le
  have h3 := inv_abs_log_le N hn
  have hπT : 0 < π * T := mul_pos Real.pi_pos hT
  calc ‖LSeries.term f s n *
        ((if 0 < Real.log (xN N / n) then (1 : ℂ) else 0) - perron (Real.log (xN N / n)) c T)‖
      = ‖LSeries.term f s n‖ *
        ‖perron (Real.log (xN N / n)) c T - (if 0 < Real.log (xN N / n) then (1 : ℂ) else 0)‖ := by
        rw [norm_mul, norm_sub_rev]
    _ ≤ ‖LSeries.term f s n‖ * (Real.exp (c * Real.log (xN N / n)) / (π * T * |Real.log (xN N / n)|)) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (‖LSeries.term f s n‖ * Real.exp (c * Real.log (xN N / n))) * (1 / |Real.log (xN N / n)|) /
          (π * T) := by ring
    _ ≤ (‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ * xN N ^ c) * (4 * xN N + 2) / (π * T) := by
        apply div_le_div_of_nonneg_right _ hπT.le
        exact mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = xN N ^ c * (4 * xN N + 2) / (π * T) *
          ‖LSeries.term (fun _ => (1 : ℂ)) ((s.re + c : ℝ) : ℂ) n‖ := by ring

end ATK.ZeroClasses.PerronD

#print axioms ATK.ZeroClasses.PerronD.xN_pos
#print axioms ATK.ZeroClasses.PerronD.abs_log_ge
#print axioms ATK.ZeroClasses.PerronD.log_ne_zero
#print axioms ATK.ZeroClasses.PerronD.inv_abs_log_le
#print axioms ATK.ZeroClasses.PerronD.termo
#print axioms ATK.ZeroClasses.PerronD.norm_term_le_um
#print axioms ATK.ZeroClasses.PerronD.summable_um
#print axioms ATK.ZeroClasses.PerronD.termo_div
#print axioms ATK.ZeroClasses.PerronD.ne_zero_ct
#print axioms ATK.ZeroClasses.PerronD.soma_perron
#print axioms ATK.ZeroClasses.PerronD.perron_LSeries
