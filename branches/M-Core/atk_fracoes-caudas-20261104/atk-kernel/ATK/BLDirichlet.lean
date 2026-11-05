import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Bohr–Landau, passo 4 — média quadrática do polinômio de Dirichlet

`D_N(σ + it) = Σ_{n<N} (n+1)^{−(σ+it)}`. Para `1/2 < σ₀ ≤ 3/4`, existe `C` tal que, para todo
`σ ≥ σ₀`, todo `N` e todo `U ≥ max(N, 1)`:

  **`∫_U^{2U} |D_N(σ + it)|² dt ≤ C·U`** (`media_D`).

Prova elementar: `|D|² = Σ_{m,n} a_m a_n cos(t(L_n − L_m))` com `a_m = (m+1)^{−σ}`,
`L_m = log(m+1)`; a diagonal dá `U Σ a_m²`; fora dela `|∫cos| ≤ 2/|L_n − L_m|`,
`1/|log((n+1)/(m+1))| ≤ max(m+1,n+1)/|n − m|`, AM-GM, e somas harmônicas.
-/

open Complex Finset intervalIntegral

namespace ATK.BLDirichlet

/-- `D_N(σ + it)`. -/
noncomputable def D (N : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ range N, ((n : ℂ) + 1) ^ (-((σ : ℂ) + (t : ℂ) * I))

noncomputable def a (σ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-σ)
noncomputable def L (n : ℕ) : ℝ := Real.log ((n : ℝ) + 1)

theorem a_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ a σ n := Real.rpow_nonneg (by positivity) _

theorem term_eq (σ t : ℝ) (n : ℕ) :
    ((n : ℂ) + 1) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      (a σ n : ℂ) * Complex.exp (-((t * L n : ℝ) : ℂ) * I) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hc, cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← ofReal_log hpos.le]
  unfold a L
  rw [Real.rpow_def_of_pos hpos, ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

theorem normSq_D (N : ℕ) (σ t : ℝ) :
    ‖D N σ t‖ ^ 2 =
      ∑ m ∈ range N, ∑ n ∈ range N, a σ m * a σ n * Real.cos (t * (L n - L m)) := by
  have hns : ∀ z : ℂ, ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
    intro z; rw [Complex.mul_conj, Complex.sq_norm]; simp
  rw [hns]
  unfold D
  simp_rw [term_eq]
  rw [map_sum, Finset.sum_mul_sum, re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hconj : (starRingEnd ℂ) ((a σ n : ℂ) * Complex.exp (-((t * L n : ℝ) : ℂ) * I)) =
      (a σ n : ℂ) * Complex.exp (((t * L n : ℝ) : ℂ) * I) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal]
    ring_nf
  rw [hconj]
  have key : (a σ m : ℂ) * Complex.exp (-((t * L m : ℝ) : ℂ) * I) *
      ((a σ n : ℂ) * Complex.exp (((t * L n : ℝ) : ℂ) * I)) =
      ((a σ m * a σ n : ℝ) : ℂ) * Complex.exp (((t * (L n - L m) : ℝ) : ℂ) * I) := by
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    push_cast; ring_nf
  rw [key, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem integral_cos_bound {l U : ℝ} (hl : l ≠ 0) :
    |∫ t in U..2 * U, Real.cos (t * l)| ≤ 2 / |l| := by
  have h : (fun t : ℝ => Real.cos (t * l)) = fun t => Real.cos (l * t) := by
    funext t; rw [mul_comm]
  rw [h, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hl, integral_cos,
    smul_eq_mul, abs_mul, abs_inv]
  have : |Real.sin (l * (2 * U)) - Real.sin (l * U)| ≤ 2 := by
    have h1 := Real.abs_sin_le_one (l * (2 * U))
    have h2 := Real.abs_sin_le_one (l * U)
    calc _ ≤ |Real.sin (l * (2 * U))| + |Real.sin (l * U)| := abs_sub _ _
      _ ≤ 2 := by linarith
  calc |l|⁻¹ * |Real.sin (l * (2 * U)) - Real.sin (l * U)| ≤ |l|⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (abs_nonneg l))
    _ = 2 / |l| := by ring

theorem L_injective {m n : ℕ} (h : m ≠ n) : L n - L m ≠ 0 := by
  unfold L
  intro he
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr hn) (Set.mem_Ioi.mpr hm) (by linarith)
  apply h
  exact_mod_cast (by linarith : (m : ℝ) = n)

theorem continuous_term (σ : ℝ) (m n : ℕ) :
    Continuous fun t : ℝ => a σ m * a σ n * Real.cos (t * (L n - L m)) := by fun_prop

/-- Expansão integrada: diagonal mais fora da diagonal. -/
theorem integral_D_sq_le (N : ℕ) (σ : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    ∫ t in U..2 * U, ‖D N σ t‖ ^ 2 ≤
      U * ∑ m ∈ range N, a σ m ^ 2 +
        ∑ m ∈ range N, ∑ n ∈ range N,
          (if m = n then 0 else 2 * (a σ m * a σ n) / |L n - L m|) := by
  simp_rw [normSq_D]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_finsetSum fun n _ =>
    (continuous_term σ _ n).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m hm => ?_
  have hsplit : ∀ n ∈ range N, a σ m * a σ n * ∫ t in U..2 * U, Real.cos (t * (L n - L m)) ≤
      (if m = n then U * a σ m ^ 2 else 0) +
        (if m = n then 0 else 2 * (a σ m * a σ n) / |L n - L m|) := by
    intro n _
    by_cases hmn : m = n
    · subst hmn
      simp only [sub_self, mul_zero, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul,
        mul_one, if_true, add_zero]
      nlinarith [a_nonneg σ m]
    · simp only [hmn, if_false, zero_add]
      have hl := L_injective hmn
      have hb := integral_cos_bound (U := U) hl
      have hpos : 0 ≤ a σ m * a σ n := mul_nonneg (a_nonneg σ m) (a_nonneg σ n)
      calc a σ m * a σ n * ∫ t in U..2 * U, Real.cos (t * (L n - L m))
          ≤ a σ m * a σ n * |∫ t in U..2 * U, Real.cos (t * (L n - L m))| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hpos
        _ ≤ a σ m * a σ n * (2 / |L n - L m|) := mul_le_mul_of_nonneg_left hb hpos
        _ = 2 * (a σ m * a σ n) / |L n - L m| := by ring
  calc ∑ n ∈ range N, a σ m * a σ n * ∫ t in U..2 * U, Real.cos (t * (L n - L m))
      ≤ ∑ n ∈ range N, ((if m = n then U * a σ m ^ 2 else 0) +
          (if m = n then 0 else 2 * (a σ m * a σ n) / |L n - L m|)) := Finset.sum_le_sum hsplit
    _ = U * a σ m ^ 2 + ∑ n ∈ range N,
          (if m = n then 0 else 2 * (a σ m * a σ n) / |L n - L m|) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq _ _ (fun _ => U * a σ m ^ 2)]
        simp [hm]

/-- `1/|L_n − L_m| ≤ max(m+1,n+1)/|n − m|` para `m ≠ n`. -/
theorem inv_abs_L_le {m n : ℕ} (h : m ≠ n) :
    1 / |L n - L m| ≤ max ((m : ℝ) + 1) ((n : ℝ) + 1) / |(n : ℝ) - m| := by
  have key : ∀ {p q : ℕ}, p < q → 1 / (L q - L p) ≤ ((q : ℝ) + 1) / ((q : ℝ) - p) ∧
      0 < L q - L p := by
    intro p q hpq
    have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
    have hlog : ((q : ℝ) - p) / ((q : ℝ) + 1) ≤ L q - L p := by
      unfold L
      rw [← Real.log_div hq.ne' hp.ne']
      have := Real.one_sub_inv_le_log_of_pos (div_pos hq hp)
      calc ((q : ℝ) - p) / ((q : ℝ) + 1) = 1 - (((q : ℝ) + 1) / ((p : ℝ) + 1))⁻¹ := by
            field_simp; ring
        _ ≤ _ := this
    have hpos : 0 < ((q : ℝ) - p) / ((q : ℝ) + 1) := div_pos (by linarith) hq
    refine ⟨?_, lt_of_lt_of_le hpos hlog⟩
    calc 1 / (L q - L p) ≤ 1 / (((q : ℝ) - p) / ((q : ℝ) + 1)) :=
          one_div_le_one_div_of_le hpos hlog
      _ = ((q : ℝ) + 1) / ((q : ℝ) - p) := by field_simp
  rcases lt_or_gt_of_ne h with hlt | hgt
  · obtain ⟨h1, h2⟩ := key hlt
    have hmn : (m : ℝ) < n := by exact_mod_cast hlt
    rw [abs_of_pos h2, abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) - m),
      max_eq_right (by linarith)]
    exact h1
  · obtain ⟨h1, h2⟩ := key hgt
    have hnm : (n : ℝ) < m := by exact_mod_cast hgt
    rw [abs_of_neg (by linarith : L n - L m < 0), abs_of_neg (by linarith : (n : ℝ) - m < 0),
      max_eq_left (by linarith)]
    rw [show -(L n - L m) = L m - L n by ring, show -((n : ℝ) - m) = (m : ℝ) - n by ring]
    exact h1

/-- O núcleo fora da diagonal. -/
noncomputable def k (m n : ℕ) : ℝ :=
  if m = n then 0 else max ((m : ℝ) + 1) ((n : ℝ) + 1) / |(n : ℝ) - m|

theorem k_symm (m n : ℕ) : k m n = k n m := by
  unfold k
  by_cases h : m = n
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, abs_sub_comm]

theorem k_nonneg (m n : ℕ) : 0 ≤ k m n := by
  unfold k; split_ifs
  · rfl
  · positivity

theorem offdiag_le (σ : ℝ) (m n : ℕ) :
    (if m = n then 0 else 2 * (a σ m * a σ n) / |L n - L m|) ≤
      (a σ m ^ 2 + a σ n ^ 2) * k m n := by
  unfold k
  by_cases h : m = n
  · simp [h]
  · rw [if_neg h, if_neg h]
    have hb := inv_abs_L_le h
    have hamgm : 2 * (a σ m * a σ n) ≤ a σ m ^ 2 + a σ n ^ 2 := by
      nlinarith [sq_nonneg (a σ m - a σ n)]
    have hn2 : 0 ≤ 2 * (a σ m * a σ n) := by
      have := mul_nonneg (a_nonneg σ m) (a_nonneg σ n); linarith
    calc 2 * (a σ m * a σ n) / |L n - L m| = 2 * (a σ m * a σ n) * (1 / |L n - L m|) := by ring
      _ ≤ 2 * (a σ m * a σ n) * (max ((m : ℝ) + 1) ((n : ℝ) + 1) / |(n : ℝ) - m|) :=
          mul_le_mul_of_nonneg_left hb hn2
      _ ≤ (a σ m ^ 2 + a σ n ^ 2) * (max ((m : ℝ) + 1) ((n : ℝ) + 1) / |(n : ℝ) - m|) :=
          mul_le_mul_of_nonneg_right hamgm (by positivity)

/-- Simetrização: `Σ_{m,n} (a_m² + a_n²) k = 2 Σ_m a_m² Σ_n k`. -/
theorem sum_sym (σ : ℝ) (N : ℕ) :
    ∑ m ∈ range N, ∑ n ∈ range N, (a σ m ^ 2 + a σ n ^ 2) * k m n =
      2 * ∑ m ∈ range N, a σ m ^ 2 * ∑ n ∈ range N, k m n := by
  have h1 : ∑ m ∈ range N, ∑ n ∈ range N, a σ n ^ 2 * k m n =
      ∑ m ∈ range N, ∑ n ∈ range N, a σ m ^ 2 * k m n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [k_symm]
  calc ∑ m ∈ range N, ∑ n ∈ range N, (a σ m ^ 2 + a σ n ^ 2) * k m n
      = ∑ m ∈ range N, ∑ n ∈ range N, a σ m ^ 2 * k m n +
          ∑ m ∈ range N, ∑ n ∈ range N, a σ n ^ 2 * k m n := by
        simp_rw [add_mul, Finset.sum_add_distrib]
    _ = 2 * ∑ m ∈ range N, ∑ n ∈ range N, a σ m ^ 2 * k m n := by rw [h1]; ring
    _ = 2 * ∑ m ∈ range N, a σ m ^ 2 * ∑ n ∈ range N, k m n := by simp_rw [Finset.mul_sum]

/-- `k(m,n) ≤ 1 + (m+1)·h(m,n)`, `h(m,n) = 1/|n − m|` fora da diagonal. -/
theorem k_le (m n : ℕ) :
    k m n ≤ (if m = n then 0 else 1) + ((m : ℝ) + 1) * (if m = n then 0 else 1 / |(n : ℝ) - m|) := by
  unfold k
  by_cases h : m = n
  · simp [h]
  · simp only [h, if_false]
    have hpos : 0 < |(n : ℝ) - m| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast Ne.symm h))
    rcases le_or_gt n m with hnm | hmn
    · have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      rw [max_eq_left (by linarith)]
      have : ((m : ℝ) + 1) / |(n : ℝ) - m| = ((m : ℝ) + 1) * (1 / |(n : ℝ) - m|) := by ring
      linarith
    · have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
      rw [max_eq_right (by linarith), abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) - m)]
      have hne : (n : ℝ) - m ≠ 0 := by linarith
      have e : ((n : ℝ) + 1) / ((n : ℝ) - m) = 1 + ((m : ℝ) + 1) * (1 / ((n : ℝ) - m)) := by
        field_simp; ring
      linarith

/-- Soma harmônica: `Σ_{d<N} 1/(d+1) ≤ 1 + log N`. -/
theorem harm_le (N : ℕ) : ∑ d ∈ range N, 1 / ((d : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ d ∈ range N, 1 / ((d : ℝ) + 1) := by
    unfold harmonic; push_cast; simp
  rw [← e]; exact h

/-- `Σ_{n<N, n≠m} 1/|n − m| ≤ 2(1 + log N)`. -/
theorem sum_h_le {m N : ℕ} (hm : m < N) :
    ∑ n ∈ range N, (if m = n then (0 : ℝ) else 1 / |(n : ℝ) - m|) ≤ 2 * (1 + Real.log N) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = m + 1 + j := ⟨N - m - 1, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_succ]
  have hleft : ∑ n ∈ range m, (if m = n then (0 : ℝ) else 1 / |(n : ℝ) - m|) =
      ∑ d ∈ range m, 1 / ((d : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_range] at hd
    rw [if_neg (by omega)]
    have e : ((m - 1 - d : ℕ) : ℝ) - m = -((d : ℝ) + 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e, abs_neg, abs_of_pos (by positivity)]
  have hright : ∑ x ∈ range j, (if m = m + 1 + x then (0 : ℝ) else 1 / |((m + 1 + x : ℕ) : ℝ) - m|) =
      ∑ d ∈ range j, 1 / ((d : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [if_neg (by omega)]
    rw [show ((m + 1 + d : ℕ) : ℝ) - m = (d : ℝ) + 1 by push_cast; ring,
      abs_of_pos (by positivity)]
  rw [hleft, hright, if_pos rfl, add_zero]
  have hsub1 : ∑ d ∈ range m, 1 / ((d : ℝ) + 1) ≤ ∑ d ∈ range (m + 1 + j), 1 / ((d : ℝ) + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun _ _ _ => by positivity
  have hsub2 : ∑ d ∈ range j, 1 / ((d : ℝ) + 1) ≤ ∑ d ∈ range (m + 1 + j), 1 / ((d : ℝ) + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun _ _ _ => by positivity
  have hH := harm_le (m + 1 + j)
  linarith

/-- `Σ_n k(m,n) ≤ N + 2(m+1)(1 + log N)`. -/
theorem sum_k_le {m N : ℕ} (hm : m < N) :
    ∑ n ∈ range N, k m n ≤ N + 2 * ((m : ℝ) + 1) * (1 + Real.log N) := by
  calc ∑ n ∈ range N, k m n
      ≤ ∑ n ∈ range N, ((if m = n then (0 : ℝ) else 1) +
          ((m : ℝ) + 1) * (if m = n then 0 else 1 / |(n : ℝ) - m|)) :=
        Finset.sum_le_sum fun n _ => k_le m n
    _ = ∑ n ∈ range N, (if m = n then (0 : ℝ) else 1) +
          ((m : ℝ) + 1) * ∑ n ∈ range N, (if m = n then (0 : ℝ) else 1 / |(n : ℝ) - m|) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ N + ((m : ℝ) + 1) * (2 * (1 + Real.log N)) := by
        gcongr
        · calc ∑ n ∈ range N, (if m = n then (0 : ℝ) else 1) ≤ ∑ n ∈ range N, (1 : ℝ) :=
                Finset.sum_le_sum fun n _ => by split_ifs <;> norm_num
            _ = N := by simp
        · exact sum_h_le hm
    _ = N + 2 * ((m : ℝ) + 1) * (1 + Real.log N) := by ring

/-- `Σ_{m<N} (m+1)^{−q} ≤ 1 + (N^{1−q} − 1)/(1 − q)` para `N ≥ 1` (comparação com integral). -/
theorem sum_rpow_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ range N, ((m : ℝ) + 1) ^ (-q) ≤ 1 + ((N : ℝ) ^ (1 - q) - 1) / (1 - q) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = 1 + M := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_one]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-q)) (Set.Icc (1 : ℝ) (1 + M)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hs := hanti.sum_le_integral
  have hcast : ∀ i : ℕ, (1 : ℝ) + ((i + 1 : ℕ) : ℝ) = ((1 + i : ℕ) : ℝ) + 1 := by
    intro i; push_cast; ring
  simp_rw [hcast] at hs
  have hint : ∫ x in (1 : ℝ)..1 + M, x ^ (-q) = (((1 : ℝ) + M) ^ (1 - q) - 1) / (1 - q) := by
    rw [integral_rpow (Or.inr ⟨by intro h; apply hq1; linarith, by
      rw [Set.mem_uIcc]; intro h; rcases h with h | h <;> linarith [h.1, h.2]⟩)]
    rw [show -q + 1 = 1 - q by ring, Real.one_rpow]
  have hNc : ((1 + M : ℕ) : ℝ) = 1 + M := by push_cast; ring
  rw [hNc]
  linarith [hint ▸ hs]

theorem a_sq (σ : ℝ) (m : ℕ) : a σ m ^ 2 = ((m : ℝ) + 1) ^ (-2 * σ) := by
  unfold a
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

/-- `(1 + log x)(1 + 2x^{1−ε}) ≤ (4 + 2/ε)·U` para `1 ≤ x ≤ U`. -/
theorem log_bound {ε x U : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : 1 ≤ x) (hxU : x ≤ U) :
    (1 + Real.log x) * (1 + 2 * x ^ (1 - ε)) ≤ (4 + 2 / ε) * U := by
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hpow : x ^ (1 - ε) ≤ x := by
    calc x ^ (1 - ε) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = x := Real.rpow_one x
  have hpow0 : 0 ≤ x ^ (1 - ε) := Real.rpow_nonneg hx0 _
  have hl2 : Real.log x * x ^ (1 - ε) ≤ x / ε := by
    have h1 := Real.log_le_rpow_div hx0 hε
    calc Real.log x * x ^ (1 - ε) ≤ x ^ ε / ε * x ^ (1 - ε) := mul_le_mul_of_nonneg_right h1 hpow0
      _ = x / ε := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add' hx0 (by norm_num), show ε + (1 - ε) = 1 by ring,
            Real.rpow_one]
  have hxU' : x / ε ≤ U / ε := div_le_div_of_nonneg_right hxU hε.le
  have hU1 : 1 ≤ U := hx.trans hxU
  calc (1 + Real.log x) * (1 + 2 * x ^ (1 - ε))
      = 1 + 2 * x ^ (1 - ε) + Real.log x + 2 * (Real.log x * x ^ (1 - ε)) := by ring
    _ ≤ U + 2 * U + U + 2 * (U / ε) := by nlinarith
    _ = (4 + 2 / ε) * U := by ring

/-- **Média quadrática do polinômio de Dirichlet** (`N ≤ U`, `σ ≥ σ₀ > 1/2`). -/
theorem media_D {σ0 : ℝ} (h0 : 1 / 2 < σ0) (h1 : σ0 ≤ 3 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ0 ≤ σ → ∀ N : ℕ, ∀ U : ℝ, 1 ≤ U → (N : ℝ) ≤ U →
      ∫ t in U..2 * U, ‖D N σ t‖ ^ 2 ≤ C * U := by
  set ε := 2 * σ0 - 1 with hεdef
  have hε : 0 < ε := by linarith
  have hε1 : ε ≤ 1 / 2 := by linarith
  set S := 1 + 1 / ε with hS
  refine ⟨3 * S + 4 * (4 + 2 / ε), by positivity, fun σ hσ N U hU hNU => ?_⟩
  have hU0 : 0 ≤ U := by linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have : (fun t : ℝ => ‖D 0 σ t‖ ^ 2) = fun _ => 0 := by funext t; simp [D]
    rw [this, intervalIntegral.integral_zero]; positivity
  have hN1 : 1 ≤ N := hNpos
  -- soma dos quadrados
  have hSum : ∑ m ∈ range N, a σ m ^ 2 ≤ S := by
    calc ∑ m ∈ range N, a σ m ^ 2 ≤ ∑ m ∈ range N, ((m : ℝ) + 1) ^ (-(1 + ε)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [a_sq]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
            (by linarith)
      _ ≤ 1 + ((N : ℝ) ^ (1 - (1 + ε)) - 1) / (1 - (1 + ε)) :=
          sum_rpow_le (by linarith) (by linarith) hN1
      _ ≤ S := by
          rw [show 1 - (1 + ε) = -ε by ring, hS, div_neg, sub_div]
          have hp : 0 ≤ (N : ℝ) ^ (-ε) / ε :=
            div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hε.le
          linarith
  have hSum2 : ∑ m ∈ range N, a σ m ^ 2 * ((m : ℝ) + 1) ≤ 1 + 2 * (N : ℝ) ^ (1 - ε) := by
    calc ∑ m ∈ range N, a σ m ^ 2 * ((m : ℝ) + 1) ≤ ∑ m ∈ range N, ((m : ℝ) + 1) ^ (-ε) := by
          refine Finset.sum_le_sum fun m _ => ?_
          have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
          rw [a_sq, ← Real.rpow_add_one (by linarith)]
          exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      _ ≤ 1 + ((N : ℝ) ^ (1 - ε) - 1) / (1 - ε) := sum_rpow_le hε (by linarith) hN1
      _ ≤ 1 + 2 * (N : ℝ) ^ (1 - ε) := by
          have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
          have hp : 1 ≤ (N : ℝ) ^ (1 - ε) := Real.one_le_rpow hN1r (by linarith)
          have : ((N : ℝ) ^ (1 - ε) - 1) / (1 - ε) ≤ 2 * ((N : ℝ) ^ (1 - ε) - 1) := by
            rw [div_le_iff₀ (by linarith)]; nlinarith
          linarith
  have hoff : ∑ m ∈ range N, ∑ n ∈ range N,
      (if m = n then 0 else 2 * (a σ m * a σ n) / |L n - L m|) ≤
        2 * N * S + 4 * ((4 + 2 / ε) * U) := by
    calc ∑ m ∈ range N, ∑ n ∈ range N, (if m = n then 0 else 2 * (a σ m * a σ n) / |L n - L m|)
        ≤ ∑ m ∈ range N, ∑ n ∈ range N, (a σ m ^ 2 + a σ n ^ 2) * k m n :=
          Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => offdiag_le σ m n
      _ = 2 * ∑ m ∈ range N, a σ m ^ 2 * ∑ n ∈ range N, k m n := sum_sym σ N
      _ ≤ 2 * ∑ m ∈ range N, a σ m ^ 2 * (N + 2 * ((m : ℝ) + 1) * (1 + Real.log N)) := by
          gcongr with m hm
          exact sum_k_le (Finset.mem_range.mp hm)
      _ = 2 * N * ∑ m ∈ range N, a σ m ^ 2 +
            4 * (1 + Real.log N) * ∑ m ∈ range N, a σ m ^ 2 * ((m : ℝ) + 1) := by
          simp_rw [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ ≤ 2 * N * S + 4 * ((1 + Real.log N) * (1 + 2 * (N : ℝ) ^ (1 - ε))) := by
          have hlog : 0 ≤ 1 + Real.log N := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN1); linarith
          have hN0' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          nlinarith [mul_le_mul_of_nonneg_left hSum (by positivity : (0:ℝ) ≤ 2 * N),
            mul_le_mul_of_nonneg_left hSum2 hlog]
      _ ≤ 2 * N * S + 4 * ((4 + 2 / ε) * U) := by
          have hlb := log_bound (x := (N : ℝ)) (U := U) hε (by linarith)
            (by exact_mod_cast hN1) hNU
          linarith
  have hmain := integral_D_sq_le N σ hU0
  have hS0 : 0 ≤ S := by positivity
  calc ∫ t in U..2 * U, ‖D N σ t‖ ^ 2
      ≤ U * ∑ m ∈ range N, a σ m ^ 2 + (2 * N * S + 4 * ((4 + 2 / ε) * U)) := by linarith
    _ ≤ U * S + (2 * U * S + 4 * ((4 + 2 / ε) * U)) := by
        gcongr
    _ = (3 * S + 4 * (4 + 2 / ε)) * U := by ring

end ATK.BLDirichlet

#print axioms ATK.BLDirichlet.normSq_D
#print axioms ATK.BLDirichlet.integral_D_sq_le
#print axioms ATK.BLDirichlet.inv_abs_L_le
#print axioms ATK.BLDirichlet.sum_h_le
#print axioms ATK.BLDirichlet.sum_rpow_le
#print axioms ATK.BLDirichlet.media_D
#print axioms ATK.BLDirichlet.a_nonneg
#print axioms ATK.BLDirichlet.term_eq
#print axioms ATK.BLDirichlet.integral_cos_bound
#print axioms ATK.BLDirichlet.L_injective
#print axioms ATK.BLDirichlet.continuous_term
#print axioms ATK.BLDirichlet.k_symm
#print axioms ATK.BLDirichlet.k_nonneg
#print axioms ATK.BLDirichlet.offdiag_le
#print axioms ATK.BLDirichlet.sum_sym
#print axioms ATK.BLDirichlet.k_le
#print axioms ATK.BLDirichlet.harm_le
#print axioms ATK.BLDirichlet.sum_k_le
#print axioms ATK.BLDirichlet.a_sq
#print axioms ATK.BLDirichlet.log_bound
