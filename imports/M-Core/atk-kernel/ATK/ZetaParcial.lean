import ATK.ZetaRegiao
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# ATK — ζ por somas parciais: `ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − s ∫_N^∞ {u} u^{−s−1} du`

Para `Re s > 0`, `s ≠ 1` e todo `N ≥ 1`, provado por indução em `N` a partir do caso `N = 1`
(`ATK.ZetaStrip`, `ATK.ZetaRegiao.zeta_eq`). É a ferramenta que dá cotas logarítmicas de ζ perto de
`Re s = 1` (próximo módulo).
-/

open Complex Set MeasureTheory Filter Topology

namespace ATK.ZetaParcial

open ATK.ZetaStrip ATK.ZetaRetangulo ATK.ZetaRegiao

/-- A cauda a partir de `N`: `∫_N^∞ {u} u^{−s−1} du`. -/
noncomputable def HN (N : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (N : ℝ), (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ)

theorem HN_one (s : ℂ) : HN 1 s = H s := by
  rw [HN, H_eq_integral]; norm_num

theorem integrableOn_tail {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ)) (Ioi a) :=
  (integrableOn_cpow_mul_fract hs).mono_set (Ioi_subset_Ioi ha)

theorem cpow_mul_self {u : ℝ} (hu : 0 < u) (s : ℂ) :
    (u : ℂ) ^ (-s - 1) * (u : ℂ) = (u : ℂ) ^ (-s) := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  conv_rhs => rw [show -s = (-s - 1) + 1 by ring]
  rw [Complex.cpow_add _ _ hu', Complex.cpow_one]

theorem cpow_one_sub {x : ℂ} (hx : x ≠ 0) (s : ℂ) : x ^ (1 - s) = x * x ^ (-s) := by
  rw [show 1 - s = 1 + -s by ring, Complex.cpow_add _ _ hx, Complex.cpow_one]

/-- `HN N − HN (N+1) = ∫_N^{N+1} (u^{−s} − N u^{−s−1}) du`. -/
theorem HN_sub {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    HN N s - HN (N + 1) s =
      ∫ u in (N : ℝ)..((N : ℝ) + 1), ((u : ℂ) ^ (-s) - (N : ℂ) * (u : ℂ) ^ (-s - 1)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hunion : Ioc (N : ℝ) ((N : ℝ) + 1) ∪ Ioi ((N : ℝ) + 1) = Ioi (N : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by linarith)
  have hi1 := (integrableOn_tail hs hN1).mono_set
    (Ioc_subset_Ioi_self : Ioc (N : ℝ) ((N : ℝ) + 1) ⊆ Ioi (N : ℝ))
  have hi2 := integrableOn_tail hs (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith)
  unfold HN
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hunion, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi1 hi2,
    add_sub_cancel_right, intervalIntegral.integral_of_le (by linarith),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hu0 : 0 < u := by linarith [hu.1]
  rw [fract_on hu.1.le hu.2]
  push_cast
  rw [mul_sub, cpow_mul_self hu0]
  ring

theorem nao_zero_uIcc {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) ∉ uIcc (N : ℝ) ((N : ℝ) + 1) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [uIcc_of_le (by linarith)]
  intro h
  linarith [h.1]

/-- Valor da integral de um intervalo. -/
theorem integral_peca {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (N : ℝ)..((N : ℝ) + 1), ((u : ℂ) ^ (-s) - (N : ℂ) * (u : ℂ) ^ (-s - 1)) =
      (((N : ℂ) + 1) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) -
        (N : ℂ) * ((((N : ℂ) + 1) ^ (-s) - (N : ℂ) ^ (-s)) / (-s)) := by
  have h0 := nao_zero_uIcc hN
  have hr1 : -s ≠ -1 := by intro h; apply hs1; linear_combination -h
  have hr2 : -s - 1 ≠ -1 := by intro h; apply hs0; linear_combination -h
  rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_cpow (Or.inr h0))
      ((intervalIntegral.intervalIntegrable_cpow (Or.inr h0)).const_mul _),
    intervalIntegral.integral_const_mul, integral_cpow (Or.inr ⟨hr1, h0⟩),
    integral_cpow (Or.inr ⟨hr2, h0⟩)]
  rw [show -s + 1 = 1 - s by ring, show -s - 1 + 1 = -s by ring]
  push_cast
  ring

/-- **Fórmula de somas parciais.** -/
theorem zeta_parcial {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1) - s * HN N s := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, Complex.one_cpow, HN_one]
    rw [zeta_eq hs hs1]
    field_simp
    ring
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hsub := HN_sub hs N hN
    rw [integral_peca hs0 hs1 N hN] at hsub
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hN10 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (show N + 1 ≠ 0 by omega)
    push_cast
    rw [cpow_one_sub hN0, cpow_one_sub hN10] at hsub ⊢
    have hH : HN (N + 1) s = HN N s -
        (((N : ℂ) + 1) * ((N : ℂ) + 1) ^ (-s) - (N : ℂ) * (N : ℂ) ^ (-s)) / (1 - s) +
          (N : ℂ) * ((((N : ℂ) + 1) ^ (-s) - (N : ℂ) ^ (-s)) / (-s)) := by
      linear_combination -hsub
    rw [hH]
    field_simp
    ring

end ATK.ZetaParcial

#print axioms ATK.ZetaParcial.HN_one
#print axioms ATK.ZetaParcial.integrableOn_tail
#print axioms ATK.ZetaParcial.cpow_mul_self
#print axioms ATK.ZetaParcial.cpow_one_sub
#print axioms ATK.ZetaParcial.HN_sub
#print axioms ATK.ZetaParcial.nao_zero_uIcc
#print axioms ATK.ZetaParcial.integral_peca
#print axioms ATK.ZetaParcial.zeta_parcial
