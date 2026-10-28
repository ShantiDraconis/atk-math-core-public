import ATK.Cert.Transc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# ATK — Cotas certificadas para `γ`, `log π`, `log 2π` e `C₀ = 2 + γ − log 4π`

* `atanh_cota`: para `0 < x < 1`, `2x + 2x³/3 ≤ log(1+x) − log(1−x) ≤ 2x + 2x³/3 + 2x⁵/(5(1−x²))`.
* Duas sequências que cercam `γ`:
  `u_n = H_n − log(n + ½) − 1/(24(n+1)²)` é **decrescente** e `l_n = H_{n+1} − log(n + 3/2) − 1/(24(n+1)(n+2))`
  é **crescente**, ambas `→ γ` (`u_anti`, `l_mono`, `tendsto_u`, `tendsto_l`); logo `l_m ≤ γ ≤ u_n`.
* Em `n = 40` (`n + ½ = 81/2`, `log(81/2) = 4 log 3 − log 2`): **`0,5772156 < γ < 0,5772163`**
  (`gama_cotas`; a Mathlib só tem `½ < γ < ⅔`).
* `1,1447295 < log π < 1,1447300` (`log_pi_cotas`) e **`0,04619 < 2 + γ − log 4π < 0,04620`** (`C0_cotas`).
-/

open Real Filter Topology

namespace ATK.GamaCotas

/-! ## 1. A série de `atanh` com resto -/

theorem atanh_cota {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    2 * x + 2 * x ^ 3 / 3 ≤ Real.log (1 + x) - Real.log (1 - x) ∧
      Real.log (1 + x) - Real.log (1 - x) ≤ 2 * x + 2 * x ^ 3 / 3 + 2 * x ^ 5 / (5 * (1 - x ^ 2)) := by
  have habs : |x| < 1 := by rw [abs_of_pos h0]; exact h1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  have hpart : ∑ k ∈ Finset.range 2, f k = 2 * x + 2 * x ^ 3 / 3 := by
    simp only [hf, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  have hx2 : x ^ 2 < 1 := by nlinarith
  have htail : ∑' k, f (k + 2) ≤ 2 * x ^ 5 / (5 * (1 - x ^ 2)) := by
    have hgeo : HasSum (fun k : ℕ => 2 * x ^ 5 / 5 * (x ^ 2) ^ k) (2 * x ^ 5 / 5 * (1 - x ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hx2).mul_left _
    have hle : ∀ k, f (k + 2) ≤ 2 * x ^ 5 / 5 * (x ^ 2) ^ k := by
      intro k
      simp only [hf]
      have hp : x ^ (2 * (k + 2) + 1) = x ^ 5 * (x ^ 2) ^ k := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      push_cast
      rw [hp]
      have hden : (5 : ℝ) ≤ 2 * ((k : ℝ) + 2) + 1 := by
        have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
      have hpos : 0 ≤ x ^ 5 * (x ^ 2) ^ k := by positivity
      rw [show 2 * x ^ 5 / 5 * (x ^ 2) ^ k = 2 * (1 / 5) * (x ^ 5 * (x ^ 2) ^ k) by ring]
      gcongr
    have := (hS.summable.comp_injective (add_left_injective 2)).tsum_le_tsum hle hgeo.summable
    rw [hgeo.tsum_eq] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  constructor
  · rw [← hpart]; exact sum_le_hasSum (Finset.range 2) (fun k _ => hf0 k) hS
  · have hsplit := hS.summable.sum_add_tsum_nat_add 2
    rw [hS.tsum_eq] at hsplit
    rw [← hsplit, hpart]
    linarith

/-- `log(m + ½) − log(m − ½) = log(1 + x) − log(1 − x)` com `x = 1/(2m)`, `m ≥ 1`. -/
theorem log_passo {m : ℝ} (hm : 1 ≤ m) :
    Real.log (m + 1 / 2) - Real.log (m - 1 / 2) =
      Real.log (1 + 1 / (2 * m)) - Real.log (1 - 1 / (2 * m)) := by
  have hm0 : 0 < m := by linarith
  have e1 : m + 1 / 2 = (1 + 1 / (2 * m)) * m := by field_simp
  have e2 : m - 1 / 2 = (1 - 1 / (2 * m)) * m := by field_simp
  have h1 : 0 < 1 + 1 / (2 * m) := by positivity
  have h2 : 0 < 1 - 1 / (2 * m) := by
    rw [sub_pos, div_lt_one (by positivity)]; linarith
  rw [e1, e2, Real.log_mul h1.ne' hm0.ne', Real.log_mul h2.ne' hm0.ne']
  ring

theorem passo_cota {m : ℝ} (hm : 1 ≤ m) :
    1 / m + 1 / (12 * m ^ 3) ≤ Real.log (m + 1 / 2) - Real.log (m - 1 / 2) ∧
      Real.log (m + 1 / 2) - Real.log (m - 1 / 2) ≤
        1 / m + 1 / (12 * m ^ 3) + 1 / (20 * m ^ 3 * (4 * m ^ 2 - 1)) := by
  have hm0 : 0 < m := by linarith
  have hx0 : 0 < 1 / (2 * m) := by positivity
  have hx1 : 1 / (2 * m) < 1 := by rw [div_lt_one (by positivity)]; linarith
  obtain ⟨hlo, hhi⟩ := atanh_cota hx0 hx1
  rw [log_passo hm]
  have hq : 0 < 4 * m ^ 2 - 1 := by nlinarith
  have e1 : 2 * (1 / (2 * m)) + 2 * (1 / (2 * m)) ^ 3 / 3 = 1 / m + 1 / (12 * m ^ 3) := by
    field_simp; ring
  have e2 : 2 * (1 / (2 * m)) ^ 5 / (5 * (1 - (1 / (2 * m)) ^ 2)) = 1 / (20 * m ^ 3 * (4 * m ^ 2 - 1)) := by
    field_simp; ring
  rw [e1] at hlo
  rw [e1, e2] at hhi
  exact ⟨hlo, hhi⟩

/-! ## 2. As sequências `u` (decrescente) e `l` (crescente) -/

/-- `u_n = H_n − log(n + ½) − 1/(24(n+1)²)`. -/
noncomputable def u (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log ((n : ℝ) + 1 / 2) - 1 / (24 * ((n : ℝ) + 1) ^ 2)

/-- `l_n = H_{n+1} − log(n + 3/2) − 1/(24(n+1)(n+2))`. -/
noncomputable def l (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 3 / 2) - 1 / (24 * ((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem u_succ_le (n : ℕ) : u (n + 1) ≤ u n := by
  unfold u
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith [n.cast_nonneg (α := ℝ)]
  have hP := (passo_cota ha1).1
  have e1 : ((n + 1 : ℕ) : ℝ) + 1 / 2 = a + 1 / 2 := by push_cast; ring
  have e2 : (n : ℝ) + 1 / 2 = a - 1 / 2 := by rw [ha]; ring
  have e3 : ((n + 1 : ℕ) : ℝ) + 1 = a + 1 := by push_cast; ring
  have hH : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / a := by
    rw [harmonic_succ]; push_cast; rw [ha]; ring
  rw [e1, e2, e3, hH]
  have ha0 : 0 < a := by linarith
  have key : 1 / (24 * a ^ 2) - 1 / (24 * (a + 1) ^ 2) - 1 / (12 * a ^ 3) =
      -(3 * a + 2) / (24 * a ^ 3 * (a + 1) ^ 2) := by
    field_simp; ring
  have hneg : -(3 * a + 2) / (24 * a ^ 3 * (a + 1) ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

theorem u_anti : Antitone u := antitone_nat_of_succ_le u_succ_le

theorem chave_l (a : ℝ) (ha : 2 ≤ a) :
    1 / (24 * (a - 1) * a) - 1 / (24 * a * (a + 1)) - 1 / (12 * a ^ 3) -
      1 / (20 * a ^ 3 * (4 * a ^ 2 - 1)) = (17 * a ^ 2 - 2) / (60 * a ^ 3 * (a ^ 2 - 1) * (4 * a ^ 2 - 1)) := by
  have h1 : a - 1 ≠ 0 := by linarith
  have h2 : a ≠ 0 := by linarith
  have h3 : a + 1 ≠ 0 := by linarith
  have h4 : 4 * a ^ 2 - 1 ≠ 0 := by nlinarith
  have h5 : a ^ 2 - 1 ≠ 0 := by nlinarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity),
    div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem l_le_succ (n : ℕ) : l n ≤ l (n + 1) := by
  unfold l
  set a : ℝ := (n : ℝ) + 2 with ha
  have ha2 : 2 ≤ a := by rw [ha]; linarith [n.cast_nonneg (α := ℝ)]
  have hP := (passo_cota (by linarith : (1 : ℝ) ≤ a)).2
  have e1 : ((n + 1 : ℕ) : ℝ) + 3 / 2 = a + 1 / 2 := by push_cast; ring
  have e2 : (n : ℝ) + 3 / 2 = a - 1 / 2 := by rw [ha]; ring
  have e3 : ((n + 1 : ℕ) : ℝ) + 1 = a := by push_cast; ring
  have e4 : ((n + 1 : ℕ) : ℝ) + 2 = a + 1 := by push_cast; ring
  have e5 : (n : ℝ) + 1 = a - 1 := by rw [ha]; ring
  have hH : (harmonic (n + 1 + 1) : ℝ) = (harmonic (n + 1) : ℝ) + 1 / a := by
    rw [harmonic_succ]; push_cast; rw [ha]; ring
  rw [e1, e2, e3, e4, e5, hH]
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hq : 0 < 4 * a ^ 2 - 1 := by nlinarith
  have hq2 : 0 < a ^ 2 - 1 := by nlinarith
  have key := chave_l a ha2
  have hpos : 0 ≤ (17 * a ^ 2 - 2) / (60 * a ^ 3 * (a ^ 2 - 1) * (4 * a ^ 2 - 1)) :=
    div_nonneg (by nlinarith) (by positivity)
  linarith

theorem l_mono : Monotone l := monotone_nat_of_le_succ l_le_succ

theorem tendsto_u : Tendsto u atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1 / 2) - Real.log n) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log (1 / 2)).comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun n : ℕ => 1 / (24 * ((n : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 24 * ((n : ℝ) + 1) ^ 2) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop (by norm_num) ?_
      exact (tendsto_pow_atTop two_ne_zero).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact this.inv_tendsto_atTop.congr fun n => by simp only [Pi.inv_apply, one_div]
  have := (h1.sub h2).sub h3
  rw [sub_zero, sub_zero] at this
  refine this.congr fun n => ?_
  unfold u; ring

theorem tendsto_l : Tendsto l atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) atTop
      (𝓝 eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => Real.log (((n + 1 : ℕ) : ℝ) + 1 / 2) - Real.log ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log (1 / 2)).comp hN
  have h3 : Tendsto (fun n : ℕ => 1 / (24 * ((n : ℝ) + 1) * ((n : ℝ) + 2))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 24 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) atTop atTop := by
      have ha : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have hb : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact ((ha.const_mul_atTop (by norm_num : (0 : ℝ) < 24))).atTop_mul_atTop₀ hb
    exact this.inv_tendsto_atTop.congr fun n => by simp only [Pi.inv_apply, one_div]
  have := (h1.sub h2).sub h3
  rw [sub_zero, sub_zero] at this
  refine this.congr fun n => ?_
  unfold l
  push_cast
  ring_nf

theorem gama_le_u (n : ℕ) : eulerMascheroniConstant ≤ u n := u_anti.le_of_tendsto tendsto_u n

theorem l_le_gama (n : ℕ) : l n ≤ eulerMascheroniConstant := l_mono.ge_of_tendsto tendsto_l n

/-! ## 3. Os números em `n = 40` -/

theorem harmonic_40 : (harmonic 40 : ℝ) = 2078178381193813 / 485721041551200 := by
  have : harmonic 40 = 2078178381193813 / 485721041551200 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [this]; push_cast; ring

theorem log3_sub_log2 :
    (4054651081081 / 10 ^ 13 : ℝ) < Real.log 3 - Real.log 2 ∧
      Real.log 3 - Real.log 2 < 4054651081082 / 10 ^ 13 := by
  have h := ATK.Cert.mem_dLog 10 (j := 2) (by norm_num)
  unfold ATK.Cert.dLog ATK.Cert.atS ATK.Cert.IR.mem at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log_81_2 : Real.log ((40 : ℕ) + 1 / 2 : ℝ) = 4 * Real.log 3 - Real.log 2 := by
  have e : ((40 : ℕ) + 1 / 2 : ℝ) = 3 ^ 4 / 2 := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

theorem log_81_2' : Real.log ((39 : ℕ) + 3 / 2 : ℝ) = 4 * Real.log 3 - Real.log 2 := by
  have e : ((39 : ℕ) + 3 / 2 : ℝ) = (40 : ℕ) + 1 / 2 := by norm_num
  rw [e, log_81_2]

/-- **`0,5772156 < γ < 0,5772163`.** -/
theorem gama_cotas :
    (5772156 / 10 ^ 7 : ℝ) < eulerMascheroniConstant ∧ eulerMascheroniConstant < 5772163 / 10 ^ 7 := by
  have hu := gama_le_u 40
  have hl := l_le_gama 39
  unfold u at hu
  unfold l at hl
  rw [log_81_2] at hu
  rw [show (39 + 1 : ℕ) = 40 from rfl, log_81_2'] at hl
  rw [harmonic_40] at hu hl
  obtain ⟨h3a, h3b⟩ := log3_sub_log2
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  push_cast at hu hl
  constructor
  · norm_num at hl; linarith
  · norm_num at hu; linarith

/-! ## 4. `log π`, `log 2π`, `C₀` -/

theorem log_div3_cotas {a : ℝ} (ha : 3 < a) :
    2 * ((a - 3) / (a + 3)) + 2 * ((a - 3) / (a + 3)) ^ 3 / 3 ≤ Real.log (a / 3) ∧
      Real.log (a / 3) ≤ 2 * ((a - 3) / (a + 3)) + 2 * ((a - 3) / (a + 3)) ^ 3 / 3 +
        2 * ((a - 3) / (a + 3)) ^ 5 / (5 * (1 - ((a - 3) / (a + 3)) ^ 2)) := by
  have hx0 : 0 < (a - 3) / (a + 3) := div_pos (by linarith) (by linarith)
  have hx1 : (a - 3) / (a + 3) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have e : Real.log (1 + (a - 3) / (a + 3)) - Real.log (1 - (a - 3) / (a + 3)) = Real.log (a / 3) := by
    have h1 : 1 + (a - 3) / (a + 3) = 2 * a / (a + 3) := by field_simp; ring
    have h2 : 1 - (a - 3) / (a + 3) = 6 / (a + 3) := by field_simp; ring
    rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [← e]
  exact atanh_cota hx0 hx1

theorem log3_cotas :
    (10986122884 / 10 ^ 10 : ℝ) < Real.log 3 ∧ Real.log 3 < 10986122890 / 10 ^ 10 := by
  obtain ⟨h3a, h3b⟩ := log3_sub_log2
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  constructor <;> norm_num at h2a h2b ⊢ <;> linarith

/-- **`1,1447295 < log π < 1,1447300`.** -/
theorem log_pi_cotas : (11447295 / 10 ^ 7 : ℝ) < Real.log π ∧ Real.log π < 11447300 / 10 ^ 7 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  obtain ⟨h3a, h3b⟩ := log3_cotas
  have hlo := (log_div3_cotas (a := 3.141592) (by norm_num)).1
  have hhi := (log_div3_cotas (a := 3.141593) (by norm_num)).2
  have e1 : Real.log (3.141592 / 3) = Real.log 3.141592 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have e2 : Real.log (3.141593 / 3) = Real.log 3.141593 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [e1] at hlo
  rw [e2] at hhi
  have m1 : Real.log 3.141592 < Real.log π := Real.log_lt_log (by norm_num) hp1
  have m2 : Real.log π < Real.log 3.141593 := Real.log_lt_log Real.pi_pos hp2
  norm_num at hlo hhi
  constructor <;> linarith

theorem log_two_pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
  Real.log_mul (by norm_num) Real.pi_pos.ne'

theorem log_four_pi : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

/-- **`0,04619 < C₀ = 2 + γ − log 4π < 0,04620`.** -/
theorem C0_cotas :
    (4619 / 10 ^ 5 : ℝ) < 2 + eulerMascheroniConstant - Real.log (4 * π) ∧
      2 + eulerMascheroniConstant - Real.log (4 * π) < 4620 / 10 ^ 5 := by
  rw [log_four_pi]
  obtain ⟨hg1, hg2⟩ := gama_cotas
  obtain ⟨hp1, hp2⟩ := log_pi_cotas
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  norm_num at h2a h2b
  constructor <;> linarith

end ATK.GamaCotas

-- Auditoria de axiomas (kernel)
#print axioms ATK.GamaCotas.atanh_cota
#print axioms ATK.GamaCotas.log_passo
#print axioms ATK.GamaCotas.passo_cota
#print axioms ATK.GamaCotas.u_succ_le
#print axioms ATK.GamaCotas.u_anti
#print axioms ATK.GamaCotas.chave_l
#print axioms ATK.GamaCotas.l_le_succ
#print axioms ATK.GamaCotas.l_mono
#print axioms ATK.GamaCotas.tendsto_u
#print axioms ATK.GamaCotas.tendsto_l
#print axioms ATK.GamaCotas.gama_le_u
#print axioms ATK.GamaCotas.l_le_gama
#print axioms ATK.GamaCotas.harmonic_40
#print axioms ATK.GamaCotas.log3_sub_log2
#print axioms ATK.GamaCotas.log_81_2
#print axioms ATK.GamaCotas.log_81_2'
#print axioms ATK.GamaCotas.gama_cotas
#print axioms ATK.GamaCotas.log_div3_cotas
#print axioms ATK.GamaCotas.log3_cotas
#print axioms ATK.GamaCotas.log_pi_cotas
#print axioms ATK.GamaCotas.log_two_pi
#print axioms ATK.GamaCotas.log_four_pi
#print axioms ATK.GamaCotas.C0_cotas
