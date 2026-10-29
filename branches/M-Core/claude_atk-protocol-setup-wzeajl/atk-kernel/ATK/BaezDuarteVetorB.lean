/-
ATK-RH — O vetor b da fórmula de Gram em forma fechada: b_k = (log k + 1 − γ)/k.

`ATK.GramBaezDuarte` provou `D_N = 1 − b ⬝ G⁻¹ b` com `b_k = ∫_0^1 ρ_{k+1}`.  O script
`numerics/nb_gram.py` usa `b_k = (log k + 1 − γ)/k`.  Aqui essa fórmula é certificada:

* `integral_fract_inv` : **∫_0^1 {1/x} dx = 1 − γ**  (γ = constante de Euler–Mascheroni da Mathlib);
* `integral_rho_Ioc`    : para k ≥ 1, **∫_0^1 {1/(kt)} dt = (log k + 1 − γ)/k**;
* `b_formula`           : `b N j = (log (j+1) + 1 − γ)/(j+1)`;
* `b_pos`               : todos os `b_k` são estritamente positivos.

Prova de `integral_fract_inv`: em cada degrau `(1/(n+2), 1/(n+1)]` vale `{1/x} = 1/x − (n+1)`,
logo `∫_{1/(M+1)}^1 {1/x} = log(M+1) + 1 − H_{M+1}` (indução); `H_n − log n → γ` (Mathlib)
e convergência monótona das integrais em `(1/(M+1), 1] ↑ (0,1]`.

`integral_rho_Ioc`: em `(1/k, 1]`, `{1/(kt)} = 1/(kt)` (dá `log k / k`); em `(0, 1/k]`, a troca
`t = s/k` dá `(1/k)∫_0^1 {1/s} = (1 − γ)/k`.

Nada aqui decide se `D_N → 0` (obrigação O1).  OPEN_MATH continua true.
-/
import ATK.GramBaezDuarte
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ATK.BaezDuarteVetorB

open MeasureTheory Set Filter Topology Real intervalIntegral
open ATK.Conditional.Riemann (rho)

/-- `fr(x) = {1/x}`. -/
noncomputable def fr (x : ℝ) : ℝ := Int.fract (1 / x)

theorem measurable_fr : Measurable fr := by
  unfold fr
  exact measurable_fract.comp (by fun_prop)

theorem fr_nonneg (x : ℝ) : 0 ≤ fr x := Int.fract_nonneg _

theorem fr_le_one (x : ℝ) : fr x ≤ 1 := (Int.fract_lt_one _).le

theorem integrableOn_fr (a b : ℝ) : IntegrableOn fr (Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := 1) ?_ measurable_fr.aestronglyMeasurable ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (fr_nonneg x)]
    exact fr_le_one x

theorem intervalIntegrable_fr {a b : ℝ} (hab : a ≤ b) : IntervalIntegrable fr volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (integrableOn_fr a b)

/-! ### Um degrau -/

/-- Em `(1/(n+2), 1/(n+1)]`, `{1/x} = 1/x − (n+1)`. -/
theorem fr_on_step (n : ℕ) {x : ℝ} (hx : x ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    fr x = x⁻¹ - ((n : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := hx
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hx0 : 0 < x := lt_trans (by positivity) h1
  have h2' : x * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ hn1).mp h2
  have h1' : 1 < x * ((n : ℝ) + 2) := (div_lt_iff₀ hn2).mp h1
  have hfl : ⌊1 / x⌋ = (n : ℤ) + 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · rw [le_div_iff₀ hx0]; linarith [mul_comm x ((n : ℝ) + 1)]
    · rw [div_lt_iff₀ hx0]; nlinarith [mul_comm x ((n : ℝ) + 2)]
  unfold fr Int.fract
  rw [hfl]
  push_cast
  rw [one_div]
  try ring

/-- `∫_{1/(n+2)}^{1/(n+1)} {1/x} dx = log(n+2) − log(n+1) − 1/(n+2)`. -/
theorem integral_step (n : ℕ) :
    ∫ x in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), fr x
      = Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hab : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le hn1 (by linarith)
  have ha : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have hb : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hpt : ∀ x ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)), fr x = x⁻¹ - ((n : ℝ) + 1) :=
    fun x hx => fr_on_step n hx
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) :=
    intervalIntegrable_inv (f := fun x => x)
      (fun x hx => by
        rw [Set.uIcc_of_le hab] at hx
        exact (lt_of_lt_of_le ha hx.1).ne')
      continuousOn_id
  rw [intervalIntegral.integral_of_le hab, setIntegral_congr_fun measurableSet_Ioc hpt,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_sub hinv intervalIntegrable_const,
    integral_inv_of_pos ha hb, intervalIntegral.integral_const, smul_eq_mul]
  have e : (1 / ((n : ℝ) + 1)) / (1 / ((n : ℝ) + 2)) = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
    field_simp
  rw [e, Real.log_div hn2.ne' hn1.ne']
  field_simp
  ring

/-! ### Somas parciais e o limite -/

/-- `∫_{1/(M+1)}^1 {1/x} dx = log(M+1) + 1 − H_{M+1}`. -/
theorem integral_partial (M : ℕ) :
    ∫ x in (1 / ((M : ℝ) + 1))..1, fr x = Real.log ((M : ℝ) + 1) + 1 - (harmonic (M + 1) : ℝ) := by
  induction M with
  | zero =>
    simp [harmonic]
  | succ M ih =>
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have e1 : (1 : ℝ) / (((M + 1 : ℕ) : ℝ) + 1) = 1 / ((M : ℝ) + 2) := by push_cast; ring
    have e2 : Real.log (((M + 1 : ℕ) : ℝ) + 1) = Real.log ((M : ℝ) + 2) := by
      congr 1; push_cast; ring
    have hab : 1 / ((M : ℝ) + 2) ≤ 1 / ((M : ℝ) + 1) :=
      one_div_le_one_div_of_le hM1 (by linarith)
    have hb1 : 1 / ((M : ℝ) + 1) ≤ 1 := by rw [div_le_one hM1]; linarith [M.cast_nonneg (α := ℝ)]
    rw [e1, e2, ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_fr hab)
      (intervalIntegrable_fr hb1), ih, integral_step M, harmonic_succ (M + 1)]
    push_cast
    have e3 : ((M : ℝ) + 1 + 1) = (M : ℝ) + 2 := by ring
    rw [e3]
    ring

theorem tendsto_partial :
    Tendsto (fun M : ℕ => ∫ x in (1 / ((M : ℝ) + 1))..1, fr x) atTop
      (𝓝 (1 - eulerMascheroniConstant)) := by
  have h := tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine h2.congr fun M => ?_
  rw [integral_partial]
  simp only [Function.comp_apply]
  push_cast
  ring

/-- **`∫_0^1 {1/x} dx = 1 − γ`.** -/
theorem integral_fract_inv : ∫ x in Ioc (0 : ℝ) 1, fr x = 1 - eulerMascheroniConstant := by
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
  have hlim := tendsto_setIntegral_of_monotone (μ := volume) (f := fr)
    (fun M => measurableSet_Ioc) hmono (by rw [hU]; exact integrableOn_fr 0 1)
  rw [hU] at hlim
  have hlim2 : Tendsto (fun M : ℕ => ∫ x in s M, fr x) atTop (𝓝 (1 - eulerMascheroniConstant)) := by
    refine tendsto_partial.congr fun M => ?_
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hb1 : 1 / ((M : ℝ) + 1) ≤ 1 := by rw [div_le_one hM1]; linarith [M.cast_nonneg (α := ℝ)]
    exact intervalIntegral.integral_of_le hb1
  exact tendsto_nhds_unique hlim hlim2

theorem one_sub_gamma_pos : 0 < 1 - eulerMascheroniConstant := by
  have := eulerMascheroniConstant_lt_two_thirds
  linarith

/-! ### ∫_0^1 ρ_k = (log k + 1 − γ)/k -/

theorem intervalIntegrable_rho (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (rho k) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr ?_
  refine Measure.integrableOn_of_bounded (M := 1) ?_
    (ATK.RiemannFaithful.measurable_rho k).aestronglyMeasurable ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (ATK.RiemannFaithful.rho_nonneg k x)]
    exact ATK.RiemannFaithful.rho_le_one k x

/-- **`∫_0^1 {1/(kt)} dt = (log k + 1 − γ)/k`** para `k ≥ 1`. -/
theorem integral_rho_Ioc {k : ℕ} (hk : 1 ≤ k) :
    ∫ t in Ioc (0 : ℝ) 1, rho k t = (Real.log k + 1 - eulerMascheroniConstant) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hk0]; exact hk1
  have hb0 : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  rw [← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_rho k hb0.le)
      (intervalIntegrable_rho k hb)]
  -- (0, 1/k]: troca t = s/k
  have p1 : ∫ t in (0 : ℝ)..(1 / (k : ℝ)), rho k t = (k : ℝ)⁻¹ * (1 - eulerMascheroniConstant) := by
    have h := intervalIntegral.integral_comp_mul_left (f := fr) (a := 0) (b := 1 / (k : ℝ))
      (c := (k : ℝ)) hk0.ne'
    have e : (fun t => rho k t) = fun x => fr ((k : ℝ) * x) := by
      funext t; rfl
    rw [e, h, mul_zero, mul_one_div_cancel hk0.ne', smul_eq_mul,
      intervalIntegral.integral_of_le zero_le_one, integral_fract_inv]
  -- (1/k, 1]: {1/(kt)} = 1/(kt)
  have p2 : ∫ t in (1 / (k : ℝ))..1, rho k t = (k : ℝ)⁻¹ * Real.log k := by
    have hpt : ∀ t ∈ Ioc (1 / (k : ℝ)) 1, rho k t = (k : ℝ)⁻¹ * t⁻¹ := by
      intro t ht
      have ht0 : 0 < t := lt_trans hb0 ht.1
      have hkt : 1 < (k : ℝ) * t := by
        have := (div_lt_iff₀ hk0).mp ht.1
        linarith [mul_comm t (k : ℝ)]
      have hpos : 0 < (k : ℝ) * t := by positivity
      unfold rho
      rw [Int.fract_eq_self.mpr ⟨le_of_lt (one_div_pos.mpr hpos),
        by rw [div_lt_one hpos]; exact hkt⟩]
      rw [one_div, mul_inv]
    rw [intervalIntegral.integral_of_le hb, setIntegral_congr_fun measurableSet_Ioc hpt,
      ← intervalIntegral.integral_of_le hb, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hb0 one_pos, one_div_one_div]
  rw [p1, p2]
  field_simp
  ring

/-- **Fórmula fechada do vetor b**: `b_j = (log(j+1) + 1 − γ)/(j+1)`. -/
theorem b_formula (N : ℕ) (j : Fin N) :
    ATK.GramBaezDuarte.b N j
      = (Real.log ((j.val : ℝ) + 1) + 1 - eulerMascheroniConstant) / ((j.val : ℝ) + 1) := by
  rw [ATK.GramBaezDuarte.b_eq_integral_Ioc, integral_rho_Ioc (Nat.succ_pos _)]
  push_cast
  ring

/-- Todos os `b_j` são estritamente positivos. -/
theorem b_pos (N : ℕ) (j : Fin N) : 0 < ATK.GramBaezDuarte.b N j := by
  rw [b_formula]
  have h1 : (0 : ℝ) ≤ Real.log ((j.val : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(j.val).cast_nonneg (α := ℝ)])
  have h2 := one_sub_gamma_pos
  have h3 : (0 : ℝ) < (j.val : ℝ) + 1 := by positivity
  exact div_pos (by linarith) h3

/-- Caso `k = 1`: `b_0 = ∫_0^1 {1/t} dt = 1 − γ`. -/
theorem b_zero (N : ℕ) (hN : 0 < N) : ATK.GramBaezDuarte.b N ⟨0, hN⟩ = 1 - eulerMascheroniConstant := by
  rw [b_formula]
  simp

end ATK.BaezDuarteVetorB

#print axioms ATK.BaezDuarteVetorB.measurable_fr
#print axioms ATK.BaezDuarteVetorB.fr_nonneg
#print axioms ATK.BaezDuarteVetorB.fr_le_one
#print axioms ATK.BaezDuarteVetorB.integrableOn_fr
#print axioms ATK.BaezDuarteVetorB.intervalIntegrable_fr
#print axioms ATK.BaezDuarteVetorB.fr_on_step
#print axioms ATK.BaezDuarteVetorB.integral_step
#print axioms ATK.BaezDuarteVetorB.integral_partial
#print axioms ATK.BaezDuarteVetorB.tendsto_partial
#print axioms ATK.BaezDuarteVetorB.integral_fract_inv
#print axioms ATK.BaezDuarteVetorB.one_sub_gamma_pos
#print axioms ATK.BaezDuarteVetorB.intervalIntegrable_rho
#print axioms ATK.BaezDuarteVetorB.integral_rho_Ioc
#print axioms ATK.BaezDuarteVetorB.b_formula
#print axioms ATK.BaezDuarteVetorB.b_pos
#print axioms ATK.BaezDuarteVetorB.b_zero
