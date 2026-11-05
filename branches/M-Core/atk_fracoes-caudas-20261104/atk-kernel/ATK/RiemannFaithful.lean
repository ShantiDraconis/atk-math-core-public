import ATK.RiemannConcrete
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# ATK — Fidelidade da família de Báez-Duarte e primeiro passo de dissipação estrito

Dois fatos **incondicionais**, verificados pelo kernel, sobre o objeto concreto de O1
(`D_N = inf_c ∫_{(0,∞)} (χ − Σ_{k≤N} c_k ρ_k)²`, `ρ_k(t) = {1/(k t)}`):

1. **Fidelidade** (`integrable_residual`): para todo `N` e todo `c`, o integrando é integrável em
   `(0, ∞)`. Logo `residualSq N c` é a integral genuína (de Lebesgue) do quadrado da distância —
   o valor-lixo `0` que a integral de Bochner atribui a funções não integráveis **nunca** ocorre.
   Isso fecha a rota espúria "provar `D_N → 0` usando valores-lixo": O1 formal é o critério real.

2. **Dissipação não trivial** (`DN_one_lt_one`): `D_1 < D_0 = 1`. A primeira etapa de dissipação
   `δ_0 = D_0 − D_1` é estritamente positiva — a lei `D_{n+1} ≤ D_n − δ_n` da teoria de estados é
   realizada pela família concreta com `δ_0 > 0`.

Ingredientes: `0 ≤ ρ_k ≤ 1`, `ρ_k(t) ≤ 1/t` para `t > 0`, `∫_1^∞ t⁻² < ∞`, e
`∫_0^1 {1/t} dt > 0` (pois `{1/t} = 1/t − 1 > 0` em `(1/2, 1)`).

O que continua aberto em O1 é exatamente `inf_N D_N = 0` (⟺ RH, Báez-Duarte).
-/

open MeasureTheory Set Filter Topology

namespace ATK.RiemannFaithful

open ATK.Conditional.Riemann ATK.RiemannConcrete

/-! ## Cotas pontuais -/

theorem rho_nonneg (k : ℕ) (t : ℝ) : 0 ≤ rho k t := Int.fract_nonneg _

theorem rho_le_one (k : ℕ) (t : ℝ) : rho k t ≤ 1 := (Int.fract_lt_one _).le

/-- `ρ_k(t) ≤ 1/t` para `k ≥ 1`, `t > 0`. -/
theorem rho_le_inv {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) : rho k t ≤ 1 / t := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 ≤ 1 / ((k : ℝ) * t) := by positivity
  have h1 : rho k t ≤ 1 / ((k : ℝ) * t) := by
    unfold rho Int.fract
    have h0 : (0 : ℝ) ≤ (⌊1 / ((k : ℝ) * t)⌋ : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr hpos
    linarith
  refine h1.trans (one_div_le_one_div_of_le ht ?_)
  nlinarith

theorem chi_of_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : chi t = 1 := by
  unfold chi; simp [ht]

theorem chi_of_gt_one {t : ℝ} (ht : 1 < t) : chi t = 0 := by
  have hn : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
  unfold chi; simp [hn]

theorem chi_nonneg (t : ℝ) : 0 ≤ chi t := by
  unfold chi; by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]

theorem chi_le_one (t : ℝ) : chi t ≤ 1 := by
  unfold chi; by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]

theorem chi_sq (t : ℝ) : chi t ^ 2 = chi t := by
  unfold chi; by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]

/-! ## Mensurabilidade -/

theorem measurable_rho (k : ℕ) : Measurable (rho k) := by
  unfold rho
  exact measurable_fract.comp (by fun_prop)

theorem measurable_chi : Measurable chi := by
  unfold chi
  exact measurable_const.indicator measurableSet_Ioc

/-! ## Integrabilidade (fidelidade) -/

/-- Critério: `|f| ≤ B` em `(0,1]` e `|f| ≤ B/t` em `(1,∞)` ⇒ `f²` integrável em `(0,∞)`. -/
theorem integrableOn_sq_of_bounds {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (h1 : ∀ t ∈ Ioc (0 : ℝ) 1, |f t| ≤ B) (h2 : ∀ t ∈ Ioi (1 : ℝ), |f t| ≤ B * (1 / t)) :
    IntegrableOn (fun t => f t ^ 2) (Ioi 0) := by
  have hm : Measurable (fun t => f t ^ 2) := hf.pow_const 2
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable (B ^ 2) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1 t ht) 2
  · have hg : IntegrableOn (fun t : ℝ => B ^ 2 * t ^ (-2 : ℝ)) (Ioi 1) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one) _
    refine Integrable.mono' hg hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |f t| ^ 2 ≤ (B * (1 / t)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h2 t ht) 2
      _ = B ^ 2 * t ^ (-2 : ℝ) := by rw [Real.rpow_neg ht0.le, Real.rpow_two]; ring

theorem abs_sum_le {N : ℕ} (c : Fin N → ℝ) (t B : ℝ)
    (hB : ∀ k : Fin N, |rho (k.val + 1) t| ≤ B) :
    |∑ k : Fin N, c k * rho (k.val + 1) t| ≤ (∑ k : Fin N, |c k|) * B := by
  calc |∑ k : Fin N, c k * rho (k.val + 1) t|
        ≤ ∑ k : Fin N, |c k * rho (k.val + 1) t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin N, |c k| * B := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB k) (abs_nonneg _)
    _ = (∑ k : Fin N, |c k|) * B := (Finset.sum_mul _ _ _).symm

/-- **Fidelidade**: o integrando de `residualSq N c` é integrável em `(0, ∞)`, para todo `N, c`. -/
theorem integrable_residual (N : ℕ) (c : Fin N → ℝ) :
    IntegrableOn (fun t => (chi t - ∑ k : Fin N, c k * rho (k.val + 1) t) ^ 2) (Ioi 0) := by
  have hC0 : 0 ≤ ∑ k : Fin N, |c k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hmeas : Measurable (fun t => chi t - ∑ k : Fin N, c k * rho (k.val + 1) t) :=
    measurable_chi.sub (Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_rho _))
  refine integrableOn_sq_of_bounds hmeas (B := 1 + ∑ k : Fin N, |c k|) ?_ ?_
  · intro t _
    have hS := abs_sum_le c t 1 fun k => by
      rw [abs_of_nonneg (rho_nonneg _ _)]; exact rho_le_one _ _
    obtain ⟨h3, h4⟩ := abs_le.mp hS
    have h1 := chi_nonneg t
    have h2 := chi_le_one t
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hS := abs_sum_le c t (1 / t) fun k => by
      rw [abs_of_nonneg (rho_nonneg _ _)]; exact rho_le_inv (Nat.succ_pos _) ht0
    rw [chi_of_gt_one ht, zero_sub, abs_neg]
    exact hS.trans (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (one_div_pos.mpr ht0)))

/-! ## `D_0 = 1` -/

theorem integrable_chi_sq : IntegrableOn (fun t => chi t ^ 2) (Ioi 0) :=
  integrableOn_sq_of_bounds measurable_chi (B := 1)
    (fun t _ => by rw [abs_of_nonneg (chi_nonneg t)]; exact chi_le_one t)
    (fun t ht => by
      rw [chi_of_gt_one ht, abs_zero]
      exact mul_nonneg zero_le_one (le_of_lt (one_div_pos.mpr (lt_trans zero_lt_one ht))))

theorem integral_chi_sq : ∫ t in Ioi (0 : ℝ), chi t ^ 2 = 1 := by
  have hsq : (fun t : ℝ => chi t ^ 2) = Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) := by
    funext t; unfold chi
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]
  rw [hsq, integral_indicator measurableSet_Ioc]
  simp only [integral_const, smul_eq_mul, mul_one]
  rw [Measure.restrict_restrict measurableSet_Ioc]
  have : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := by
    ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, h.1⟩
  rw [this]
  simp

theorem residualSq_zero (c : Fin 0 → ℝ) : residualSq 0 c = 1 := by
  unfold residualSq
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  exact integral_chi_sq

/-- **`D_0 = 1`** exatamente. -/
theorem DN_zero_eq_one : DN 0 = 1 :=
  le_antisymm DN_zero_le_one (le_ciInf fun c => (residualSq_zero c).ge)

/-! ## Primeiro passo de dissipação: `D_1 < 1` -/

/-- `ρ_1(t) = {1/t} > 0` em `(1/2, 1)`. -/
theorem rho_one_pos {t : ℝ} (ht : t ∈ Ioo (1 / 2 : ℝ) 1) : 0 < rho 1 t := by
  obtain ⟨h1, h2⟩ := ht
  have ht0 : 0 < t := by linarith
  have hu1 : 1 < 1 / t := one_lt_one_div ht0 h2
  have hu2 : 1 / t < 2 := (div_lt_iff₀ ht0).mpr (by linarith)
  have hfl : ⌊(1 / t : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  unfold rho
  rw [Nat.cast_one, one_mul, Int.fract, hfl]
  push_cast
  linarith

theorem integrable_chi_rho : IntegrableOn (fun t => chi t * rho 1 t) (Ioi 0) := by
  refine Integrable.mono' integrable_chi_sq
    (measurable_chi.mul (measurable_rho 1)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (chi_nonneg t) (rho_nonneg 1 t)), chi_sq]
  calc chi t * rho 1 t ≤ chi t * 1 := mul_le_mul_of_nonneg_left (rho_le_one 1 t) (chi_nonneg t)
    _ = chi t := mul_one _

theorem integrable_rho_one_sq : IntegrableOn (fun t => rho 1 t ^ 2) (Ioi 0) :=
  integrableOn_sq_of_bounds (measurable_rho 1) (B := 1)
    (fun t _ => by rw [abs_of_nonneg (rho_nonneg 1 t)]; exact rho_le_one 1 t)
    (fun t ht => by
      rw [abs_of_nonneg (rho_nonneg 1 t), one_mul]
      exact rho_le_inv le_rfl (lt_trans zero_lt_one ht))

/-- `⟨χ, ρ_1⟩ = ∫_0^1 {1/t} dt > 0`. -/
theorem integral_chi_rho_pos : 0 < ∫ t in Ioi (0 : ℝ), chi t * rho 1 t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ integrable_chi_rho]
  · have hsub : Ioo (1 / 2 : ℝ) 1 ⊆ Function.support (fun t => chi t * rho 1 t) ∩ Ioi 0 := by
      intro t ht
      refine ⟨?_, ?_⟩
      · have hchi : chi t = 1 := chi_of_mem ⟨by linarith [ht.1], ht.2.le⟩
        simp only [Function.mem_support, hchi, one_mul]
        exact (rho_one_pos ht).ne'
      · show (0 : ℝ) < t
        linarith [ht.1]
    calc (0 : ENNReal) < volume (Ioo (1 / 2 : ℝ) 1) := by
          rw [Real.volume_Ioo, ENNReal.ofReal_pos]; norm_num
      _ ≤ _ := measure_mono hsub
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t _ => mul_nonneg (chi_nonneg t) (rho_nonneg 1 t))

/-- Expansão exata de `‖χ − ε ρ_1‖²`. -/
theorem residualSq_one (ε : ℝ) :
    residualSq 1 (fun _ => ε) =
      1 - 2 * ε * (∫ t in Ioi (0 : ℝ), chi t * rho 1 t) +
        ε ^ 2 * ∫ t in Ioi (0 : ℝ), rho 1 t ^ 2 := by
  unfold residualSq
  simp only [Fin.sum_univ_one]
  show ∫ t in Ioi (0 : ℝ), (chi t - ε * rho 1 t) ^ 2 = _
  have hexp : (fun t => (chi t - ε * rho 1 t) ^ 2) =
      fun t => (chi t ^ 2 - (2 * ε) * (chi t * rho 1 t)) + ε ^ 2 * rho 1 t ^ 2 := by
    funext t; ring
  have hC : IntegrableOn (fun t => 2 * ε * (chi t * rho 1 t)) (Ioi 0) :=
    Integrable.const_mul integrable_chi_rho _
  have hA : IntegrableOn (fun t => chi t ^ 2 - 2 * ε * (chi t * rho 1 t)) (Ioi 0) :=
    Integrable.sub integrable_chi_sq hC
  have hB : IntegrableOn (fun t => ε ^ 2 * rho 1 t ^ 2) (Ioi 0) :=
    Integrable.const_mul integrable_rho_one_sq _
  rw [hexp, integral_add hA hB, integral_sub integrable_chi_sq hC, integral_const_mul,
    integral_const_mul, integral_chi_sq]

/-- **`D_1 < 1 = D_0`**: o primeiro passo de dissipação da família concreta é estrito. -/
theorem DN_one_lt_one : DN 1 < 1 := by
  set I := ∫ t in Ioi (0 : ℝ), chi t * rho 1 t with hI
  set J := ∫ t in Ioi (0 : ℝ), rho 1 t ^ 2 with hJ
  have hI0 : 0 < I := integral_chi_rho_pos
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  set ε := I / (J + 1) with hε
  have hε0 : 0 < ε := div_pos hI0 (by linarith)
  have hεJ : ε * J < I := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hres : residualSq 1 (fun _ => ε) < 1 := by
    rw [residualSq_one, ← hI, ← hJ]
    nlinarith [mul_lt_mul_of_pos_left hεJ hε0, mul_pos hε0 hI0]
  exact lt_of_le_of_lt (DN_le_residualSq 1 _) hres

/-- `δ_0 = D_0 − D_1 > 0`. -/
theorem primeiro_delta_pos : 0 < DN 0 - DN 1 := by
  rw [DN_zero_eq_one]; linarith [DN_one_lt_one]

/-- Para todo `N ≥ 1`, `D_N < 1`. -/
theorem DN_lt_one {N : ℕ} (hN : 1 ≤ N) : DN N < 1 :=
  lt_of_le_of_lt (DN_antitone hN) DN_one_lt_one

end ATK.RiemannFaithful

#print axioms ATK.RiemannFaithful.rho_nonneg
#print axioms ATK.RiemannFaithful.rho_le_one
#print axioms ATK.RiemannFaithful.rho_le_inv
#print axioms ATK.RiemannFaithful.chi_of_mem
#print axioms ATK.RiemannFaithful.chi_of_gt_one
#print axioms ATK.RiemannFaithful.chi_nonneg
#print axioms ATK.RiemannFaithful.chi_le_one
#print axioms ATK.RiemannFaithful.chi_sq
#print axioms ATK.RiemannFaithful.measurable_rho
#print axioms ATK.RiemannFaithful.measurable_chi
#print axioms ATK.RiemannFaithful.integrableOn_sq_of_bounds
#print axioms ATK.RiemannFaithful.abs_sum_le
#print axioms ATK.RiemannFaithful.integrable_residual
#print axioms ATK.RiemannFaithful.integrable_chi_sq
#print axioms ATK.RiemannFaithful.integral_chi_sq
#print axioms ATK.RiemannFaithful.residualSq_zero
#print axioms ATK.RiemannFaithful.DN_zero_eq_one
#print axioms ATK.RiemannFaithful.rho_one_pos
#print axioms ATK.RiemannFaithful.integrable_chi_rho
#print axioms ATK.RiemannFaithful.integrable_rho_one_sq
#print axioms ATK.RiemannFaithful.integral_chi_rho_pos
#print axioms ATK.RiemannFaithful.residualSq_one
#print axioms ATK.RiemannFaithful.DN_one_lt_one
#print axioms ATK.RiemannFaithful.primeiro_delta_pos
#print axioms ATK.RiemannFaithful.DN_lt_one
