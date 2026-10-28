/-
ATK-RH — A matriz de Gram de ρ_m em L²(0,1) é definida positiva: INCONDICIONAL.

Descarrega a hipótese `DetectsSteps` de `OmegaGramRho` no caso que importa:
o produto interno de L²(0,1).  Resultado principal:

  `integral_sq_pos`:  c ≠ 0  ⇒  0 < ∫_{(0,1]} (Σ c_i ρ_{m_i})²
  `gramL2_posDef`  :  PosDefQ (gramL2 m)

Argumento: F = Σ c_i ρ_{m_i} é constante igual a S_k em cada degrau
I_k = (1/(k+1), 1/k], que tem medida 1/(k(k+1)) > 0.  Se ∫F² = 0 então F² = 0
q.t.p., logo S_k = 0 para todo k, logo c = 0 por `coeffs_eq_zero_of_stepVal`.

Continua não decidindo se D_N → 0.
-/
import ATK.RhoIndependente
import ATK.OmegaGramRho
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor

namespace ATK.OmegaGramL2

open MeasureTheory Set Finset ATK.RhoIndependente

/-! ### Medibilidade e limitação de ρ_m -/

theorem measurable_rho (m : ℕ) : Measurable (rho (K := ℝ) m) := by
  unfold rho
  fun_prop

theorem abs_rho_le_one (m : ℕ) (hm : 1 ≤ m) (x : ℝ) : |rho (K := ℝ) m x| ≤ 1 := by
  obtain ⟨h1, h2⟩ := rho_bounds (K := ℝ) m hm x
  have hmK : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have : (1 : ℝ) / m ≤ 1 := by rw [div_le_one (by linarith)]; exact hmK
  rw [abs_le]; constructor <;> linarith

/-- O degrau de índice k. -/
noncomputable def step (k : ℕ) : Set ℝ := Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))

theorem step_subset (k : ℕ) (hk : 1 ≤ k) : step k ⊆ Ioc 0 1 := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · exact lt_trans (by positivity) h1
  · exact h2.trans (by rw [div_le_one (by linarith)]; exact hk')

theorem volume_step (k : ℕ) (hk : 1 ≤ k) : 0 < volume (step k) := by
  rw [step, Real.volume_Ioc]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : (1 : ℝ) / ((k : ℝ) + 1) < 1 / k :=
    one_div_lt_one_div_of_lt hk' (by linarith)
  rw [ENNReal.ofReal_pos]; linarith

/-- Em x ∈ I_k, ⌊1/x⌋₊ = k. -/
theorem floor_inv_of_mem_step (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ step k) :
    ⌊1 / x⌋₊ = k := by
  obtain ⟨h1, h2⟩ := hx
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx0 : 0 < x := lt_trans (by positivity) h1
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · -- k ≤ 1/x  ⇐  x ≤ 1/k
    rw [le_div_iff₀ hx0]; rwa [le_div_iff₀ hk', mul_comm] at h2
  · -- 1/x < k+1  ⇐  1/(k+1) < x
    rw [div_lt_iff₀ hx0]; rwa [div_lt_iff₀ (by positivity), mul_comm] at h1

/-- Σ c_i ρ_{m_i} é constante igual a stepVal em cada degrau. -/
theorem comb_eq_stepVal_on_step (I : Finset ℕ) (c : ℕ → ℝ) (hI : ∀ m ∈ I, 1 ≤ m)
    (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ step k) :
    ∑ m ∈ I, c m * rho m x = stepVal I c k := by
  have hx0 : 0 < x := lt_trans (by positivity) hx.1
  rw [sum_rho_eq_stepVal I c hI hx0, floor_inv_of_mem_step k hk hx]

/-! ### Integrabilidade -/

theorem integrableOn_rho_mul (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IntegrableOn (fun x => rho (K := ℝ) m x * rho n x) (Ioc 0 1) := by
  apply Measure.integrableOn_of_bounded (M := 1)
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  · exact ((measurable_rho m).mul (measurable_rho n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |rho m x| * |rho n x| ≤ 1 * 1 :=
          mul_le_mul (abs_rho_le_one m hm x) (abs_rho_le_one n hn x) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul _

theorem integrableOn_comb_sq (I : Finset ℕ) (c : ℕ → ℝ) (hI : ∀ m ∈ I, 1 ≤ m) :
    IntegrableOn (fun x => (∑ m ∈ I, c m * rho (K := ℝ) m x) ^ 2) (Ioc 0 1) := by
  have h1 : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hmeas : Measurable (fun x : ℝ => ∑ m ∈ I, c m * rho (K := ℝ) m x) :=
    Finset.measurable_sum I (fun m _ => (measurable_rho m).const_mul (c m))
  have h2 : AEStronglyMeasurable (fun x : ℝ => (∑ m ∈ I, c m * rho (K := ℝ) m x) ^ 2) volume :=
    (hmeas.pow_const 2).aestronglyMeasurable
  have h3 : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖(∑ m ∈ I, c m * rho (K := ℝ) m x) ^ 2‖ ≤ (∑ m ∈ I, |c m|) ^ 2 := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc |∑ m ∈ I, c m * rho m x| ≤ ∑ m ∈ I, |c m * rho m x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ I, |c m| := by
          apply sum_le_sum; intro m hm
          rw [abs_mul]
          calc |c m| * |rho m x| ≤ |c m| * 1 :=
                mul_le_mul_of_nonneg_left (abs_rho_le_one m (hI m hm) x) (abs_nonneg _)
            _ = |c m| := mul_one _
  exact Measure.integrableOn_of_bounded h1 h2 h3

/-! ### Positividade -/

/-- Se c não é identicamente nula em I (índices ≥ 2), a integral de (Σ c ρ)² em (0,1]
é estritamente positiva. -/
theorem integral_sq_pos (I : Finset ℕ) (c : ℕ → ℝ) (hI : ∀ m ∈ I, 2 ≤ m)
    (hc : ∃ m ∈ I, c m ≠ 0) :
    0 < ∫ x in Ioc (0 : ℝ) 1, (∑ m ∈ I, c m * rho m x) ^ 2 := by
  have hI1 : ∀ m ∈ I, 1 ≤ m := fun m hm => by have := hI m hm; omega
  -- existe um degrau k com stepVal ≠ 0
  have hk : ∃ k : ℕ, 1 ≤ k ∧ stepVal I c k ≠ 0 := by
    by_contra hcon
    have hall : ∀ k : ℕ, stepVal I c k = 0 := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · unfold stepVal; simp
      · by_contra h; exact hcon ⟨k, hk, h⟩
    obtain ⟨m, hm, hne⟩ := hc
    exact hne (coeffs_eq_zero_of_stepVal I c hI hall m hm)
  obtain ⟨k, hk1, hSk⟩ := hk
  rw [setIntegral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall fun x => sq_nonneg _) (integrableOn_comb_sq I c hI1)]
  -- o degrau está no suporte
  have hsub : step k ⊆ Function.support (fun x => (∑ m ∈ I, c m * rho m x) ^ 2) ∩ Ioc 0 1 := by
    intro x hx
    refine ⟨?_, step_subset k hk1 hx⟩
    rw [Function.mem_support, comb_eq_stepVal_on_step I c hI1 k hk1 hx]
    exact pow_ne_zero 2 hSk
  exact lt_of_lt_of_le (volume_step k hk1) (measure_mono hsub)

/-! ### A matriz de Gram em L² -/

/-- G_{ij} = ∫_{(0,1]} ρ_{m_i} ρ_{m_j}. -/
noncomputable def gramL2 {N : ℕ} (m : Fin N → ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∫ x in Ioc (0 : ℝ) 1, rho (m i) x * rho (m j) x

/-- cᵀ G c = ∫ (Σ c_i ρ_{m_i})². -/
theorem quad_gramL2 {N : ℕ} (m : Fin N → ℕ) (hm : ∀ i, 1 ≤ m i) (c : Fin N → ℝ) :
    ATK.OmegaGramRho.quad (gramL2 m) c
      = ∫ x in Ioc (0 : ℝ) 1, (∑ i, c i * rho (m i) x) ^ 2 := by
  unfold ATK.OmegaGramRho.quad gramL2
  have hint : ∀ i j, IntegrableOn (fun x => c i * rho (m i) x * (c j * rho (m j) x)) (Ioc 0 1) := by
    intro i j
    have this : IntegrableOn (fun x => c i * c j * (rho (K := ℝ) (m i) x * rho (m j) x)) (Ioc 0 1) :=
      (integrableOn_rho_mul (m i) (m j) (hm i) (hm j)).const_mul (c i * c j)
    exact IntegrableOn.congr_fun this (fun x _ => by ring) measurableSet_Ioc
  calc ∑ i, ∑ j, c i * (∫ x in Ioc (0:ℝ) 1, rho (m i) x * rho (m j) x) * c j
      = ∑ i, ∑ j, ∫ x in Ioc (0:ℝ) 1, c i * rho (m i) x * (c j * rho (m j) x) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [← integral_const_mul, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
    _ = ∫ x in Ioc (0:ℝ) 1, ∑ i, ∑ j, c i * rho (m i) x * (c j * rho (m j) x) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        refine sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hint i j]
    _ = ∫ x in Ioc (0:ℝ) 1, (∑ i, c i * rho (m i) x) ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [sq, sum_mul_sum]

/-- **Teorema (incondicional).** Para índices distintos m_i ≥ 2, a matriz de Gram
de ρ_{m_1}, …, ρ_{m_N} em L²(0,1) é definida positiva. -/
theorem gramL2_posDef {N : ℕ} (m : Fin N → ℕ) (hm : ∀ i, 2 ≤ m i) (hinj : Function.Injective m) :
    ATK.OmegaGramRho.PosDefQ (gramL2 m) := by
  classical
  have hm1 : ∀ i, 1 ≤ m i := fun i => by have := hm i; omega
  constructor
  · intro c
    rw [quad_gramL2 m hm1]
    exact integral_nonneg fun x => sq_nonneg _
  · intro c hc
    by_contra hne
    rw [quad_gramL2 m hm1] at hc
    -- reescreve Σ_i como Σ_{n ∈ image m} e aplica integral_sq_pos
    let I : Finset ℕ := univ.image m
    let c' : ℕ → ℝ := fun n => if h : ∃ i, m i = n then c h.choose else 0
    have hI : ∀ n ∈ I, 2 ≤ n := by
      intro n hn; obtain ⟨i, _, rfl⟩ := mem_image.mp hn; exact hm i
    have hcomb : ∀ x : ℝ, ∑ i, c i * rho (m i) x = ∑ n ∈ I, c' n * rho n x := by
      intro x
      rw [sum_image (fun a _ b _ hab => hinj hab)]
      refine sum_congr rfl fun i _ => ?_
      have h : ∃ j, m j = m i := ⟨i, rfl⟩
      have : h.choose = i := hinj h.choose_spec
      simp [c', h, this]
    have hc' : ∃ n ∈ I, c' n ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h; exact hne (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
      refine ⟨m i, mem_image_of_mem m (mem_univ i), ?_⟩
      have h : ∃ j, m j = m i := ⟨i, rfl⟩
      have : h.choose = i := hinj h.choose_spec
      simp [c', h, this, hi]
    have hpos := integral_sq_pos I c' hI hc'
    have : (∫ x in Ioc (0:ℝ) 1, (∑ i, c i * rho (m i) x) ^ 2)
        = ∫ x in Ioc (0:ℝ) 1, (∑ n ∈ I, c' n * rho n x) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i, c i * rho (m i) x) ^ 2 = (∑ n ∈ I, c' n * rho n x) ^ 2
      rw [hcomb x]
    rw [this] at hc
    linarith

/-- O produto interno de L² restrito às ρ detecta os degraus: consequência direta. -/
theorem gramL2_eq_gram_of_integral {N : ℕ} (m : Fin N → ℕ) :
    gramL2 m = fun i j => ∫ x in Ioc (0 : ℝ) 1, rho (m i) x * rho (m j) x := rfl

end ATK.OmegaGramL2

#print axioms ATK.OmegaGramL2.measurable_rho
#print axioms ATK.OmegaGramL2.abs_rho_le_one
#print axioms ATK.OmegaGramL2.step_subset
#print axioms ATK.OmegaGramL2.volume_step
#print axioms ATK.OmegaGramL2.floor_inv_of_mem_step
#print axioms ATK.OmegaGramL2.comb_eq_stepVal_on_step
#print axioms ATK.OmegaGramL2.integrableOn_rho_mul
#print axioms ATK.OmegaGramL2.integrableOn_comb_sq
#print axioms ATK.OmegaGramL2.integral_sq_pos
#print axioms ATK.OmegaGramL2.quad_gramL2
#print axioms ATK.OmegaGramL2.gramL2_posDef
#print axioms ATK.OmegaGramL2.gramL2_eq_gram_of_integral
