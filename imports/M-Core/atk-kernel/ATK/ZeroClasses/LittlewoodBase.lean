import ATK.ZeroClasses.ExplicitaGauss
import ATK.ZeroClasses.PsiLog2

/-!
# Littlewood, parte 1: o lado `ψ` da fórmula gaussiana e a localização (rodada 90)

Primeira parte do teorema de Littlewood `ψ(x) − x = Ω±(√x log log log x)` a partir da fórmula explícita
gaussiana da rodada 89 (`ExplicitaGauss.formula_gauss`). Aqui se troca o lado aritmético pela função
`F(y) = (ψ(e^y) − e^y) e^{−y/2}` e se prova a localização que transforma uma média gaussiana grande de `F`
num valor grande de `F` numa janela `[u − 1, u + 1]`.

* §1 `integral_kg_exp`: `∫ k_τ(v) e^{lv} dv = e^{τl²}` (núcleo do calor `k_τ(v) = (4πτ)^{−1/2} e^{−v²/(4τ)}`),
  e as caudas `cauda_dir`/`cauda_esq`: `∫_{v ≥ 1} k_τ(v) e^{v} ≤ e^{1 − 1/(4τ)}` para `τ ≤ ½`.
* §2 `A_eq_psi`: `A_τ(u) = Σ Λ(n) n^{−1/2} Φ_τ(u − log n) = ∫ ψ(e^{u − v}) e^{−(u − v)/2} k_τ(v) dv`,
  e `A_sub_eq`: `A_τ(u) − e^{u/2 + τ/4} = ∫ k_τ(v) F(u − v) dv` (o termo `W(1)` é exatamente a parte `x`).
* §3 `Fpsi_le_RH`: sob RH, `|F(y)| ≤ B(1 + y²)` (von Koch, rodada 67); `localiza_menos`/`localiza_mais`:
  se `∫ k_τ F(u − ·) < −L − 8B(1 + 2u²)e^{1 − 1/(4τ)}` então `F(y) ≤ −L` em algum `y ∈ [u − 1, u + 1]`
  (e simetricamente por cima).
* §4 `re_pw_RH`: em `Re ρ = ½`, `Re(W(ρ)/ρ) = e^{−τγ²}(cos(γu)/2 + γ sen(γu))/|ρ|²`.
* §5 `formula_psi` (sem hipóteses): ao longo de alturas boas `T_k ∈ [k + 6, k + 7]`,
  `Σ_{|γ| ≤ T_k} m_ρ Re(W(ρ)/ρ) → −∫ k_τ(v) F(u − v) dv + e^{−5u/2 + 25τ/4}/2 − e^{−u/2 + τ/4} log 2π + Re(E)`.

Classificação: **ferramenta**. O teorema de Littlewood em si continua BUILD_PENDING: faltam as estimativas da
soma sobre zeros sob RH (termo principal `≍ e^{−A} log T` via Riemann–von Mangoldt, cauda gaussiana, alinhamento
de Dirichlet com cota explícita) e a montagem com o caso `¬RH` (rodada 87, `Unilateral.psi_omega_mais`).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace ATK.ZeroClasses.LittlewoodBase

open ATK.ZeroClasses.ExplicitaGauss (Wg kg kg_nonneg Phi Aτ pw)

/-! ## 1. O núcleo do calor: função geradora de momentos e caudas -/

theorem integrable_kg_exp {τ : ℝ} (hτ : 0 < τ) (l : ℝ) :
    Integrable fun v : ℝ => kg τ v * Real.exp (l * v) := by
  have h := integrable_cexp_quadratic (b := ((1 / (4 * τ) : ℝ) : ℂ)) (by simp; positivity) (l : ℂ) 0
  have h2 := h.re
  refine (h2.const_mul ((4 * π * τ) ^ (-(1 / 2 : ℝ)))).congr (Eventually.of_forall fun v => ?_)
  simp only [kg]
  have e : (cexp (-((1 / (4 * τ) : ℝ) : ℂ) * (v : ℂ) ^ 2 + (l : ℂ) * v + 0)).re =
      Real.exp (-(v ^ 2 / (4 * τ)) + l * v) := by
    rw [show -((1 / (4 * τ) : ℝ) : ℂ) * (v : ℂ) ^ 2 + (l : ℂ) * v + 0 =
      ((-(v ^ 2 / (4 * τ)) + l * v : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp, ofReal_re]
  rw [RCLike.re_to_complex, e, Real.exp_add]
  ring

/-- **A função geradora de momentos**: `∫ k_τ(v) e^{lv} dv = e^{τl²}`. -/
theorem integral_kg_exp {τ : ℝ} (hτ : 0 < τ) (l : ℝ) :
    ∫ v : ℝ, kg τ v * Real.exp (l * v) = Real.exp (τ * l ^ 2) := by
  have h := integral_cexp_quadratic (b := -((1 / (4 * τ) : ℝ) : ℂ)) (by simp; positivity) (l : ℂ) 0
  have e2 : ((π : ℂ) / -(-((1 / (4 * τ) : ℝ) : ℂ))) ^ (1 / 2 : ℂ) *
      cexp (0 - (l : ℂ) ^ 2 / (4 * -((1 / (4 * τ) : ℝ) : ℂ))) =
      ((Real.sqrt (4 * π * τ) * Real.exp (τ * l ^ 2) : ℝ) : ℂ) := by
    rw [show (π : ℂ) / -(-((1 / (4 * τ) : ℝ) : ℂ)) = ((4 * π * τ : ℝ) : ℂ) by
      push_cast; field_simp,
      show (0 : ℂ) - (l : ℂ) ^ 2 / (4 * -((1 / (4 * τ) : ℝ) : ℂ)) = ((τ * l ^ 2 : ℝ) : ℂ) by
      push_cast; field_simp; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← ofReal_exp, ← Real.sqrt_eq_rpow]
    push_cast; ring
  rw [e2] at h
  have hr : ∫ v : ℝ, Real.exp (-(v ^ 2 / (4 * τ)) + l * v) = Real.sqrt (4 * π * τ) * Real.exp (τ * l ^ 2) := by
    apply Complex.ofReal_injective
    rw [← h, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  have hk : ∀ v : ℝ, kg τ v * Real.exp (l * v) =
      (4 * π * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(v ^ 2 / (4 * τ)) + l * v) := fun v => by
    simp only [kg]; rw [Real.exp_add]; ring
  simp_rw [hk]
  rw [integral_const_mul, hr, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt (4 * π * τ) := Real.sqrt_pos.mpr (by positivity)
  field_simp

theorem integral_kg {τ : ℝ} (hτ : 0 < τ) : ∫ v : ℝ, kg τ v = 1 := by
  have := integral_kg_exp hτ 0
  simpa using this

theorem integrable_kg {τ : ℝ} (hτ : 0 < τ) : Integrable (kg τ) := by
  have := integrable_kg_exp hτ 0
  simpa using this

/-- **Cauda de Chernoff com peso**: `∫_{v ≥ 1} k_τ(v) e^{v} dv ≤ e^{1 − 1/(4τ)}` para `τ ≤ ½`. -/
theorem cauda_dir {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) :
    ∫ v in Ici (1 : ℝ), kg τ v * Real.exp v ≤ Real.exp (1 - 1 / (4 * τ)) := by
  set l : ℝ := 1 / (2 * τ) - 1 with hl
  have hl0 : 0 ≤ l := by
    rw [hl, sub_nonneg, le_div_iff₀ (by positivity)]; linarith only [hτ1]
  have hint := integrable_kg_exp hτ (1 + l)
  calc ∫ v in Ici (1 : ℝ), kg τ v * Real.exp v
      ≤ ∫ v in Ici (1 : ℝ), kg τ v * Real.exp ((1 + l) * v) * Real.exp (-l) := by
        refine setIntegral_mono_on ((integrable_kg_exp hτ 1).integrableOn.congr_fun
          (fun v _ => by simp) measurableSet_Ici) ((hint.mul_const _).integrableOn) measurableSet_Ici
          fun v hv => ?_
        have hv1 : (1 : ℝ) ≤ v := hv
        rw [mul_assoc, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left _ (kg_nonneg τ v hτ)
        exact Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hl0 (sub_nonneg.mpr hv1)])
    _ ≤ ∫ v : ℝ, kg τ v * Real.exp ((1 + l) * v) * Real.exp (-l) :=
        setIntegral_le_integral (hint.mul_const _) (Eventually.of_forall fun v =>
          mul_nonneg (mul_nonneg (kg_nonneg τ v hτ) (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ = Real.exp (τ * (1 + l) ^ 2) * Real.exp (-l) := by rw [integral_mul_const, integral_kg_exp hτ]
    _ = Real.exp (1 - 1 / (4 * τ)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hl]
        field_simp
        ring

theorem kg_neg (τ v : ℝ) : kg τ (-v) = kg τ v := by simp [kg]

/-- A mesma cauda à esquerda: `∫_{v ≤ −1} k_τ(v) e^{−v} dv ≤ e^{1 − 1/(4τ)}`. -/
theorem cauda_esq {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) :
    ∫ v in Iic (-1 : ℝ), kg τ v * Real.exp (-v) ≤ Real.exp (1 - 1 / (4 * τ)) := by
  have h := cauda_dir hτ hτ1
  have e : ∫ v in Iic (-1 : ℝ), kg τ v * Real.exp (-v) =
      ∫ v in Iic (-1 : ℝ), (fun w : ℝ => kg τ w * Real.exp w) (-v) := by
    congr 1; funext v; simp [kg_neg]
  rw [e, integral_comp_neg_Iic (-1) (fun w : ℝ => kg τ w * Real.exp w), neg_neg,
    ← integral_Ici_eq_integral_Ioi]
  exact h

/-! ## 2. O lado aritmético é `ψ` suavizado -/

/-- `F(y) = (ψ(e^y) − e^y) e^{−y/2}`. -/
noncomputable def Fpsi (y : ℝ) : ℝ := (Chebyshev.psi (Real.exp y) - Real.exp y) * Real.exp (-(y / 2))

theorem measurable_Fpsi : Measurable Fpsi := by
  unfold Fpsi
  have h1 : Measurable fun y : ℝ => Chebyshev.psi (Real.exp y) :=
    Chebyshev.psi_mono.measurable.comp Real.measurable_exp
  fun_prop

/-- `Φ_τ(c) = ∫_{v ≤ c} e^{−(c−v)/2} k_τ(v) dv`. -/
theorem phi_eq (τ c : ℝ) : Phi τ c = ∫ v in Iic c, Real.exp (-((c - v) / 2)) * kg τ v := by
  unfold Phi
  rw [integral_Iic_eq_integral_Iio, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Iio,
    ← integral_sub_left_eq_self (fun w => (Ioi (0 : ℝ)).indicator
      (fun w => Real.exp (-(w / 2)) * kg τ (c - w)) w) volume c]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [indicator, mem_Ioi, mem_Iio, sub_pos]
  split_ifs <;> simp [sub_sub_cancel]

/-- O peso `g(v) = e^{−(u−v)/2} k_τ(v)`. -/
noncomputable def gw (τ u v : ℝ) : ℝ := Real.exp (-((u - v) / 2)) * kg τ v

theorem gw_nonneg {τ : ℝ} (hτ : 0 < τ) (u v : ℝ) : 0 ≤ gw τ u v :=
  mul_nonneg (Real.exp_pos _).le (kg_nonneg τ v hτ)

theorem gw_eq (τ u v : ℝ) : gw τ u v = Real.exp (-(u / 2)) * (kg τ v * Real.exp ((1 / 2) * v)) := by
  unfold gw
  rw [show -((u - v) / 2) = -(u / 2) + (1 / 2) * v by ring, Real.exp_add]
  ring

theorem integrable_gw {τ : ℝ} (hτ : 0 < τ) (u : ℝ) : Integrable (gw τ u) := by
  have := (integrable_kg_exp hτ (1 / 2)).const_mul (Real.exp (-(u / 2)))
  exact this.congr (Eventually.of_forall fun v => (gw_eq τ u v).symm)

theorem measurable_gw (τ u : ℝ) : Measurable (gw τ u) := by
  unfold gw kg; fun_prop

theorem termo_eq (τ u : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) * Phi τ (u - Real.log n) =
      ∫ v, (Iic (u - Real.log n)).indicator (fun v => ArithmeticFunction.vonMangoldt n * gw τ u v) v := by
  rw [phi_eq, integral_indicator measurableSet_Iic, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Iic fun v _ => ?_
  simp only [gw]
  rw [mul_assoc, ← mul_assoc (Real.exp _), ← Real.exp_add]
  congr 3
  ring

/-- As somas parciais `S_N(v) = Σ_{n<N} Λ(n) 1[v ≤ u − log n] g(v)`. -/
noncomputable def Sn (τ u : ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (Iic (u - Real.log n)).indicator (fun v => ArithmeticFunction.vonMangoldt n * gw τ u v) v

theorem ind_eq (τ u v : ℝ) (n : ℕ) :
    (Iic (u - Real.log n)).indicator (fun v => ArithmeticFunction.vonMangoldt n * gw τ u v) v =
      (if (n : ℝ) ≤ Real.exp (u - v) then ArithmeticFunction.vonMangoldt n else 0) * gw τ u v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hiff : v ∈ Iic (u - Real.log n) ↔ (n : ℝ) ≤ Real.exp (u - v) := by
      rw [mem_Iic, ← Real.log_le_iff_le_exp hn']
      constructor <;> intro h <;> linarith
    by_cases h : (n : ℝ) ≤ Real.exp (u - v)
    · rw [indicator_of_mem (hiff.mpr h)]
      simp [h]
    · rw [indicator_of_notMem (fun h' => h (hiff.mp h'))]
      simp [h]

theorem soma_ite {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : ⌊x⌋₊ + 1 ≤ N) :
    ∑ n ∈ Finset.range N, (if (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0) = Chebyshev.psi x := by
  rw [ATK.ZeroClasses.PNT.psi_eq_range x rfl, ← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    have := Nat.le_floor h
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    have h' : n ≤ ⌊x⌋₊ := by omega
    exact (Nat.le_floor_iff hx).mp h'

theorem soma_ite_le (x : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (if (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0) ≤ Chebyshev.psi x := by
  rcases lt_or_ge x 0 with hx | hx
  · have : ∀ n ∈ Finset.range N, (if (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0) = 0 := by
      intro n _
      have : ¬ (n : ℝ) ≤ x := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      simp [this]
    rw [Finset.sum_eq_zero this]
    exact Chebyshev.psi_nonneg x
  · calc ∑ n ∈ Finset.range N, (if (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0)
        ≤ ∑ n ∈ Finset.range (max N (⌊x⌋₊ + 1)), (if (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _)) fun n _ _ => by
            split_ifs
            · exact ArithmeticFunction.vonMangoldt_nonneg
            · exact le_rfl
      _ = Chebyshev.psi x := soma_ite hx (le_max_right _ _)

theorem Sn_eq (τ u v : ℝ) (N : ℕ) : Sn τ u N v =
    (∑ n ∈ Finset.range N, (if (n : ℝ) ≤ Real.exp (u - v) then ArithmeticFunction.vonMangoldt n else 0)) *
      gw τ u v := by
  unfold Sn
  simp_rw [ind_eq]
  rw [Finset.sum_mul]

theorem measurable_psi_exp (u : ℝ) : Measurable fun v : ℝ => Chebyshev.psi (Real.exp (u - v)) :=
  Chebyshev.psi_mono.measurable.comp (Real.measurable_exp.comp (measurable_const.sub measurable_id))

theorem integrable_psi_gw {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    Integrable fun v => Chebyshev.psi (Real.exp (u - v)) * gw τ u v := by
  have hψm := measurable_psi_exp u
  refine ((integrable_kg_exp hτ (-(1 / 2))).const_mul ((Real.log 4 + 4) * Real.exp (u / 2))).mono'
    (hψm.mul (measurable_gw τ u)).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  have hψ0 := Chebyshev.psi_nonneg (Real.exp (u - v))
  have hψ := Chebyshev.psi_le_const_mul_self (Real.exp_pos (u - v)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hψ0 (gw_nonneg hτ u v))]
  calc Chebyshev.psi (Real.exp (u - v)) * gw τ u v
      ≤ (Real.log 4 + 4) * Real.exp (u - v) * gw τ u v :=
        mul_le_mul_of_nonneg_right hψ (gw_nonneg hτ u v)
    _ = (Real.log 4 + 4) * Real.exp (u / 2) * (kg τ v * Real.exp (-(1 / 2) * v)) := by
        unfold gw
        rw [show (Real.log 4 + 4) * Real.exp (u - v) * (Real.exp (-((u - v) / 2)) * kg τ v) =
          (Real.log 4 + 4) * kg τ v * (Real.exp (u - v) * Real.exp (-((u - v) / 2))) by ring,
          ← Real.exp_add]
        rw [show (Real.log 4 + 4) * Real.exp (u / 2) * (kg τ v * Real.exp (-(1 / 2) * v)) =
          (Real.log 4 + 4) * kg τ v * (Real.exp (u / 2) * Real.exp (-(1 / 2) * v)) by ring,
          ← Real.exp_add]
        congr 2
        ring

/-- **`A_τ(u) = ∫ k_τ(v) e^{−(u−v)/2} ψ(e^{u−v}) dv`**. -/
theorem A_eq_psi {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    Aτ τ u = ∫ v, Chebyshev.psi (Real.exp (u - v)) * gw τ u v := by
  set bd : ℝ → ℝ := fun v => Chebyshev.psi (Real.exp (u - v)) * gw τ u v with hbd
  have hbdi : Integrable bd := integrable_psi_gw hτ u
  have hterm : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) *
      Phi τ (u - Real.log n) = ∫ v, (Iic (u - Real.log n)).indicator
        (fun v => ArithmeticFunction.vonMangoldt n * gw τ u v) v := termo_eq τ u
  have hint_n : ∀ n : ℕ, Integrable ((Iic (u - Real.log n)).indicator
      (fun v => ArithmeticFunction.vonMangoldt n * gw τ u v)) := fun n =>
    ((integrable_gw hτ u).const_mul _).indicator measurableSet_Iic
  have hnn : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) *
      Phi τ (u - Real.log n) := fun n => by
    rw [hterm]
    refine integral_nonneg fun v => ?_
    simp only [indicator]
    split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (gw_nonneg hτ u v)
    · exact le_rfl
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n *
      Real.exp (-(Real.log n / 2)) * Phi τ (u - Real.log n) = ∫ v, Sn τ u N v := by
    intro N
    unfold Sn
    rw [integral_finsetSum _ fun n _ => hint_n n]
    exact Finset.sum_congr rfl fun n _ => hterm n
  have hlim : Tendsto (fun N => ∫ v, Sn τ u N v) atTop (𝓝 (∫ v, bd v)) := by
    refine tendsto_integral_of_dominated_convergence bd (fun N => ?_) hbdi (fun N => ?_) ?_
    · exact (Finset.measurable_sum _ fun n _ =>
        ((measurable_const.mul (measurable_gw τ u)).indicator measurableSet_Iic)).aestronglyMeasurable
    · refine Eventually.of_forall fun v => ?_
      rw [Sn_eq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Finset.sum_nonneg fun n _ => by
        split_ifs
        · exact ArithmeticFunction.vonMangoldt_nonneg
        · exact le_rfl) (gw_nonneg hτ u v))]
      exact mul_le_mul_of_nonneg_right (soma_ite_le _ N) (gw_nonneg hτ u v)
    · refine Eventually.of_forall fun v => ?_
      refine tendsto_atTop_of_eventually_const (i₀ := ⌊Real.exp (u - v)⌋₊ + 1) fun N hN => ?_
      rw [Sn_eq, soma_ite (Real.exp_pos _).le hN]
  have hsum : HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n * Real.exp (-(Real.log n / 2)) *
      Phi τ (u - Real.log n)) (∫ v, bd v) :=
    (hasSum_iff_tendsto_nat_of_nonneg hnn _).mpr (hlim.congr fun N => (hpart N).symm)
  unfold Aτ
  exact hsum.tsum_eq

/-- **O lado aritmético menos `W(1)` é `F` suavizado**: `A_τ(u) − e^{u/2 + τ/4} = ∫ k_τ(v) F(u − v) dv`. -/
theorem A_sub_eq {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    Aτ τ u - Real.exp (u / 2 + τ / 4) = ∫ v, kg τ v * Fpsi (u - v) := by
  have hW : ∫ v, Real.exp (u - v) * gw τ u v = Real.exp (u / 2 + τ / 4) := by
    have e : ∀ v : ℝ, Real.exp (u - v) * gw τ u v = Real.exp (u / 2) * (kg τ v * Real.exp (-(1 / 2) * v)) := by
      intro v
      unfold gw
      rw [show Real.exp (u - v) * (Real.exp (-((u - v) / 2)) * kg τ v) =
        kg τ v * (Real.exp (u - v) * Real.exp (-((u - v) / 2))) by ring, ← Real.exp_add,
        show Real.exp (u / 2) * (kg τ v * Real.exp (-(1 / 2) * v)) =
        kg τ v * (Real.exp (u / 2) * Real.exp (-(1 / 2) * v)) by ring, ← Real.exp_add]
      congr 2
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_kg_exp hτ, ← Real.exp_add]
    congr 1
    ring
  have hWi : Integrable fun v => Real.exp (u - v) * gw τ u v := by
    have := (integrable_kg_exp hτ (-(1 / 2))).const_mul (Real.exp (u / 2))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only
    unfold gw
    rw [show Real.exp (u / 2) * (kg τ v * Real.exp (-(1 / 2) * v)) =
      kg τ v * (Real.exp (u / 2) * Real.exp (-(1 / 2) * v)) by ring, ← Real.exp_add,
      show Real.exp (u - v) * (Real.exp (-((u - v) / 2)) * kg τ v) =
      kg τ v * (Real.exp (u - v) * Real.exp (-((u - v) / 2))) by ring, ← Real.exp_add]
    congr 2
    ring
  rw [A_eq_psi hτ u, ← hW, ← integral_sub (integrable_psi_gw hτ u) hWi]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [gw, Fpsi]
  rw [show -((u - v) / 2) = -((u - v) / 2) by rfl]
  ring

/-! ## 3. Sob RH, `|F(y)| ≪ 1 + y²`, e a localização -/

/-- **Sob RH**, `|F(y)| ≤ B(1 + y²)` para todo `y` (von Koch, `|ψ(x) − x| ≤ K√x log² x`, rodada 67). -/
theorem Fpsi_le_RH (hRH : RiemannHypothesis) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, |Fpsi y| ≤ B * (1 + y ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := ATK.ZeroClasses.Koch.psi_RH_log2 hRH
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨K + 10 * (Real.log 4 + 5), by positivity, fun y => ?_⟩
  have hx0 : 0 < Real.exp y := Real.exp_pos y
  have he : 0 < Real.exp (-(y / 2)) := Real.exp_pos _
  unfold Fpsi
  rw [abs_mul, abs_of_pos he]
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  rcases le_or_gt 100 (Real.exp y) with h | h
  · have hb := hK (Real.exp y) h
    rw [Real.log_exp, ← Real.exp_half] at hb
    have : |Chebyshev.psi (Real.exp y) - Real.exp y| * Real.exp (-(y / 2)) ≤ K * y ^ 2 := by
      calc |Chebyshev.psi (Real.exp y) - Real.exp y| * Real.exp (-(y / 2))
          ≤ K * Real.exp (y / 2) * y ^ 2 * Real.exp (-(y / 2)) := mul_le_mul_of_nonneg_right hb he.le
        _ = K * y ^ 2 * (Real.exp (y / 2) * Real.exp (-(y / 2))) := by ring
        _ = K * y ^ 2 := by rw [← Real.exp_add, show y / 2 + -(y / 2) = 0 by ring, Real.exp_zero, mul_one]
    nlinarith only [this, hy2, hK0, hl4, mul_nonneg hl4 hy2]
  · have hψ0 := Chebyshev.psi_nonneg (Real.exp y)
    have hψ := Chebyshev.psi_le_const_mul_self hx0.le
    have h1 : |Chebyshev.psi (Real.exp y) - Real.exp y| ≤ (Real.log 4 + 5) * Real.exp y := by
      rw [abs_le]
      constructor <;> nlinarith only [hψ0, hψ, hx0, hl4, mul_nonneg hl4 hx0.le]
    have hs : Real.exp y * Real.exp (-(y / 2)) = Real.exp (y / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hy10 : Real.exp (y / 2) ≤ 10 := by
      rw [Real.exp_half]
      calc Real.sqrt (Real.exp y) ≤ Real.sqrt 100 := Real.sqrt_le_sqrt h.le
        _ = 10 := by rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have : |Chebyshev.psi (Real.exp y) - Real.exp y| * Real.exp (-(y / 2)) ≤ 10 * (Real.log 4 + 5) := by
      calc |Chebyshev.psi (Real.exp y) - Real.exp y| * Real.exp (-(y / 2))
          ≤ (Real.log 4 + 5) * Real.exp y * Real.exp (-(y / 2)) := mul_le_mul_of_nonneg_right h1 he.le
        _ = (Real.log 4 + 5) * Real.exp (y / 2) := by rw [mul_assoc, hs]
        _ ≤ (Real.log 4 + 5) * 10 := mul_le_mul_of_nonneg_left hy10 (by positivity)
        _ = 10 * (Real.log 4 + 5) := by ring
    nlinarith only [this, hy2, hK0, hl4, mul_nonneg hK0 hy2, mul_nonneg hl4 hy2]

theorem um_add_le_exp (v : ℝ) : 1 + 2 * v ^ 2 ≤ 4 * Real.exp |v| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg v)
  have h2 : |v| ^ 2 = v ^ 2 := sq_abs v
  nlinarith [abs_nonneg v]

/-- A cauda `T(v) = 1[v ≥ 1] k_τ(v) e^v + 1[v ≤ −1] k_τ(v) e^{−v}`. -/
noncomputable def cauda (τ v : ℝ) : ℝ :=
  (Ici (1 : ℝ)).indicator (fun v => kg τ v * Real.exp v) v +
    (Iic (-1 : ℝ)).indicator (fun v => kg τ v * Real.exp (-v)) v

theorem integrable_ind1 {τ : ℝ} (hτ : 0 < τ) :
    Integrable ((Ici (1 : ℝ)).indicator (fun v => kg τ v * Real.exp v)) := by
  have := (integrable_kg_exp hτ 1).indicator (measurableSet_Ici : MeasurableSet (Ici (1 : ℝ)))
  refine this.congr (Eventually.of_forall fun v => ?_)
  simp only [one_mul]

theorem integrable_ind2 {τ : ℝ} (hτ : 0 < τ) :
    Integrable ((Iic (-1 : ℝ)).indicator (fun v => kg τ v * Real.exp (-v))) := by
  have := (integrable_kg_exp hτ (-1)).indicator (measurableSet_Iic : MeasurableSet (Iic (-1 : ℝ)))
  refine this.congr (Eventually.of_forall fun v => ?_)
  simp only [neg_one_mul]

theorem integrable_cauda {τ : ℝ} (hτ : 0 < τ) : Integrable (cauda τ) :=
  (integrable_ind1 hτ).add (integrable_ind2 hτ)

theorem integral_cauda_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) :
    ∫ v, cauda τ v ≤ 2 * Real.exp (1 - 1 / (4 * τ)) := by
  unfold cauda
  rw [integral_add (integrable_ind1 hτ) (integrable_ind2 hτ), integral_indicator measurableSet_Ici,
    integral_indicator measurableSet_Iic, two_mul]
  exact add_le_add (cauda_dir hτ hτ1) (cauda_esq hτ hτ1)

theorem cauda_pt {τ : ℝ} (hτ : 0 < τ) {v : ℝ} (hv : v ∉ Icc (-1 : ℝ) 1) :
    kg τ v * (1 + 2 * v ^ 2) ≤ 4 * cauda τ v := by
  have hk := kg_nonneg τ v hτ
  have h := mul_le_mul_of_nonneg_left (um_add_le_exp v) hk
  simp only [mem_Icc, not_and_or, not_le] at hv
  unfold cauda
  rcases hv with hv | hv
  · rw [indicator_of_notMem (by simp; linarith), indicator_of_mem (by simp; linarith), zero_add,
      abs_of_neg (by linarith)] at *
    linarith
  · rw [indicator_of_mem (by simp; linarith), indicator_of_notMem (by simp; linarith), add_zero,
      abs_of_pos (by linarith)] at *
    linarith

theorem integrable_kF {τ B u : ℝ} (hτ : 0 < τ) (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2)) :
    Integrable fun v => kg τ v * Fpsi (u - v) := by
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 0); simpa using this
  have hi := ((integrable_kg_exp hτ 1).add (integrable_kg_exp hτ (-1))).const_mul (4 * B * (1 + 2 * u ^ 2))
  refine hi.mono' ((by unfold kg; fun_prop : Measurable (kg τ)).mul
    (measurable_Fpsi.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hk := kg_nonneg τ v hτ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  have h1 := hB (u - v)
  have h2 : 1 + (u - v) ^ 2 ≤ (1 + 2 * u ^ 2) * (1 + 2 * v ^ 2) := by nlinarith [sq_nonneg (u + v), sq_nonneg (u * v)]
  have h3 := um_add_le_exp v
  have h4 : Real.exp |v| ≤ Real.exp v + Real.exp (-v) := by
    rcases le_or_gt 0 v with hv | hv
    · rw [abs_of_nonneg hv]; linarith [Real.exp_pos (-v)]
    · rw [abs_of_neg hv]; linarith [Real.exp_pos v]
  calc kg τ v * |Fpsi (u - v)| ≤ kg τ v * (B * ((1 + 2 * u ^ 2) * (1 + 2 * v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hk
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
    _ ≤ kg τ v * (B * ((1 + 2 * u ^ 2) * (4 * (Real.exp v + Real.exp (-v))))) := by
        gcongr
        exact h3.trans (by linarith)
    _ = 4 * B * (1 + 2 * u ^ 2) * (kg τ v * Real.exp (1 * v) + kg τ v * Real.exp (-1 * v)) := by
        simp only [one_mul, neg_one_mul]; ring

/-- A parte de `∫ k_τ(v) F(u − v) dv` fora de `|v| ≤ 1` é `≤ 8B(1 + 2u²)e^{1 − 1/(4τ)}` em valor absoluto. -/
theorem fora_le {τ B u : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2)) :
    |∫ v in (Icc (-1 : ℝ) 1)ᶜ, kg τ v * Fpsi (u - v)| ≤ 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) := by
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 0); simpa using this
  have hci := integrable_cauda hτ
  calc |∫ v in (Icc (-1 : ℝ) 1)ᶜ, kg τ v * Fpsi (u - v)|
      ≤ ∫ v in (Icc (-1 : ℝ) 1)ᶜ, 4 * B * (1 + 2 * u ^ 2) * cauda τ v := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((hci.const_mul _).integrableOn) ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
        have hk := kg_nonneg τ v hτ
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
        have h1 := hB (u - v)
        have h2 : 1 + (u - v) ^ 2 ≤ (1 + 2 * u ^ 2) * (1 + 2 * v ^ 2) := by
          nlinarith [sq_nonneg (u + v), sq_nonneg (u * v)]
        have h3 := cauda_pt hτ hv
        calc kg τ v * |Fpsi (u - v)| ≤ kg τ v * (B * ((1 + 2 * u ^ 2) * (1 + 2 * v ^ 2))) := by
              apply mul_le_mul_of_nonneg_left _ hk
              exact h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
          _ = B * (1 + 2 * u ^ 2) * (kg τ v * (1 + 2 * v ^ 2)) := by ring
          _ ≤ B * (1 + 2 * u ^ 2) * (4 * cauda τ v) := by gcongr
          _ = 4 * B * (1 + 2 * u ^ 2) * cauda τ v := by ring
    _ ≤ ∫ v, 4 * B * (1 + 2 * u ^ 2) * cauda τ v := by
        refine setIntegral_le_integral (hci.const_mul _) (Eventually.of_forall fun v => ?_)
        have : 0 ≤ cauda τ v := by
          unfold cauda
          exact add_nonneg (indicator_nonneg (fun v _ => mul_nonneg (kg_nonneg τ v hτ) (Real.exp_pos _).le) _)
            (indicator_nonneg (fun v _ => mul_nonneg (kg_nonneg τ v hτ) (Real.exp_pos _).le) _)
        positivity
    _ = 4 * B * (1 + 2 * u ^ 2) * ∫ v, cauda τ v := integral_const_mul _ _
    _ ≤ 4 * B * (1 + 2 * u ^ 2) * (2 * Real.exp (1 - 1 / (4 * τ))) := by
        gcongr
        exact integral_cauda_le hτ hτ1
    _ = 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) := by ring

theorem integral_Icc_kg_le {τ : ℝ} (hτ : 0 < τ) : ∫ v in Icc (-1 : ℝ) 1, kg τ v ≤ 1 := by
  rw [← integral_kg hτ]
  exact setIntegral_le_integral (integrable_kg hτ) (Eventually.of_forall fun v => kg_nonneg τ v hτ)

/-- **A localização por baixo**: se `∫ k_τ(v) F(u − v) dv < −L − 8B(1 + 2u²)e^{1 − 1/(4τ)}` (`L ≥ 0`), então
`F(y) ≤ −L` para algum `y ∈ [u − 1, u + 1]`. -/
theorem localiza_menos {τ B u L : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2))
    (hL : 0 ≤ L) (h : ∫ v, kg τ v * Fpsi (u - v) < -L - 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ))) :
    ∃ y ∈ Icc (u - 1) (u + 1), Fpsi y ≤ -L := by
  by_contra hne
  push Not at hne
  have hint := integrable_kF (u := u) hτ hB
  rw [← integral_add_compl measurableSet_Icc hint] at h
  have h1 : -L ≤ ∫ v in Icc (-1 : ℝ) 1, kg τ v * Fpsi (u - v) := by
    calc -L ≤ -L * ∫ v in Icc (-1 : ℝ) 1, kg τ v := by
          have h0 : 0 ≤ ∫ v in Icc (-1 : ℝ) 1, kg τ v := setIntegral_nonneg measurableSet_Icc
            fun v _ => kg_nonneg τ v hτ
          have hI := integral_Icc_kg_le hτ
          nlinarith only [h0, hI, hL, mul_nonneg hL (sub_nonneg.mpr hI)]
      _ = ∫ v in Icc (-1 : ℝ) 1, kg τ v * (-L) := by rw [integral_mul_const]; ring
      _ ≤ ∫ v in Icc (-1 : ℝ) 1, kg τ v * Fpsi (u - v) := by
          refine setIntegral_mono_on ((integrable_kg hτ).integrableOn.mul_const _) hint.integrableOn
            measurableSet_Icc fun v hv => ?_
          apply mul_le_mul_of_nonneg_left _ (kg_nonneg τ v hτ)
          exact (hne (u - v) ⟨by linarith only [hv.2], by linarith only [hv.1]⟩).le
  have h2 := fora_le (u := u) hτ hτ1 hB
  have h3 := neg_abs_le (∫ v in (Icc (-1 : ℝ) 1)ᶜ, kg τ v * Fpsi (u - v))
  generalize 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) = E at h h2
  linarith

/-- **A localização por cima**: se `∫ k_τ(v) F(u − v) dv > L + 8B(1 + 2u²)e^{1 − 1/(4τ)}` (`L ≥ 0`), então
`F(y) ≥ L` para algum `y ∈ [u − 1, u + 1]`. -/
theorem localiza_mais {τ B u L : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hB : ∀ y, |Fpsi y| ≤ B * (1 + y ^ 2))
    (hL : 0 ≤ L) (h : L + 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) < ∫ v, kg τ v * Fpsi (u - v)) :
    ∃ y ∈ Icc (u - 1) (u + 1), L ≤ Fpsi y := by
  by_contra hne
  push Not at hne
  have hint := integrable_kF (u := u) hτ hB
  rw [← integral_add_compl measurableSet_Icc hint] at h
  have h1 : ∫ v in Icc (-1 : ℝ) 1, kg τ v * Fpsi (u - v) ≤ L := by
    calc ∫ v in Icc (-1 : ℝ) 1, kg τ v * Fpsi (u - v) ≤ ∫ v in Icc (-1 : ℝ) 1, kg τ v * L := by
          refine setIntegral_mono_on hint.integrableOn ((integrable_kg hτ).integrableOn.mul_const _)
            measurableSet_Icc fun v hv => ?_
          apply mul_le_mul_of_nonneg_left _ (kg_nonneg τ v hτ)
          exact (hne (u - v) ⟨by linarith only [hv.2], by linarith only [hv.1]⟩).le
      _ = L * ∫ v in Icc (-1 : ℝ) 1, kg τ v := by rw [integral_mul_const]; ring
      _ ≤ L := by
          have := integral_Icc_kg_le hτ
          nlinarith only [this, hL, mul_nonneg hL (sub_nonneg.mpr this)]
  have h2 := fora_le (u := u) hτ hτ1 hB
  have h3 := le_abs_self (∫ v in (Icc (-1 : ℝ) 1)ᶜ, kg τ v * Fpsi (u - v))
  generalize 8 * B * (1 + 2 * u ^ 2) * Real.exp (1 - 1 / (4 * τ)) = E at h h2
  linarith

/-! ## 4. Sob RH, a parte real dos termos -/

/-- Para `Re ρ = ½`: `Re(W(ρ)/ρ) = e^{−τγ²}(cos(γu)/2 + γ sen(γu))/|ρ|²`, `γ = Im ρ`. -/
theorem re_pw_RH {ρ : ℂ} (hρ : ρ.re = 1 / 2) (u τ : ℝ) :
    (pw (Wg u τ) ρ).re = Real.exp (-(τ * ρ.im ^ 2)) *
      (Real.cos (ρ.im * u) / 2 + ρ.im * Real.sin (ρ.im * u)) / ‖ρ‖ ^ 2 := by
  have hρ' : ρ - 1 / 2 = ρ.im * I := by
    apply Complex.ext <;> simp [hρ]
  have hW : Wg u τ ρ = cexp (((-(τ * ρ.im ^ 2) : ℝ) : ℂ) + ((ρ.im * u : ℝ) : ℂ) * I) := by
    unfold Wg
    rw [hρ']
    congr 1
    push_cast
    have hI : I ^ 2 = -1 := I_sq
    linear_combination (τ : ℂ) * (ρ.im : ℂ) ^ 2 * hI
  unfold pw
  rw [hW, Complex.div_re, Complex.exp_re, Complex.exp_im, Complex.normSq_eq_norm_sq]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_im, mul_im,
    zero_add, hρ]
  ring_nf

/-! ## 5. A fórmula gaussiana no lado de `ψ` -/

open ATK.ZeroClasses.ExplicitaGauss (formula_gauss Fw)
open ATK.ZeroClasses.ExplicitaT (Zfin)

theorem Wg_real (u τ x : ℝ) : Wg u τ (x : ℂ) = ((Real.exp ((x - 1 / 2) * u + τ * (x - 1 / 2) ^ 2) : ℝ) : ℂ) := by
  unfold Wg
  rw [ofReal_exp]
  push_cast
  ring_nf

/-- **A fórmula gaussiana em termos de `F`** (sem hipóteses): ao longo de alturas boas,
`Σ_{|γ| ≤ T_k} m_ρ Re(W(ρ)/ρ) → −∫ k_τ(v) F(u − v) dv + e^{−5u/2 + 25τ/4}/2 − e^{−u/2 + τ/4} log 2π + Re(E)`,
`E = (1/2π) ∫ F_W(−5/2 + iy) dy` (`O(e^{−3u})`, `ExplicitaGauss.esq_le`). -/
theorem formula_psi {τ : ℝ} (hτ : 0 < τ) (u : ℝ) : ∃ T : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 6 ≤ T k ∧ T k ≤ k + 7) ∧
    Tendsto (fun k => ∑ ρ ∈ Zfin (T k), (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg u τ) ρ).re) atTop
      (𝓝 (-(∫ v, kg τ v * Fpsi (u - v)) + Real.exp (-(5 / 2) * u + τ * (25 / 4)) / 2 -
        Real.exp (-(1 / 2) * u + τ * (1 / 4)) * Real.log (2 * π) +
        ((1 / (2 * π : ℂ)) * ∫ y : ℝ, Fw (Wg u τ) (((-5 / 2 : ℝ) : ℂ) + y * I)).re)) := by
  obtain ⟨T, hT, hlim⟩ := formula_gauss hτ u
  refine ⟨T, hT, ?_⟩
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have e1 : (fun k => ∑ ρ ∈ Zfin (T k), (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg u τ) ρ).re) =
      Complex.re ∘ fun k => ∑ ρ ∈ Zfin (T k), (analyticOrderNatAt riemannZeta ρ : ℂ) * pw (Wg u τ) ρ := by
    funext k
    simp only [Function.comp, Complex.re_sum]
    exact Finset.sum_congr rfl fun ρ _ => by simp [Complex.mul_re]
  rw [e1]
  convert hre using 2
  have h1 : Wg u τ 1 = ((Real.exp (u / 2 + τ / 4) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, Wg_real]; congr 2; ring
  have h2 : Wg u τ (-2) = ((Real.exp (-(5 / 2) * u + τ * (25 / 4)) : ℝ) : ℂ) := by
    rw [show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by simp, Wg_real]; congr 2; ring
  have h0 : Wg u τ 0 = ((Real.exp (-(1 / 2) * u + τ * (1 / 4)) : ℝ) : ℂ) := by
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, Wg_real]; congr 2; ring
  rw [h1, h2, h0, ← A_sub_eq hτ u]
  simp only [add_re, sub_re, div_re, ofReal_re, ofReal_im, mul_re, mul_im, zero_mul, sub_zero]
  norm_num
  ring

end ATK.ZeroClasses.LittlewoodBase

#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_kg_exp
#print axioms ATK.ZeroClasses.LittlewoodBase.integral_kg_exp
#print axioms ATK.ZeroClasses.LittlewoodBase.integral_kg
#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_kg
#print axioms ATK.ZeroClasses.LittlewoodBase.cauda_dir
#print axioms ATK.ZeroClasses.LittlewoodBase.kg_neg
#print axioms ATK.ZeroClasses.LittlewoodBase.cauda_esq
#print axioms ATK.ZeroClasses.LittlewoodBase.measurable_Fpsi
#print axioms ATK.ZeroClasses.LittlewoodBase.phi_eq
#print axioms ATK.ZeroClasses.LittlewoodBase.gw_nonneg
#print axioms ATK.ZeroClasses.LittlewoodBase.gw_eq
#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_gw
#print axioms ATK.ZeroClasses.LittlewoodBase.measurable_gw
#print axioms ATK.ZeroClasses.LittlewoodBase.termo_eq
#print axioms ATK.ZeroClasses.LittlewoodBase.ind_eq
#print axioms ATK.ZeroClasses.LittlewoodBase.soma_ite
#print axioms ATK.ZeroClasses.LittlewoodBase.soma_ite_le
#print axioms ATK.ZeroClasses.LittlewoodBase.Sn_eq
#print axioms ATK.ZeroClasses.LittlewoodBase.measurable_psi_exp
#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_psi_gw
#print axioms ATK.ZeroClasses.LittlewoodBase.A_eq_psi
#print axioms ATK.ZeroClasses.LittlewoodBase.A_sub_eq
#print axioms ATK.ZeroClasses.LittlewoodBase.Fpsi_le_RH
#print axioms ATK.ZeroClasses.LittlewoodBase.um_add_le_exp
#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_ind1
#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_ind2
#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_cauda
#print axioms ATK.ZeroClasses.LittlewoodBase.integral_cauda_le
#print axioms ATK.ZeroClasses.LittlewoodBase.cauda_pt
#print axioms ATK.ZeroClasses.LittlewoodBase.integrable_kF
#print axioms ATK.ZeroClasses.LittlewoodBase.fora_le
#print axioms ATK.ZeroClasses.LittlewoodBase.integral_Icc_kg_le
#print axioms ATK.ZeroClasses.LittlewoodBase.localiza_menos
#print axioms ATK.ZeroClasses.LittlewoodBase.localiza_mais
#print axioms ATK.ZeroClasses.LittlewoodBase.re_pw_RH
#print axioms ATK.ZeroClasses.LittlewoodBase.Wg_real
#print axioms ATK.ZeroClasses.LittlewoodBase.formula_psi
