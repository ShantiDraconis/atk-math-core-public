/-
ATK — Programa de ataque, frente 1: BSD (parte do posto) para `y² = x³ − x`.

O kernel já sabe que `E : y² = x³ − x` tem posto 0 (`ATK.LigacaoBSDTestes.posto_curva32`, pela
descida de Fermat) e que o enunciado do Clay obriga `L(E, 1) ≠ 0` nessa curva
(`clay_curva32`).  Este arquivo prova o lado analítico a partir de duas pontes publicadas,
explícitas como hipóteses (nunca como `axiom`):

* **P1 — modularidade com sinal** (`PonteModular E c ε`): a teta da curva
  `g(x) = Σₙ aₙ e^{−c n x}`, `c = 2π/√N`, satisfaz `g(1/x) = ε x² g(x)`.  É a forma, no eixo
  imaginário, da equação funcional `Λ(s) = ε Λ(2 − s)` da newform de peso 2 e nível `N`
  (Wiles, Taylor–Wiles, BCDT; para `y² = x³ − x`, multiplicação complexa: Deuring/Hecke),
  com `N = 32` e sinal `ε = +1`;
* **P2 — cota dos coeficientes** (`CotaCoef E`): `|aₙ| ≤ n` (Hasse; para esta curva, também
  `a_p = 0` se `p ≡ 3 mod 4`).

Com elas, sem mais nada:

* `par`: `(g, g)` é um FE-pair forte da Mathlib de peso `k = 2` — `Λ = M[g]` é inteira;
* **`Λ₀_um`**: pela dobra de Mellin (`ATK.BaseRiemannTeta.Λ₀_eq_caudas`),
  `Λ(1) = (1 + ε) ∫₁^∞ g(x) dx`;
* **`integral_teta`**: `∫₁^∞ g = Σₙ aₙ e^{−cn}/(cn)` (série que converge rapidamente);
* **`mellin_teta`**: `Λ(s) = Γ(s) c^{−s} L(E, s)` para `Re s > 2`;
* `Lc = c^s Λ(s)/Γ(s)` é inteira e coincide com `L(E, s)` em `Re s > 2`, logo **toda
  continuação de `L(E, s)` é `Lc`** (`continuacao_eq`);
* **`serie_re_pos`**: se `e^{−c} < 1/2`, `Re Σₙ aₙ e^{−cn}/(cn) > 0` (só `a₁ = 1` e `|aₙ| ≤ n`);
* **`L1_ne_zero`**: com sinal `+1`, `|aₙ| ≤ n` e `e^{−c} < 1/2` (isto é, `N < (2π/log 2)² ≈ 82`),
  `L(E, 1) ≠ 0`;
* **`bsd_posto_curva32`**: para `y² = x³ − x`, toda continuação `G` de `L(E, s)` tem
  `G(1) ≠ 0` e **ordem 0 em `s = 1` = posto de Mordell–Weil**: a parte do posto da conjectura
  de BSD vale para esta curva, módulo P1 e P2.

O resultado é clássico (Coates–Wiles, 1977); o que é novo aqui é a redução formal a duas pontes
publicadas e a uma estimativa elementar certificada. Nada aqui prova BSD em geral.
-/
import ATK.LigacaoBSDTestes
import ATK.BaseRiemannTeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex Set MeasureTheory Filter Asymptotics Topology
open scoped Real

noncomputable section

namespace ATK.AtaqueBSD

open ATK.LigacaoBSD ATK.LigacaoBSDTestes ATK.BaseRiemannTeta

/-! ### A teta da curva e as pontes -/

section Teta

variable (W : WeierstrassCurve ℚ) (c : ℝ)

/-- Teta da curva: `g(x) = Σₙ aₙ e^{−c n x}`. -/
def teta (x : ℝ) : ℂ := ∑' n : ℕ, coef W n * (Real.exp (-(c * n * x)) : ℂ)

/-- **Ponte P1** (modularidade com sinal `ε`): `g(1/x) = ε x² g(x)` para `x > 0`. -/
def PonteModular (ε : ℂ) : Prop :=
  ∀ x : ℝ, 0 < x → teta W c (1 / x) = ε * (x : ℂ) ^ 2 * teta W c x

/-- **Ponte P2** (cota dos coeficientes): `|aₙ| ≤ n`. -/
def CotaCoef : Prop := ∀ n : ℕ, ‖coef W n‖ ≤ n

variable {W c}

theorem coef_zero : coef W 0 = 0 := by simp [coef]

theorem exp_nat (x : ℝ) (n : ℕ) : Real.exp (-(c * n * x)) = Real.exp (-(c * x)) ^ n := by
  rw [← Real.exp_nat_mul]
  ring_nf

theorem norm_termo_le (hK : CotaCoef W) (n : ℕ) (x : ℝ) :
    ‖coef W n * (Real.exp (-(c * n * x)) : ℂ)‖ ≤ n * Real.exp (-(c * x)) ^ n := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), exp_nat]
  exact mul_le_mul_of_nonneg_right (hK n) (by positivity)

theorem summable_maj {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℕ => (n : ℝ) * r ^ n := by
  have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
    (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  simpa using this

theorem exp_neg_lt_one (hc : 0 < c) {x : ℝ} (hx : 0 < x) : Real.exp (-(c * x)) < 1 :=
  Real.exp_lt_one_iff.mpr (by nlinarith)

theorem summable_teta (hc : 0 < c) (hK : CotaCoef W) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => coef W n * (Real.exp (-(c * n * x)) : ℂ) :=
  Summable.of_norm_bounded (summable_maj (Real.exp_pos _).le (exp_neg_lt_one hc hx))
    fun n => norm_termo_le hK n x

/-- A teta é contínua em `(0, ∞)` (teste M de Weierstrass em cada `[x₀/2, ∞)`). -/
theorem continuousOn_teta (hc : 0 < c) (hK : CotaCoef W) : ContinuousOn (teta W c) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀' : (0 : ℝ) < x₀ := hx₀
  have hδ : 0 < x₀ / 2 := half_pos hx₀'
  have h : ContinuousOn (fun x : ℝ => ∑' n : ℕ, coef W n * (Real.exp (-(c * n * x)) : ℂ))
      (Ici (x₀ / 2)) := by
    refine continuousOn_tsum (u := fun n : ℕ => (n : ℝ) * Real.exp (-(c * (x₀ / 2))) ^ n)
      (fun n => ?_) (summable_maj (Real.exp_pos _).le (exp_neg_lt_one hc hδ)) (fun n x hx => ?_)
    · exact (continuous_const.mul (continuous_ofReal.comp
        (Real.continuous_exp.comp (by fun_prop)))).continuousOn
    · have hx' : x₀ / 2 ≤ x := hx
      refine (norm_termo_le hK n x).trans ?_
      have : Real.exp (-(c * x)) ≤ Real.exp (-(c * (x₀ / 2))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le this n)
        (Nat.cast_nonneg n)
  exact (h.continuousAt (Ici_mem_nhds (by linarith))).continuousWithinAt

/-- **Decaimento exponencial** da teta. -/
theorem teta_isBigO_exp (hc : 0 < c) (hK : CotaCoef W) :
    teta W c =O[atTop] fun x => Real.exp (-c * x) := by
  set r := Real.exp (-(c * 1)) with hr_def
  have hr : r < 1 := exp_neg_lt_one hc one_pos
  set S := ∑' n : ℕ, (n : ℝ) * r ^ n
  have hS : HasSum (fun n : ℕ => (n : ℝ) * r ^ n) S :=
    (summable_maj (Real.exp_pos _).le hr).hasSum
  refine IsBigO.of_bound (S * Real.exp c) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hb : ∀ n : ℕ, ‖coef W n * (Real.exp (-(c * n * x)) : ℂ)‖ ≤
      (n * r ^ n) * (Real.exp c * Real.exp (-c * x)) := by
    intro n
    refine (norm_termo_le hK n x).trans ?_
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      simp
    · have e1 : Real.exp (-(c * x)) ^ n = Real.exp (-(c * n * x)) := (exp_nat x n).symm
      have e2 : r ^ n * (Real.exp c * Real.exp (-c * x)) =
          Real.exp (-(c * n * 1) + c + -c * x) := by
        rw [hr_def, ← exp_nat, Real.exp_add, Real.exp_add]
        ring
      rw [e1, mul_assoc (n : ℝ) (r ^ n), e2]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      apply Real.exp_le_exp.mpr
      have h1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
      have h2 : 0 ≤ c * ((n : ℝ) - 1) * (x - 1) :=
        mul_nonneg (mul_nonneg hc.le (by linarith)) (by linarith)
      nlinarith [h2]
  have hle := tsum_of_norm_bounded (hS.mul_right (Real.exp c * Real.exp (-c * x))) hb
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc ‖teta W c x‖ ≤ S * (Real.exp c * Real.exp (-c * x)) := hle
    _ = S * Real.exp c * Real.exp (-c * x) := by ring

theorem teta_isBigO_rpow (hc : 0 < c) (hK : CotaCoef W) (r : ℝ) :
    (fun x => teta W c x - 0) =O[atTop] (· ^ r) := by
  simpa using (teta_isBigO_exp hc hK).trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

end Teta

/-! ### O FE-pair de peso 2 -/

section Par

variable {W : WeierstrassCurve ℚ} {c : ℝ} {ε : ℂ}

/-- `(g, g)` é um FE-pair de peso 2 com sinal `ε`. -/
def par (hc : 0 < c) (hK : CotaCoef W) (hε : ε ≠ 0) (hM : PonteModular W c ε) :
    WeakFEPair ℂ where
  f := teta W c
  g := teta W c
  k := 2
  ε := ε
  f₀ := 0
  g₀ := 0
  hf_int := (continuousOn_teta hc hK).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_teta hc hK).locallyIntegrableOn measurableSet_Ioi
  hk := two_pos
  hε := hε
  h_feq x hx := by
    rw [hM x hx, Real.rpow_two, ofReal_pow, smul_eq_mul]
  hf_top r := teta_isBigO_rpow hc hK r
  hg_top r := teta_isBigO_rpow hc hK r

variable (hc : 0 < c) (hK : CotaCoef W) (hε : ε ≠ 0) (hM : PonteModular W c ε)

theorem par_forte : IsStrongFEPair (par hc hK hε hM) := ⟨rfl, rfl⟩

/-- `Λ₀ = M[g]` (o par é forte). -/
theorem Λ₀_eq_mellin (s : ℂ) : (par hc hK hε hM).Λ₀ s = mellin (teta W c) s := by
  rw [WeakFEPair.Λ₀_eq, (par_forte hc hK hε hM).Λ_eq]
  simp [par]

/-- **Dobra de Mellin em `s = 1`**: `Λ(1) = (1 + ε) ∫₁^∞ g`. -/
theorem Λ₀_um : (par hc hK hε hM).Λ₀ 1 = (1 + ε) * ∫ x in Ioi (1 : ℝ), teta W c x := by
  set P := par hc hK hε hM
  rw [Λ₀_eq_caudas]
  have hk : (P.k : ℂ) - 1 = 1 := by
    show ((2 : ℝ) : ℂ) - 1 = 1
    norm_num
  have hcs : cauda P.symm = cauda P := rfl
  have hm : mellin (cauda P) 1 = ∫ x in Ioi (1 : ℝ), teta W c x := by
    rw [mellin]
    simp only [sub_self, cpow_zero, one_smul]
    rw [cauda, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
    simp [P, par]
  have hεP : P.ε = ε := rfl
  rw [hk, hcs, hm, hεP]
  ring

end Par

/-! ### A série rápida para `∫₁^∞ g` -/

section Serie

variable {W : WeierstrassCurve ℚ} {c : ℝ}

theorem integral_exp_Ioi_um {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (1 : ℝ), Real.exp (-(a * x)) = Real.exp (-a) / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) 1
  simp only [neg_mul, mul_one] at h
  rw [h, neg_div_neg_eq]

theorem integral_termo (hc : 0 < c) (n : ℕ) :
    ∫ x in Ioi (1 : ℝ), coef W n * (Real.exp (-(c * n * x)) : ℂ) =
      coef W n * ((Real.exp (-(c * n)) / (c * n) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [coef_zero]
  · have hcn : 0 < c * n := mul_pos hc (Nat.cast_pos.mpr hn)
    rw [integral_const_mul, integral_complex_ofReal, integral_exp_Ioi_um hcn]

theorem integrable_termo (hc : 0 < c) (n : ℕ) :
    Integrable (fun x : ℝ => coef W n * (Real.exp (-(c * n * x)) : ℂ))
      (volume.restrict (Ioi 1)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [coef_zero]
  · have hcn : 0 < c * n := mul_pos hc (Nat.cast_pos.mpr hn)
    have hi : IntegrableOn (fun x : ℝ => Real.exp ((-(c * n)) * x)) (Ioi 1) :=
      integrableOn_exp_mul_Ioi (by linarith) 1
    have e : (fun x : ℝ => coef W n * (Real.exp (-(c * n * x)) : ℂ)) =
        fun x => coef W n * ((Real.exp ((-(c * n)) * x) : ℝ) : ℂ) := by
      funext x
      ring_nf
    rw [e]
    exact hi.ofReal.const_mul _

theorem integral_norm_termo (hc : 0 < c) (n : ℕ) :
    ∫ x in Ioi (1 : ℝ), ‖coef W n * (Real.exp (-(c * n * x)) : ℂ)‖ =
      ‖coef W n‖ * (Real.exp (-(c * n)) / (c * n)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [coef_zero]
  · have hcn : 0 < c * n := mul_pos hc (Nat.cast_pos.mpr hn)
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [integral_const_mul, integral_exp_Ioi_um hcn]

theorem cota_integral_termo (hc : 0 < c) (hK : CotaCoef W) (n : ℕ) :
    ‖coef W n‖ * (Real.exp (-(c * n)) / (c * n)) ≤ (1 / c) * Real.exp (-c) ^ n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [coef_zero]
    positivity
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have he : Real.exp (-(c * n)) = Real.exp (-c) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    calc ‖coef W n‖ * (Real.exp (-(c * n)) / (c * n))
        ≤ n * (Real.exp (-(c * n)) / (c * n)) :=
          mul_le_mul_of_nonneg_right (hK n) (by positivity)
      _ = (1 / c) * Real.exp (-c) ^ n := by
          rw [he]
          field_simp

theorem summable_serie (hc : 0 < c) (hK : CotaCoef W) :
    Summable fun n : ℕ => (1 / c) * Real.exp (-c) ^ n :=
  (summable_geometric_of_lt_one (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by linarith))).mul_left _

/-- **`∫₁^∞ g = Σₙ aₙ e^{−cn}/(cn)`.** -/
theorem integral_teta (hc : 0 < c) (hK : CotaCoef W) :
    ∫ x in Ioi (1 : ℝ), teta W c x =
      ∑' n : ℕ, coef W n * ((Real.exp (-(c * n)) / (c * n) : ℝ) : ℂ) := by
  have hsum : Summable fun n : ℕ =>
      ∫ x in Ioi (1 : ℝ), ‖coef W n * (Real.exp (-(c * n * x)) : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (summable_serie hc hK)
    rw [integral_norm_termo hc n]
    exact cota_integral_termo hc hK n
  have h := integral_tsum_of_summable_integral_norm (integrable_termo (W := W) hc) hsum
  simp_rw [integral_termo hc] at h
  rw [h]
  rfl

end Serie

/-! ### `Λ(s) = Γ(s) c^{−s} L(E, s)` em `Re s > 2` -/

section Mellin

variable {W : WeierstrassCurve ℚ} {c : ℝ}

theorem integral_mellin_termo (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (coef W n * (Real.exp (-(c * n * t)) : ℂ)) =
      Gamma s * ((c : ℂ) ^ s)⁻¹ * LSeries.term (coef W) s n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [coef_zero]
  · have hcn : 0 < c * n := mul_pos hc (Nat.cast_pos.mpr hn)
    have e : (fun t : ℝ => (t : ℂ) ^ (s - 1) * (coef W n * (Real.exp (-(c * n * t)) : ℂ))) =
        fun t : ℝ => coef W n * ((t : ℂ) ^ (s - 1) * cexp (-(((c * n : ℝ) : ℂ) * (t : ℂ)))) := by
      funext t
      rw [ofReal_exp]
      push_cast
      ring
    rw [e, integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hs hcn,
      LSeries.term_def₀ coef_zero]
    have hc0 : (0 : ℝ) ≤ c := hc.le
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [one_div, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hcn.le]; exact Real.pi_ne_zero.symm),
      ofReal_mul, mul_cpow_ofReal_nonneg hc0 hn0, cpow_neg, ofReal_natCast, mul_inv]
    ring

theorem integrable_mellin_termo (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * (coef W n * (Real.exp (-(c * n * t)) : ℂ)))
      (volume.restrict (Ioi 0)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [coef_zero]
  · have hcn : 0 < c * n := mul_pos hc (Nat.cast_pos.mpr hn)
    have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := c * n)
      (by linarith) one_pos hcn
    refine Integrable.mono' (hg.const_mul ‖coef W n‖) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (s - 1)) t :=
        (continuousAt_ofReal_cpow_const _ _ (Or.inr ht'.ne'))
      exact h1.mul (continuousAt_const.mul (continuous_ofReal.comp
        (Real.continuous_exp.comp (by fun_prop))).continuousAt)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_one, sub_re, one_re]
      have : Real.exp (-(c * n * t)) = Real.exp (-(c * n) * t) := by ring_nf
      rw [this]
      ring_nf
      exact le_refl _

theorem integral_norm_mellin_termo (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * (coef W n * (Real.exp (-(c * n * t)) : ℂ))‖ =
      ‖coef W n‖ * ((1 / (c * n)) ^ s.re * Real.Gamma s.re) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [coef_zero]
  · have hcn : 0 < c * n := mul_pos hc (Nat.cast_pos.mpr hn)
    have e : ∀ t ∈ Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s - 1) * (coef W n * (Real.exp (-(c * n * t)) : ℂ))‖ =
          ‖coef W n‖ * (t ^ (s.re - 1) * Real.exp (-((c * n) * t))) := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sub_re, one_re]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs hcn]

/-- **`M[g](s) = Γ(s) c^{−s} L(E, s)` para `Re s > 2`.** -/
theorem mellin_teta (hc : 0 < c) (hK : CotaCoef W) {s : ℂ} (hs : 2 < s.re) :
    mellin (teta W c) s = Gamma s * ((c : ℂ) ^ s)⁻¹ * LSeries (coef W) s := by
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable fun n : ℕ => ∫ t in Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) * (coef W n * (Real.exp (-(c * n * t)) : ℂ))‖ := by
    simp_rw [integral_norm_mellin_termo hc hs0]
    have hp : Summable fun n : ℕ => (n : ℝ) ^ (1 - s.re) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hp.mul_left ((1 / c) ^ s.re * Real.Gamma s.re))
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      simp [coef_zero]
      positivity
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hG : 0 < Real.Gamma s.re := Real.Gamma_pos_of_pos hs0
      calc ‖coef W n‖ * ((1 / (c * n)) ^ s.re * Real.Gamma s.re)
          ≤ n * ((1 / (c * n)) ^ s.re * Real.Gamma s.re) :=
            mul_le_mul_of_nonneg_right (hK n) (by positivity)
        _ = (1 / c) ^ s.re * Real.Gamma s.re * (n : ℝ) ^ (1 - s.re) := by
            rw [show (1 : ℝ) / (c * n) = (1 / c) * (n : ℝ)⁻¹ by field_simp,
              Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hn'.le,
              Real.rpow_sub hn', Real.rpow_one]
            field_simp
  have h := integral_tsum_of_summable_integral_norm
    (integrable_mellin_termo (W := W) hc hs0) hsum
  simp_rw [integral_mellin_termo hc hs0] at h
  rw [tsum_mul_left] at h
  rw [mellin, LSeries, h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, teta, ← tsum_mul_left]

end Mellin

/-! ### A continuação `Lc = c^s Λ(s) / Γ(s)` -/

section Continuacao

variable {W : WeierstrassCurve ℚ} {c : ℝ} {ε : ℂ}
variable (hc : 0 < c) (hK : CotaCoef W) (hε : ε ≠ 0) (hM : PonteModular W c ε)

/-- `L(E, s)` reconstruída do FE-pair: `Lc(s) = c^s Λ(s) / Γ(s)` (inteira). -/
def Lc (s : ℂ) : ℂ := (c : ℂ) ^ s * (par hc hK hε hM).Λ₀ s * (Gamma s)⁻¹

theorem differentiable_Lc : Differentiable ℂ (Lc hc hK hε hM) := by
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have h1 : Differentiable ℂ fun s : ℂ => (c : ℂ) ^ s :=
    differentiable_id.const_cpow (Or.inl hc0)
  have h2 : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ := by
    simpa [one_div] using differentiable_one_div_Gamma
  exact (h1.mul (par hc hK hε hM).differentiable_Λ₀).mul h2

/-- `Lc = L(E, s)` em `Re s > 2`. -/
theorem Lc_eq {s : ℂ} (hs : 2 < s.re) : Lc hc hK hε hM s = W.LSeries s := by
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hcs : (c : ℂ) ^ s ≠ 0 := by
    rw [cpow_def_of_ne_zero hc0]
    exact Complex.exp_ne_zero _
  rw [Lc, Λ₀_eq_mellin, mellin_teta hc hK hs, lseries_coef]
  field_simp

/-- **Toda continuação de `L(E, s)` é `Lc`.** -/
theorem continuacao_eq {G : ℂ → ℂ} (hG : Continuacao W G) : G = Lc hc hK hε hM := by
  have hGa : AnalyticOnNhd ℂ G univ := fun z _ => hG.1.analyticAt z
  have hLa : AnalyticOnNhd ℂ (Lc hc hK hε hM) univ :=
    fun z _ => (differentiable_Lc hc hK hε hM).analyticAt z
  refine hGa.eq_of_eventuallyEq hLa (z₀ := 3) ?_
  have hopen : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : (3 : ℂ) ∈ {s : ℂ | 2 < s.re} := by norm_num
  filter_upwards [hopen.mem_nhds hmem] with s hs
  have hs' : 2 < s.re := hs
  rw [hG.2 s (by linarith), Lc_eq hc hK hε hM hs']

/-- **`L(E, 1) = c (1 + ε) Σₙ aₙ e^{−cn}/(cn)`.** -/
theorem Lc_um : Lc hc hK hε hM 1 =
    (c : ℂ) * (1 + ε) * ∑' n : ℕ, coef W n * ((Real.exp (-(c * n)) / (c * n) : ℝ) : ℂ) := by
  rw [Lc, Λ₀_um, integral_teta hc hK, cpow_one, Complex.Gamma_one, inv_one, mul_one]
  ring

end Continuacao

/-! ### Positividade da série -/

section Positividade

variable {W : WeierstrassCurve ℚ} {c : ℝ}

/-- **Se `e^{−c} < 1/2`, a série tem parte real positiva** (só usa `a₁ = 1` e `|aₙ| ≤ n`). -/
theorem serie_re_pos (hc : 0 < c) (hK : CotaCoef W) (hq : Real.exp (-c) < 1 / 2) :
    0 < (∑' n : ℕ, coef W n * ((Real.exp (-(c * n)) / (c * n) : ℝ) : ℂ)).re := by
  set q := Real.exp (-c) with hq_def
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by linarith
  set b : ℕ → ℂ := fun n => coef W n * ((Real.exp (-(c * n)) / (c * n) : ℝ) : ℂ) with hb
  have hnb : ∀ n, ‖b n‖ ≤ (1 / c) * q ^ n := by
    intro n
    simp only [hb, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact cota_integral_termo hc hK n
  have hsb : Summable b := Summable.of_norm_bounded (summable_serie hc hK) hnb
  have hre : HasSum (fun n => (b n).re) (∑' n, b n).re := Complex.hasSum_re hsb.hasSum
  set ℓ : ℕ → ℝ := fun n => (if n = 1 then q / c else 0) -
    (q ^ n / c - (if n = 0 then 1 / c else 0) - (if n = 1 then q / c else 0)) with hℓ
  have hℓsum : HasSum ℓ (q / c - ((1 - q)⁻¹ / c - 1 / c - q / c)) := by
    refine (hasSum_ite_eq 1 (q / c)).sub ?_
    exact (((hasSum_geometric_of_lt_one hq0.le hq1).div_const c).sub
      (hasSum_ite_eq 0 (1 / c))).sub (hasSum_ite_eq 1 (q / c))
  have hle : ∀ n, ℓ n ≤ (b n).re := by
    intro n
    have hbre : (b n).re = (coef W n).re * (Real.exp (-(c * n)) / (c * n)) := by
      simp only [hb]
      exact Complex.re_mul_ofReal _ _
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · simp [hℓ, hbre, coef_zero]
      · have h1 : (coef W 1).re = 1 := by rw [coef_um]; simp
        simp [hℓ, hbre, h1, hq_def]
    · have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have hab : |(coef W n).re| ≤ ‖coef W n‖ := Complex.abs_re_le_norm _
      have hpos : 0 ≤ Real.exp (-(c * n)) / (c * n) := by positivity
      have hlow : -(‖coef W n‖ * (Real.exp (-(c * n)) / (c * n))) ≤ (b n).re := by
        rw [hbre, ← neg_mul]
        exact mul_le_mul_of_nonneg_right (neg_le_of_abs_le hab) hpos
      have hc2 := cota_integral_termo hc hK n
      simp only [hℓ, hn0, hn1, ite_false, sub_zero, zero_sub]
      have : q ^ n / c = (1 / c) * q ^ n := by ring
      linarith
  have hval := hasSum_le hle hℓsum hre
  have hpos : 0 < q / c - ((1 - q)⁻¹ / c - 1 / c - q / c) := by
    have h1q : 0 < 1 - q := by linarith
    have key : (1 - q)⁻¹ < 2 * q + 1 := by
      rw [inv_eq_one_div, div_lt_iff₀ h1q]
      nlinarith
    have e : q / c - ((1 - q)⁻¹ / c - 1 / c - q / c) = (2 * q + 1 - (1 - q)⁻¹) / c := by ring
    rw [e]
    exact div_pos (by linarith) hc
  linarith

end Positividade

/-! ### Não anulação em `s = 1` e BSD (posto) para `y² = x³ − x` -/

section Final

variable {W : WeierstrassCurve ℚ} {c : ℝ}

/-- **Critério de não anulação**: sinal `+1`, `|aₙ| ≤ n` e `e^{−c} < 1/2` (isto é,
`N < (2π / log 2)²`) ⇒ toda continuação de `L(E, s)` é não nula em `s = 1`. -/
theorem L1_ne_zero (hc : 0 < c) (hK : CotaCoef W) (hq : Real.exp (-c) < 1 / 2)
    (hM : PonteModular W c 1) {G : ℂ → ℂ} (hG : Continuacao W G) : G 1 ≠ 0 := by
  rw [continuacao_eq hc hK one_ne_zero hM hG, Lc_um]
  intro h0
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have h2 : (1 : ℂ) + 1 ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hc0 h'
    · exact h2 h'
  · have := serie_re_pos hc hK hq
    rw [h, zero_re] at this
    exact lt_irrefl 0 this

/-- `c = 2π/√32` (condutor 32). -/
def c32 : ℝ := 2 * π / Real.sqrt 32

theorem c32_pos : 0 < c32 := div_pos (by positivity) (Real.sqrt_pos.mpr (by norm_num))

theorem um_lt_c32 : 1 < c32 := by
  rw [c32, one_lt_div (Real.sqrt_pos.mpr (by norm_num)), Real.sqrt_lt' (by positivity)]
  nlinarith [Real.pi_gt_three]

theorem exp_neg_c32 : Real.exp (-c32) < 1 / 2 := by
  have h1 : Real.exp (-c32) < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith [um_lt_c32])
  have h2 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num at this ⊢
    linarith
  linarith

/-- **BSD (parte do posto) para `y² = x³ − x`, módulo as pontes P1 e P2**: toda continuação
`G` de `L(E, s)` tem `G(1) ≠ 0`, e a ordem de `G` em `s = 1` é o posto de Mordell–Weil (= 0). -/
theorem bsd_posto_curva32 (hM : PonteModular ATK.CongruentCurve.E c32 1)
    (hK : CotaCoef ATK.CongruentCurve.E) {G : ℂ → ℂ}
    (hG : Continuacao ATK.CongruentCurve.E G) :
    G 1 ≠ 0 ∧ analyticOrderAt G 1 = postoMW ATK.CongruentCurve.E := by
  have h1 := L1_ne_zero c32_pos hK exp_neg_c32 hM hG
  refine ⟨h1, ?_⟩
  rw [posto_curva32]
  exact analyticOrderAt_eq_zero.mpr (Or.inr h1)

/-- **O enunciado do Clay para `y² = x³ − x`**, dadas as pontes P1, P2 e a existência da
continuação (modularidade, `ATK.LigacaoBSD.Modularidade`). -/
theorem clay_curva32_de_pontes (hM : PonteModular ATK.CongruentCurve.E c32 1)
    (hK : CotaCoef ATK.CongruentCurve.E) (hex : ∃ G, Continuacao ATK.CongruentCurve.E G) :
    ∃ G : ℂ → ℂ, Continuacao ATK.CongruentCurve.E G ∧
      analyticOrderAt G 1 = postoMW ATK.CongruentCurve.E := by
  obtain ⟨G, hG⟩ := hex
  exact ⟨G, hG, (bsd_posto_curva32 hM hK hG).2⟩

end Final

end ATK.AtaqueBSD

#print axioms ATK.AtaqueBSD.coef_zero
#print axioms ATK.AtaqueBSD.exp_nat
#print axioms ATK.AtaqueBSD.norm_termo_le
#print axioms ATK.AtaqueBSD.summable_maj
#print axioms ATK.AtaqueBSD.exp_neg_lt_one
#print axioms ATK.AtaqueBSD.summable_teta
#print axioms ATK.AtaqueBSD.continuousOn_teta
#print axioms ATK.AtaqueBSD.teta_isBigO_exp
#print axioms ATK.AtaqueBSD.teta_isBigO_rpow
#print axioms ATK.AtaqueBSD.par_forte
#print axioms ATK.AtaqueBSD.Λ₀_eq_mellin
#print axioms ATK.AtaqueBSD.Λ₀_um
#print axioms ATK.AtaqueBSD.integral_exp_Ioi_um
#print axioms ATK.AtaqueBSD.integral_termo
#print axioms ATK.AtaqueBSD.integrable_termo
#print axioms ATK.AtaqueBSD.integral_norm_termo
#print axioms ATK.AtaqueBSD.cota_integral_termo
#print axioms ATK.AtaqueBSD.summable_serie
#print axioms ATK.AtaqueBSD.integral_teta
#print axioms ATK.AtaqueBSD.integral_mellin_termo
#print axioms ATK.AtaqueBSD.integrable_mellin_termo
#print axioms ATK.AtaqueBSD.integral_norm_mellin_termo
#print axioms ATK.AtaqueBSD.mellin_teta
#print axioms ATK.AtaqueBSD.differentiable_Lc
#print axioms ATK.AtaqueBSD.Lc_eq
#print axioms ATK.AtaqueBSD.continuacao_eq
#print axioms ATK.AtaqueBSD.Lc_um
#print axioms ATK.AtaqueBSD.serie_re_pos
#print axioms ATK.AtaqueBSD.L1_ne_zero
#print axioms ATK.AtaqueBSD.c32_pos
#print axioms ATK.AtaqueBSD.um_lt_c32
#print axioms ATK.AtaqueBSD.exp_neg_c32
#print axioms ATK.AtaqueBSD.bsd_posto_curva32
#print axioms ATK.AtaqueBSD.clay_curva32_de_pontes
