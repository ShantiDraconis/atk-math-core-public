import ATK.ZeroClasses.PsiRH
import ATK.ZeroClasses.PiLi

/-!
# RH ⟺ `θ(x) = x + O(√x log³ x)` ⟺ `π(x) = Li(x) + O(√x log² x)` (rodada 65)

Com a rodada 64 (`ψ(x) = x + O(√x log³ x)` sob RH) e as identidades de Chebyshev da Mathlib:

* **`theta_RH`**: sob RH, `|θ(x) − x| ≤ K √x log³ x` para `x ≥ 2` (`ψ − θ ≤ 2√x log x`, `psi_sub_theta_le`, e
  `ψ(x) ≤ x²` em `[2, 100]`);
* **`pi_RH`**: sob RH, `|π(x) − Li(x)| ≤ K √x log² x` para `x ≥ 2`, pela fórmula de partes
  `π(x) − Li(x) = (θ(x) − x)/log x + ∫_2^x (θ(t) − t)/(t log² t) dt + 2/log 2` (`pi_sub_Li`) e
  `∫_2^x log t · t^{−1/2} dt ≤ 2√x log x`;
* as recíprocas pela rodada 60 (`ATK.ZeroClasses.PiLi.rh_iff_theta`, `rh_iff_pi`), com
  `√x log^k x ≤ (k/ε)^k x^{½+ε}` (`sqrt_log_pow_le`): **`rh_iff_thetaLog3`** e **`rh_iff_piLog2`**.

Classificação (rodada 65): **reformulação** — a forma quantitativa de von Koch para `θ` e `π` (a clássica tem `log x`
para `π`, pela fórmula explícita; aqui `log² x`). RH continua OPEN_MATH.
-/

open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

namespace ATK.ZeroClasses.PiLiRH

open ATK.ZeroClasses.PiLi (Li Li_partes log_pos_of_ge integral_rpow_le ErroTheta ErroPi rh_iff_theta
  rh_iff_pi)

/-! ## 1. `√x log^k x ≤ (k/ε)^k x^{½+ε}` -/

theorem sqrt_log_pow_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
    √x * Real.log x ^ k ≤ ((k : ℝ) / ε) ^ k * x ^ (1 / 2 + ε) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl : Real.log x ≤ ((k : ℝ) / ε) * x ^ (ε / k) := by
    have := Real.log_le_rpow_div hx0.le (by positivity : 0 < ε / k)
    calc Real.log x ≤ x ^ (ε / k) / (ε / k) := this
      _ = ((k : ℝ) / ε) * x ^ (ε / k) := by field_simp
  have hlk : Real.log x ^ k ≤ ((k : ℝ) / ε) ^ k * x ^ ε := by
    have h1 := pow_le_pow_left₀ hl0 hl k
    have h2 : (((k : ℝ) / ε) * x ^ (ε / k)) ^ k = ((k : ℝ) / ε) ^ k * x ^ ε := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ (ε / k)) k, ← Real.rpow_mul hx0.le]
      congr 2
      field_simp
    rw [h2] at h1
    exact h1
  have hs : √x * x ^ ε = x ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  calc √x * Real.log x ^ k ≤ √x * (((k : ℝ) / ε) ^ k * x ^ ε) := mul_le_mul_of_nonneg_left hlk hs0
    _ = ((k : ℝ) / ε) ^ k * (√x * x ^ ε) := by ring
    _ = ((k : ℝ) / ε) ^ k * x ^ (1 / 2 + ε) := by rw [hs]

/-! ## 2. `θ` -/

/-- **`θ(x) = x + O(√x log³ x)`**. -/
def ThetaLog3 : Prop :=
  ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ K * √x * Real.log x ^ 3

theorem log_dois_gt : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

theorem sqrt_log3_ge {x : ℝ} (hx : 2 ≤ x) : (1 / 4 : ℝ) ≤ √x * Real.log x ^ 3 := by
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h69 := log_dois_gt
  have hs : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
  have h3 : (0.69 : ℝ) ^ 3 ≤ Real.log x ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have h0 : (0 : ℝ) ≤ Real.log x ^ 3 := by positivity
  have := mul_le_mul hs h3 (by norm_num) (Real.sqrt_nonneg x)
  norm_num at this
  linarith

/-- **Sob RH, `|θ(x) − x| ≤ K √x log³ x`** para `x ≥ 2`. -/
theorem theta_RH (hRH : RiemannHypothesis) : ThetaLog3 := by
  obtain ⟨K, hK⟩ := ATK.ZeroClasses.PsiRH.psi_RH hRH
  have hK0 : 0 ≤ K := by
    have h := hK 100 le_rfl
    have hp : 0 < √(100 : ℝ) * Real.log 100 ^ 3 := by
      have : 0 < Real.log (100 : ℝ) := Real.log_pos (by norm_num)
      positivity
    by_contra hneg
    push Not at hneg
    have : K * √(100 : ℝ) * Real.log 100 ^ 3 < 0 := by
      rw [mul_assoc]
      exact mul_neg_of_neg_of_pos hneg hp
    linarith [abs_nonneg (Chebyshev.psi 100 - 100)]
  refine ⟨K + 2 + 40400, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hge := sqrt_log3_ge hx
  have hq0 : 0 ≤ √x * Real.log x ^ 3 := by linarith
  have h1 := Chebyshev.theta_le_psi x
  have hθ0 := Chebyshev.theta_nonneg x
  rcases le_or_gt 100 x with h100 | h100
  · have hψ := hK x h100
    have h2 := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ x)
    have hl1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      have := Real.exp_one_lt_d9
      linarith
    have h3 : 2 * √x * Real.log x ≤ 2 * (√x * Real.log x ^ 3) := by
      have hs := Real.sqrt_nonneg x
      have : Real.log x ≤ Real.log x ^ 3 := by
        have h' : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hl1
        calc Real.log x = Real.log x * 1 := by ring
          _ ≤ Real.log x * Real.log x ^ 2 := mul_le_mul_of_nonneg_left h' (by linarith)
          _ = Real.log x ^ 3 := by ring
      have := mul_le_mul_of_nonneg_left this hs
      linarith
    have e : K * √x * Real.log x ^ 3 = K * (√x * Real.log x ^ 3) := by ring
    rw [e] at hψ
    have hA : (2 + 40400) * (√x * Real.log x ^ 3) ≥ 0 := by positivity
    rw [abs_le] at hψ ⊢
    have e2 : (K + 2 + 40400) * √x * Real.log x ^ 3 =
        K * (√x * Real.log x ^ 3) + 2 * (√x * Real.log x ^ 3) + 40400 * (√x * Real.log x ^ 3) := by ring
    rw [e2]
    constructor <;> nlinarith
  · -- `x < 100`: `|θ − x| ≤ ψ(100) + 100 ≤ 10100`
    have hψ100 : Chebyshev.psi x ≤ 10000 := by
      have := Chebyshev.psi_mono h100.le
      have h2 := ATK.ZeroClasses.PsiRH.psi_le_sq 100
      norm_num at h2
      linarith
    have habs : |Chebyshev.theta x - x| ≤ 10100 := by
      rw [abs_le]
      constructor <;> linarith
    have : (10100 : ℝ) ≤ 40400 * (√x * Real.log x ^ 3) := by linarith
    have e2 : (K + 2 + 40400) * √x * Real.log x ^ 3 =
        (K + 2) * (√x * Real.log x ^ 3) + 40400 * (√x * Real.log x ^ 3) := by ring
    have hB : 0 ≤ (K + 2) * (√x * Real.log x ^ 3) := mul_nonneg (by linarith) hq0
    rw [e2]
    linarith

theorem erroTheta_of_log3 (h : ThetaLog3) {ε : ℝ} (hε : 0 < ε) : ErroTheta (1 / 2 + ε) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨|K| * ((3 : ℕ) / ε) ^ 3, fun x hx => ?_⟩
  have hb := sqrt_log_pow_le (by linarith : (1 : ℝ) ≤ x) hε 3 (by norm_num)
  have hq0 : 0 ≤ √x * Real.log x ^ 3 := by
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    positivity
  calc |Chebyshev.theta x - x| ≤ K * √x * Real.log x ^ 3 := hK x hx
    _ = K * (√x * Real.log x ^ 3) := by ring
    _ ≤ |K| * (√x * Real.log x ^ 3) := mul_le_mul_of_nonneg_right (le_abs_self K) hq0
    _ ≤ |K| * (((3 : ℕ) / ε) ^ 3 * x ^ (1 / 2 + ε)) := mul_le_mul_of_nonneg_left hb (abs_nonneg K)
    _ = |K| * ((3 : ℕ) / ε) ^ 3 * x ^ (1 / 2 + ε) := by ring

/-- **RH ⟺ `θ(x) = x + O(√x log³ x)`.** -/
theorem rh_iff_thetaLog3 : RiemannHypothesis ↔ ThetaLog3 :=
  ⟨theta_RH, fun h => rh_iff_theta.mpr fun _ hε => erroTheta_of_log3 h hε⟩

/-! ## 3. `π` -/

/-- **A fórmula de partes**: `π(x) − Li(x) = (θ(x) − x)/log x + ∫_2^x (θ(t) − t)/(t log² t) dt + 2/log 2`. -/
theorem pi_sub_Li {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x = (Chebyshev.theta x - x) / Real.log x +
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) + 2 / Real.log 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx0 : 0 < Real.log x := log_pos_of_ge hx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hLi := Li_partes hx
  have hint1 : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hint2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  rw [hπ, hLi]
  have e : ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) =
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
        ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (log_pos_of_ge ht.1).ne'
    field_simp
  rw [e]
  field_simp
  ring

/-- **`π(x) = Li(x) + O(√x log² x)`**. -/
def PiLog2 : Prop :=
  ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * √x * Real.log x ^ 2

theorem pi_of_thetaLog3 (h : ThetaLog3) : PiLog2 := by
  obtain ⟨K₀, hK₀⟩ := h
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ K * √x * Real.log x ^ 3 := by
    intro x hx
    have hq0 : 0 ≤ √x * Real.log x ^ 3 := by
      have : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      positivity
    calc |Chebyshev.theta x - x| ≤ K₀ * √x * Real.log x ^ 3 := hK₀ x hx
      _ = K₀ * (√x * Real.log x ^ 3) := by ring
      _ ≤ K * (√x * Real.log x ^ 3) := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0
      _ = K * √x * Real.log x ^ 3 := by ring
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h69 := log_dois_gt
  refine ⟨4 * K + 7, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 < Real.log x := by linarith
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
  set L := Real.log x with hL
  -- (1) o termo de fronteira
  have hb1 : |(Chebyshev.theta x - x) / L| ≤ K * √x * L ^ 2 := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    calc |Chebyshev.theta x - x| ≤ K * √x * L ^ 3 := hK x hx
      _ = K * √x * L ^ 2 * L := by ring
  -- (2) a integral
  have hb2 : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤ 2 * K * √x * L := by
    have hle : ∀ t ∈ Ioc (2 : ℝ) x, ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤
        K * L * t ^ ((1 / 2 : ℝ) - 1) := by
      intro t ht
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := by linarith
      have hlt0 : 0 < Real.log t := log_pos_of_ge ht2
      have hltx : Real.log t ≤ L := Real.log_le_log ht0 ht.2
      have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (pow_pos hlt0 2)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
      have hst' : t ^ ((1 / 2 : ℝ) - 1) * t = √t := by
        rw [← Real.rpow_add_one ht0.ne', Real.sqrt_eq_rpow]
        norm_num
      have hq : 0 ≤ K * √t * Real.log t ^ 2 := by positivity
      calc |Chebyshev.theta t - t| ≤ K * √t * Real.log t ^ 3 := hK t ht2
        _ = (K * √t * Real.log t ^ 2) * Real.log t := by ring
        _ ≤ (K * √t * Real.log t ^ 2) * L := mul_le_mul_of_nonneg_left hltx hq
        _ = K * L * (t ^ ((1 / 2 : ℝ) - 1) * t) * Real.log t ^ 2 := by rw [hst']; ring
        _ = K * L * t ^ ((1 / 2 : ℝ) - 1) * (t * Real.log t ^ 2) := by ring
    have hn := intervalIntegral.norm_integral_le_of_norm_le hx (Eventually.of_forall hle)
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1 / 2 - 1)).const_mul _)
    rw [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hi := integral_rpow_le hx (by norm_num : (0 : ℝ) < 1 / 2)
    have hs : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
    rw [hs] at hi
    calc K * L * ∫ t in (2 : ℝ)..x, t ^ ((1 / 2 : ℝ) - 1) ≤ K * L * (√x / (1 / 2)) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
      _ = 2 * K * √x * L := by ring
  -- (3) a constante
  have hb3 : |2 / Real.log 2| ≤ 3 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ hl2]
    linarith
  -- a soma
  have hsum : |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * √x * L ^ 2 + 2 * K * √x * L + 3 := by
    rw [pi_sub_Li hx]
    have a1 := abs_add_le ((Chebyshev.theta x - x) / L +
      ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) (2 / Real.log 2)
    have a2 := abs_add_le ((Chebyshev.theta x - x) / L)
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
    linarith
  -- `L ≤ L²/0,69` e `1 ≤ √x L²/0,47`
  have hLL : L ≤ L ^ 2 / 0.69 := by
    rw [le_div_iff₀ (by norm_num)]
    have : 0.69 ≤ L := by linarith
    nlinarith
  have hsL : (0.47 : ℝ) ≤ √x * L ^ 2 := by
    have h1 : (0.69 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have := mul_le_mul hs1 h1 (by norm_num) (Real.sqrt_nonneg x)
    norm_num at this
    linarith
  have hq : 0 ≤ K * √x := by positivity
  have h2 : 2 * K * √x * L ≤ 3 * K * √x * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLL hq
    have e : K * √x * (L ^ 2 / 0.69) = (1 / 0.69) * (K * √x * L ^ 2) := by ring
    rw [e] at this
    have hpos : 0 ≤ K * √x * L ^ 2 := by positivity
    nlinarith
  have h3 : (3 : ℝ) ≤ 7 * (√x * L ^ 2) := by linarith
  calc |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * √x * L ^ 2 + 2 * K * √x * L + 3 := hsum
    _ ≤ K * √x * L ^ 2 + 3 * K * √x * L ^ 2 + 7 * (√x * L ^ 2) := by linarith
    _ = (4 * K + 7) * √x * L ^ 2 := by ring

/-- **Sob RH, `|π(x) − Li(x)| ≤ K √x log² x`** para `x ≥ 2`. -/
theorem pi_RH (hRH : RiemannHypothesis) : PiLog2 := pi_of_thetaLog3 (theta_RH hRH)

theorem erroPi_of_log2 (h : PiLog2) {ε : ℝ} (hε : 0 < ε) : ErroPi (1 / 2 + ε) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨|K| * ((2 : ℕ) / ε) ^ 2, fun x hx => ?_⟩
  have hb := sqrt_log_pow_le (by linarith : (1 : ℝ) ≤ x) hε 2 (by norm_num)
  have hq0 : 0 ≤ √x * Real.log x ^ 2 := by positivity
  calc |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * √x * Real.log x ^ 2 := hK x hx
    _ = K * (√x * Real.log x ^ 2) := by ring
    _ ≤ |K| * (√x * Real.log x ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self K) hq0
    _ ≤ |K| * (((2 : ℕ) / ε) ^ 2 * x ^ (1 / 2 + ε)) := mul_le_mul_of_nonneg_left hb (abs_nonneg K)
    _ = |K| * ((2 : ℕ) / ε) ^ 2 * x ^ (1 / 2 + ε) := by ring

/-- **RH ⟺ `π(x) = Li(x) + O(√x log² x)`.** -/
theorem rh_iff_piLog2 : RiemannHypothesis ↔ PiLog2 :=
  ⟨pi_RH, fun h => rh_iff_pi.mpr fun _ hε => erroPi_of_log2 h hε⟩

end ATK.ZeroClasses.PiLiRH

#print axioms ATK.ZeroClasses.PiLiRH.sqrt_log_pow_le
#print axioms ATK.ZeroClasses.PiLiRH.log_dois_gt
#print axioms ATK.ZeroClasses.PiLiRH.sqrt_log3_ge
#print axioms ATK.ZeroClasses.PiLiRH.theta_RH
#print axioms ATK.ZeroClasses.PiLiRH.erroTheta_of_log3
#print axioms ATK.ZeroClasses.PiLiRH.rh_iff_thetaLog3
#print axioms ATK.ZeroClasses.PiLiRH.pi_sub_Li
#print axioms ATK.ZeroClasses.PiLiRH.pi_of_thetaLog3
#print axioms ATK.ZeroClasses.PiLiRH.pi_RH
#print axioms ATK.ZeroClasses.PiLiRH.erroPi_of_log2
#print axioms ATK.ZeroClasses.PiLiRH.rh_iff_piLog2
