import ATK.IndeterminacyStates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ATK — Yang–Mills: o gap de massa num modelo de rede exatamente solúvel (e por que o contínuo é a lacuna)

Modelo: cadeia de spins `±1` com peso `e^{β σᵢ σᵢ₊₁}` por elo (cadeia de Ising 1D; é também a
redução, por fixação de calibre, da teoria de calibre `ℤ₂` na rede 2D, em que o laço de Wilson de área
`A` vale `tanh(β)^A`). A matriz de transferência `T = [[e^β, e^{−β}], [e^{−β}, e^β]]` tem autovalores
`C = e^β + e^{−β}` e `S = e^β − e^{−β}`.

* `W_formula`: `Tⁿ(a, b) = (Cⁿ + σ_a σ_b Sⁿ)/2` (provado por indução);
* `correl_eq`, `razao_eq_tanh`: a correlação a distância `n` é `(S/C)ⁿ = tanh(β)ⁿ`;
* `massa_pos`, `correl_exp`: para todo `β > 0`, **gap de massa** `m(β) = log(C/S) > 0` e
  correlação `= e^{−m n}`; `correl_estado_zero`: decaimento (estado `zero`);
* `massa_tende_zero`: `m(β) → 0` quando `β → ∞` (acoplamento fraco).

O último item é a lacuna de Yang–Mills em miniatura: na rede o gap existe para cada `β`, mas o
**limite contínuo** exige `m(β)/a(β)` com limite positivo quando o espaçamento `a → 0`. Em 4D, para
grupo não abeliano, isso é a obrigação O8 (e o próprio modelo contínuo, L5, não existe na Mathlib).
-/

open Real Filter Topology

namespace ATK.YMToy

open ATK.IndeterminacyStates

/-- Spin `±1`. -/
def σ (b : Bool) : ℝ := if b then 1 else -1

/-- Peso de Boltzmann de um elo. -/
noncomputable def w (β : ℝ) (a b : Bool) : ℝ := rexp (β * σ a * σ b)

/-- Potências da matriz de transferência. -/
noncomputable def W (β : ℝ) : ℕ → Bool → Bool → ℝ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, b => W β n a true * w β true b + W β n a false * w β false b

/-- Autovalores: `C = 2 cosh β`, `S = 2 sinh β`. -/
noncomputable def C (β : ℝ) : ℝ := rexp β + rexp (-β)
noncomputable def S (β : ℝ) : ℝ := rexp β - rexp (-β)

theorem exp_eq (β : ℝ) : rexp β = (C β + S β) / 2 := by unfold C S; ring

theorem exp_neg_eq (β : ℝ) : rexp (-β) = (C β - S β) / 2 := by unfold C S; ring

/-- Os autovetores `(1, 1)` e `(1, −1)` da matriz de transferência. -/
theorem autovetores (β : ℝ) :
    rexp β + rexp (-β) = C β ∧ rexp β - rexp (-β) = S β := ⟨rfl, rfl⟩

theorem W_formula (β : ℝ) (n : ℕ) (a b : Bool) :
    W β n a b = (C β ^ n + σ a * σ b * S β ^ n) / 2 := by
  induction n generalizing b with
  | zero => cases a <;> cases b <;> norm_num [W, σ]
  | succ n ih =>
    simp only [W, ih, w]
    cases a <;> cases b <;> simp only [σ, ↓reduceIte, Bool.false_eq_true, mul_one, mul_neg,
      neg_neg, neg_mul, one_mul] <;> simp only [exp_neg_eq β, exp_eq β] <;> ring

/-- Função de partição e correlação spin–spin a distância `n`. -/
noncomputable def Z (β : ℝ) (n : ℕ) : ℝ := ∑ a : Bool, ∑ b : Bool, W β n a b
noncomputable def G (β : ℝ) (n : ℕ) : ℝ := ∑ a : Bool, ∑ b : Bool, σ a * σ b * W β n a b

theorem Z_formula (β : ℝ) (n : ℕ) : Z β n = 2 * C β ^ n := by
  simp only [Z, Fintype.sum_bool, W_formula, σ, ↓reduceIte, Bool.false_eq_true]; ring

theorem G_formula (β : ℝ) (n : ℕ) : G β n = 2 * S β ^ n := by
  simp only [G, Fintype.sum_bool, W_formula, σ, ↓reduceIte, Bool.false_eq_true]; ring

theorem C_pos (β : ℝ) : 0 < C β := by unfold C; positivity

theorem S_lt_C (β : ℝ) : S β < C β := by unfold S C; have := exp_pos (-β); linarith

theorem S_pos {β : ℝ} (hβ : 0 < β) : 0 < S β := by
  unfold S; have := Real.exp_lt_exp.mpr (show -β < β by linarith); linarith

/-- Correlação normalizada. -/
noncomputable def correl (β : ℝ) (n : ℕ) : ℝ := G β n / Z β n

theorem correl_eq (β : ℝ) (n : ℕ) : correl β n = (S β / C β) ^ n := by
  have hC := (C_pos β).ne'
  rw [correl, Z_formula, G_formula, div_pow]
  field_simp

/-- `S/C = tanh β`. -/
theorem razao_eq_tanh (β : ℝ) : S β / C β = Real.tanh β := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  unfold S C
  have h := (C_pos β).ne'
  unfold C at h
  field_simp

/-- O gap de massa da rede. -/
noncomputable def massa (β : ℝ) : ℝ := Real.log (C β / S β)

theorem massa_pos {β : ℝ} (hβ : 0 < β) : 0 < massa β :=
  Real.log_pos ((one_lt_div (S_pos hβ)).mpr (S_lt_C β))

/-- **Decaimento exponencial**: `correlação(n) = e^{−m(β) n}`. -/
theorem correl_exp {β : ℝ} (hβ : 0 < β) (n : ℕ) : correl β n = rexp (-(massa β) * n) := by
  have hr : 0 < S β / C β := div_pos (S_pos hβ) (C_pos β)
  rw [correl_eq, massa, show -Real.log (C β / S β) = Real.log (S β / C β) by
    rw [← Real.log_inv, inv_div], mul_comm, Real.exp_nat_mul, Real.exp_log hr]

/-- **Estado `zero`** da correlação, para todo `β > 0`. -/
theorem correl_estado_zero {β : ℝ} (hβ : 0 < β) : Comporta atTop (correl β) Estado7.zero := by
  show Tendsto (correl β) atTop (𝓝 0)
  have hr0 : 0 ≤ S β / C β := (div_pos (S_pos hβ) (C_pos β)).le
  have hr1 : S β / C β < 1 := (div_lt_one (C_pos β)).mpr (S_lt_C β)
  rw [show correl β = fun n => (S β / C β) ^ n from funext (correl_eq β)]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

theorem razao_inversa {β : ℝ} (hβ : 0 < β) :
    C β / S β = (1 + rexp (-2 * β)) / (1 - rexp (-2 * β)) := by
  have hS := (S_pos hβ).ne'
  have h2 : rexp (-2 * β) = rexp (-β) * rexp (-β) := by rw [← Real.exp_add]; ring_nf
  have he : rexp β * rexp (-β) = 1 := by rw [← Real.exp_add]; simp
  have hden : 1 - rexp (-2 * β) ≠ 0 := by
    have : rexp (-2 * β) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  rw [div_eq_div_iff hS hden, h2]
  unfold C S
  linear_combination (-2 * rexp (-β)) * he

/-- **O gap fecha no acoplamento fraco**: `m(β) → 0` quando `β → ∞`. -/
theorem massa_tende_zero : Tendsto massa atTop (𝓝 0) := by
  have hu : Tendsto (fun β : ℝ => rexp (-2 * β)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have hq : Tendsto (fun β : ℝ => (1 + rexp (-2 * β)) / (1 - rexp (-2 * β))) atTop
      (𝓝 ((1 + 0) / (1 - 0))) :=
    (tendsto_const_nhds.add hu).div (tendsto_const_nhds.sub hu) (by norm_num)
  have hl : Tendsto (fun β : ℝ => Real.log ((1 + rexp (-2 * β)) / (1 - rexp (-2 * β)))) atTop
      (𝓝 (Real.log ((1 + 0) / (1 - 0)))) :=
    ((Real.continuousAt_log (by norm_num)).tendsto).comp hq
  simp only [add_zero, sub_zero, div_one, Real.log_one] at hl
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  rw [massa, razao_inversa hβ]

end ATK.YMToy

#print axioms ATK.YMToy.exp_eq
#print axioms ATK.YMToy.exp_neg_eq
#print axioms ATK.YMToy.autovetores
#print axioms ATK.YMToy.W_formula
#print axioms ATK.YMToy.Z_formula
#print axioms ATK.YMToy.G_formula
#print axioms ATK.YMToy.C_pos
#print axioms ATK.YMToy.S_lt_C
#print axioms ATK.YMToy.S_pos
#print axioms ATK.YMToy.correl_eq
#print axioms ATK.YMToy.razao_eq_tanh
#print axioms ATK.YMToy.massa_pos
#print axioms ATK.YMToy.correl_exp
#print axioms ATK.YMToy.correl_estado_zero
#print axioms ATK.YMToy.razao_inversa
#print axioms ATK.YMToy.massa_tende_zero
