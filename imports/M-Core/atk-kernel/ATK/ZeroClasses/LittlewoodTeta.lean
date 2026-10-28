import ATK.ZeroClasses.LittlewoodMontagem

/-!
# Littlewood para `θ` e as trocas de sinal (rodada 93)

Corolários do teorema de Littlewood da rodada 92 (`LittlewoodMontagem.littlewood`).

* `lll_ge`: `log log log x ≥ M` para `x ≥ exp(exp(exp M))`.
* **`theta_littlewood`**: `θ(x) − x = Ω±(√x log log log x)`. O lado de baixo vem de `θ ≤ ψ`; o de cima, de
  `ψ(x) − θ(x) ≤ C√x` (`Chebyshev.psi_sub_theta_le_mul_sqrt` da Mathlib), que é `o(√x log log log x)`.
* **`psi_troca_sinal`**, **`theta_troca_sinal`**: `ψ(x) − x` e `θ(x) − x` trocam de sinal infinitas vezes.

Classificação: **consequência**. A versão para `π(x) − Li(x)` segue BUILD_PENDING (precisa de
`∫₂ˣ (θ(t) − t) dt/(t log² t) = O(√x/log² x)` sob RH). RH continua OPEN_MATH.
-/

open Filter
open scoped Real

namespace ATK.ZeroClasses.LittlewoodTeta

/-- `log log log x ≥ M` para `x ≥ exp(exp(exp M))`. -/
theorem lll_ge {M x : ℝ} (hx : Real.exp (Real.exp (Real.exp M)) ≤ x) :
    M ≤ Real.log (Real.log (Real.log x)) := by
  have h0 : 0 < Real.exp (Real.exp (Real.exp M)) := Real.exp_pos _
  have h1 : Real.exp (Real.exp M) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hx
  have h2 : Real.exp M ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos (Real.exp M)])]
    exact h1
  rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos M])]
  exact h2

/-- **Littlewood para `θ`**: `θ(x) − x = Ω±(√x log log log x)`. -/
theorem theta_littlewood : ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      Chebyshev.theta x - x ≤ -(c * √x * Real.log (Real.log (Real.log x)))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * √x * Real.log (Real.log (Real.log x)) ≤ Chebyshev.theta x - x) := by
  obtain ⟨c, hc, h1, h2⟩ := ATK.ZeroClasses.LittlewoodMontagem.littlewood
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨c / 2, by positivity, fun X => ?_, fun X => ?_⟩
  · obtain ⟨x, hx, hψ⟩ := h1 (max X (Real.exp (Real.exp (Real.exp 0))))
    refine ⟨x, le_trans (le_max_left _ _) hx, ?_⟩
    have hl := lll_ge (le_trans (le_max_right _ _) hx)
    have ht := Chebyshev.theta_le_psi x
    have hp : 0 ≤ √x * Real.log (Real.log (Real.log x)) := mul_nonneg (Real.sqrt_nonneg x) hl
    have e1 : c * √x * Real.log (Real.log (Real.log x)) = c * (√x * Real.log (Real.log (Real.log x))) := by ring
    have e2 : c / 2 * √x * Real.log (Real.log (Real.log x)) =
        c / 2 * (√x * Real.log (Real.log (Real.log x))) := by ring
    rw [e1] at hψ
    rw [e2]
    nlinarith
  · set M := max 0 (2 * C / c) with hM
    obtain ⟨x, hx, hψ⟩ := h2 (max X (Real.exp (Real.exp (Real.exp M))))
    refine ⟨x, le_trans (le_max_left _ _) hx, ?_⟩
    have hl := lll_ge (le_trans (le_max_right _ _) hx)
    have hM0 : 0 ≤ M := le_max_left _ _
    have hMC : 2 * C / c ≤ M := le_max_right _ _
    have hCl : C ≤ c / 2 * Real.log (Real.log (Real.log x)) := by
      have : 2 * C / c ≤ Real.log (Real.log (Real.log x)) := hMC.trans hl
      rw [div_le_iff₀ hc] at this
      linarith
    have hs := Real.sqrt_nonneg x
    have hpt := hC x
    have h3 : C * √x ≤ c / 2 * Real.log (Real.log (Real.log x)) * √x := mul_le_mul_of_nonneg_right hCl hs
    have e : c * √x * Real.log (Real.log (Real.log x)) =
        2 * (c / 2 * Real.log (Real.log (Real.log x)) * √x) := by ring
    have e' : c / 2 * √x * Real.log (Real.log (Real.log x)) = c / 2 * Real.log (Real.log (Real.log x)) * √x := by
      ring
    rw [e']
    rw [e] at hψ
    linarith

/-- **`ψ(x) − x` troca de sinal infinitas vezes.** -/
theorem psi_troca_sinal (X : ℝ) : (∃ x : ℝ, X ≤ x ∧ Chebyshev.psi x - x < 0) ∧
    (∃ x : ℝ, X ≤ x ∧ 0 < Chebyshev.psi x - x) := by
  obtain ⟨c, hc, h1, h2⟩ := ATK.ZeroClasses.LittlewoodMontagem.littlewood
  have hpos : ∀ x : ℝ, Real.exp (Real.exp (Real.exp 1)) ≤ x → 0 < c * √x * Real.log (Real.log (Real.log x)) := by
    intro x hx
    have hl := lll_ge hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have := Real.sqrt_pos.mpr hx0
    positivity
  constructor
  · obtain ⟨x, hx, hψ⟩ := h1 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩
  · obtain ⟨x, hx, hψ⟩ := h2 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩

/-- **`θ(x) − x` troca de sinal infinitas vezes.** -/
theorem theta_troca_sinal (X : ℝ) : (∃ x : ℝ, X ≤ x ∧ Chebyshev.theta x - x < 0) ∧
    (∃ x : ℝ, X ≤ x ∧ 0 < Chebyshev.theta x - x) := by
  obtain ⟨c, hc, h1, h2⟩ := theta_littlewood
  have hpos : ∀ x : ℝ, Real.exp (Real.exp (Real.exp 1)) ≤ x → 0 < c * √x * Real.log (Real.log (Real.log x)) := by
    intro x hx
    have hl := lll_ge hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have := Real.sqrt_pos.mpr hx0
    positivity
  constructor
  · obtain ⟨x, hx, hψ⟩ := h1 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩
  · obtain ⟨x, hx, hψ⟩ := h2 (max X (Real.exp (Real.exp (Real.exp 1))))
    exact ⟨x, le_trans (le_max_left _ _) hx, by linarith [hpos x (le_trans (le_max_right _ _) hx)]⟩

end ATK.ZeroClasses.LittlewoodTeta

#print axioms ATK.ZeroClasses.LittlewoodTeta.lll_ge
#print axioms ATK.ZeroClasses.LittlewoodTeta.theta_littlewood
#print axioms ATK.ZeroClasses.LittlewoodTeta.psi_troca_sinal
#print axioms ATK.ZeroClasses.LittlewoodTeta.theta_troca_sinal
