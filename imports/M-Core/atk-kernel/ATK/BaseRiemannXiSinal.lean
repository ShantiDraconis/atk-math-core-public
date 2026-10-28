/-
ATK.Base (R2) — Sinal de ξ na reta real e `Ξ(0) > 0`.

Continua `ATK.BaseRiemannXi`.  Com `ζ(σ) < 0` em `(0, 1)` (provado no kernel em
`ATK.ZetaSimetria.zeta_real_neg`, pela fórmula de Euler–Maclaurin com a parte fracionária) e
`ζ(σ) > 0` para `σ > 1` (`riemannZeta_pos_of_one_lt` da Mathlib):

* **`Gammaℝ_ofReal`**: `Γℝ(σ) = π^{−σ/2} Γ(σ/2)` é um real positivo para `σ > 0`;
* **`riemannXi_ofReal_pos`**: `ξ(σ)` é um real **positivo** para todo `σ ∈ ℝ`
  (em particular ξ não tem zeros reais);
* **`riemannXi_meio`** e **`Xi_zero_pos`**: `Ξ(0) = ξ(1/2) > 0`;
* **`zero_of_Xi_neg`**: se `Ξ(t) < 0` para algum `t > 0`, há um zero de ζ na reta crítica com
  altura em `(0, t)`.

`Ξ(0) > 0` é o ponto de partida do argumento de Hardy (infinitos zeros na reta crítica, camada
R4): basta exibir infinitas trocas de sinal de Ξ.
-/
import ATK.BaseRiemannXi
import ATK.ZetaSimetria

open Complex Set

namespace ATK.BaseRiemannXiSinal

open ATK.BaseRiemannXi

/-- **`Γℝ` é real positiva em `(0, ∞)`.** -/
theorem Gammaℝ_ofReal {σ : ℝ} (hσ : 0 < σ) :
    ∃ g : ℝ, 0 < g ∧ Gammaℝ (σ : ℂ) = g := by
  refine ⟨Real.pi ^ (-σ / 2) * Real.Gamma (σ / 2),
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith)), ?_⟩
  rw [Gammaℝ_def, ofReal_mul, ofReal_cpow Real.pi_pos.le, ← Complex.Gamma_ofReal]
  push_cast
  ring_nf

/-- `ζ(σ)` é real positivo para `σ > 1`. -/
theorem zeta_ofReal_pos {σ : ℝ} (hσ : 1 < σ) : ∃ z : ℝ, 0 < z ∧ riemannZeta σ = z :=
  ⟨(riemannZeta σ).re, riemannZeta_re_pos_of_one_lt hσ,
    Complex.ext (by simp) (by simp [riemannZeta_im_eq_zero_of_one_lt hσ])⟩

/-- `ξ(σ) = σ(σ−1)/2 · Γℝ(σ) · ζ(σ)` na reta real positiva (fora de 1), com fatores reais. -/
theorem riemannXi_ofReal_eq {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    riemannXi σ = (σ : ℂ) * ((σ : ℂ) - 1) / 2 * Gammaℝ σ * riemannZeta σ := by
  have h0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have h1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1
  exact riemannXi_eq_zeta h0 h1 (Gammaℝ_ne_zero_of_re_pos (by simpa using hσ))

/-- Caso `σ ∈ (0, 1)`. -/
theorem riemannXi_pos_faixa {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ x : ℝ, 0 < x ∧ riemannXi σ = x := by
  obtain ⟨g, hg, hG⟩ := Gammaℝ_ofReal h0
  obtain ⟨z, hz, hZ⟩ := ATK.ZetaSimetria.zeta_real_neg h0 h1
  refine ⟨σ * (σ - 1) / 2 * g * z, ?_, ?_⟩
  · have hneg : σ * (σ - 1) / 2 < 0 := by
      have : σ * (σ - 1) < 0 := mul_neg_of_pos_of_neg h0 (by linarith)
      linarith
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hneg hg) hz
  · rw [riemannXi_ofReal_eq h0 h1.ne, hG, hZ]
    push_cast
    ring

/-- Caso `σ > 1`. -/
theorem riemannXi_pos_direita {σ : ℝ} (h1 : 1 < σ) :
    ∃ x : ℝ, 0 < x ∧ riemannXi σ = x := by
  have h0 : 0 < σ := by linarith
  obtain ⟨g, hg, hG⟩ := Gammaℝ_ofReal h0
  obtain ⟨z, hz, hZ⟩ := zeta_ofReal_pos h1
  refine ⟨σ * (σ - 1) / 2 * g * z, ?_, ?_⟩
  · have : 0 < σ * (σ - 1) / 2 := by
      have : 0 < σ * (σ - 1) := mul_pos h0 (by linarith)
      linarith
    positivity
  · rw [riemannXi_ofReal_eq h0 h1.ne', hG, hZ]
    push_cast
    ring

/-- **ξ é real e positiva em toda a reta real.** Em particular, ξ (e ζ na faixa) não tem zeros
reais. -/
theorem riemannXi_ofReal_pos (σ : ℝ) : ∃ x : ℝ, 0 < x ∧ riemannXi σ = x := by
  rcases lt_trichotomy σ 0 with hσ | hσ | hσ
  · obtain ⟨x, hx, he⟩ := riemannXi_pos_direita (σ := 1 - σ) (by linarith)
    refine ⟨x, hx, ?_⟩
    rw [← he, ← riemannXi_one_sub]
    push_cast
    ring_nf
  · exact ⟨1 / 2, by norm_num, by rw [hσ]; simp [riemannXi_zero]⟩
  · rcases lt_trichotomy σ 1 with h1 | h1 | h1
    · exact riemannXi_pos_faixa hσ h1
    · exact ⟨1 / 2, by norm_num, by rw [h1]; simp [riemannXi_one]⟩
    · exact riemannXi_pos_direita h1

theorem riemannXi_ofReal_ne_zero (σ : ℝ) : riemannXi σ ≠ 0 := by
  obtain ⟨x, hx, he⟩ := riemannXi_ofReal_pos σ
  rw [he]
  exact_mod_cast hx.ne'

/-- `ξ(1/2) = −(1/8) · Γℝ(1/2) · ζ(1/2)`. -/
theorem riemannXi_meio :
    riemannXi (1 / 2) = -(1 / 8) * Gammaℝ (1 / 2) * riemannZeta (1 / 2) := by
  have h := riemannXi_ofReal_eq (σ := 1 / 2) (by norm_num) (by norm_num)
  push_cast at h
  rw [h]
  ring

/-- `Ξ(0) = ξ(1/2)`. -/
theorem Xi_zero_eq : (Xi 0 : ℂ) = riemannXi (1 / 2) := by
  rw [← riemannXi_critical]
  simp

/-- **`Ξ(0) > 0`.** -/
theorem Xi_zero_pos : 0 < Xi 0 := by
  obtain ⟨x, hx, he⟩ := riemannXi_ofReal_pos (1 / 2)
  have h : (Xi 0 : ℂ) = (x : ℂ) := by
    rw [Xi_zero_eq, ← he]
    push_cast
    ring_nf
  rw [ofReal_inj.mp h]
  exact hx

/-- **Uma troca de sinal basta**: se `Ξ(t) < 0` para algum `t > 0`, ζ tem um zero na reta
crítica com altura em `(0, t)`. -/
theorem zero_of_Xi_neg {t : ℝ} (ht : 0 < t) (hneg : Xi t < 0) :
    ∃ u ∈ Ioo 0 t, riemannZeta (1 / 2 + u * I) = 0 :=
  zero_of_sign_change ht.le (mul_neg_of_pos_of_neg Xi_zero_pos hneg)

end ATK.BaseRiemannXiSinal

#print axioms ATK.BaseRiemannXiSinal.Gammaℝ_ofReal
#print axioms ATK.BaseRiemannXiSinal.zeta_ofReal_pos
#print axioms ATK.BaseRiemannXiSinal.riemannXi_ofReal_eq
#print axioms ATK.BaseRiemannXiSinal.riemannXi_pos_faixa
#print axioms ATK.BaseRiemannXiSinal.riemannXi_pos_direita
#print axioms ATK.BaseRiemannXiSinal.riemannXi_ofReal_pos
#print axioms ATK.BaseRiemannXiSinal.riemannXi_ofReal_ne_zero
#print axioms ATK.BaseRiemannXiSinal.riemannXi_meio
#print axioms ATK.BaseRiemannXiSinal.Xi_zero_eq
#print axioms ATK.BaseRiemannXiSinal.Xi_zero_pos
#print axioms ATK.BaseRiemannXiSinal.zero_of_Xi_neg
