import ATK.TresZeros
import ATK.FracoesGama

/-!
# ATK — Os três primeiros zeros de `ζ` em frações contínuas (rodada 103)

Junta `ATK.TresZeros.tres_zeros` (zeros certificados na reta, bolas de raio `10⁻⁶`) com
`ATK.Fracoes.Gama`: existem zeros `½ + iγ₁`, `½ + iγ₂`, `½ + iγ₃` com

`γ₁ = [14; 7, 2, 2, 1, 2, 1, …]`, `γ₂ = [21; 45, 2, 1, 2, …]`, `γ₃ = [25; 92, …]`,

e `|γ₁ − 2728/193| < 1/193²`, `|γ₂ − 7631/363| < 1/363²`, `|γ₃ − 2301/92| < 1/92²`.
Incondicional (só o kernel do ATK e a Mathlib). Classificação: **consequência**.
-/

namespace ATK.Fracoes.GamaZeros

open ATK.Fracoes.Gama Complex

theorem tres_zeros_fc :
    ∃ γ₁ γ₂ γ₃ : ℝ,
      riemannZeta ((1 / 2 : ℂ) + (γ₁ : ℂ) * I) = 0 ∧ ⌊γ₁⌋ = 14 ∧ ⌊passo γ₁⌋ = 7 ∧
        |γ₁ - 2728 / 193| < 1 / 193 ^ 2 ∧
      riemannZeta ((1 / 2 : ℂ) + (γ₂ : ℂ) * I) = 0 ∧ ⌊γ₂⌋ = 21 ∧ ⌊passo γ₂⌋ = 45 ∧
        |γ₂ - 7631 / 363| < 1 / 363 ^ 2 ∧
      riemannZeta ((1 / 2 : ℂ) + (γ₃ : ℂ) * I) = 0 ∧ ⌊γ₃⌋ = 25 ∧ ⌊passo γ₃⌋ = 92 ∧
        |γ₃ - 2301 / 92| < 1 / 92 ^ 2 := by
  obtain ⟨γ₁, γ₂, γ₃, z1, e1, z2, e2, z3, e3, -, -⟩ := ATK.TresZeros.tres_zeros
  obtain ⟨a0, a1, -⟩ := gama1_fc e1
  obtain ⟨b0, b1, -⟩ := gama2_fc e2
  obtain ⟨c0, c1, -⟩ := gama3_fc e3
  exact ⟨γ₁, γ₂, γ₃, z1, a0, a1, gama1_fc_conv e1, z2, b0, b1, gama2_fc_conv e2, z3, c0, c1,
    gama3_fc_conv e3⟩

end ATK.Fracoes.GamaZeros

#print axioms ATK.Fracoes.GamaZeros.tres_zeros_fc
