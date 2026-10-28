import Mathlib.Tactic

/-!
# ATK — Resíduos quárticos em `ℤ`: `n⁴ mod 16` e `n⁴ mod 5`

Lemas que os livros chamam de "óbvios", enunciados direto em `ℤ` com `%`:

* `fourth_pow_emod_sixteen`: `n⁴ % 16 ∈ {0, 1}`;
* `fourth_pow_emod_five`: `n⁴ % 5 ∈ {0, 1}`;
* `sum_two_fourth_pow_emod_sixteen`: `(m⁴ + n⁴) % 16 ∈ {0, 1, 2}` (nunca `3 mod 4`).

**Limite, também provado aqui** (`no_congruence_obstruction`): nenhuma congruência sozinha exclui
`x⁴ − y⁴ = z²` com `y, z ≠ 0`, porque `(1, N, 1)` é solução módulo qualquer `N`. Por isso os
resultados de `ATK.FermatRightTriangle` e `ATK.BealFermatDescent` usam descida infinita, e uma
"exclusão residual quártica" por congruências não pode, sozinha, provar esses casos de Beal.
-/

namespace ATK.QuarticResidues

/-- `n⁴ % 16 ∈ {0, 1}`. -/
theorem fourth_pow_emod_sixteen (n : ℤ) : n ^ 4 % 16 = 0 ∨ n ^ 4 % 16 = 1 := by
  obtain ⟨q, r, hr0, hr16, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 16 ∧ n = 16 * q + r :=
    ⟨n / 16, n % 16, by omega, by omega, by omega⟩
  have e : (16 * q + r) ^ 4 =
      16 * (4096 * q ^ 4 + 1024 * q ^ 3 * r + 96 * q ^ 2 * r ^ 2 + 4 * q * r ^ 3) +
        r * r * r * r := by ring
  rw [e]
  generalize 4096 * q ^ 4 + 1024 * q ^ 3 * r + 96 * q ^ 2 * r ^ 2 + 4 * q * r ^ 3 = m
  interval_cases r <;> omega

/-- `n⁴ % 5 ∈ {0, 1}` (Fermat pequeno para `p = 5`). -/
theorem fourth_pow_emod_five (n : ℤ) : n ^ 4 % 5 = 0 ∨ n ^ 4 % 5 = 1 := by
  obtain ⟨q, r, hr0, hr5, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 5 ∧ n = 5 * q + r :=
    ⟨n / 5, n % 5, by omega, by omega, by omega⟩
  have e : (5 * q + r) ^ 4 =
      5 * (125 * q ^ 4 + 100 * q ^ 3 * r + 30 * q ^ 2 * r ^ 2 + 4 * q * r ^ 3) +
        r * r * r * r := by ring
  rw [e]
  generalize 125 * q ^ 4 + 100 * q ^ 3 * r + 30 * q ^ 2 * r ^ 2 + 4 * q * r ^ 3 = m
  interval_cases r <;> omega

/-- Soma de duas quartas potências: `(m⁴ + n⁴) % 16 ∈ {0, 1, 2}`. -/
theorem sum_two_fourth_pow_emod_sixteen (m n : ℤ) :
    (m ^ 4 + n ^ 4) % 16 = 0 ∨ (m ^ 4 + n ^ 4) % 16 = 1 ∨ (m ^ 4 + n ^ 4) % 16 = 2 := by
  have hm := fourth_pow_emod_sixteen m
  have hn := fourth_pow_emod_sixteen n
  generalize m ^ 4 = A at hm ⊢
  generalize n ^ 4 = B at hn ⊢
  omega

/-- Corolário: a soma de duas quartas potências nunca é `≡ 3 (mod 4)`. -/
theorem sum_two_fourth_pow_emod_four_ne_three (m n : ℤ) : (m ^ 4 + n ^ 4) % 4 ≠ 3 := by
  have h := sum_two_fourth_pow_emod_sixteen m n
  generalize m ^ 4 + n ^ 4 = S at h ⊢
  omega

/-- **Limite das congruências**: para todo `N ≠ 0` há `x, y, z` com `y, z ≠ 0` e
`N ∣ x⁴ − y⁴ − z²`. Logo nenhum argumento só por resíduos prova `x⁴ − y⁴ ≠ z²`. -/
theorem no_congruence_obstruction (N : ℤ) (hN : N ≠ 0) :
    ∃ x y z : ℤ, y ≠ 0 ∧ z ≠ 0 ∧ N ∣ x ^ 4 - y ^ 4 - z ^ 2 :=
  ⟨1, N, 1, hN, one_ne_zero, ⟨-N ^ 3, by ring⟩⟩

end ATK.QuarticResidues

#print axioms ATK.QuarticResidues.fourth_pow_emod_sixteen
#print axioms ATK.QuarticResidues.fourth_pow_emod_five
#print axioms ATK.QuarticResidues.sum_two_fourth_pow_emod_sixteen
#print axioms ATK.QuarticResidues.sum_two_fourth_pow_emod_four_ne_three
#print axioms ATK.QuarticResidues.no_congruence_obstruction
