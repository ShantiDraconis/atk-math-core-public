import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic.IntervalCases

/-!
# ATK — Lemas quárticos auxiliares (itens 3, 4, 9 e 10 do inventário Fermat/Beal)

* `quarta_mod16` / `quarta_mod5`: `x⁴ ≡ 0` ou `1` módulo 16 e módulo 5;
* `fatoracao_quarta`: `a⁴ − b⁴ = (a − b)(a + b)(a² + b²)`;
* `divisor_comum_fatores`: se `a, b` são coprimos, todo divisor comum de `a² − b²` e `a² + b²`
  divide 2 (o mdc dos dois fatores é 1 ou 2).

Todos são fatos elementares conhecidos; aqui ficam certificados no kernel para reuso.
-/

namespace ATK.FermatAux

/-- Quartas potências em `ZMod 16`: só `0` ou `1`. -/
theorem quarta_mod16_zmod : ∀ y : ZMod 16, y ^ 4 = 0 ∨ y ^ 4 = 1 := by decide

/-- Quartas potências em `ZMod 5`: só `0` ou `1`. -/
theorem quarta_mod5_zmod : ∀ y : ZMod 5, y ^ 4 = 0 ∨ y ^ 4 = 1 := by decide

/-- `x⁴ mod 16 ∈ {0, 1}` em `ℤ`. -/
theorem quarta_mod16 (x : ℤ) : x ^ 4 % 16 = 0 ∨ x ^ 4 % 16 = 1 := by
  have hm : x ^ 4 % 16 = (x % 16) ^ 4 % 16 := ((Int.mod_modEq x 16).pow 4).symm
  rw [hm]
  have h0 : 0 ≤ x % 16 := Int.emod_nonneg x (by norm_num)
  have h1 : x % 16 < 16 := Int.emod_lt_of_pos x (by norm_num)
  generalize x % 16 = r at h0 h1 ⊢
  interval_cases r <;> decide

/-- `x⁴ mod 5 ∈ {0, 1}` em `ℤ`. -/
theorem quarta_mod5 (x : ℤ) : x ^ 4 % 5 = 0 ∨ x ^ 4 % 5 = 1 := by
  have hm : x ^ 4 % 5 = (x % 5) ^ 4 % 5 := ((Int.mod_modEq x 5).pow 4).symm
  rw [hm]
  have h0 : 0 ≤ x % 5 := Int.emod_nonneg x (by norm_num)
  have h1 : x % 5 < 5 := Int.emod_lt_of_pos x (by norm_num)
  generalize x % 5 = r at h0 h1 ⊢
  interval_cases r <;> decide

/-- Fatoração completa de `a⁴ − b⁴`. -/
theorem fatoracao_quarta (a b : ℤ) : a ^ 4 - b ^ 4 = (a - b) * (a + b) * (a ^ 2 + b ^ 2) := by
  ring

/-- Com `a, b` coprimos, todo divisor comum de `a² − b²` e `a² + b²` divide 2. -/
theorem divisor_comum_fatores {a b d : ℤ} (hab : IsCoprime a b) (h1 : d ∣ a ^ 2 - b ^ 2)
    (h2 : d ∣ a ^ 2 + b ^ 2) : d ∣ 2 := by
  obtain ⟨u, v, h⟩ : IsCoprime (a ^ 2) (b ^ 2) := hab.pow
  have e : (2 : ℤ) = (u + v) * (a ^ 2 + b ^ 2) + (u - v) * (a ^ 2 - b ^ 2) := by
    linear_combination (-2 : ℤ) * h
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)

end ATK.FermatAux

#print axioms ATK.FermatAux.quarta_mod16_zmod
#print axioms ATK.FermatAux.quarta_mod5_zmod
#print axioms ATK.FermatAux.quarta_mod16
#print axioms ATK.FermatAux.quarta_mod5
#print axioms ATK.FermatAux.fatoracao_quarta
#print axioms ATK.FermatAux.divisor_comum_fatores
