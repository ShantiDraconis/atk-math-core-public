import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# ATK — Os dois fatores de `a⁴ − b⁴` (itens 9 e 10 do inventário Fermat/Beal)

* `fatoracao_quarta`: `a⁴ − b⁴ = (a − b)(a + b)(a² + b²)`;
* `divisor_comum_fatores`: com `a, b` coprimos, todo divisor comum de `a² − b²` e `a² + b²`
  divide 2 — o mdc dos dois fatores é 1 ou 2.

Complementa `ATK.QuarticResidues` (itens 3 e 4). Fatos elementares conhecidos.
-/

namespace ATK.FatoresQuarticos

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

end ATK.FatoresQuarticos

#print axioms ATK.FatoresQuarticos.fatoracao_quarta
#print axioms ATK.FatoresQuarticos.divisor_comum_fatores
