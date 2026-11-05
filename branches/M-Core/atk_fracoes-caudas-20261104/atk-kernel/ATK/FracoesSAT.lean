import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# ATK — As frações de P vs NP: `7/8` e `(4/3)ⁿ` (rodada 103)

* **`7/8`** (`clausula_sete_oitavos`): uma cláusula com 3 literais em variáveis distintas é satisfeita por
  exatamente 7 das 8 atribuições. Por isso uma atribuição aleatória satisfaz `7/8` das cláusulas de uma
  fórmula 3-CNF em média; Håstad (2001) provou que superar `7/8 + ε` é NP-difícil (ponte, não
  formalizada). Coincidência a registrar: `7/8` também é a constante de `N(T) = (T/2π) log(T/2πe) + 7/8 +
  S(T) + O(1/T)` para os zeros de `ζ`; lá vem da fase de `Γ` (`−π/8`), aqui de `1 − 2⁻³`. Mesma fração,
  nenhum mapa.
* **`(4/3)ⁿ`** (`schoening`): `Σ_j C(n, j) 2⁻ⁿ 2⁻ʲ = (3/4)ⁿ`, a identidade central da análise do passeio
  aleatório de Schöning (1999) para 3-SAT (tempo `(4/3)ⁿ`). Para `k`-SAT a base é `2(k − 1)/k`
  (`schoening_k`, `base`): `= 1` para `k = 2` (polinomial), `4/3` para `k = 3`, `< 2` sempre.

Classificação: **consequência** (clássicas). P vs NP continua `OPEN_MATH`: nada aqui dá cota inferior.
-/

open Finset

namespace ATK.Fracoes.SAT

/-- **7 de 8**: para todo padrão de sinais `s`, a cláusula `ℓ₀ ∨ ℓ₁ ∨ ℓ₂` (`ℓᵢ` verdadeiro sse
`v i = s i`) é satisfeita por exatamente 7 atribuições. -/
theorem clausula_sete_oitavos :
    ∀ s : Fin 3 → Bool, (univ.filter (fun v : Fin 3 → Bool => ∃ i, v i = s i)).card = 7 := by
  decide

/-- A única atribuição que falha é `v = ¬s`. -/
theorem clausula_falha : ∀ s : Fin 3 → Bool,
    (univ.filter (fun v : Fin 3 → Bool => ∀ i, v i ≠ s i)).card = 1 := by
  decide

/-- **Schöning (identidade central)**: `Σ_j C(n, j) (1/2)ⁿ (1/2)ʲ = (3/4)ⁿ`. -/
theorem schoening (n : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 / 2) ^ n * (1 / 2) ^ j = (3 / 4) ^ n := by
  have h := add_pow (1 / 2 : ℚ) 1 n
  simp only [one_pow, mul_one] at h
  have e : ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 / 2) ^ n * (1 / 2) ^ j =
      (1 / 2) ^ n * ∑ j ∈ range (n + 1), (1 / 2 : ℚ) ^ j * (n.choose j : ℚ) := by
    rw [mul_sum]; refine sum_congr rfl fun j _ => by ring
  rw [e, ← h, ← mul_pow]
  norm_num

/-- **`k`-SAT**: `Σ_j C(n, j) (1/2)ⁿ (1/(k−1))ʲ = (k/(2(k−1)))ⁿ`. -/
theorem schoening_k (n : ℕ) {k : ℚ} (hk : 1 < k) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 / 2) ^ n * (1 / (k - 1)) ^ j =
      (k / (2 * (k - 1))) ^ n := by
  have hk1 : k - 1 ≠ 0 := by linarith
  have h := add_pow (1 / (k - 1) : ℚ) 1 n
  simp only [one_pow, mul_one] at h
  have e : ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 / 2) ^ n * (1 / (k - 1)) ^ j =
      (1 / 2) ^ n * ∑ j ∈ range (n + 1), (1 / (k - 1) : ℚ) ^ j * (n.choose j : ℚ) := by
    rw [mul_sum]; refine sum_congr rfl fun j _ => by ring
  rw [e, ← h, ← mul_pow]
  congr 1
  field_simp
  ring

/-- A base do tempo de Schöning, `2(k − 1)/k`: `1` em `k = 2`, `4/3` em `k = 3`, e `< 2`. -/
theorem base : (2 * (2 - 1) / 2 : ℚ) = 1 ∧ (2 * (3 - 1) / 3 : ℚ) = 4 / 3 ∧
    ∀ k : ℚ, 0 < k → 2 * (k - 1) / k < 2 := by
  refine ⟨by norm_num, by norm_num, fun k hk => ?_⟩
  rw [div_lt_iff₀ hk]
  linarith

end ATK.Fracoes.SAT

#print axioms ATK.Fracoes.SAT.clausula_sete_oitavos
#print axioms ATK.Fracoes.SAT.clausula_falha
#print axioms ATK.Fracoes.SAT.schoening
#print axioms ATK.Fracoes.SAT.schoening_k
#print axioms ATK.Fracoes.SAT.base
