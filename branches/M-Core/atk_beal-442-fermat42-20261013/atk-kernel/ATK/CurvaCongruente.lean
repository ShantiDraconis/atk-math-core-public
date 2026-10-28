import ATK.FermatRightTriangle

/-!
# ATK — Pontos racionais de `y² = x³ − x` (item 11 do inventário)

A curva `y² = x³ − x` é a "curva do número congruente 1". Um ponto racional com `y ≠ 0` dá um
triângulo retângulo racional de área 1:

  `a = (x² − 1)/y`, `b = 2x/y`, `c = (x² + 1)/y`, com `a² + b² = c²` e `ab/2 = 1`.

Como `ATK.FermatRightTriangle.one_not_congruent` exclui esse triângulo, o kernel prova:

* `pontos_racionais`: todo ponto racional afim de `y² = x³ − x` tem `y = 0` e `x ∈ {0, 1, −1}`.

Ou seja, os únicos pontos racionais são os de 2-torsão (mais o ponto no infinito): a forma
elementar de "posto 0 e torção `ℤ/2 × ℤ/2`". Resultado clássico (Fermat); nova só a formalização.
-/

namespace ATK.CurvaCongruente

open ATK.FermatRightTriangle

/-- **Todo ponto racional afim de `y² = x³ − x` é de 2-torsão.** -/
theorem pontos_racionais {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) :
    y = 0 ∧ (x = 0 ∨ x = 1 ∨ x = -1) := by
  by_cases hy : y = 0
  · refine ⟨hy, ?_⟩
    subst hy
    have hx : x * ((x - 1) * (x + 1)) = 0 := by linear_combination (-1 : ℚ) * h
    rcases mul_eq_zero.mp hx with h1 | h1
    · exact Or.inl h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  · exfalso
    refine one_not_congruent (a := (x ^ 2 - 1) / y) (b := 2 * x / y) (c := (x ^ 2 + 1) / y) ?_ ?_
    · field_simp
      ring
    · field_simp
      linear_combination (-1 : ℚ) * h

/-- Equivalentemente: o conjunto dos pontos racionais afins é exatamente `{(0,0), (1,0), (−1,0)}`. -/
theorem pontos_racionais_iff {x y : ℚ} :
    y ^ 2 = x ^ 3 - x ↔ y = 0 ∧ (x = 0 ∨ x = 1 ∨ x = -1) := by
  constructor
  · exact pontos_racionais
  · rintro ⟨rfl, hx | hx | hx⟩ <;> subst hx <;> norm_num

end ATK.CurvaCongruente

#print axioms ATK.CurvaCongruente.pontos_racionais
#print axioms ATK.CurvaCongruente.pontos_racionais_iff
