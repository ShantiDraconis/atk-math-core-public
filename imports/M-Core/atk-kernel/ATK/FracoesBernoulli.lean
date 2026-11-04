import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import ATK.FracoesChi

/-!
# ATK — As frações de Bernoulli: `ζ(−1) = −1/12` e quem mais a usa (rodada 103)

`ζ` nos inteiros negativos é **racional**: `ζ(−k) = −B'_{k+1}/(k + 1)` (Mathlib). Aqui:

* `zeta_zero … zeta_neg_nove`: `ζ(0) = −1/2`, `ζ(−1) = −1/12`, `ζ(−3) = 1/120`, `ζ(−5) = −1/252`,
  `ζ(−7) = 1/240`, `ζ(−9) = −1/132`, com `B₆ = 1/42`, `B₈ = −1/30`, `B₁₀ = 5/66` (`bernoulli'_seis`, …).
* **Uma mesma série gera as duas frações** (`doze_compartilhado`): o coeficiente de `X²` em `X/(e^X − 1)`
  é `1/12`. A mesma série dá a classe de Todd (`td = 1 + c₁/2 + (c₁² + c₂)/12 + …`) de Hirzebruch–Riemann–
  Roch, que é de onde vem o `1/12` da fórmula de Noether `χ(𝒪_S) = (K² + e)/12` para superfícies (Hodge).
  `noether_exemplos`: a fórmula é inteira em `ℙ²`, `ℙ¹ × ℙ¹`, K3 e Enriques (aritmética).
* **`240`**: `2/ζ(−3) = 1/ζ(−7) = 240` (`duzentos_e_quarenta`). É o coeficiente da série de Eisenstein
  `E₄ = 1 + 240 Σ σ₃(n)qⁿ`, a função teta do reticulado `E₈` (240 raízes), e o `240` da pressão de Casimir
  `−π²ħc/(240 a⁴)`. Só a aritmética está aqui; as identificações são teoremas clássicos não formalizados.
* **Bernoulli e `χ`** (`bernoulli_chi`): `B₄ = −χ(2, 3, 5)`, `B₆ = −χ(2, 3, 7)`, `B₈ = −χ(2, 3, 5)`,
  `B₁₀ = −χ(2, 3, 11)` e `B₂ = 1 − 1/2 − 1/3`. É von Staudt–Clausen (`B_{2k} + Σ_{(p−1) | 2k} 1/p ∈ ℤ`)
  com o inteiro igual a `1` e só três primos. **Não há mapa geométrico conhecido** por trás de `(2, 3, 5)`,
  `(2, 3, 7)`, `(2, 3, 11)`: registrado como identidade aritmética, não como conexão. O caso `(2, 3, ∞)` tem
  mapa (Harder: `χ(SL₂ℤ) = ζ(−1)`), não formalizado.

Classificação: **consequência** (valores clássicos) e **auditoria** (o que é lei e o que é coincidência).
-/

open Finset PowerSeries

namespace ATK.Fracoes.Bernoulli

open ATK.Fracoes.Chi

/-! ## 1. Os números de Bernoulli -/

theorem bernoulli'_cinco : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
theorem bernoulli'_sete : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd ⟨3, rfl⟩ (by norm_num)
theorem bernoulli'_nove : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd ⟨4, rfl⟩ (by norm_num)

theorem bernoulli'_seis : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_cinco]
  have c1 : Nat.choose 6 1 = 6 := by decide
  have c2 : Nat.choose 6 2 = 15 := by decide
  have c3 : Nat.choose 6 3 = 20 := by decide
  have c4 : Nat.choose 6 4 = 15 := by decide
  have c5 : Nat.choose 6 5 = 6 := by decide
  rw [c1, c2, c3, c4, c5]
  norm_num

theorem bernoulli'_oito : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_cinco, bernoulli'_seis, bernoulli'_sete]
  have c1 : Nat.choose 8 1 = 8 := by decide
  have c2 : Nat.choose 8 2 = 28 := by decide
  have c3 : Nat.choose 8 3 = 56 := by decide
  have c4 : Nat.choose 8 4 = 70 := by decide
  have c5 : Nat.choose 8 5 = 56 := by decide
  have c6 : Nat.choose 8 6 = 28 := by decide
  have c7 : Nat.choose 8 7 = 8 := by decide
  rw [c1, c2, c3, c4, c5, c6, c7]
  norm_num

theorem bernoulli'_dez : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [sum_range_succ, sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_cinco, bernoulli'_seis, bernoulli'_sete,
    bernoulli'_oito, bernoulli'_nove]
  have c1 : Nat.choose 10 1 = 10 := by decide
  have c2 : Nat.choose 10 2 = 45 := by decide
  have c3 : Nat.choose 10 3 = 120 := by decide
  have c4 : Nat.choose 10 4 = 210 := by decide
  have c5 : Nat.choose 10 5 = 252 := by decide
  have c6 : Nat.choose 10 6 = 210 := by decide
  have c7 : Nat.choose 10 7 = 120 := by decide
  have c8 : Nat.choose 10 8 = 45 := by decide
  have c9 : Nat.choose 10 9 = 10 := by decide
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9]
  norm_num

/-! ## 2. `ζ` nos inteiros negativos -/

/-- `ζ(−k) = −B'_{k+1}/(k + 1)` com `k` explícito. -/
theorem zeta_neg (k : ℕ) (b : ℚ) (hb : bernoulli' (k + 1) = b) :
    riemannZeta (-(k : ℂ)) = ((-b / (k + 1) : ℚ) : ℂ) := by
  rw [riemannZeta_neg_nat_eq_bernoulli', hb]
  push_cast
  ring

theorem zeta_zero : riemannZeta 0 = -1 / 2 := riemannZeta_zero

theorem zeta_neg_um : riemannZeta (-1) = -1 / 12 := by
  have h := zeta_neg 1 (1 / 6) bernoulli'_two
  norm_num at h
  rw [h]; norm_num

theorem zeta_neg_tres : riemannZeta (-3) = 1 / 120 := by
  have h := zeta_neg 3 (-1 / 30) bernoulli'_four
  norm_num at h
  rw [h]

theorem zeta_neg_cinco : riemannZeta (-5) = -1 / 252 := by
  have h := zeta_neg 5 (1 / 42) bernoulli'_seis
  norm_num at h
  rw [h]; norm_num

theorem zeta_neg_sete : riemannZeta (-7) = 1 / 240 := by
  have h := zeta_neg 7 (-1 / 30) bernoulli'_oito
  norm_num at h
  rw [h]

theorem zeta_neg_nove : riemannZeta (-9) = -1 / 132 := by
  have h := zeta_neg 9 (5 / 66) bernoulli'_dez
  norm_num at h
  rw [h]; norm_num

/-! ## 3. O mesmo `1/12`: a série `X/(e^X − 1)` -/

/-- Coeficiente de `X²` em `X/(e^X − 1)` (série de Bernoulli/Todd). -/
theorem coef_todd_dois : coeff 2 (bernoulliPowerSeries ℚ) = 1 / 12 := by
  rw [bernoulliPowerSeries, coeff_mk, bernoulli_eq_bernoulli'_of_ne_one (by norm_num),
    bernoulli'_two]
  norm_num [Nat.factorial]

/-- `X/(e^X − 1)` gera os coeficientes: `bernoulliPowerSeries · (e^X − 1) = X` (Mathlib). -/
theorem serie_geradora : bernoulliPowerSeries ℚ * (exp ℚ - 1) = X :=
  bernoulliPowerSeries_mul_exp_sub_one ℚ

/-- **O `1/12` compartilhado**: o coeficiente de Todd/Noether e `−ζ(−1)` são o mesmo número `B₂/2`. -/
theorem doze_compartilhado :
    coeff 2 (bernoulliPowerSeries ℚ) = 1 / 12 ∧
      riemannZeta (-1) = -(((coeff 2 (bernoulliPowerSeries ℚ) : ℚ)) : ℂ) := by
  refine ⟨coef_todd_dois, ?_⟩
  rw [coef_todd_dois, zeta_neg_um]
  push_cast
  ring

/-- Fórmula de Noether `χ(𝒪_S) = (K² + e)/12`, avaliada (aritmética): `ℙ²` (9, 3), `ℙ¹ × ℙ¹` (8, 4),
K3 (0, 24), Enriques (0, 12). -/
theorem noether_exemplos :
    ((9 + 3) / 12 : ℚ) = 1 ∧ ((8 + 4) / 12 : ℚ) = 1 ∧ ((0 + 24) / 12 : ℚ) = 2 ∧
      ((0 + 12) / 12 : ℚ) = 1 := by
  norm_num

/-! ## 4. `240` -/

theorem duzentos_e_quarenta : 2 / riemannZeta (-3) = 240 ∧ 1 / riemannZeta (-7) = 240 := by
  rw [zeta_neg_tres, zeta_neg_sete]
  constructor <;> norm_num

/-! ## 5. Bernoulli e `χ`: von Staudt–Clausen com inteiro `1` -/

/-- `B_{2k} + Σ_{(p−1) | 2k} 1/p = 1` para `2k = 2, 4, 6, 8, 10`. -/
theorem staudt_clausen :
    bernoulli' 2 + 1 / 2 + 1 / 3 = 1 ∧ bernoulli' 4 + 1 / 2 + 1 / 3 + 1 / 5 = 1 ∧
      bernoulli' 6 + 1 / 2 + 1 / 3 + 1 / 7 = 1 ∧ bernoulli' 8 + 1 / 2 + 1 / 3 + 1 / 5 = 1 ∧
      bernoulli' 10 + 1 / 2 + 1 / 3 + 1 / 11 = 1 := by
  rw [bernoulli'_two, bernoulli'_four, bernoulli'_seis, bernoulli'_oito, bernoulli'_dez]
  norm_num

/-- **`B_{2k} = −χ`** para os três primos de von Staudt–Clausen. Identidade aritmética; nenhuma
correspondência geométrica conhecida para `(2, 3, 5)`, `(2, 3, 7)`, `(2, 3, 11)`. -/
theorem bernoulli_chi :
    bernoulli' 4 = -chi 2 3 5 ∧ bernoulli' 6 = -chi 2 3 7 ∧ bernoulli' 8 = -chi 2 3 5 ∧
      bernoulli' 10 = -chi 2 3 11 ∧ bernoulli' 2 = 1 - 1 / 2 - 1 / 3 := by
  rw [bernoulli'_two, bernoulli'_four, bernoulli'_seis, bernoulli'_oito, bernoulli'_dez]
  norm_num [chi]

end ATK.Fracoes.Bernoulli

#print axioms ATK.Fracoes.Bernoulli.bernoulli'_cinco
#print axioms ATK.Fracoes.Bernoulli.bernoulli'_sete
#print axioms ATK.Fracoes.Bernoulli.bernoulli'_nove
#print axioms ATK.Fracoes.Bernoulli.bernoulli'_seis
#print axioms ATK.Fracoes.Bernoulli.bernoulli'_oito
#print axioms ATK.Fracoes.Bernoulli.bernoulli'_dez
#print axioms ATK.Fracoes.Bernoulli.zeta_neg
#print axioms ATK.Fracoes.Bernoulli.zeta_zero
#print axioms ATK.Fracoes.Bernoulli.zeta_neg_um
#print axioms ATK.Fracoes.Bernoulli.zeta_neg_tres
#print axioms ATK.Fracoes.Bernoulli.zeta_neg_cinco
#print axioms ATK.Fracoes.Bernoulli.zeta_neg_sete
#print axioms ATK.Fracoes.Bernoulli.zeta_neg_nove
#print axioms ATK.Fracoes.Bernoulli.coef_todd_dois
#print axioms ATK.Fracoes.Bernoulli.serie_geradora
#print axioms ATK.Fracoes.Bernoulli.doze_compartilhado
#print axioms ATK.Fracoes.Bernoulli.noether_exemplos
#print axioms ATK.Fracoes.Bernoulli.duzentos_e_quarenta
#print axioms ATK.Fracoes.Bernoulli.staudt_clausen
#print axioms ATK.Fracoes.Bernoulli.bernoulli_chi
