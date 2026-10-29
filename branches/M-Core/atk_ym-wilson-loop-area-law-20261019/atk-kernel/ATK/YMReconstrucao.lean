import ATK.YMToy

/-!
# ATK — Ponte B7 (Osterwalder–Schrader) e O8, em miniatura: reconstrução no modelo de rede

A ponte B7 diz: medida euclidiana com os axiomas OS (em particular **positividade de reflexão**) ⇒
teoria quântica (espaço de Hilbert, hamiltoniano `H ≥ 0`, vácuo), e decaimento exponencial das
correlações com taxa `m` ⇒ lacuna espectral `≥ m`. No modelo de rede exatamente solúvel de
`ATK.YMToy` (cadeia de Ising, redução da teoria de calibre `ℤ₂` 2D), tudo isso é verificável:

* `positividade_reflexao`: `Σᵢⱼ cᵢ cⱼ G(tᵢ + tⱼ) ≥ 0` — a correlação é reflexão-positiva;
* `vacuo_autovetor` / `impar_autovetor`: a matriz de transferência `T` (o operador `e^{−H}`
  reconstruído) tem o vácuo `Ω = (1, 1)` com autovalor `C` e o estado `φΩ = (1, −1)` com autovalor
  `S`;
* `vacuo_unico`: `Ω` é o único autovetor com autovalor `C` (vácuo único);
* `correl_reconstruida`: a correlação euclidiana é o elemento de matriz
  `⟨φΩ, Tⁿ φΩ⟩ / ⟨Ω, Tⁿ Ω⟩`;
* `lacuna_igual_taxa`: para `β > 0`, `Tⁿ/Cⁿ` age em `φΩ` por `e^{−m(β) n}` — **a lacuna do
  hamiltoniano reconstruído é exatamente a taxa de decaimento `m(β) > 0` das correlações**.

É a reconstrução OS num espaço de Hilbert de dimensão 2. B7 (o teorema para medidas em `ℝ⁴`) continua
`PUBLICADA_NAO_FORMALIZADA` e O8 (a medida de Yang–Mills 4D com clustering) continua `OPEN_MATH`.
-/

open Real

namespace ATK.YMReconstrucao

open ATK.YMToy

/-- **Positividade de reflexão** da correlação da rede. -/
theorem positividade_reflexao (β : ℝ) {k : ℕ} (c : Fin k → ℝ) (t : Fin k → ℕ) :
    0 ≤ ∑ i, ∑ j, c i * c j * correl β (t i + t j) := by
  have e : ∑ i, ∑ j, c i * c j * correl β (t i + t j) =
      (∑ i, c i * (S β / C β) ^ t i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [correl_eq, pow_add]
    ring
  rw [e]
  exact sq_nonneg _

/-- O vácuo `Ω = (1, 1)` é autovetor de `Tⁿ` com autovalor `Cⁿ`. -/
theorem vacuo_autovetor (β : ℝ) (n : ℕ) (a : Bool) :
    ∑ b : Bool, W β n a b * 1 = C β ^ n := by
  simp only [Fintype.sum_bool, W_formula, σ, mul_one]
  cases a <;> simp <;> ring

/-- `φΩ = (σ_b) = (1, −1)` é autovetor de `Tⁿ` com autovalor `Sⁿ`. -/
theorem impar_autovetor (β : ℝ) (n : ℕ) (a : Bool) :
    ∑ b : Bool, W β n a b * σ b = S β ^ n * σ a := by
  simp only [Fintype.sum_bool, W_formula, σ]
  cases a <;> simp <;> ring

/-- **Vácuo único**: um vetor fixo por `T/C` é constante (múltiplo de `Ω`). -/
theorem vacuo_unico (β : ℝ) (v : Bool → ℝ) (hv : ∀ a, ∑ b : Bool, W β 1 a b * v b = C β * v a) :
    v true = v false := by
  have h1 := hv true
  have h2 := hv false
  simp only [Fintype.sum_bool, W_formula, σ, pow_one] at h1 h2
  simp at h1 h2
  have hSC := S_lt_C β
  -- `(C − S)(v true − v false) = 0`
  have : (C β - S β) * (v true - v false) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (by linarith)
  · linarith

/-- A correlação euclidiana como elemento de matriz `⟨φΩ, Tⁿ φΩ⟩ / ⟨Ω, Tⁿ Ω⟩`. -/
theorem correl_reconstruida (β : ℝ) (n : ℕ) :
    correl β n = (∑ a : Bool, σ a * ∑ b : Bool, W β n a b * σ b) /
      (∑ a : Bool, 1 * ∑ b : Bool, W β n a b * 1) := by
  rw [correl, G, Z]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · simp

/-- **Lacuna = taxa de decaimento**: `Tⁿ/Cⁿ` age em `φΩ` por `e^{−m(β) n}`, `m(β) > 0`. -/
theorem lacuna_igual_taxa {β : ℝ} (hβ : 0 < β) (n : ℕ) (a : Bool) :
    (∑ b : Bool, W β n a b * σ b) / C β ^ n = rexp (-(massa β) * n) * σ a ∧ 0 < massa β := by
  refine ⟨?_, massa_pos hβ⟩
  rw [impar_autovetor, ← correl_exp hβ, correl_eq, div_pow]
  have := (C_pos β).ne'
  field_simp

end ATK.YMReconstrucao

#print axioms ATK.YMReconstrucao.positividade_reflexao
#print axioms ATK.YMReconstrucao.vacuo_autovetor
#print axioms ATK.YMReconstrucao.impar_autovetor
#print axioms ATK.YMReconstrucao.vacuo_unico
#print axioms ATK.YMReconstrucao.correl_reconstruida
#print axioms ATK.YMReconstrucao.lacuna_igual_taxa
