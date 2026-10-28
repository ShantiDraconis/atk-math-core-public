import ATK.FermatRegular

/-!
# ATK — Os expoentes de Fermat cobertos pelo kernel e o resíduo exato

Classifica todos os expoentes `n ≥ 3` segundo o que o kernel prova (`ATK.FermatRegular`):

* `flt_primos_provados`: FLT(q) para `q ∈ {3, 5, 7, 11, 13, 17, 19}`;
* `flt_de_fator`: **FLT(n) sempre que `4 ∣ n` ou `n` tem um fator primo ímpar `≤ 19`**;
* `flt_de_fator_regular`: FLT(n) sempre que `n` tem um fator primo ímpar regular (Kummer);
* `Residuo n`: `n ≥ 3`, `4 ∤ n` e todo fator primo ímpar de `n` é `≥ 23`;
  `flt_fora_do_residuo` e **`flt_iff_residuo`: `FermatLastTheorem ⟺ ∀ n, Residuo n → FLT(n)`**;
* `ResiduoIrregular n`: `n ≥ 3`, `4 ∤ n` e todo fator primo ímpar de `n` é irregular — o resíduo
  exato do método de Kummer; **`flt_iff_residuo_irregular`**.

Nenhum desses resíduos é vazio por cálculo do kernel: o método de Kummer não alcança os primos
irregulares (37, 59, 67, …, infinitos por Jensen, 1915), e para 23, 29, 31 a regularidade não está
formalizada aqui (falta calcular o grupo de classes). B2 continua `PARCIAL`.
-/

namespace ATK.FermatExpoentes

open ATK.FermatRegular

/-- Os primos ímpares com FLT provado no kernel. -/
def primosProvados : List ℕ := [3, 5, 7, 11, 13, 17, 19]

theorem flt_primos_provados {q : ℕ} (hq : q ∈ primosProvados) : FermatLastTheoremFor q := by
  simp only [primosProvados, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fermatLastTheoremThree
  · exact flt_cinco
  · exact flt_sete
  · exact flt_onze
  · exact flt_treze
  · exact flt_dezessete
  · exact flt_dezenove

/-- **FLT(n) sempre que `4 ∣ n` ou `n` tem um fator primo ímpar `≤ 19`.** -/
theorem flt_de_fator {n : ℕ} (h : 4 ∣ n ∨ ∃ q, q.Prime ∧ q ∣ n ∧ 3 ≤ q ∧ q ≤ 19) :
    FermatLastTheoremFor n := by
  rcases h with h4 | ⟨q, hq, hqn, h3, h19⟩
  · exact fermatLastTheoremFour.mono h4
  · have hmem : q ∈ primosProvados := by
      interval_cases q <;> first | (simp [primosProvados]; done) | (exfalso; norm_num at hq)
    exact (flt_primos_provados hmem).mono hqn

/-- FLT(n) sempre que `n` tem um fator primo ímpar regular. -/
theorem flt_de_fator_regular {n q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hreg : IsRegularPrime q)
    (hqn : q ∣ n) : FermatLastTheoremFor n :=
  (flt_primo_regular hq hreg hq2).mono hqn

/-- O resíduo: `n ≥ 3`, sem o fator 4, com todos os fatores primos ímpares `≥ 23`. -/
def Residuo (n : ℕ) : Prop :=
  3 ≤ n ∧ ¬ 4 ∣ n ∧ ∀ q, q.Prime → q ∣ n → q = 2 ∨ 23 ≤ q

/-- Fora do resíduo, FLT(n) está provado. -/
theorem flt_fora_do_residuo {n : ℕ} (hn : 3 ≤ n) (h : ¬ Residuo n) : FermatLastTheoremFor n := by
  apply flt_de_fator
  simp only [Residuo, not_and, not_forall, not_or, not_le] at h
  by_cases h4 : 4 ∣ n
  · exact Or.inl h4
  · obtain ⟨q, hq, hqn, hq2, hq23⟩ := h hn h4
    have h3 : 3 ≤ q := by
      have := hq.two_le
      omega
    refine Or.inr ⟨q, hq, hqn, h3, ?_⟩
    by_contra hc
    push Not at hc
    have h20 : q = 20 ∨ q = 21 ∨ q = 22 := by omega
    rcases h20 with rfl | rfl | rfl <;> norm_num at hq

/-- **`FermatLastTheorem ⟺ FLT(n)` para todo `n` do resíduo.** -/
theorem flt_iff_residuo : FermatLastTheorem ↔ ∀ n, Residuo n → FermatLastTheoremFor n := by
  constructor
  · intro h n hn
    exact h n hn.1
  · intro h n hn
    by_cases hr : Residuo n
    · exact h n hr
    · exact flt_fora_do_residuo hn hr

/-- O resíduo exato do método de Kummer: todo fator primo ímpar de `n` é irregular. -/
def ResiduoIrregular (n : ℕ) : Prop :=
  3 ≤ n ∧ ¬ 4 ∣ n ∧ ∀ q, q.Prime → q ∣ n → q = 2 ∨ ¬ IsRegularPrime q

/-- O resíduo irregular está contido no resíduo (`3, …, 19` são regulares). -/
theorem residuoIrregular_sub {n : ℕ} (h : ResiduoIrregular n) : Residuo n := by
  refine ⟨h.1, h.2.1, fun q hq hqn => ?_⟩
  rcases h.2.2 q hq hqn with h2 | hreg
  · exact Or.inl h2
  · right
    by_contra hc
    push Not at hc
    have := hq.two_le
    interval_cases q
    all_goals first
      | (exfalso; norm_num at hq; done)
      | exact (hreg isRegularPrime_two).elim
      | exact (hreg regular_tres).elim
      | exact (hreg regular_cinco).elim
      | exact (hreg regular_sete).elim
      | exact (hreg regular_onze).elim
      | exact (hreg regular_treze).elim
      | exact (hreg regular_dezessete).elim
      | exact (hreg regular_dezenove).elim

/-- **`FermatLastTheorem ⟺ FLT(n)` para todo `n` cujos fatores primos ímpares são irregulares.** -/
theorem flt_iff_residuo_irregular :
    FermatLastTheorem ↔ ∀ n, ResiduoIrregular n → FermatLastTheoremFor n := by
  constructor
  · intro h n hn
    exact h n hn.1
  · intro h n hn
    by_cases hr : ResiduoIrregular n
    · exact h n hr
    · simp only [ResiduoIrregular, not_and, not_forall, not_or, not_not] at hr
      by_cases h4 : 4 ∣ n
      · exact fermatLastTheoremFour.mono h4
      · obtain ⟨q, hq, hqn, hq2, hreg⟩ := hr hn h4
        exact flt_de_fator_regular hq hq2 hreg hqn

end ATK.FermatExpoentes

#print axioms ATK.FermatExpoentes.flt_primos_provados
#print axioms ATK.FermatExpoentes.flt_de_fator
#print axioms ATK.FermatExpoentes.flt_de_fator_regular
#print axioms ATK.FermatExpoentes.flt_fora_do_residuo
#print axioms ATK.FermatExpoentes.flt_iff_residuo
#print axioms ATK.FermatExpoentes.residuoIrregular_sub
#print axioms ATK.FermatExpoentes.flt_iff_residuo_irregular
