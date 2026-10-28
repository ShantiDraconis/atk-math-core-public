import ATK.FltRegular.SmallNumbers.SmallNumbers
import ATK.FltRegular.FltRegular
import ATK.FermatOnze
import ATK.FermatTreze
import ATK.FermatDezessete
import ATK.FermatDezenove
import Mathlib.NumberTheory.FLT.Four

/-!
# ATK — Último teorema de Fermat para primos regulares e para `n = 5, 7, 11, 13, 17, 19` (ponte B2)

`ATK/FltRegular/` é a formalização do projeto **flt-regular** (Lean 4, Apache 2.0;
<https://github.com/leanprover-community/flt-regular>, commit `faae830`, de 05/09/2026; autores
principais Riccardo Brasca, Ruben Van de Velde, Chris Birkbeck, Eric Rodriguez, Andrew Yang,
Alex J. Best e colaboradores), copiada sem mudança de conteúdo matemático: os `import` passaram
de `FltRegular.…` para `ATK.FltRegular.…`, e uma única adaptação à Mathlib v4.34.1 foi feita em
`NumberTheory/Hilbert92.lean` (`MulEquiv.Monoid.End` → `MulEquiv.monoidEnd _`, com a lista de
reescritas da versão posterior do próprio projeto). Ver `ATK/FltRegular/ORIGEM.md`.

Teoremas expostos aqui (todos com axiomas padrão):

* `flt_primo_regular`: **FLT para todo primo ímpar regular** (Kummer; casos I e II);
* `regular_tres`, `regular_cinco`, `regular_sete`: `3, 5, 7` são regulares (`𝓞(ℚ(ζₚ))` principal);
* `flt_cinco`, `flt_sete`: **FLT(5)** e **FLT(7)** (flt-regular); `flt_onze`, `flt_treze`,
  `flt_dezessete`, `flt_dezenove`: **FLT(11)**, **FLT(13)**, **FLT(17)** e **FLT(19)**
  (`ATK.FermatOnze`, `ATK.FermatTreze`, `ATK.FermatDezessete`, `ATK.FermatDezenove`:
  `𝓞(ℚ(ζₚ))` principal pela cota de Minkowski com certificados explícitos, conferidos pelo
  kernel);
* `flt_tres_a_vinte_e_dois`: FLT(n) para todo `3 ≤ n ≤ 22`;
* `flt_iff_irregulares`: **a ponte B2 (`FermatLastTheorem`) equivale a FLT para os primos
  irregulares `p ≥ 23`** — os únicos expoentes que faltam.

B2 continua `PARCIAL`: o primeiro primo irregular é 37, e FLT para primos irregulares não está
formalizado (Wiles–Taylor, via modularidade). `19` é o último primo com `𝓞(ℚ(ζₚ))` principal; a
regularidade de `23, 29, 31` pede o cálculo do número de classes (3, 8 e 9).
-/

namespace ATK.FermatRegular

/-- **FLT para primos regulares** (flt-regular). -/
theorem flt_primo_regular {p : ℕ} (hp : p.Prime) (hreg : IsRegularPrime p) (h2 : p ≠ 2) :
    FermatLastTheoremFor p :=
  @flt_regular p ⟨hp⟩ hreg h2

/-- `3` é regular. -/
theorem regular_tres : IsRegularPrime 3 := isRegularPrime_three

/-- `5` é regular. -/
theorem regular_cinco : IsRegularPrime 5 := isRegularPrime_five

/-- `7` é regular. -/
theorem regular_sete : IsRegularPrime 7 := isRegularPrime_seven

/-- **Último teorema de Fermat para `n = 5`.** -/
theorem flt_cinco : FermatLastTheoremFor 5 := fermatLastTheoremFive

/-- **Último teorema de Fermat para `n = 7`.** -/
theorem flt_sete : FermatLastTheoremFor 7 := fermatLastTheoremSeven

/-- FLT(n) para todo `3 ≤ n ≤ 10`. -/
theorem flt_tres_a_dez {n : ℕ} (h3 : 3 ≤ n) (h10 : n ≤ 10) : FermatLastTheoremFor n :=
  FLT_small (Finset.mem_Icc.mpr ⟨h3, h10⟩)

/-- `11` é regular. -/
theorem regular_onze : IsRegularPrime 11 := ATK.FermatOnze.regular_onze

/-- `13` é regular. -/
theorem regular_treze : IsRegularPrime 13 := ATK.FermatTreze.regular_treze

/-- **Último teorema de Fermat para `n = 11`.** -/
theorem flt_onze : FermatLastTheoremFor 11 := ATK.FermatOnze.flt_onze

/-- **Último teorema de Fermat para `n = 13`.** -/
theorem flt_treze : FermatLastTheoremFor 13 := ATK.FermatTreze.flt_treze

/-- `17` é regular. -/
theorem regular_dezessete : IsRegularPrime 17 := ATK.FermatDezessete.regular_dezessete

/-- **Último teorema de Fermat para `n = 17`.** -/
theorem flt_dezessete : FermatLastTheoremFor 17 := ATK.FermatDezessete.flt_dezessete

/-- `19` é regular. -/
theorem regular_dezenove : IsRegularPrime 19 := ATK.FermatDezenove.regular_dezenove

/-- **Último teorema de Fermat para `n = 19`.** -/
theorem flt_dezenove : FermatLastTheoremFor 19 := ATK.FermatDezenove.flt_dezenove

/-- **FLT(n) para todo `3 ≤ n ≤ 18`.** -/
theorem flt_tres_a_dezoito {n : ℕ} (h3 : 3 ≤ n) (h18 : n ≤ 18) : FermatLastTheoremFor n := by
  by_cases h10 : n ≤ 10
  · exact flt_tres_a_dez h3 h10
  · interval_cases n
    · exact flt_onze
    · exact fermatLastTheoremThree.mono (by norm_num)
    · exact flt_treze
    · exact flt_sete.mono (by norm_num)
    · exact flt_cinco.mono (by norm_num)
    · exact fermatLastTheoremFour.mono (by norm_num)
    · exact flt_dezessete
    · exact fermatLastTheoremThree.mono (by norm_num)

/-- **FLT(n) para todo `3 ≤ n ≤ 22`.** -/
theorem flt_tres_a_vinte_e_dois {n : ℕ} (h3 : 3 ≤ n) (h22 : n ≤ 22) : FermatLastTheoremFor n := by
  by_cases h18 : n ≤ 18
  · exact flt_tres_a_dezoito h3 h18
  · interval_cases n
    · exact flt_dezenove
    · exact fermatLastTheoremFour.mono (by norm_num)
    · exact fermatLastTheoremThree.mono (by norm_num)
    · exact flt_onze.mono (by norm_num)

/-- **A ponte B2 reduzida aos primos irregulares**: `FermatLastTheorem` ⟺ FLT(p) para todo primo
`p ≥ 23` que não é regular. -/
theorem flt_iff_irregulares :
    FermatLastTheorem ↔
      ∀ p : ℕ, p.Prime → 23 ≤ p → ¬ IsRegularPrime p → FermatLastTheoremFor p := by
  constructor
  · intro h p _ hp _
    exact h p (by omega)
  · intro h
    refine FermatLastTheorem.of_odd_primes fun p hp hodd => ?_
    have hne2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    by_cases hreg : IsRegularPrime p
    · exact flt_primo_regular hp hreg hne2
    · refine h p hp ?_ hreg
      by_contra hlt
      push Not at hlt
      have h2 := hp.two_le
      interval_cases p
      all_goals first
        | exact hne2 rfl
        | exact hreg regular_tres
        | exact hreg regular_cinco
        | exact hreg regular_sete
        | exact hreg regular_onze
        | exact hreg regular_treze
        | exact hreg regular_dezessete
        | exact hreg regular_dezenove
        | exact absurd hp (by norm_num)

end ATK.FermatRegular

#print axioms ATK.FermatRegular.flt_primo_regular
#print axioms ATK.FermatRegular.regular_tres
#print axioms ATK.FermatRegular.regular_cinco
#print axioms ATK.FermatRegular.regular_sete
#print axioms ATK.FermatRegular.flt_cinco
#print axioms ATK.FermatRegular.flt_sete
#print axioms ATK.FermatRegular.flt_tres_a_dez
#print axioms ATK.FermatRegular.regular_onze
#print axioms ATK.FermatRegular.regular_treze
#print axioms ATK.FermatRegular.flt_onze
#print axioms ATK.FermatRegular.flt_treze
#print axioms ATK.FermatRegular.regular_dezessete
#print axioms ATK.FermatRegular.flt_dezessete
#print axioms ATK.FermatRegular.regular_dezenove
#print axioms ATK.FermatRegular.flt_dezenove
#print axioms ATK.FermatRegular.flt_tres_a_dezoito
#print axioms ATK.FermatRegular.flt_tres_a_vinte_e_dois
#print axioms ATK.FermatRegular.flt_iff_irregulares
