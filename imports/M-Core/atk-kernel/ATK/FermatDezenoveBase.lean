import ATK.FltRegular.SmallNumbers.Cyclotomic
import ATK.FltRegular.SmallNumbers.OrderOf
import ATK.FltRegular.FltRegular
import ATK.FltRegular.NumberTheory.RegularPrimes
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ComputeDegree
import ATK.PolyLista

/-!
# ATK — Último teorema de Fermat para `n = 19`: cota de Minkowski e polinômio ciclotômico

Base de `ATK.FermatDezenove` (separada para que os certificados caibam em módulos menores):

* `minkowski_dezenove`: a cota de Minkowski de `ℚ(ζ₁₉)` (grau 18, discriminante `−19¹⁷`, 9 lugares
  complexos) tem parte inteira `105933` (`piso_dezenove`, com os limites de `π` da Mathlib);
* `ciclotomico_dezenove`, `phi_poly`: `Φ₁₉` sobre `ℤ`, também como lista de coeficientes
  (`ATK.PolyLista`).
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista

namespace ATK.FermatDezenoveBase

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

instance fact_prime_dezenove : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- `Φ₁₉` sobre `ℤ`. -/
noncomputable abbrev Φ19 : ℤ[X] := X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

theorem phi_poly : Φ19 = poly [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  simp only [poly, Φ19, map_one, map_zero]
  ring

theorem piso_dezenove :
    ⌊(4 / π) ^ 9 * (18! / 18 ^ 18 * √5480386857784802185939)⌋₊ = 105933 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      (105933 : ℝ) ≤ (4 / 3.141593) ^ 9 * (18! / 18 ^ 18 * 74029634996) := by norm_num [Nat.factorial]
      _ ≤ (4 / π) ^ 9 * (18! / 18 ^ 18 * √5480386857784802185939) := by
        gcongr
        · exact pi_lt_d6.le
        · exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  · calc
      (4 / π) ^ 9 * (18! / 18 ^ 18 * √5480386857784802185939) ≤
          (4 / 3.141592) ^ 9 * (18! / 18 ^ 18 * 74029634997) := by
        gcongr
        · exact pi_gt_d6.le
        · exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ < _ := by norm_num [Nat.factorial]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {19} ℚ K]

theorem minkowski_dezenove : ⌊(M K)⌋₊ = 105933 := by
  rw [discr_prime 19 K, IsCyclotomicExtension.finrank (n := 19) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 19, totient_prime
      fact_prime_dezenove.out]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact piso_dezenove

theorem ciclotomico_dezenove : cyclotomic 19 ℤ = Φ19 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

end ATK.FermatDezenoveBase

#print axioms ATK.FermatDezenoveBase.phi_poly
#print axioms ATK.FermatDezenoveBase.piso_dezenove
#print axioms ATK.FermatDezenoveBase.minkowski_dezenove
#print axioms ATK.FermatDezenoveBase.ciclotomico_dezenove
