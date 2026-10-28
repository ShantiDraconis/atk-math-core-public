import ATK.FltRegular.SmallNumbers.Cyclotomic
import ATK.FltRegular.SmallNumbers.OrderOf
import ATK.FltRegular.FltRegular
import ATK.FltRegular.NumberTheory.RegularPrimes
import Mathlib.Tactic.NormNum.Prime

/-!
# ATK — Último teorema de Fermat para `n = 11`

Com o teorema de Kummer de flt-regular (`flt_regular`: FLT para primos regulares) basta provar que
`11` é regular. Como em flt-regular para `n = 7`, mostramos que `𝓞(ℚ(ζ₁₁))` é principal pelo
critério `IsCyclotomicExtension.Rat.pid6` (cota de Minkowski + Kummer–Dedekind):

* `minkowski_onze`: a cota de Minkowski de `ℚ(ζ₁₁)` (grau 10, discriminante `−11⁹`, 5 lugares
  complexos) tem parte inteira `58`;
* todo primo `p ≤ 58`, `p ≠ 11`, tem classe de norma `p^f > 58`, exceto `p = 23` (`23 ≡ 1 mod 11`);
* `certificado_23`: o ideal `(23, θ − 4)` é gerado por `1 + θ + θ³` (norma 23), com as identidades
  polinomiais em `ℤ[X]` conferidas por `ring` (cofatores calculados fora do kernel);
* `pid_onze`: **`𝓞(ℚ(ζ₁₁))` é principal**; `regular_onze`; `flt_onze`: **FLT(11)**.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

namespace ATK.FermatOnze

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

instance fact_prime_onze : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem piso_onze : ⌊(4 / π) ^ 5 * (10! / 10 ^ 10 * √2357947691)⌋₊ = 58 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      (58 : ℝ) ≤ (4 / 3.15) ^ 5 * (10! / 10 ^ 10 * 48558) := by norm_num [Nat.factorial]
      _ ≤ (4 / π) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr
        · exact pi_lt_d2.le
        · exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  · calc
      (4 / π) ^ 5 * (10! / 10 ^ 10 * √2357947691) ≤ (4 / 3.1415) ^ 5 * (10! / 10 ^ 10 * 48559) := by
        gcongr
        · exact pi_gt_d4.le
        · exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ < _ := by norm_num [Nat.factorial]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K]

theorem minkowski_onze : ⌊(M K)⌋₊ = 58 := by
  rw [discr_prime 11 K, IsCyclotomicExtension.finrank (n := 11) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 11, totient_prime
      fact_prime_onze.out]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact piso_onze

theorem ciclotomico_onze : cyclotomic 11 ℤ =
    X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

/-- Certificado para `p = 23` (único primo abaixo da cota com classe de grau 1): o ideal
`(23, θ − 4)` é gerado por `1 + θ + θ³` (norma 23). -/
theorem certificado_23 :
    haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23 (uff fact_prime_onze.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23 : ℕ) : ℤ[X]) * A =
          X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 ∧
        (((23 : ℕ) : ℤ[X]) = G * Qp + Rp *
            (X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ∧
          P = G * QP + RP *
            (X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ∧
          G = C1 * P + C2 * ((23 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  refine ⟨X - C 4,
    (349525 : ℤ[X]) + 87381 * X + 21845 * X ^ 2 + 5461 * X ^ 3 + 1365 * X ^ 4 + 341 * X ^ 5 +
      85 * X ^ 6 + 21 * X ^ 7 + 5 * X ^ 8 + X ^ 9,
    60787, 1 + X + X ^ 3,
    (-2 : ℤ[X]) - 14 * X - 17 * X ^ 2 - 12 * X ^ 3 - 5 * X ^ 4 - 9 * X ^ 5 - 10 * X ^ 6 -
      16 * X ^ 7 - 6 * X ^ 8 - 15 * X ^ 9,
    (25 : ℤ[X]) - 9 * X + 15 * X ^ 2,
    (1 : ℤ[X]) + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 + 3 * X ^ 7 +
      X ^ 8 + 3 * X ^ 9,
    (-5 : ℤ[X]) + 2 * X - 3 * X ^ 2,
    17 + 4 * X + X ^ 2, 3, monic_X_sub_C 4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  all_goals
    simp only [map_ofNat, Nat.cast_ofNat]
    ring

variable (K) in
/-- **`𝓞(ℚ(ζ₁₁))` é principal** (cota de Minkowski `58`; só `23` precisa de certificado). -/
theorem pid_onze : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 11
  rw [minkowski_onze, ciclotomico_onze]
  intro p hple hp hpn
  fin_cases hple
  any_goals norm_num at hp
  all_goals simp only [reduceAdd]
  all_goals first
    | exact absurd rfl hpn
    | exact Or.inr certificado_23
    | (left
       refine orderOf_lt_of (by norm_num) (fun i hi hipos ↦ ?_)
       have hmem := Finset.mem_Icc.mpr ⟨hipos, hi⟩
       fin_cases hmem <;> norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- **`11` é um primo regular.** -/
theorem regular_onze : IsRegularPrime 11 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (pid_onze (CyclotomicField _ ℚ))

/-- **Último teorema de Fermat para `n = 11`.** -/
theorem flt_onze : FermatLastTheoremFor 11 :=
  @flt_regular 11 fact_prime_onze regular_onze (by norm_num)

end ATK.FermatOnze

#print axioms ATK.FermatOnze.piso_onze
#print axioms ATK.FermatOnze.minkowski_onze
#print axioms ATK.FermatOnze.ciclotomico_onze
#print axioms ATK.FermatOnze.certificado_23
#print axioms ATK.FermatOnze.pid_onze
#print axioms ATK.FermatOnze.regular_onze
#print axioms ATK.FermatOnze.flt_onze
