import ATK.FltRegular.SmallNumbers.Cyclotomic
import ATK.FltRegular.SmallNumbers.OrderOf
import ATK.FltRegular.FltRegular
import ATK.FltRegular.NumberTheory.RegularPrimes
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ComputeDegree

/-!
# ATK — Último teorema de Fermat para `n = 13`

Mesmo método de `ATK.FermatOnze`, com o critério `IsCyclotomicExtension.Rat.pid6` de flt-regular:

* `minkowski_treze`: a cota de Minkowski de `ℚ(ζ₁₃)` (grau 12, discriminante `13¹¹`, 6 lugares
  complexos) tem parte inteira `306`;
* abaixo dela, os primos com classe de norma `≤ 306` são `3` (grau 3) e `53, 79, 131, 157`
  (grau 1); para cada um, `certificado_p` exibe um gerador `G` do ideal primo correspondente
  e as identidades polinomiais em `ℤ[X]` que o kernel confere por `ring` (geradores e cofatores
  calculados fora do kernel, conferidos dentro dele);
* `pid_treze`: **`𝓞(ℚ(ζ₁₃))` é principal**; `regular_treze`: `13` é regular;
  `flt_treze`: **FLT(13)**, pelo teorema de Kummer de flt-regular.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

namespace ATK.FermatTreze

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

instance fact_prime_treze : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `Φ₁₃` sobre `ℤ`. -/
noncomputable abbrev Φ13 : ℤ[X] := X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

theorem piso_treze : ⌊(4 / π) ^ 6 * (12! / 12 ^ 12 * √1792160394037)⌋₊ = 306 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      (306 : ℝ) ≤ (4 / 3.1416) ^ 6 * (12! / 12 ^ 12 * 1338715) := by norm_num [Nat.factorial]
      _ ≤ (4 / π) ^ 6 * (12! / 12 ^ 12 * √1792160394037) := by
        gcongr
        · exact pi_lt_d4.le
        · exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  · calc
      (4 / π) ^ 6 * (12! / 12 ^ 12 * √1792160394037) ≤
          (4 / 3.1415) ^ 6 * (12! / 12 ^ 12 * 1338716) := by
        gcongr
        · exact pi_gt_d4.le
        · exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ < _ := by norm_num [Nat.factorial]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K]

theorem minkowski_treze : ⌊(M K)⌋₊ = 306 := by
  rw [discr_prime 13 K, IsCyclotomicExtension.finrank (n := 13) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 13, totient_prime
      fact_prime_treze.out]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat, Int.cast_one]
  exact piso_treze

theorem ciclotomico_treze : cyclotomic 13 ℤ = Φ13 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

/-- Certificado para `p = 3` (classe de grau 3): o ideal `(3, P(θ))` é principal. -/
theorem certificado_3 :
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3 (uff fact_prime_treze.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3 : ℕ) : ℤ[X]) * A = Φ13 ∧
        (((3 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ13 ∧ P = G * QP + RP * Φ13 ∧
          G = C1 * P + C2 * ((3 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨(X ^ 3 + 2 * X + 2 : ℤ[X]),
    ((29 : ℤ[X]) - 27 * X - 19 * X ^ 2 + 5 * X ^ 3 + 9 * X ^ 4 + X ^ 5 - 3 * X ^ 6 - X ^ 7 +
      X ^ 8 + X ^ 9),
    ((-19 : ℤ[X]) - X + 31 * X ^ 2),
    ((-1 : ℤ[X]) - X + X ^ 3),
    ((1 : ℤ[X]) + X ^ 2 + X ^ 3 + 2 * X ^ 5 + X ^ 7 + 2 * X ^ 8 - X ^ 9 + 3 * X ^ 10),
    ((4 : ℤ[X]) - 3 * X),
    ((2 : ℤ[X]) + X + X ^ 2 + 2 * X ^ 3 + X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 + X ^ 7 + 3 * X ^ 8
      + X ^ 9 + 2 * X ^ 10 + 3 * X ^ 11),
    ((4 : ℤ[X]) + X - 3 * X ^ 2),
    ((1 : ℤ[X])),
    ((-1 : ℤ[X]) - X),
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 3 + 2 * X + 2 : ℤ[X])).natDegree = 3 by compute_degree!]
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ ?_
    · ext
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
      decide
    · intro h
      have := congrArg Units.val h
      simp only [ZMod.coe_unitOfCoprime, Units.val_one] at this
      exact absurd this (by decide)
  all_goals
    simp only [map_ofNat, map_intCast, Nat.cast_ofNat, Φ13]
    ring

/-- Certificado para `p = 53` (classe de grau 1): o ideal `(53, P(θ))` é principal. -/
theorem certificado_53 :
    haveI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 53 (uff fact_prime_treze.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((53 : ℕ) : ℤ[X]) * A = Φ13 ∧
        (((53 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ13 ∧ P = G * QP + RP * Φ13 ∧
          G = C1 * P + C2 * ((53 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  refine ⟨X + C (17 : ℤ),
    ((-32367902068320 : ℤ[X]) + 1903994239313 * X - 111999661136 * X ^ 2 + 6588215361 * X ^
      3 - 387542080 * X ^ 4 + 22796593 * X ^ 5 - 1340976 * X ^ 6 + 78881 * X ^ 7 - 4640
      * X ^ 8 + 273 * X ^ 9 - 16 * X ^ 10 + X ^ 11),
    ((10382157267197 : ℤ[X])),
    ((-1 : ℤ[X]) - X - X ^ 3),
    ((-1 : ℤ[X]) + 24 * X + 35 * X ^ 2 + 25 * X ^ 3 + 10 * X ^ 4 + 14 * X ^ 5 + 20 * X ^ 6 +
      29 * X ^ 7 + 16 * X ^ 8 + 23 * X ^ 9 + 7 * X ^ 10 + 36 * X ^ 11),
    ((52 : ℤ[X]) - 29 * X + 36 * X ^ 2),
    ((-1 : ℤ[X]) + 7 * X + 11 * X ^ 2 + 8 * X ^ 3 + 3 * X ^ 4 + 4 * X ^ 5 + 6 * X ^ 6 + 9 *
      X ^ 7 + 5 * X ^ 8 + 7 * X ^ 9 + 2 * X ^ 10 + 11 * X ^ 11),
    ((16 : ℤ[X]) - 9 * X + 11 * X ^ 2),
    ((-290 : ℤ[X]) + 17 * X - X ^ 2),
    ((93 : ℤ[X])),
    monic_X_add_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_add_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  all_goals
    simp only [map_ofNat, map_intCast, Nat.cast_ofNat, Φ13]
    ring

/-- Certificado para `p = 79` (classe de grau 1): o ideal `(79, P(θ))` é principal. -/
theorem certificado_79 :
    haveI : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 79 (uff fact_prime_treze.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((79 : ℕ) : ℤ[X]) * A = Φ13 ∧
        (((79 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ13 ∧ P = G * QP + RP * Φ13 ∧
          G = C1 * P + C2 * ((79 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 79) := ⟨by norm_num⟩
  refine ⟨X + C (27 : ℤ),
    ((-5360522689178540 : ℤ[X]) + 198537877376983 * X - 7353254717666 * X ^ 2 + 272342767321
      * X ^ 3 - 10086769160 * X ^ 4 + 373584043 * X ^ 5 - 13836446 * X ^ 6 + 512461 * X
      ^ 7 - 18980 * X ^ 8 + 703 * X ^ 9 - 26 * X ^ 10 + X ^ 11),
    ((1832077374782539 : ℤ[X])),
    ((-1 : ℤ[X]) - X - X ^ 2 - X ^ 4),
    ((15 : ℤ[X]) + 32 * X + 46 * X ^ 2 + 25 * X ^ 3 + 17 * X ^ 4 + 29 * X ^ 5 + 11 * X ^ 6 +
      38 * X ^ 7 + 37 * X ^ 8 - X ^ 9 + 56 * X ^ 10 + 10 * X ^ 11),
    ((94 : ℤ[X]) - 47 * X + 46 * X ^ 2 + 10 * X ^ 3),
    ((5 : ℤ[X]) + 11 * X + 16 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 + 10 * X ^ 5 + 4 * X ^ 6 + 13
      * X ^ 7 + 13 * X ^ 8 + 19 * X ^ 10 + 4 * X ^ 11),
    ((32 : ℤ[X]) - 15 * X + 15 * X ^ 2 + 4 * X ^ 3),
    ((19709 : ℤ[X]) - 730 * X + 27 * X ^ 2 - X ^ 3),
    ((-6736 : ℤ[X])),
    monic_X_add_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_add_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  all_goals
    simp only [map_ofNat, map_intCast, Nat.cast_ofNat, Φ13]
    ring

/-- Certificado para `p = 131` (classe de grau 1): o ideal `(131, P(θ))` é principal. -/
theorem certificado_131 :
    haveI : Fact (Nat.Prime 131) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 131 (uff fact_prime_treze.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((131 : ℕ) : ℤ[X]) * A = Φ13 ∧
        (((131 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ13 ∧ P = G * QP + RP * Φ13 ∧
          G = C1 * P + C2 * ((131 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  refine ⟨X + C (18 : ℤ),
    ((-60885862180325 : ℤ[X]) + 3382547898907 * X - 187919327717 * X ^ 2 + 10439962651 * X ^
      3 - 579997925 * X ^ 4 + 32222107 * X ^ 5 - 1790117 * X ^ 6 + 99451 * X ^ 7 - 5525
      * X ^ 8 + 307 * X ^ 9 - 17 * X ^ 10 + X ^ 11),
    ((8365996330121 : ℤ[X])),
    ((-1 : ℤ[X]) - X ^ 2 + X ^ 3),
    ((13 : ℤ[X]) + 5 * X + 20 * X ^ 2 + 41 * X ^ 3 + 18 * X ^ 4 + 12 * X ^ 5 + 56 * X ^ 6 +
      39 * X ^ 7 - 11 * X ^ 8 + 50 * X ^ 9 + 83 * X ^ 10 - 28 * X ^ 11),
    ((144 : ℤ[X]) - 139 * X + 28 * X ^ 2),
    ((2 : ℤ[X]) + X + 3 * X ^ 2 + 6 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + 8 * X ^ 6 + 6 * X ^ 7
      - X ^ 8 + 7 * X ^ 9 + 12 * X ^ 10 - 3 * X ^ 11),
    ((20 : ℤ[X]) - 18 * X + 3 * X ^ 2),
    ((342 : ℤ[X]) - 19 * X + X ^ 2),
    ((-47 : ℤ[X])),
    monic_X_add_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_add_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  all_goals
    simp only [map_ofNat, map_intCast, Nat.cast_ofNat, Φ13]
    ring

/-- Certificado para `p = 157` (classe de grau 1): o ideal `(157, P(θ))` é principal. -/
theorem certificado_157 :
    haveI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 157 (uff fact_prime_treze.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((157 : ℕ) : ℤ[X]) * A = Φ13 ∧
        (((157 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ13 ∧ P = G * QP + RP * Φ13 ∧
          G = C1 * P + C2 * ((157 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  refine ⟨X + C (90 : ℤ),
    ((-3103621280010989010989 : ℤ[X]) + 34484680889010989011 * X - 383163120989010989 * X ^
      2 + 4257368010989011 * X ^ 3 - 47304089010989 * X ^ 4 + 525600989011 * X ^ 5 -
      5840010989 * X ^ 6 + 64889011 * X ^ 7 - 720989 * X ^ 8 + 8011 * X ^ 9 - 89 * X ^
      10 + X ^ 11),
    ((1779145956694197522223 : ℤ[X])),
    ((-1 : ℤ[X]) - X ^ 2 + X ^ 3 - X ^ 4),
    ((11 : ℤ[X]) + 51 * X + 68 * X ^ 2 + 87 * X ^ 3 + 99 * X ^ 4 + 57 * X ^ 5 + 47 * X ^ 6 +
      82 * X ^ 7 + 38 * X ^ 8 + 35 * X ^ 9 + 124 * X ^ 10 + 48 * X ^ 11),
    ((168 : ℤ[X]) - 117 * X + 28 * X ^ 2 + 48 * X ^ 3),
    ((6 : ℤ[X]) + 29 * X + 39 * X ^ 2 + 50 * X ^ 3 + 57 * X ^ 4 + 33 * X ^ 5 + 27 * X ^ 6 +
      47 * X ^ 7 + 22 * X ^ 8 + 20 * X ^ 9 + 71 * X ^ 10 + 28 * X ^ 11),
    ((96 : ℤ[X]) - 66 * X + 15 * X ^ 2 + 28 * X ^ 3),
    ((737190 : ℤ[X]) - 8191 * X + 91 * X ^ 2 - X ^ 3),
    ((-422593 : ℤ[X])),
    monic_X_add_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_add_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  all_goals
    simp only [map_ofNat, map_intCast, Nat.cast_ofNat, Φ13]
    ring


set_option maxHeartbeats 20000000 in
variable (K) in
/-- **`𝓞(ℚ(ζ₁₃))` é principal.** -/
theorem pid_treze : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 13
  rw [minkowski_treze, ciclotomico_treze]
  intro p hple hp hpn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hple
  interval_cases p
  any_goals norm_num at hp
  all_goals first
    | exact absurd rfl hpn
    | exact Or.inr certificado_3
    | exact Or.inr certificado_53
    | exact Or.inr certificado_79
    | exact Or.inr certificado_131
    | exact Or.inr certificado_157
    | (left
       refine orderOf_lt_of (by norm_num) (fun i hi hipos ↦ ?_)
       have hmem := Finset.mem_Icc.mpr ⟨hipos, hi⟩
       fin_cases hmem <;> norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- **`13` é um primo regular.** -/
theorem regular_treze : IsRegularPrime 13 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (pid_treze (CyclotomicField _ ℚ))

/-- **Último teorema de Fermat para `n = 13`.** -/
theorem flt_treze : FermatLastTheoremFor 13 :=
  @flt_regular 13 fact_prime_treze regular_treze (by norm_num)

end ATK.FermatTreze

#print axioms ATK.FermatTreze.piso_treze
#print axioms ATK.FermatTreze.minkowski_treze
#print axioms ATK.FermatTreze.ciclotomico_treze
#print axioms ATK.FermatTreze.certificado_3
#print axioms ATK.FermatTreze.certificado_53
#print axioms ATK.FermatTreze.certificado_79
#print axioms ATK.FermatTreze.certificado_131
#print axioms ATK.FermatTreze.certificado_157
#print axioms ATK.FermatTreze.pid_treze
#print axioms ATK.FermatTreze.regular_treze
#print axioms ATK.FermatTreze.flt_treze
