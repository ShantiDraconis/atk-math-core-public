import ATK.FltRegular.SmallNumbers.Cyclotomic
import ATK.FltRegular.SmallNumbers.OrderOf
import ATK.FltRegular.FltRegular
import ATK.FltRegular.NumberTheory.RegularPrimes
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ComputeDegree
import ATK.PolyLista

/-!
# ATK — Último teorema de Fermat para `n = 17`

Mesmo método de `ATK.FermatOnze` e `ATK.FermatTreze` (critério `pid6` de flt-regular):

* `minkowski_dezessete`: a cota de Minkowski de `ℚ(ζ₁₇)` (grau 16, discriminante `17¹⁵`, 8
  lugares complexos) tem parte inteira `13254`;
* `excecoes`: conferido pelo kernel (`decide +kernel`, sem `native_decide`), todo `p < 13255` com
  algum `pⁱ ≤ 13254`, `pⁱ ≡ 1 (mód 17)`, `i ≥ 1`, está na lista `primosCertificados` (103 primos:
  `2` com classe de grau 8, `67` e `101` com grau 2 e os 100 primos `≡ 1 (mód 17)` até 13254), é
  `1`, ou tem um divisor primo `≤ 115`;
* `certificado_p` para cada um dos 103 primos: um gerador do ideal primo e as identidades
  polinomiais em `ℤ[X]`, reduzidas por `ATK.PolyLista` a igualdades de listas de inteiros que o
  kernel confere por cálculo (geradores achados fora do kernel por redução de reticulados);
* **`pid_dezessete`**: `𝓞(ℚ(ζ₁₇))` é principal; `regular_dezessete`; **`flt_dezessete`: FLT(17)**.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista

namespace ATK.FermatDezessete

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

instance fact_prime_dezessete : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `Φ₁₇` sobre `ℤ`. -/
noncomputable abbrev Φ17 : ℤ[X] := X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

theorem phi_poly : Φ17 = poly [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  simp only [poly, Φ17, map_one, map_zero]
  ring

theorem piso_dezessete :
    ⌊(4 / π) ^ 8 * (16! / 16 ^ 16 * √2862423051509815793)⌋₊ = 13254 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      (13254 : ℝ) ≤ (4 / 3.141593) ^ 8 * (16! / 16 ^ 16 * 1691869691) := by norm_num [Nat.factorial]
      _ ≤ (4 / π) ^ 8 * (16! / 16 ^ 16 * √2862423051509815793) := by
        gcongr
        · exact pi_lt_d6.le
        · exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  · calc
      (4 / π) ^ 8 * (16! / 16 ^ 16 * √2862423051509815793) ≤
          (4 / 3.141592) ^ 8 * (16! / 16 ^ 16 * 1691869692) := by
        gcongr
        · exact pi_gt_d6.le
        · exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ < _ := by norm_num [Nat.factorial]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {17} ℚ K]

theorem minkowski_dezessete : ⌊(M K)⌋₊ = 13254 := by
  rw [discr_prime 17 K, IsCyclotomicExtension.finrank (n := 17) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 17, totient_prime
      fact_prime_dezessete.out]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, one_mul, Int.cast_ofNat, abs_ofNat]
  exact piso_dezessete

theorem ciclotomico_dezessete : cyclotomic 17 ℤ = Φ17 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

/-- Os 103 primos com certificado. -/
def primosCertificados : List ℕ := [2, 67, 101, 103, 137, 239, 307, 409, 443, 613, 647, 919, 953, 1021, 1123, 1259, 1327, 1361, 1429, 1531, 1667, 1871, 1973, 2143, 2347, 2381, 2551, 2687, 2789, 2857, 3061, 3163, 3299, 3469, 3571, 3673, 3877, 3911, 4013, 4217, 4421, 4523, 4591, 4931, 4999, 5101, 5237, 5407, 5441, 5849, 6053, 6121, 6257, 6359, 6427, 6529, 6563, 6733, 6869, 6971, 7039, 7243, 7481, 7549, 7583, 7753, 8059, 8093, 8161, 8263, 8297, 8467, 8501, 8807, 9011, 9181, 9283, 9419, 9521, 9623, 9929, 10099, 10133, 10303, 10337, 10711, 10847, 10949, 11119, 11527, 11731, 11833, 11867, 11969, 12037, 12071, 12241, 12343, 12377, 12479, 12547, 12853, 13159]

/-- Os primos até `115 = ⌊√13254⌋`. -/
def primosPequenos : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

/-- `p` tem alguma potência `pⁱ ≤ 13254`, `i ≥ 1`, congruente a `1` módulo 17. -/
def condicao (p : ℕ) : Bool :=
  (List.range 15).any fun i => decide (1 ≤ i) && decide (p ^ i ≤ 13254) && decide (p ^ i % 17 = 1)

/-- O teste conferido pelo kernel. -/
def teste (p : ℕ) : Bool :=
  !(condicao p) || primosCertificados.contains p || p == 1 ||
    primosPequenos.any fun q => decide (q < p) && decide (p % q = 0)

theorem teste_0 : ∀ p, 0 ≤ p → p < 1000 → teste p = true := by
  decide +kernel

theorem teste_1 : ∀ p, 1000 ≤ p → p < 2000 → teste p = true := by
  decide +kernel

theorem teste_2 : ∀ p, 2000 ≤ p → p < 3000 → teste p = true := by
  decide +kernel

theorem teste_3 : ∀ p, 3000 ≤ p → p < 4000 → teste p = true := by
  decide +kernel

theorem teste_4 : ∀ p, 4000 ≤ p → p < 5000 → teste p = true := by
  decide +kernel

theorem teste_5 : ∀ p, 5000 ≤ p → p < 6000 → teste p = true := by
  decide +kernel

theorem teste_6 : ∀ p, 6000 ≤ p → p < 7000 → teste p = true := by
  decide +kernel

theorem teste_7 : ∀ p, 7000 ≤ p → p < 8000 → teste p = true := by
  decide +kernel

theorem teste_8 : ∀ p, 8000 ≤ p → p < 9000 → teste p = true := by
  decide +kernel

theorem teste_9 : ∀ p, 9000 ≤ p → p < 10000 → teste p = true := by
  decide +kernel

theorem teste_10 : ∀ p, 10000 ≤ p → p < 11000 → teste p = true := by
  decide +kernel

theorem teste_11 : ∀ p, 11000 ≤ p → p < 12000 → teste p = true := by
  decide +kernel

theorem teste_12 : ∀ p, 12000 ≤ p → p < 13000 → teste p = true := by
  decide +kernel

theorem teste_13 : ∀ p, 13000 ≤ p → p < 13255 → teste p = true := by
  decide +kernel

/-- **Exceções**: `teste p` vale para todo `p ≤ 13254`. -/
theorem excecoes (p : ℕ) (hp : p ≤ 13254) : teste p = true := by
  rcases lt_or_ge p 1000 with h0 | h0
  · exact teste_0 p (by omega) h0
  rcases lt_or_ge p 2000 with h1 | h1
  · exact teste_1 p (by omega) h1
  rcases lt_or_ge p 3000 with h2 | h2
  · exact teste_2 p (by omega) h2
  rcases lt_or_ge p 4000 with h3 | h3
  · exact teste_3 p (by omega) h3
  rcases lt_or_ge p 5000 with h4 | h4
  · exact teste_4 p (by omega) h4
  rcases lt_or_ge p 6000 with h5 | h5
  · exact teste_5 p (by omega) h5
  rcases lt_or_ge p 7000 with h6 | h6
  · exact teste_6 p (by omega) h6
  rcases lt_or_ge p 8000 with h7 | h7
  · exact teste_7 p (by omega) h7
  rcases lt_or_ge p 9000 with h8 | h8
  · exact teste_8 p (by omega) h8
  rcases lt_or_ge p 10000 with h9 | h9
  · exact teste_9 p (by omega) h9
  rcases lt_or_ge p 11000 with h10 | h10
  · exact teste_10 p (by omega) h10
  rcases lt_or_ge p 12000 with h11 | h11
  · exact teste_11 p (by omega) h11
  rcases lt_or_ge p 13000 with h12 | h12
  · exact teste_12 p (by omega) h12
  exact teste_13 p (by omega) (by omega)

set_option maxHeartbeats 4000000 in
theorem certificado_2 :
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hP : poly [1, 0, 0, 1, 1, 1, 0, 0, 1] = (X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2 : ℕ) : ℤ[X]) = poly [2] := by simp [poly]
  refine ⟨(X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + 1 : ℤ[X]),
    poly [1, 1, 1, 0, 1, 0, 1, 1, 1],
    poly [0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    poly [-1, 0, 0, -1, -1, -1, 0, 0, -1],
    poly [-1, 0, -1, -1, -1, -1, -1, -1, 0, -1, 0, -1, -1, -2, -1, -1],
    poly [1, -1, -1, -1, 0, -1, 0, -1],
    poly [-1],
    poly [],
    poly [1],
    poly [-1, 0, 0, -1, -1, -1, 0, 0, -1],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + 1 : ℤ[X])).natDegree = 8 by compute_degree!]
    refine (orderOf_eq_iff (by norm_num)).mpr ⟨?_, fun m hm hm0 => ?_⟩
    · ext
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
      decide
    · intro h
      have h' := congrArg Units.val h
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h'
      interval_cases m <;> exact absurd h' (by decide)
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_67 :
    haveI : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 67 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((67 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((67 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((67 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  have hP : poly [1, 4, 1] = (X ^ 2 + 4 * X + 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((67 : ℕ) : ℤ[X]) = poly [67] := by simp [poly]
  refine ⟨(X ^ 2 + 4 * X + 1 : ℤ[X]),
    poly [1, -3, 12, 23, 31, -12, 18, 8, 18, -12, 31, 23, 12, -3, 1],
    poly [0, 0, 0, -1, -2, -2, 0, -1, -1, -1, 0, -2, -2, -1],
    poly [-1, 0, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0, -1, -1],
    poly [-10, 9, 10, -13, 11, 5, 5, 11, -13, 10, 9, -10, 0, -21, -14, -21],
    poly [57, -48, -9, -14, 34, -9, -8, 20, -5, -10, 14, 0, -14, -21],
    poly [1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1],
    poly [2, 3, -1, 0, 1, 2, 1, 0, 1, 1, 1, 1],
    poly [-1, 4, -16, -8, -20, 21, 2, -29, -20, -26, -11, 3, -1],
    poly [0, 0, 0, 1, 1, 1, -1, 0, 2, 2, 2, 1],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 2 + 4 * X + 1 : ℤ[X])).natDegree = 2 by compute_degree!]
    refine (orderOf_eq_iff (by norm_num)).mpr ⟨?_, fun m hm hm0 => ?_⟩
    · ext
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
      decide
    · intro h
      have h' := congrArg Units.val h
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h'
      interval_cases m <;> exact absurd h' (by decide)
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_101 :
    haveI : Fact (Nat.Prime 101) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 101 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((101 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((101 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((101 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  have hP : poly [1, 8, 1] = (X ^ 2 + 8 * X + 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((101 : ℕ) : ℤ[X]) = poly [101] := by simp [poly]
  refine ⟨(X ^ 2 + 8 * X + 1 : ℤ[X]),
    poly [1, -7, -45, -36, 31, -9, 42, -23, 42, -9, 31, -36, -45, -7, 1],
    poly [0, 0, 1, 4, 3, -2, 0, -3, 1, -3, 0, -2, 3, 4, 1],
    poly [-1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, -1],
    poly [-27, -38, -24, -24, -38, -27, 0, -25, -54, 1, -6, -5, -6, 1, -54, -25],
    poly [74, -112, 14, -27, -25, 25, 54, -28, -32, 55, -29, -25],
    poly [2, 0, -1, 0, 0, -1, 0, 2, 0, -2, 2, 2, 2, 2, 2, -2],
    poly [3, 5, -8, 2, -2, -2, 0, 4, -2, 0, 4, -2],
    poly [-1, 8, 38, -10, 42, -23, 42, -10, 38, 8, -1],
    poly [0, 0, -1, -3, 0, -3, 1, -3, 0, -3, -1],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 2 + 8 * X + 1 : ℤ[X])).natDegree = 2 by compute_degree!]
    refine (orderOf_eq_iff (by norm_num)).mpr ⟨?_, fun m hm hm0 => ?_⟩
    · ext
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
      decide
    · intro h
      have h' := congrArg Units.val h
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h'
      interval_cases m <;> exact absurd h' (by decide)
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_103 :
    haveI : Fact (Nat.Prime 103) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 103 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((103 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((103 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((103 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 103) := ⟨by norm_num⟩
  have hP : poly [-8, 1] = X - C (8 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((103 : ℕ) : ℤ[X]) = poly [103] := by simp [poly]
  refine ⟨X - C (8 : ℤ),
    poly [-13, 24, -10, -40, -18, -41, -31, -4, 38, -34, -43, 46, -33, -30, 9, 1],
    poly [-1, 2, -1, -3, -1, -3, -2, 0, 3, -3, -3, 4, -3, -2, 1],
    poly [0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-31, -22, -8, -32, -35, -74, -66, -65, -52, -89, -55, -25, -47, -24, -34, -61],
    poly [103, -103, -31, 9, 14, -24, -3, -39, -23, 10, 27, -61],
    poly [3, 2, 1, 3, 3, 6, 5, 5, 4, 7, 4, 2, 4, 2, 3, 5],
    poly [-8, 9, 2, -1, -1, 2, 0, 3, 2, -1, -2, 5],
    poly [0, 0, 13, -37, 34, 30, -22, 23, 3, 39, -8, -1],
    poly [0, 0, 1, -3, 3, 2, -2, 2, 0, 3, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_137 :
    haveI : Fact (Nat.Prime 137) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 137 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((137 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((137 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((137 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 137) := ⟨by norm_num⟩
  have hP : poly [-16, 1] = X - C (16 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((137 : ℕ) : ℤ[X]) = poly [137] := by simp [poly]
  refine ⟨X - C (16 : ℤ),
    poly [-60, 39, -49, 14, -42, 23, -50, -46, 57, -65, 13, 35, -15, -1, 17, 1],
    poly [-7, 5, -6, 2, -5, 3, -6, -5, 7, -8, 2, 4, -2, 0, 2],
    poly [-1, 0, 0, 1, 0, 0, 0, -1],
    poly [-36, -4, -2, -19, -80, -41, -30, -55, -48, -39, -47, 21, -9, -28, 65, 28],
    poly [101, -105, 2, 19, -93, 37, 28],
    poly [4, 0, 0, 2, 9, 4, 3, 6, 5, 4, 5, -3, 1, 3, -8, -3],
    poly [-12, 13, -1, -2, 11, -5, -3],
    poly [60, 38, -49, 14, 18, -16, -1],
    poly [7, 4, -6, 2, 2, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_239 :
    haveI : Fact (Nat.Prime 239) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 239 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((239 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((239 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((239 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 239) := ⟨by norm_num⟩
  have hP : poly [-6, 1] = X - C (6 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((239 : ℕ) : ℤ[X]) = poly [239] := by simp [poly]
  refine ⟨X - C (6 : ℤ),
    poly [-40, 33, 85, 14, 42, -33, 74, 52, -111, 61, 10, -118, 20, 43, 7, 1],
    poly [-1, 1, 2, 0, 1, -1, 2, 1, -3, 2, 0, -3, 1, 1],
    poly [-1, 0, 0, -1, 0, 0, 0, 0, 0, -1],
    poly [-111, -10, -33, 3, 9, 10, 50, -23, -75, -4, -32, 43, -64, -42, -118, -51],
    poly [128, -138, -23, -75, 107, -22, 76, -67, -51],
    poly [3, 0, 1, 0, 0, 0, -1, 1, 2, 0, 1, -1, 2, 1, 3, 1],
    poly [-3, 4, 0, 2, -3, 1, -2, 2, 1],
    poly [40, -73, -52, 111, -101, 23, -36, -6, -1],
    poly [1, -2, -1, 3, -3, 1, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_307 :
    haveI : Fact (Nat.Prime 307) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 307 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((307 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((307 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((307 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 307) := ⟨by norm_num⟩
  have hP : poly [-9, 1] = X - C (9 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((307 : ℕ) : ℤ[X]) = poly [307] := by simp [poly]
  refine ⟨X - C (9 : ℤ),
    poly [34, 106, 114, 149, -120, 123, 150, 153, 51, 142, 118, 13, -101, 91, 10, 1],
    poly [1, 3, 3, 4, -4, 4, 4, 4, 1, 4, 3, 0, -3, 3],
    poly [-1, 0, 0, 1, -1],
    poly [-9, -10, 24, 96, 104, 139, 177, 113, 140, 143, 41, 132, 108, 3, 196, 81],
    poly [298, -308, 34, 81],
    poly [0, 0, -1, -3, -3, -4, -5, -3, -4, -4, -1, -4, -3, 0, -6, -2],
    poly [-9, 10, -2, -2],
    poly [-34, -72, -8, -1],
    poly [-1, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 19 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 18 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_409 :
    haveI : Fact (Nat.Prime 409) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 409 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((409 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((409 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((409 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 409) := ⟨by norm_num⟩
  have hP : poly [-5, 1] = X - C (5 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((409 : ℕ) : ℤ[X]) = poly [409] := by simp [poly]
  refine ⟨X - C (5 : ℤ),
    poly [-82, 147, 111, 22, 86, 17, 85, -65, -95, -101, -184, -37, 156, 31, 6, 1],
    poly [-1, 2, 1, 0, 1, 0, 1, -1, -1, -1, -2, 0, 2],
    poly [1, 1, 0, 0, 0, 0, 0, -1],
    poly [-47, -220, -91, -147, -240, -95, -66, -142, -239, -13, -295, -106, -150, -77, -226, -174],
    poly [456, -189, 44, -73, 149, -52, -174],
    poly [1, 3, 1, 2, 3, 1, 1, 2, 3, 0, 4, 1, 2, 1, 3, 2],
    poly [-6, 3, -1, 1, -2, 1, 2],
    poly [-82, 147, 193, -125, -25, -5, -1],
    poly [-1, 2, 2, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_443 :
    haveI : Fact (Nat.Prime 443) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 443 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((443 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((443 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((443 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 443) := ⟨by norm_num⟩
  have hP : poly [-13, 1] = X - C (13 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((443 : ℕ) : ℤ[X]) = poly [443] := by simp [poly]
  refine ⟨X - C (13 : ℤ),
    poly [34, 207, 84, -164, -149, -216, -153, -80, 96, -129, -10, -69, 165, 183, 14, 1],
    poly [1, 6, 2, -5, -4, -6, -4, -2, 3, -4, 0, -2, 5, 5],
    poly [-1, -1, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-71, 128, 7, 134, 246, -18, 98, 141, 8, 100, 73, 105, -97, 126, 75, 37],
    poly [372, -315, 78, 6, 239, -223, 51, 38, 37],
    poly [2, -4, 0, -4, -7, 1, -3, -4, 0, -3, -2, -3, 3, -4, -2, -1],
    poly [-11, 10, -3, 0, -7, 7, -2, -1, -1],
    poly [-34, -207, -50, -72, -210, 18, -169, -13, -1],
    poly [-1, -6, -1, -2, -6, 1, -5],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_613 :
    haveI : Fact (Nat.Prime 613) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 613 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((613 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((613 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((613 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 613) := ⟨by norm_num⟩
  have hP : poly [-37, 1] = X - C (37 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((613 : ℕ) : ℤ[X]) = poly [613] := by simp [poly]
  refine ⟨X - C (37 : ℤ),
    poly [-116, -86, -284, 42, -148, -120, 63, -164, -137, -70, -267, 175, -45, 181, 38, 1],
    poly [-7, -5, -17, 3, -9, -7, 4, -10, -8, -4, -16, 11, -3, 11, 2],
    poly [1, 0, 0, -1, 0, 0, 0, 0, 0, -1],
    poly [267, -24, -65, 83, 87, -62, -182, -3, -81, 66, -46, -165, 130, 22, -246, -71],
    poly [346, -322, 41, 119, -295, 108, 268, -175, -71],
    poly [-16, 2, 4, -5, -5, 4, 11, 0, 5, -4, 3, 10, -8, -1, 15, 4],
    poly [-21, 20, -3, -7, 18, -7, -16, 11, 4],
    poly [-116, 30, -198, -171, -220, 226, -143, -37, -1],
    poly [-7, 2, -12, -10, -13, 14, -9, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_647 :
    haveI : Fact (Nat.Prime 647) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 647 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((647 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((647 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((647 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 647) := ⟨by norm_num⟩
  have hP : poly [-43, 1] = X - C (43 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((647 : ℕ) : ℤ[X]) = poly [647] := by simp [poly]
  refine ⟨X - C (43 : ℤ),
    poly [-316, 113, -193, 161, 94, 273, -99, 103, -118, -78, 269, -69, -122, -48, 44, 1],
    poly [-21, 8, -13, 11, 6, 18, -7, 7, -8, -5, 18, -5, -8, -3, 3],
    poly [-1, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-278, -134, 80, -231, -163, -26, -83, 21, -112, -85, 36, 99, -50, 97, -35, -339],
    poly [369, -503, -64, -167, 282, -174, 11, 241, -190, -147, 132, 304, -339],
    poly [19, 9, -5, 16, 11, 2, 6, -1, 8, 6, -2, -6, 4, -6, 3, 23],
    poly [-24, 34, 4, 11, -19, 12, -1, -16, 13, 10, -9, -20, 23],
    poly [316, 218, -25, -136, -274, 114, -208, 266, -54, 74, 92, -43, -1],
    poly [21, 14, -2, -9, -18, 8, -14, 18, -4, 5, 6, -3],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_919 :
    haveI : Fact (Nat.Prime 919) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 919 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((919 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((919 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((919 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 919) := ⟨by norm_num⟩
  have hP : poly [-58, 1] = X - C (58 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((919 : ℕ) : ℤ[X]) = poly [919] := by simp [poly]
  refine ⟨X - C (58 : ℤ),
    poly [-206, -368, 263, -249, -36, -270, 233, 4, -301, 280, -423, -39, 31, -253, 59, 1],
    poly [-13, -23, 17, -16, -2, -17, 15, 0, -19, 18, -27, -2, 2, -16, 4],
    poly [1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
    poly [302, 22, 239, -90, 142, 146, 51, -220, 13, 223, 290, 307, 133, 130, 431, -55],
    poly [617, -639, -217, 27, 48, -221, 122, 17, -174, -3, 301, -486, 55],
    poly [-19, -1, -15, 6, -9, -9, -3, 14, -1, -14, -18, -19, -8, -8, -27, 4],
    poly [-39, 41, 13, -2, -3, 14, -8, -1, 11, 0, -19, 31, -4],
    poly [-206, -162, -288, 201, 51, 397, -215, -384, -70, 284, -312, 58, 1],
    poly [-13, -10, -18, 13, 3, 25, -14, -24, -4, 18, -20, 4],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_953 :
    haveI : Fact (Nat.Prime 953) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 953 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((953 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((953 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((953 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 953) := ⟨by norm_num⟩
  have hP : poly [-16, 1] = X - C (16 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((953 : ℕ) : ℤ[X]) = poly [953] := by simp [poly]
  refine ⟨X - C (16 : ℤ),
    poly [-417, 93, 244, 313, -457, -386, -322, -318, 397, 263, -341, 336, -396, 273, 17, 1],
    poly [-7, 2, 4, 5, -8, -6, -5, -5, 7, 4, -6, 6, -7, 5],
    poly [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
    poly [248, -213, 56, -225, -183, 177, -277, 52, 13, -49, -172, -1, -169, 297, 207, -156],
    poly [705, -492, -269, 33, 171, -168, 466, -90, -363, 156],
    poly [-4, 4, -1, 4, 3, -3, 5, -1, 0, 1, 3, 0, 3, -5, -3, 3],
    poly [-12, 9, 4, -1, -3, 3, -8, 2, 6, -3],
    poly [-417, -443, 151, -348, 276, -221, 284, 256, 16, 1],
    poly [-7, -7, 3, -6, 5, -4, 5, 4],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1021 :
    haveI : Fact (Nat.Prime 1021) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1021 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1021 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1021 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1021 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1021) := ⟨by norm_num⟩
  have hP : poly [-9, 1] = X - C (9 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1021 : ℕ) : ℤ[X]) = poly [1021] := by simp [poly]
  refine ⟨X - C (9 : ℤ),
    poly [-227, 315, -192, 92, 237, 480, 507, 510, 170, -435, 65, 234, -201, 91, 10, 1],
    poly [-2, 3, -2, 1, 2, 4, 4, 4, 1, -4, 1, 2, -2, 1],
    poly [-1, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, -1],
    poly [-345, -43, 104, -220, -256, -260, -147, -21, -7, 108, -333, -382, -274, -262, -601, 42],
    poly [676, -719, 147, -669, 266, -202, 91, -108, -12, 339, -643, 42],
    poly [3, 0, -1, 2, 2, 2, 1, 0, 0, -1, 3, 3, 2, 2, 5, -1],
    poly [-6, 7, -2, 6, -3, 2, -1, 1, 0, -3, 6, -1],
    poly [227, 479, 507, -57, 334, 491, 168, -435, 292, -81, -9, -1],
    poly [2, 4, 4, -1, 3, 4, 1, -4, 3, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1123 :
    haveI : Fact (Nat.Prime 1123) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1123 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1123 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1123 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1123 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1123) := ⟨by norm_num⟩
  have hP : poly [-6, 1] = X - C (6 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1123 : ℕ) : ℤ[X]) = poly [1123] := by simp [poly]
  refine ⟨X - C (6 : ℤ),
    poly [187, 31, 5, 375, -312, 135, -352, -246, 146, -163, 347, 432, 259, 43, 7, 1],
    poly [1, 0, 0, 2, -2, 1, -2, -1, 1, -1, 2, 2, 1],
    poly [-1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1],
    poly [-331, -199, -177, 201, 264, -287, -566, -51, 222, -294, -380, -20, 40, 50, -697, -260],
    poly [792, -1322, 154, 69, 573, -797, -320, -10, 747, -437, -260],
    poly [2, 1, 1, -1, -1, 2, 3, 0, -1, 2, 2, 0, 0, 0, 4, 1],
    poly [-4, 8, -2, 0, -3, 5, 1, 0, -4, 3, 1],
    poly [-187, -31, 182, -531, 473, 79, -174, -216, -36, -6, -1],
    poly [-1, 0, 1, -3, 3, 0, -1, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1259 :
    haveI : Fact (Nat.Prime 1259) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1259 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1259 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1259 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1259 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1259) := ⟨by norm_num⟩
  have hP : poly [-51, 1] = X - C (51 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1259 : ℕ) : ℤ[X]) = poly [1259] := by simp [poly]
  refine ⟨X - C (51 : ℤ),
    poly [-395, -304, 389, -338, -451, 238, 449, -559, 384, 205, 4, -74, 591, 135, 52, 1],
    poly [-16, -12, 16, -14, -18, 10, 18, -23, 16, 8, 0, -3, 24, 5, 2],
    poly [1, -1, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [634, 523, 743, 772, 896, 775, 822, 502, 2, 165, 341, 616, 967, 1122, 656, 400],
    poly [625, -514, -331, 191, -95, 245, 466, 256, 400],
    poly [-26, -21, -30, -31, -36, -31, -33, -20, 0, -7, -14, -25, -39, -45, -26, -16],
    poly [-25, 21, 13, -8, 4, -10, -19, -10, -16],
    poly [-395, 486, 602, -161, 614, -457, -83, -51, -1],
    poly [-16, 20, 24, -7, 25, -19, -3, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1327 :
    haveI : Fact (Nat.Prime 1327) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1327 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1327 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1327 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1327 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1327) := ⟨by norm_num⟩
  have hP : poly [-111, 1] = X - C (111 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1327 : ℕ) : ℤ[X]) = poly [1327] := by simp [poly]
  refine ⟨X - C (111 : ℤ),
    poly [263, 98, -298, 344, 27, -203, 572, -222, 261, 624, -628, -448, -16, 490, 112, 1],
    poly [22, 8, -25, 29, 2, -17, 48, -19, 22, 52, -53, -37, -1, 41, 9],
    poly [-1, 0, 0, 0, -1, 0, 0, -1, 0, -1],
    poly [-515, -424, -471, -53, 154, 120, -227, -529, -723, -127, -289, -147, -337, -793, -295, 104],
    poly [812, -1236, -47, 418, -308, 57, -394, -399, 104],
    poly [43, 35, 39, 4, -13, -10, 19, 44, 60, 10, 24, 12, 28, 66, 24, -9],
    poly [-68, 104, 3, -35, 26, -5, 33, 33, -9],
    poly [-263, 165, 396, -642, 54, 395, -379, -111, -1],
    poly [-22, 14, 33, -54, 5, 33, -32, -9],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1361 :
    haveI : Fact (Nat.Prime 1361) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1361 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1361 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1361 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1361 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1361) := ⟨by norm_num⟩
  have hP : poly [-46, 1] = X - C (46 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1361 : ℕ) : ℤ[X]) = poly [1361] := by simp [poly]
  refine ⟨X - C (46 : ℤ),
    poly [-503, -366, 495, -581, -131, 293, -112, 323, 7, 296, 36, -88, 146, -559, 47, 1],
    poly [-17, -12, 17, -20, -4, 10, -4, 11, 0, 10, 1, -3, 5, -19, 2],
    poly [-1, 0, -1, 0, 0, 0, 0, 1, -1],
    poly [63, 449, -16, 181, -81, 150, 658, 314, 129, -378, 469, 517, 163, 392, -106, -176],
    poly [1424, -975, -402, 583, -727, 428, 246, -176],
    poly [-2, -15, 1, -6, 3, -5, -22, -10, -4, 13, -16, -17, -5, -13, 4, 6],
    poly [-48, 34, 13, -20, 25, -15, -8, 6],
    poly [503, -137, -358, -422, 50, 652, -45, -1],
    poly [17, -5, -12, -14, 2, 22, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1429 :
    haveI : Fact (Nat.Prime 1429) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1429 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1429 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1429 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1429 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1429) := ⟨by norm_num⟩
  have hP : poly [-301, 1] = X - C (301 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1429 : ℕ) : ℤ[X]) = poly [1429] := by simp [poly]
  refine ⟨X - C (301 : ℤ),
    poly [470, -364, 70, 437, -573, -301, 469, 106, 665, -558, -206, 118, -688, -553, 302, 1],
    poly [99, -77, 15, 92, -121, -63, 99, 22, 140, -118, -43, 25, -145, -116, 64],
    poly [-1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1],
    poly [85, 147, -413, -149, 94, 204, -52, 232, -351, -709, 358, 447, 58, -24, -67, 137],
    poly [1514, -1367, -560, 264, 243, 110, -256, 284, -498, -211, 569, -122, 180, -204, 137],
    poly [-18, -31, 87, 31, -20, -43, 11, -49, 74, 149, -76, -94, -12, 5, 14, -29],
    poly [-319, 289, 117, -56, -51, -23, 54, -60, 105, 44, -120, 26, -38, 43, -29],
    poly [-470, -595, -434, -367, -419, -272, 659, 363, 400, 158, 48, -166, -575, -301, -1],
    poly [-99, -125, -91, -77, -88, -57, 139, 76, 84, 33, 10, -35, -121, -63],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1531 :
    haveI : Fact (Nat.Prime 1531) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1531 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1531 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1531 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1531 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1531) := ⟨by norm_num⟩
  have hP : poly [-45, 1] = X - C (45 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1531 : ℕ) : ℤ[X]) = poly [1531] := by simp [poly]
  refine ⟨X - C (45 : ℤ),
    poly [34, 409, -93, 134, 71, 682, -189, 336, -673, -49, 169, 412, -195, 540, 46, 1],
    poly [1, 12, -3, 4, 2, 20, -6, 10, -20, -1, 5, 12, -6, 16, 1],
    poly [-1, -1, 0, -1, 0, 0, -1, -1],
    poly [364, 236, -5, 534, 580, 547, 138, 265, 540, 376, -172, 88, 434, 918, -228, 461],
    poly [1895, -1295, -369, 662, 457, -228, 461],
    poly [-11, -7, 0, -16, -17, -16, -4, -8, -16, -11, 5, -3, -13, -27, 7, -14],
    poly [-56, 39, 10, -20, -13, 7, -14],
    poly [-34, -409, 127, 241, -539, -46, -1],
    poly [-1, -12, 4, 7, -16, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1667 :
    haveI : Fact (Nat.Prime 1667) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1667 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1667 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1667 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1667 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1667) := ⟨by norm_num⟩
  have hP : poly [-415, 1] = X - C (415 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1667 : ℕ) : ℤ[X]) = poly [1667] := by simp [poly]
  refine ⟨X - C (415 : ℤ),
    poly [715, -408, 710, -167, 96, 422, 712, 70, 675, -147, 799, -456, 23, -727, 416, 1],
    poly [178, -102, 177, -42, 24, 105, 177, 17, 168, -37, 199, -114, 6, -181, 104],
    poly [0, -1, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1],
    poly [-4, -478, 31, -498, -672, 380, 17, -490, 276, -638, -592, -142, -161, 88, 422, -7],
    poly [1667, -1671, -474, 509, -529, -174, 1048, -837, -2, -237, -583, 95, 422, -7],
    poly [1, 119, -8, 124, 167, -95, -4, 122, -69, 159, 147, 35, 40, -22, -105, 2],
    poly [-415, 417, 117, -127, 132, 43, -261, 209, 0, 59, 145, -24, -105, 2],
    poly [0, -715, -544, 549, -790, -263, 626, 833, 476, -272, 393, 728, -416, -1],
    poly [0, -178, -135, 137, -197, -65, 156, 207, 118, -68, 98, 181, -104],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1871 :
    haveI : Fact (Nat.Prime 1871) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1871 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1871 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1871 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1871 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1871) := ⟨by norm_num⟩
  have hP : poly [-3, 1] = X - C (3 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1871 : ℕ) : ℤ[X]) = poly [1871] := by simp [poly]
  refine ⟨X - C (3 : ℤ),
    poly [-624, -832, 346, 115, 38, 636, -412, 486, -462, -778, 364, 121, 40, 13, 4, 1],
    poly [-1, -1, 1, 0, 0, 1, -1, 1, -1, -1, 1],
    poly [1, 0, 0, 0, 0, 1, 1, 0, 0, -1],
    poly [622, -418, -141, 575, 190, -562, -189, 559, -439, -148, -51, 605, 200, 65, 20, 5],
    poly [1249, -831, -277, -716, 385, 130, 45, 15, 5],
    poly [-1, 1, 0, -1, 0, 1, 0, -1, 1, 0, 0, -1],
    poly [-2, 2, 0, 1, -1],
    poly [-624, -208, -693, -231, -77, -26, -9, -3, -1],
    poly [-1, 0, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 19 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_1973 :
    haveI : Fact (Nat.Prime 1973) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1973 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1973 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((1973 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((1973 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1973) := ⟨by norm_num⟩
  have hP : poly [-68, 1] = X - C (68 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1973 : ℕ) : ℤ[X]) = poly [1973] := by simp [poly]
  refine ⟨X - C (68 : ℤ),
    poly [29, -812, -99, 927, 768, -540, -95, 811, 186, 554, -253, -526, -501, 747, 69, 1],
    poly [1, -28, -3, 32, 26, -19, -3, 28, 6, 19, -9, -18, -17, 26, 2],
    poly [-1, 0, 0, -1, 0, 0, 0, 0, -1, -1, -1],
    poly [-835, -296, -143, -634, -206, -780, 82, -1240, -389, -1392, 73, -979, -66, -894, -558, -437],
    poly [1138, -1434, 153, -1326, 967, -421, 371, -894, -558, -437],
    poly [29, 10, 5, 22, 7, 27, -3, 43, 13, 48, -3, 34, 2, 31, 19, 15],
    poly [-39, 50, -6, 46, -34, 15, -13, 31, 19, 15],
    poly [-29, 841, -713, 918, -973, 595, 502, -747, -69, -1],
    poly [-1, 29, -25, 32, -34, 21, 17, -26, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2143 :
    haveI : Fact (Nat.Prime 2143) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2143 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2143 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2143 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2143 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2143) := ⟨by norm_num⟩
  have hP : poly [-8, 1] = X - C (8 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2143 : ℕ) : ℤ[X]) = poly [2143] := by simp [poly]
  refine ⟨X - C (8 : ℤ),
    poly [-268, 770, 364, 849, 106, 281, 35, 540, 871, -427, 1018, 395, 585, 73, 9, 1],
    poly [-1, 3, 1, 3, 0, 1, 0, 2, 3, -2, 4, 1, 2],
    poly [-1, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [242, 808, 343, 17, 512, 306, 816, 344, 285, -526, 712, 331, 1087, 110, -280, 207],
    poly [2385, -1335, 101, -549, 977, 390, -487, 207],
    poly [-1, -3, -1, 0, -2, -1, -3, -1, -1, 2, -3, -1, -4, 0, 1, -1],
    poly [-9, 6, -1, 2, -4, -1, 2, -1],
    poly [268, -770, -632, 189, -512, -64, -8, -1],
    poly [1, -3, -2, 1, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2347 :
    haveI : Fact (Nat.Prime 2347) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2347 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2347 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2347 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2347 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2347) := ⟨by norm_num⟩
  have hP : poly [-183, 1] = X - C (183 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2347 : ℕ) : ℤ[X]) = poly [2347] := by simp [poly]
  refine ⟨X - C (183 : ℤ),
    poly [513, 208, -576, 279, 553, 811, -111, 1128, -789, -761, -1043, 456, -1062, 815, 184, 1],
    poly [40, 16, -45, 22, 43, 63, -9, 88, -62, -59, -81, 36, -83, 64, 14],
    poly [-1, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, -1],
    poly [-1156, 428, -102, -464, -171, -272, -93, -387, 227, -257, -747, -506, 252, -1347, -163, 318],
    poly [1191, -763, -530, -362, -863, 327, 77, -758, 1599, -1184, -481, 318],
    poly [90, -34, 8, 36, 13, 21, 7, 30, -18, 20, 58, 39, -20, 105, 12, -25],
    poly [-93, 60, 41, 28, 67, -26, -6, 59, -125, 93, 37, -25],
    poly [-513, 305, 784, -855, -787, -466, -849, 829, -470, -631, -183, -1],
    poly [-40, 24, 61, -67, -61, -36, -66, 65, -37, -49, -14],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2381 :
    haveI : Fact (Nat.Prime 2381) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2381 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2381 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2381 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2381 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2381) := ⟨by norm_num⟩
  have hP : poly [-283, 1] = X - C (283 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2381 : ℕ) : ℤ[X]) = poly [2381] := by simp [poly]
  refine ⟨X - C (283 : ℤ),
    poly [-875, 182, -1152, 669, 1155, 206, 800, -889, -163, -640, 1041, 458, -133, -581, 284, 1],
    poly [-104, 22, -137, 80, 137, 24, 95, -106, -19, -76, 124, 54, -16, -69, 34],
    poly [0, -1, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1],
    poly [405, 11, 506, 289, 894, -694, 310, 221, 919, -248, 76, 237, 633, -493, -9, -327],
    poly [2381, -1976, 11, 101, 683, -6, -488, -396, 1126, -484, 318, -327],
    poly [-48, -1, -60, -34, -106, 83, -37, -26, -109, 30, -9, -28, -75, 59, 1, 39],
    poly [-283, 236, -2, -12, -81, 1, 58, 47, -134, 58, -38, 39],
    poly [0, 875, -182, 277, 388, -983, -584, -591, -448, 865, -283, -1],
    poly [0, 104, -22, 33, 46, -117, -69, -70, -53, 103, -34],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2551 :
    haveI : Fact (Nat.Prime 2551) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2551 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2551 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2551 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2551 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2551) := ⟨by norm_num⟩
  have hP : poly [-70, 1] = X - C (70 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2551 : ℕ) : ℤ[X]) = poly [2551] := by simp [poly]
  refine ⟨X - C (70 : ℤ),
    poly [-328, -770, -339, 724, -99, 363, -1161, -1037, -1181, 56, 183, 1023, 1035, -131, 71, 1],
    poly [-9, -21, -9, 20, -3, 10, -32, -28, -32, 2, 5, 28, 28, -4, 2],
    poly [-1, -1, 0, -1, 0, 0, 0, -1],
    poly [-410, 313, 214, 905, 514, -184, 462, 617, 437, 70, -409, 641, 656, 474, -549, 639],
    poly [2141, -2238, 624, 182, 1023, -1188, 639],
    poly [11, -9, -6, -25, -14, 5, -13, -17, -12, -2, 11, -18, -18, -13, 15, -18],
    poly [-59, 62, -18, -5, -28, 33, -18],
    poly [328, 770, 11, -1166, 202, -70, -1],
    poly [9, 21, 0, -32, 6, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2687 :
    haveI : Fact (Nat.Prime 2687) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2687 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2687 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2687 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2687 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2687) := ⟨by norm_num⟩
  have hP : poly [-98, 1] = X - C (98 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2687 : ℕ) : ℤ[X]) = poly [2687] := by simp [poly]
  refine ⟨X - C (98 : ℤ),
    poly [-1179, 646, 34, 1289, 397, -654, -1076, 1168, 149, -163, 108, -136, -303, -1045, 99, 1],
    poly [-43, 24, 1, 47, 14, -24, -39, 43, 5, -6, 4, -5, -11, -38, 4],
    poly [-1, -1, 0, 0, 1, 1, 0, -1],
    poly [-332, 542, -820, 208, 383, -191, 187, -193, 516, 770, -708, 593, 195, 1178, -649, 292],
    poly [2355, -2145, -488, -334, 1535, -941, 292],
    poly [12, -20, 30, -8, -14, 7, -7, 7, -19, -28, 26, -22, -7, -43, 24, -11],
    poly [-86, 79, 17, 12, -56, 35, -11],
    poly [1179, -646, -1213, -643, 1145, -98, -1],
    poly [43, -24, -44, -23, 42, -4],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2789 :
    haveI : Fact (Nat.Prime 2789) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2789 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2789 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2789 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2789 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2789) := ⟨by norm_num⟩
  have hP : poly [-690, 1] = X - C (690 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2789 : ℕ) : ℤ[X]) = poly [2789] := by simp [poly]
  refine ⟨X - C (690 : ℤ),
    poly [481, 607, 1359, -572, -498, 165, -792, -660, -5, 97, 1237, -459, 929, -128, 691, 1],
    poly [119, 150, 336, -142, -123, 41, -196, -163, -1, 24, 306, -114, 230, -32, 171],
    poly [-1, -1, 0, -1, 0, -1, 0, 0, -1],
    poly [572, 1551, 1993, 1355, 1443, 950, 1018, 1778, 1577, 643, 868, 1414, 954, 1883, 1274, 1358],
    poly [3361, -1238, 1421, 376, 429, 609, -84, 1358],
    poly [-142, -384, -493, -335, -357, -235, -252, -440, -390, -159, -215, -350, -236, -466, -315, -336],
    poly [-832, 307, -352, -93, -106, -151, 21, -336],
    poly [-481, -607, -878, 698, -1058, 819, -690, -1],
    poly [-119, -150, -217, 173, -262, 203, -171],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2857 :
    haveI : Fact (Nat.Prime 2857) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2857 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2857 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((2857 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((2857 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2857) := ⟨by norm_num⟩
  have hP : poly [-64, 1] = X - C (64 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2857 : ℕ) : ℤ[X]) = poly [2857] := by simp [poly]
  refine ⟨X - C (64 : ℤ),
    poly [1116, 1312, -292, 1290, 1404, -112, 400, 408, 51, 1340, -113, -1341, 604, 1304, 65, 1],
    poly [25, 29, -7, 29, 31, -3, 9, 9, 1, 30, -3, -30, 14, 29, 1],
    poly [1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    poly [625, 233, 584, 277, 49, 224, -800, -816, -102, 177, 226, -175, -1208, 249, -130, -2],
    poly [2232, -2465, -351, 307, -397, 842, 281, 49, -401, -1033, 1457, -379, 128, 2],
    poly [-14, -5, -13, -6, -1, -5, 18, 18, 2, -4, -5, 4, 27, -6, 3],
    poly [-50, 56, 7, -7, 9, -19, -6, -1, 9, 23, -33, 9, -3],
    poly [1116, 196, 1253, -1275, 1230, 421, -1288, -1404, 1228, 912, -700, 1239, 64, 1],
    poly [25, 4, 28, -29, 28, 9, -29, -31, 28, 20, -16, 28, 1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3061 :
    haveI : Fact (Nat.Prime 3061) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3061 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3061 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3061 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3061 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3061) := ⟨by norm_num⟩
  have hP : poly [-25, 1] = X - C (25 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3061 : ℕ) : ℤ[X]) = poly [3061] := by simp [poly]
  refine ⟨X - C (25 : ℤ),
    poly [-1102, -289, -1236, -1029, 571, 635, 760, 765, 153, -851, 823, -212, 971, 651, 26, 1],
    poly [-9, -2, -10, -8, 5, 5, 6, 6, 1, -7, 7, -2, 8, 5],
    poly [0, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1],
    poly [730, 147, 491, 15, -1106, 196, -609, -29, -618, -764, 577, -104, -621, -1009, -45, 116],
    poly [3061, -3061, 730, -583, 1074, -329, -1360, 1170, -1672, 908, -331, 227, -848, -161, 116],
    poly [-6, -1, -4, 0, 9, -2, 5, 0, 5, 6, -5, 1, 5, 8, 0, -1],
    poly [-25, 26, -7, 5, -9, 3, 11, -10, 14, -8, 3, -2, 7, 1, -1],
    poly [0, 0, 1102, -813, -1012, 82, -1466, 676, -830, -1380, 557, -345, -626, -25, -1],
    poly [0, 0, 9, -7, -8, 1, -12, 6, -7, -11, 5, -3, -5],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3163 :
    haveI : Fact (Nat.Prime 3163) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3163 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3163 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3163 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3163 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3163) := ⟨by norm_num⟩
  have hP : poly [-409, 1] = X - C (409 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3163 : ℕ) : ℤ[X]) = poly [3163] := by simp [poly]
  refine ⟨X - C (409 : ℤ),
    poly [116, -688, 849, -315, -1300, -908, 1065, -67, 1562, -785, -551, 772, -872, 52, 410, 1],
    poly [15, -89, 110, -41, -168, -117, 138, -9, 202, -102, -71, 100, -113, 7, 53],
    poly [-1, -1, 0, 0, -1, -1, -1, 0, -1, -1],
    poly [-87, 516, 154, 1027, 975, 681, -8, 841, 410, -202, 1204, -579, 654, -39, 1274, 790],
    poly [3076, -2647, 241, 511, 734, 170, -829, 1274, 790],
    poly [11, -67, -20, -133, -126, -88, 1, -109, -53, 26, -156, 75, -85, 5, -165, -102],
    poly [-398, 343, -32, -66, -95, -22, 107, -165, -102],
    poly [-116, 688, -733, -373, -1130, 1281, -51, -410, -1],
    poly [-15, 89, -95, -48, -146, 166, -7, -53],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3299 :
    haveI : Fact (Nat.Prime 3299) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3299 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3299 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3299 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3299 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3299) := ⟨by norm_num⟩
  have hP : poly [-676, 1] = X - C (676 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3299 : ℕ) : ℤ[X]) = poly [3299] := by simp [poly]
  refine ⟨X - C (676 : ℤ),
    poly [-1059, -880, 638, 1587, 383, -1239, -158, -132, 1010, -345, -225, 1493, -193, -908, 677, 1],
    poly [-217, -180, 131, 325, 78, -254, -32, -27, 207, -71, -46, 306, -40, -186, 139],
    poly [-1, 0, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1],
    poly [-647, 372, 720, -236, 153, -271, -623, -604, -277, -379, 470, -1066, -1283, -156, -901, -1395],
    poly [2652, -2280, -299, 63, 737, -2027, 409, 962, -633, -650, 494, -1395],
    poly [133, -76, -147, 49, -31, 56, 128, 124, 57, 78, -96, 219, 263, 32, 185, 286],
    poly [-543, 468, 61, -13, -151, 416, -84, -197, 130, 133, -101, 286],
    poly [1059, -179, -459, -1128, -314, -1567, 1003, -101, -1391, 1584, -676, -1],
    poly [217, -37, -94, -231, -64, -321, 206, -21, -285, 325, -139],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3469 :
    haveI : Fact (Nat.Prime 3469) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3469 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3469 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3469 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3469 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3469) := ⟨by norm_num⟩
  have hP : poly [-495, 1] = X - C (495 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3469 : ℕ) : ℤ[X]) = poly [3469] := by simp [poly]
  refine ⟨X - C (495 : ℤ),
    poly [869, -1519, -809, -317, -1178, 1196, -1224, -458, -64, 981, -1715, -466, -50, -778, 496, 1],
    poly [124, -217, -115, -45, -168, 171, -175, -65, -9, 140, -245, -66, -7, -111, 71],
    poly [-1, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-2246, -50, -424, -1504, 386, -1187, -1036, -433, -621, -292, -1735, -77, -1244, -69, -1258,
      -1779],
    poly [1223, -3519, -424, -1504, 2632, -1137, -612, -1175, 1189, 521, -1779],
    poly [321, 7, 61, 215, -55, 170, 148, 62, 89, 42, 248, 11, 178, 10, 180, 254],
    poly [-174, 503, 60, 215, -376, 163, 87, 168, -170, -74, 254],
    poly [-869, 1519, 809, 317, -1422, 754, 415, -728, 1274, -495, -1],
    poly [-124, 217, 115, 45, -203, 108, 59, -104, 182, -71],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3571 :
    haveI : Fact (Nat.Prime 3571) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3571 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3571 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3571 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3571 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3571) := ⟨by norm_num⟩
  have hP : poly [-47, 1] = X - C (47 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3571 : ℕ) : ℤ[X]) = poly [3571] := by simp [poly]
  refine ⟨X - C (47 : ℤ),
    poly [-76, 1290, 1547, -347, -1451, 349, 1451, -501, 1129, 24, 1748, 645, -1050, -1314, 48, 1],
    poly [-1, 17, 20, -5, -19, 5, 19, -7, 15, 0, 23, 8, -14, -17, 1],
    poly [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1],
    poly [1067, 26, -528, 220, -68, -530, 68, -907, -16, -149, 456, 13, -1516, 123, -298, -155],
    poly [2504, -2530, 554, -748, 288, 1529, -1639, 421, -143, -155],
    poly [-14, 0, 7, -3, 1, 7, -1, 12, 0, 2, -6, 0, 20, -2, 4, 2],
    poly [-33, 34, -8, 10, -4, -20, 22, -6, 2, 2],
    poly [-76, 1366, 257, 1677, -1104, -1695, -264, 1362, -47, -1],
    poly [-1, 18, 3, 22, -15, -22, -3, 18, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3673 :
    haveI : Fact (Nat.Prime 3673) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3673 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3673 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3673 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3673 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3673) := ⟨by norm_num⟩
  have hP : poly [-69, 1] = X - C (69 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3673 : ℕ) : ℤ[X]) = poly [3673] := by simp [poly]
  refine ⟨X - C (69 : ℤ),
    poly [692, -682, -1181, -1135, 90, 853, 1769, -347, -1602, 30, -1703, 135, -903, 1158, 70, 1],
    poly [13, -13, -22, -21, 2, 16, 33, -7, -30, 1, -32, 3, -17, 22, 1],
    poly [-1, -1, 1, -1, -1, 0, 0, -1],
    poly [-144, 333, 819, 2423, 1701, 1797, 1479, 1155, 1310, 567, 503, 715, 931, 2052, 1323, 2590],
    poly [3529, -3340, 1107, 1469, 729, -1267, 2590],
    poly [2, -7, -16, -46, -32, -34, -28, -22, -25, -11, -10, -14, -18, -39, -25, -49],
    poly [-67, 63, -21, -28, -14, 24, -49],
    poly [-692, 682, -1108, -1613, -1088, -69, -1],
    poly [-13, 13, -21, -30, -20, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3877 :
    haveI : Fact (Nat.Prime 3877) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3877 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3877 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3877 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3877 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3877) := ⟨by norm_num⟩
  have hP : poly [-403, 1] = X - C (403 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3877 : ℕ) : ℤ[X]) = poly [3877] := by simp [poly]
  refine ⟨X - C (403 : ℤ),
    poly [-1039, 1123, -1219, 199, 241, 1232, -401, 1038, -363, 1750, -1102, 1575, -708, -21, 404, 1],
    poly [-108, 117, -127, 21, 25, 128, -42, 108, -38, 182, -115, 164, -74, -2, 42],
    poly [-1, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [-924, 536, 1569, 927, 733, 771, 1483, 744, 569, 963, -633, 479, 501, 97, -943, 180],
    poly [2953, -3341, 2493, -533, 624, 877, 108, -1145, 584, 1040, -1123, 180],
    poly [96, -56, -163, -96, -76, -80, -154, -77, -59, -100, 66, -50, -52, -10, 98, -19],
    poly [-307, 348, -260, 56, -65, -91, -11, 119, -61, -108, 117, -19],
    poly [1039, -1123, 180, -1914, 255, 1309, -776, 1191, 686, 425, -403, -1],
    poly [108, -117, 19, -199, 27, 136, -81, 124, 71, 44, -42],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3911 :
    haveI : Fact (Nat.Prime 3911) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3911 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3911 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((3911 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((3911 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3911) := ⟨by norm_num⟩
  have hP : poly [-29, 1] = X - C (29 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3911 : ℕ) : ℤ[X]) = poly [3911] := by simp [poly]
  refine ⟨X - C (29 : ℤ),
    poly [944, 1516, 1266, -1305, 899, 975, -371, -822, -1377, -1531, -862, 1184, 1794, 871, 30, 1],
    poly [7, 11, 9, -10, 7, 7, -3, -6, -10, -11, -6, 9, 13, 6],
    poly [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, -1],
    poly [2135, 860, -128, 1726, -233, -840, 1162, 287, 1066, 958, 1224, 424, 801, 814, 275, 661],
    poly [1776, -2636, 988, -1854, -176, -253, 261, 9, -674, 539, -386, 661],
    poly [-16, -6, 1, -13, 2, 6, -9, -2, -8, -7, -9, -3, -6, -6, -2, -5],
    poly [-13, 20, -8, 14, 1, 2, -2, 0, 5, -4, 3, -5],
    poly [944, 572, -250, 1340, -763, 1592, -1024, 639, -922, -841, -29, -1],
    poly [7, 4, -2, 10, -6, 12, -8, 5, -7, -6],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_4013 :
    haveI : Fact (Nat.Prime 4013) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4013 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4013 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((4013 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((4013 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4013) := ⟨by norm_num⟩
  have hP : poly [-53, 1] = X - C (53 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4013 : ℕ) : ℤ[X]) = poly [4013] := by simp [poly]
  refine ⟨X - C (53 : ℤ),
    poly [530, 540, -747, -847, -16, 984, 700, -1274, 1566, 1241, 932, 169, -754, -1150, 54, 1],
    poly [7, 7, -10, -11, 0, 13, 9, -17, 21, 16, 12, 2, -10, -15, 1],
    poly [-1, 0, -1, -1, 0, 0, -1, -1, -1, 0, 0, -1],
    poly [-625, 1559, -217, 2021, -284, 1414, 386, -542, 1712, -1047, 491, -10, 662, 1659, -1048, 1021],
    poly [3388, -1829, -2401, 3797, -1897, 2160, -1720, 24, 2707, -2069, 1021],
    poly [8, -21, 3, -27, 4, -19, -5, 7, -23, 14, -7, 0, -9, -22, 14, -14],
    poly [-45, 25, 31, -51, 26, -29, 23, -1, -36, 28, -14],
    poly [-530, -10, 757, -440, 446, 387, -977, -397, 1204, -53, -1],
    poly [-7, 0, 10, -6, 6, 5, -13, -5, 16, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_4217 :
    haveI : Fact (Nat.Prime 4217) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4217 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4217 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((4217 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((4217 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4217) := ⟨by norm_num⟩
  have hP : poly [-190, 1] = X - C (190 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4217 : ℕ) : ℤ[X]) = poly [4217] := by simp [poly]
  refine ⟨X - C (190 : ℤ),
    poly [-1709, -9, -222, -1577, 2078, -1121, 1237, -393, 1374, 1805, 409, 1467, 496, -1662, 191, 1],
    poly [-77, 0, -10, -71, 94, -51, 56, -18, 62, 81, 18, 66, 22, -75, 9],
    poly [-1, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1],
    poly [-1176, 549, 891, -794, -248, 909, 449, -1329, 526, -463, 353, -930, -737, 174, 1000, -61],
    poly [3041, -2492, 342, -1685, 546, -19, 89, -887, 1061, -61],
    poly [53, -25, -40, 36, 11, -41, -20, 60, -24, 21, -16, 42, 33, -8, -45, 3],
    poly [-137, 113, -16, 76, -25, 1, -4, 40, -48, 3],
    poly [1709, -1700, 213, 1355, 562, 691, 1868, 1852, -190, -1],
    poly [77, -77, 10, 61, 25, 31, 84, 83, -9],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_4421 :
    haveI : Fact (Nat.Prime 4421) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4421 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4421 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((4421 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((4421 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4421) := ⟨by norm_num⟩
  have hP : poly [-150, 1] = X - C (150 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4421 : ℕ) : ℤ[X]) = poly [4421] := by simp [poly]
  refine ⟨X - C (150 : ℤ),
    poly [-560, -269, -886, -1568, 1139, 656, -143, -1062, 1555, -697, -1832, -808, -2098, 546, 151, 1],
    poly [-19, -9, -30, -53, 39, 22, -5, -36, 53, -24, -62, -27, -71, 19, 5],
    poly [-1, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0, -1],
    poly [-552, -202, 1274, 1107, 428, 394, -962, 90, 1217, 134, -669, 593, -47, -346, 212, -1199],
    poly [3869, -4071, 924, 183, 245, 149, -559, 299, -558, 1411, -1199],
    poly [19, 7, -43, -37, -14, -13, 33, -3, -41, -4, 23, -20, 2, 12, -7, 41],
    poly [-131, 139, -32, -6, -8, -5, 19, -10, 19, -48, 41],
    poly [560, -291, 1177, 391, -1530, 874, -1291, -1777, -395, -150, -1],
    poly [19, -10, 40, 13, -52, 30, -44, -60, -13, -5],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_4523 :
    haveI : Fact (Nat.Prime 4523) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4523 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4523 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((4523 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((4523 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4523) := ⟨by norm_num⟩
  have hP : poly [-524, 1] = X - C (524 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4523 : ℕ) : ℤ[X]) = poly [4523] := by simp [poly]
  refine ⟨X - C (524 : ℤ),
    poly [164, 406, 1425, 1660, -696, 1233, 1487, 538, -2131, 1377, 486, 1874, 392, -802, 525, 1],
    poly [19, 47, 165, 192, -81, 143, 172, 62, -247, 160, 56, 217, 45, -93, 61],
    poly [1, 0, 0, 0, -1, 1, 0, 1, -1],
    poly [1854, 839, -52, 1336, -146, -1340, -13, -537, -538, -374, -132, 887, 1122, -1234, 695, 949],
    poly [2669, -3508, 891, -1388, 3336, -1675, -1203, 949],
    poly [-215, -97, 6, -155, 17, 155, 1, 62, 62, 43, 15, -103, -130, 143, -81, -110],
    poly [-309, 407, -104, 161, -387, 195, 139, -110],
    poly [164, 242, 1019, 235, 2003, 1851, -523, -1],
    poly [19, 28, 118, 27, 232, 214, -61],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_4591 :
    haveI : Fact (Nat.Prime 4591) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4591 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4591 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((4591 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((4591 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4591) := ⟨by norm_num⟩
  have hP : poly [-245, 1] = X - C (245 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4591 : ℕ) : ℤ[X]) = poly [4591] := by simp [poly]
  refine ⟨X - C (245 : ℤ),
    poly [2080, 402, 1482, 81, -1124, -1410, 1231, -1213, 70, -1199, -1504, -662, 1740, 588, 246, 1],
    poly [111, 21, 79, 4, -60, -75, 66, -65, 4, -64, -80, -35, 93, 31, 13],
    poly [-1, -1, 0, 1, -1, 0, 0, 0, -1],
    poly [1700, 770, 2359, 2759, 1730, 2644, 2198, 2496, 2441, 2066, 1596, 1313, 2305, 304, 2938, 1281],
    poly [6291, -3821, 659, 289, 2001, -2634, 1657, 1281],
    poly [-91, -41, -126, -147, -92, -141, -117, -133, -130, -110, -85, -70, -123, -16, -157, -68],
    poly [-336, 205, -36, -15, -107, 141, -89, -68],
    poly [-2080, -402, 598, -2190, -1152, -342, -245, -1],
    poly [-111, -21, 32, -117, -61, -18, -13],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_4931 :
    haveI : Fact (Nat.Prime 4931) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4931 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4931 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((4931 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((4931 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4931) := ⟨by norm_num⟩
  have hP : poly [-214, 1] = X - C (214 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4931 : ℕ) : ℤ[X]) = poly [4931] := by simp [poly]
  refine ⟨X - C (214 : ℤ),
    poly [-2189, -978, 1954, -60, -392, -2283, 358, 2375, -588, -2330, 1026, 120, -852, 1632, 215, 1],
    poly [-95, -42, 85, -3, -17, -99, 16, 103, -26, -101, 45, 5, -37, 71, 9],
    poly [0, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0, -1, -1, 0, -1],
    poly [2621, 306, 1839, -435, 2089, -526, 130, 1193, 668, 366, 42, 870, -1246, 1970, 326, 1240],
    poly [4931, -4931, 2621, -2315, 1533, 347, 2830, -776, -2400, 2846, -2890, 2884, -914, 1240],
    poly [-114, -13, -80, 19, -91, 23, -6, -52, -29, -16, -2, -38, 54, -86, -14, -54],
    poly [-214, 215, -115, 101, -67, -15, -123, 34, 104, -124, 126, -126, 40, -54],
    poly [0, 0, 2189, -1211, 1999, -728, 1310, -63, 161, 2328, 2269, -1418, -214, -1],
    poly [0, 0, 95, -53, 87, -32, 57, -3, 7, 101, 98, -62, -9],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_4999 :
    haveI : Fact (Nat.Prime 4999) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4999 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4999 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((4999 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((4999 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4999) := ⟨by norm_num⟩
  have hP : poly [-320, 1] = X - C (320 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4999 : ℕ) : ℤ[X]) = poly [4999] := by simp [poly]
  refine ⟨X - C (320 : ℤ),
    poly [1859, 287, -1780, 1541, 1567, -1776, -896, -2143, 1493, 817, -2247, -132, 2296, -2258, 321, 1],
    poly [119, 18, -114, 99, 100, -114, -57, -137, 96, 52, -144, -8, 147, -145, 21],
    poly [1, 0, 0, 1, 1, 1, 1, 1, 0, 1],
    poly [2687, 1555, 1364, 1504, 1192, 1316, 754, 721, 2080, 194, 1969, 1584, 2442, 2101, 1147, -12],
    poly [2312, -3867, 191, -2827, -1243, -1488, -942, -1159, 12],
    poly [-172, -99, -87, -96, -76, -84, -48, -46, -133, -12, -126, -101, -156, -134, -73, 1],
    poly [-148, 248, -13, 181, 79, 95, 60, 74, -1],
    poly [1859, -1572, -2067, 181, 313, -124, 2421, 320, 1],
    poly [119, -101, -132, 12, 20, -8, 155, 20],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_5101 :
    haveI : Fact (Nat.Prime 5101) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 5101 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((5101 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((5101 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((5101 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 5101) := ⟨by norm_num⟩
  have hP : poly [-366, 1] = X - C (366 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((5101 : ℕ) : ℤ[X]) = poly [5101] := by simp [poly]
  refine ⟨X - C (366 : ℤ),
    poly [2439, 1484, -428, 626, 824, 2497, -2251, -1149, -700, 904, 1215, -2366, -1219, 1697, 367, 1],
    poly [175, 106, -31, 45, 59, 179, -162, -82, -50, 65, 87, -170, -87, 122, 26],
    poly [1, 0, 0, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [2583, -2720, 262, 1190, -2459, 1308, 496, -3325, 1668, -172, -1292, 1353, -2138, -1158, 991,
      -1693],
    poly [2518, 202, -2982, 1655, -1654, 1798, -980, -2149, 2684, -1693],
    poly [-185, 196, -19, -85, 177, -94, -35, 239, -120, 13, 93, -97, 154, 83, -71, 122],
    poly [-181, -14, 214, -119, 119, -129, 71, 154, -193, 122],
    poly [2439, -955, -1912, -1385, 1153, 1146, -2185, -1330, -366, -1],
    poly [175, -69, -137, -99, 83, 82, -157, -95, -26],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_5237 :
    haveI : Fact (Nat.Prime 5237) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 5237 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((5237 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((5237 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((5237 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 5237) := ⟨by norm_num⟩
  have hP : poly [-533, 1] = X - C (533 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((5237 : ℕ) : ℤ[X]) = poly [5237] := by simp [poly]
  refine ⟨X - C (533 : ℤ),
    poly [1464, 101, 236, 1602, 2312, -202, -1317, 2336, 1321, -27, -904, -41, -1356, 1825, 534, 1],
    poly [149, 10, 24, 163, 235, -21, -134, 238, 134, -3, -92, -4, -138, 186, 54],
    poly [-1, 0, -1, -1, 0, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [-1518, 346, -73, 614, 350, -692, 829, -190, -919, -2011, -608, -1696, -912, -1785, -1541,
      -2641],
    poly [3719, -3373, -1937, 1033, 1181, -774, 1944, -2325, -1768, -244, 1100, -2641],
    poly [155, -35, 8, -62, -35, 71, -84, 20, 94, 205, 62, 173, 93, 182, 157, 269],
    poly [-378, 344, 197, -105, -120, 79, -198, 237, 180, 25, -112, 269],
    poly [-1464, 1363, -1599, -1467, 518, 1013, -961, -1849, -2057, -1291, -533, -1],
    poly [-149, 139, -163, -149, 53, 103, -98, -188, -209, -131, -54],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_5407 :
    haveI : Fact (Nat.Prime 5407) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 5407 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((5407 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((5407 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((5407 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 5407) := ⟨by norm_num⟩
  have hP : poly [-531, 1] = X - C (531 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((5407 : ℕ) : ℤ[X]) = poly [5407] := by simp [poly]
  refine ⟨X - C (531 : ℤ),
    poly [-1059, 2116, 1287, -690, -1824, -2376, 2419, -2256, -269, 641, 1885, -27, -2617, 1329, 532, 1],
    poly [-104, 208, 126, -68, -179, -233, 238, -222, -26, 63, 185, -3, -257, 131, 52],
    poly [-1, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1],
    poly [424, 659, 802, 843, 1006, 599, 2146, 2098, -71, 933, -1010, 1420, 1058, 1597, -744, 1950],
    poly [5831, -5172, 143, 465, 398, -264, 1588, 539, -2341, 2694, -1950],
    poly [-42, -65, -79, -83, -99, -59, -211, -206, 7, -92, 99, -140, -104, -157, 73, -192],
    poly [-573, 509, -15, -46, -39, 26, -156, -53, 230, -265, 192],
    poly [1059, 2232, 829, -2371, -2041, 1381, 2589, 1461, 797, 531, 1],
    poly [104, 219, 81, -233, -200, 136, 254, 143, 78, 52],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_5441 :
    haveI : Fact (Nat.Prime 5441) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 5441 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((5441 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((5441 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((5441 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 5441) := ⟨by norm_num⟩
  have hP : poly [-190, 1] = X - C (190 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((5441 : ℕ) : ℤ[X]) = poly [5441] := by simp [poly]
  refine ⟨X - C (190 : ℤ),
    poly [315, -972, 1799, -506, 1916, 726, 147, -2462, -2218, 2537, 987, -453, 1544, -1796, 191, 1],
    poly [11, -34, 63, -18, 67, 25, 5, -86, -77, 89, 34, -16, 54, -63, 7],
    poly [1, 0, 0, 1, 1, 0, 0, 1, 0, -1, 1],
    poly [397, 485, -30, -1035, -38, 1485, 548, 1889, -1569, -499, -207, 310, 685, 2262, 638, 744],
    poly [5044, -5529, 515, 608, -1482, -1096, 2457, -1730, 850, -744],
    poly [-14, -17, 1, 36, 1, -52, -19, -66, 55, 17, 7, -11, -24, -79, -22, -26],
    poly [-176, 194, -19, -21, 52, 38, -86, 61, -30, 26],
    poly [315, -1287, -2670, -1990, 1450, 294, -113, -2177, 189, 1],
    poly [11, -45, -93, -69, 51, 10, -4, -76, 7],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_5849 :
    haveI : Fact (Nat.Prime 5849) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 5849 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((5849 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((5849 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((5849 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 5849) := ⟨by norm_num⟩
  have hP : poly [-752, 1] = X - C (752 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((5849 : ℕ) : ℤ[X]) = poly [5849] := by simp [poly]
  refine ⟨X - C (752 : ℤ),
    poly [70, 1019, -1072, -927, 621, -2457, 2439, -1039, 2612, -1451, 2207, -2346, 518, -1096, 753, 1],
    poly [9, 131, -138, -119, 80, -316, 314, -134, 336, -187, 284, -302, 67, -141, 97],
    poly [1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1],
    poly [1530, -288, -1706, -1879, -1467, -1062, -167, 1522, 272, 37, -1060, -307, -376, -1395, -253,
      1693],
    poly [4319, -4031, -112, 1991, 1006, -1762, -1019, 1142, 1946, -1693],
    poly [-197, 37, 219, 241, 188, 136, 21, -196, -35, -5, 136, 39, 48, 179, 32, -218],
    poly [-555, 519, 14, -256, -129, 227, 131, -147, -250, 218],
    poly [70, 949, -2021, 1094, -543, -2863, 1614, -1849, 752, 1],
    poly [9, 122, -260, 141, -70, -368, 208, -238, 97],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6053 :
    haveI : Fact (Nat.Prime 6053) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6053 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6053 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6053 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6053 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6053) := ⟨by norm_num⟩
  have hP : poly [-336, 1] = X - C (336 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6053 : ℕ) : ℤ[X]) = poly [6053] := by simp [poly]
  refine ⟨X - C (336 : ℤ),
    poly [-1207, 717, -1367, 1293, -2230, 768, -340, 17, 1153, -1726, -2257, -1556, -2869, -1774, 337, 1],
    poly [-67, 40, -76, 72, -124, 43, -19, 1, 64, -96, -125, -86, -159, -98, 19],
    poly [-1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1],
    poly [-1177, 639, 1365, -38, 1381, 1115, 862, -1859, 673, 32, 1129, -399, 1470, -416, -890, 2027],
    poly [4876, -5414, 2542, -1854, 655, 2518, -557, -416, -890, 2027],
    poly [65, -36, -76, 2, -77, -62, -48, 103, -38, -2, -63, 22, -82, 23, 49, -113],
    poly [-271, 301, -142, 103, -37, -140, 31, 23, 49, -113],
    poly [1207, -717, 160, 631, 146, 1892, 2870, 1774, -337, -1],
    poly [67, -40, 9, 35, 8, 105, 159, 98, -19],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6121 :
    haveI : Fact (Nat.Prime 6121) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6121 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6121 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6121 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6121 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6121) := ⟨by norm_num⟩
  have hP : poly [-110, 1] = X - C (110 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6121 : ℕ) : ℤ[X]) = poly [6121] := by simp [poly]
  refine ⟨X - C (110 : ℤ),
    poly [1725, 906, -270, 2279, 132, 502, -1164, 1937, 2466, 1970, 630, -1608, 2712, -31, 111, 1],
    poly [31, 16, -5, 41, 2, 9, -21, 35, 44, 35, 11, -29, 49, -1, 2],
    poly [-1, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [553, 1504, 1457, 2959, 1192, 1009, -1608, 1540, 567, 1838, 681, 1060, 2232, 462, -667, 380],
    poly [6674, -4617, 904, 2008, 1239, -1046, -792, 1770, 1129, -1047, 380],
    poly [-10, -27, -26, -53, -21, -18, 29, -28, -10, -33, -12, -19, -40, -8, 12, -7],
    poly [-120, 84, -17, -36, -22, 19, 14, -32, -20, 19, -7],
    poly [-1725, -906, 1995, 3023, -1308, -2349, -1802, -2743, 142, -110, -1],
    poly [-31, -16, 36, 54, -24, -42, -32, -49, 3, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6257 :
    haveI : Fact (Nat.Prime 6257) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6257 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6257 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6257 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6257 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6257) := ⟨by norm_num⟩
  have hP : poly [-275, 1] = X - C (275 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6257 : ℕ) : ℤ[X]) = poly [6257] := by simp [poly]
  refine ⟨X - C (275 : ℤ),
    poly [2116, -1585, 2224, 1396, 1484, 2986, -2947, -261, -2481, 2289, 1510, -1974, -576, 817, 276, 1],
    poly [93, -70, 98, 61, 65, 131, -130, -11, -109, 101, 66, -87, -25, 36, 12],
    poly [1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1],
    poly [2798, 1352, 1415, -496, 1158, -1043, 1065, 1778, 1007, -634, -913, 1293, 1119, 140, 637, 161],
    poly [3459, -4811, -63, 1911, 1144, 755, -2045, 174, 979, -497, 476, 161],
    poly [-123, -59, -62, 22, -51, 46, -47, -78, -44, 28, 40, -57, -49, -6, -28, -7],
    poly [-152, 212, 2, -84, -50, -33, 90, -8, -43, 22, -21, -7],
    poly [2116, 2556, -2448, -828, -2028, -1054, 2772, 1398, 1393, -541, -275, -1],
    poly [93, 112, -108, -36, -89, -46, 122, 61, 61, -24, -12],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6359 :
    haveI : Fact (Nat.Prime 6359) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6359 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6359 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6359 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6359 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6359) := ⟨by norm_num⟩
  have hP : poly [-133, 1] = X - C (133 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6359 : ℕ) : ℤ[X]) = poly [6359] := by simp [poly]
  refine ⟨X - C (133 : ℤ),
    poly [-765, -962, 949, 294, 1580, -275, -1293, 2094, -1323, -1779, -874, -1680, -1447, -1254, 134, 1],
    poly [-16, -20, 20, 6, 33, -6, -27, 44, -28, -37, -18, -35, -30, -26, 3],
    poly [-1, -1, 0, -1, -1, -1, 0, 0, 0, -1, -1, -1],
    poly [212, 3417, 668, 2512, 1474, 2279, 1281, 891, 1414, 892, 2179, 1089, 268, 1744, -1018, 3599],
    poly [6571, -2942, 456, -693, 4223, 435, 2107, -3331, 1744, -1018, 3599],
    poly [-5, -72, -14, -53, -31, -48, -27, -19, -30, -19, -46, -23, -6, -37, 21, -76],
    poly [-138, 62, -10, 14, -89, -9, -44, 70, -37, 21, -76],
    poly [765, 962, -1714, -491, 331, -380, 1814, 1448, 1254, -134, -1],
    poly [16, 20, -36, -10, 7, -8, 38, 30, 26, -3],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6427 :
    haveI : Fact (Nat.Prime 6427) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6427 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6427 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6427 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6427 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6427) := ⟨by norm_num⟩
  have hP : poly [-579, 1] = X - C (579 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6427 : ℕ) : ℤ[X]) = poly [6427] := by simp [poly]
  refine ⟨X - C (579 : ℤ),
    poly [111, 644, -676, -1977, 1040, 357, -954, 3173, 1393, -264, -2720, -38, -2098, 1617, 580, 1],
    poly [10, 58, -61, -178, 94, 32, -86, 286, 125, -24, -245, -3, -189, 146, 52],
    poly [-1, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1],
    poly [-2506, -701, -1819, 166, -1651, 799, -1217, -2386, -1167, -1509, -2109, 221, -1329, -2808, 686,
      -1528],
    poly [3921, -4622, -1118, 1985, -4323, 1749, -1329, -2808, 686, -1528],
    poly [226, 63, 164, -15, 149, -72, 110, 215, 105, 136, 190, -20, 120, 253, -62, 138],
    poly [-353, 417, 100, -179, 390, -158, 120, 253, -62, 138],
    poly [-111, -533, 1320, 1301, -3128, 39, 2098, -1617, -580, -1],
    poly [-10, -48, 119, 117, -282, 4, 189, -146, -52],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6529 :
    haveI : Fact (Nat.Prime 6529) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6529 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6529 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6529 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6529 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6529) := ⟨by norm_num⟩
  have hP : poly [-64, 1] = X - C (64 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6529 : ℕ) : ℤ[X]) = poly [6529] := by simp [poly]
  refine ⟨X - C (64 : ℤ),
    poly [102, 2756, -263, 812, 2155, 2278, 2790, 2798, 1982, 337, -1627, 2831, -1384, -2368, 65, 1],
    poly [1, 27, -3, 8, 21, 22, 27, 27, 19, 3, -16, 28, -14, -23, 1],
    poly [-1, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1, -1],
    poly [-194, 7, -908, 1016, 638, 20, -2234, -841, 711, -897, -106, -2440, 584, -1001, -2556, -642],
    poly [6335, -6328, -915, 1730, -371, -1332, -1439, 3140, -359, -2556, -642],
    poly [2, 0, 9, -10, -6, 0, 22, 8, -7, 9, 1, 24, -6, 10, 25, 6],
    poly [-62, 63, 8, -17, 4, 13, 14, -31, 4, 25, 6],
    poly [-102, -2654, 3019, -1177, 2430, 242, 1330, 1449, 2369, -65, -1],
    poly [-1, -26, 30, -12, 24, 2, 13, 14, 23, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6563 :
    haveI : Fact (Nat.Prime 6563) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6563 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6563 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6563 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6563 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6563) := ⟨by norm_num⟩
  have hP : poly [-1302, 1] = X - C (1302 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6563 : ℕ) : ℤ[X]) = poly [6563] := by simp [poly]
  refine ⟨X - C (1302 : ℤ),
    poly [-2848, -2084, 1435, 1846, -2403, -1383, 2731, -2115, -1534, -722, 1678, -1768, 2272, 3253,
      1303, 1],
    poly [-565, -413, 285, 366, -477, -274, 542, -420, -304, -143, 333, -351, 451, 645, 258],
    poly [1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    poly [-1874, -3307, -2305, -3514, -1171, -2878, -1231, -3120, -1332, -1996, -2924, -979, -791, -3533,
      -2779, -1488],
    poly [8437, -3256, 2305, 3514, -703, 1445, 2233, 37, 2242, 1291, 1488],
    poly [372, 656, 457, 697, 232, 571, 244, 619, 264, 396, 580, 194, 157, 701, 551, 295],
    poly [-1674, 647, -458, -697, 140, -287, -443, -7, -445, -256, -295],
    poly [-2848, -2084, 1435, 1846, 445, -2147, -788, 322, 1951, 1302, 1],
    poly [-565, -413, 285, 366, 88, -426, -156, 64, 387, 258],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6733 :
    haveI : Fact (Nat.Prime 6733) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6733 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6733 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6733 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6733 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6733) := ⟨by norm_num⟩
  have hP : poly [-832, 1] = X - C (832 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6733 : ℕ) : ℤ[X]) = poly [6733] := by simp [poly]
  refine ⟨X - C (832 : ℤ),
    poly [3148, -2513, 2797, -1777, 2021, -3008, -999, -3044, -2132, 1883, 504, -1189, 2572, -442, 833,
      1],
    poly [389, -311, 346, -220, 250, -372, -123, -376, -263, 233, 62, -147, 318, -55, 103],
    poly [1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1],
    poly [-515, -1948, -1974, -922, 18, -3315, -1045, -3292, 614, -1016, -322, -3542, -147, -2336, 777,
      -2432],
    poly [7248, -4785, 1459, -511, -559, 2419, 11, -963, 2189, -3113, 3209, -2432],
    poly [64, 241, 244, 114, -2, 410, 129, 407, -76, 126, 40, 438, 18, 289, -96, 301],
    poly [-896, 592, -181, 63, 69, -299, -1, 119, -271, 385, -397, 301],
    poly [3148, -2513, -351, -2849, 296, -2654, -861, -2971, -3014, 1275, -832, -1],
    poly [389, -311, -43, -352, 37, -328, -106, -367, -372, 158, -103],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6869 :
    haveI : Fact (Nat.Prime 6869) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6869 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6869 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6869 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6869 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6869) := ⟨by norm_num⟩
  have hP : poly [-339, 1] = X - C (339 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6869 : ℕ) : ℤ[X]) = poly [6869] := by simp [poly]
  refine ⟨X - C (339 : ℤ),
    poly [1621, -2062, -1080, 706, -2551, 1654, -603, -3183, 2645, 332, -769, -1988, 2608, -1512, 340, 1],
    poly [80, -102, -53, 35, -126, 82, -30, -157, 131, 16, -38, -98, 129, -75, 17],
    poly [-1, 0, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1],
    poly [-1449, -1818, -1272, -237, -1936, -2326, -2084, -2833, -4517, -1746, -1211, -2952, -3950, -407,
      -1126, -3357],
    poly [5420, -7238, -903, 666, -1153, -804, -1826, -593, -407, -1126, -3357],
    poly [72, 90, 63, 12, 96, 115, 103, 140, 223, 86, 60, 146, 195, 20, 56, 166],
    poly [-267, 358, 44, -33, 57, 40, 90, 29, 20, 56, 166],
    poly [-1621, -3186, -2603, 1897, 2275, -743, 2328, -2607, 1512, -340, -1],
    poly [-80, -157, -128, 94, 112, -37, 115, -129, 75, -17],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6971 :
    haveI : Fact (Nat.Prime 6971) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6971 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6971 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((6971 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((6971 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6971) := ⟨by norm_num⟩
  have hP : poly [-52, 1] = X - C (52 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6971 : ℕ) : ℤ[X]) = poly [6971] := by simp [poly]
  refine ⟨X - C (52 : ℤ),
    poly [-2279, -2725, -1393, 1850, 3387, -203, 2141, -2640, -2866, -2066, 1703, 2982, -3026, 2757, 53,
      1],
    poly [-17, -20, -10, 14, 25, -2, 16, -20, -21, -15, 13, 22, -23, 21],
    poly [1, 0, 0, 1, 1, 0, 0, 0, -1],
    poly [3596, 984, 1470, 675, 1330, 2281, 1629, 544, 2534, -377, 1846, 146, 1722, 3361, 2186, 1225],
    poly [3375, -4359, -486, -2801, -1639, 1175, 961, 1225],
    poly [-27, -7, -11, -5, -10, -17, -12, -4, -19, 3, -14, -1, -13, -25, -16, -9],
    poly [-25, 33, 3, 21, 12, -9, -7, -9],
    poly [-2279, -446, 1332, 964, -1188, -2704, -52, -1],
    poly [-17, -3, 10, 7, -9, -20],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_7039 :
    haveI : Fact (Nat.Prime 7039) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7039 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7039 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((7039 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((7039 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7039) := ⟨by norm_num⟩
  have hP : poly [-174, 1] = X - C (174 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7039 : ℕ) : ℤ[X]) = poly [7039] := by simp [poly]
  refine ⟨X - C (174 : ℤ),
    poly [-445, -1378, -1262, 1085, -3311, -2689, -420, 2708, 946, -1815, 1365, 1626, -1892, 2295, 175,
      1],
    poly [-11, -34, -31, 27, -82, -66, -10, 67, 23, -45, 34, 40, -47, 57, 4],
    poly [1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1],
    poly [3915, 418, -128, 3267, 657, 642, 1006, 1089, 2829, 2839, 250, 2541, 1381, -972, 754, 1573],
    poly [3124, -3542, -3369, 102, 3156, -3380, -1669, -486, -1976, -3360, 192, 972, -754, -1573],
    poly [-97, -10, 3, -81, -16, -16, -25, -27, -70, -70, -6, -63, -34, 24, -19, -39],
    poly [-77, 88, 83, -3, -78, 84, 41, 12, 49, 83, -5, -24, 19, 39],
    poly [-445, -933, -329, 1414, 2759, 2969, -2572, 2372, -755, 1452, -1893, 2295, 175, 1],
    poly [-11, -23, -8, 35, 68, 73, -64, 59, -19, 36, -47, 57, 4],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_7243 :
    haveI : Fact (Nat.Prime 7243) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7243 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7243 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((7243 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((7243 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7243) := ⟨by norm_num⟩
  have hP : poly [-82, 1] = X - C (82 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7243 : ℕ) : ℤ[X]) = poly [7243] := by simp [poly]
  refine ⟨X - C (82 : ℤ),
    poly [-265, 1940, -418, -2390, -3474, -1014, -984, -277, -1240, -2930, -1714, 1834, 464, -436, 83, 1],
    poly [-3, 22, -5, -27, -39, -11, -11, -3, -14, -33, -19, 21, 5, -5, 1],
    poly [0, -1, 0, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0, -1, -1],
    poly [3596, 460, 2365, 180, 595, 1925, -532, 233, 154, 948, 1311, 3347, -338, 942, -279, 2091],
    poly [7243, -3647, -3136, 1905, 1411, 875, 99, -2737, 2591, 2126, 2032, -1149, -279, 2091],
    poly [-41, -5, -27, -2, -7, -22, 6, -3, -2, -11, -15, -38, 4, -11, 3, -24],
    poly [-82, 42, 35, -22, -16, -10, -1, 31, -30, -24, -23, 13, 3, -24],
    poly [0, 265, -2205, 2358, 2237, -856, -2307, -2943, 2614, -2353, -382, 437, -83, -1],
    poly [0, 3, -25, 27, 25, -10, -26, -33, 30, -27, -4, 5, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_7481 :
    haveI : Fact (Nat.Prime 7481) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7481 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7481 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((7481 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((7481 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7481) := ⟨by norm_num⟩
  have hP : poly [-319, 1] = X - C (319 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7481 : ℕ) : ℤ[X]) = poly [7481] := by simp [poly]
  refine ⟨X - C (319 : ℤ),
    poly [3377, 292, -2696, 3392, 2004, -1307, 3326, 456, -2930, 624, -1710, 2715, -953, -2653, 320, 1],
    poly [144, 12, -115, 145, 85, -56, 142, 19, -125, 27, -73, 116, -41, -113, 14],
    poly [-1, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0, -1],
    poly [-446, 2015, 2609, 1579, 1224, 3099, 150, 1712, 943, 1949, 1061, -44, -1478, 933, -1686, 135],
    poly [7035, -5466, 3055, -882, 1076, 1668, -89, 1313, 2232, -4097, 2754, -1821, 135],
    poly [19, -86, -111, -67, -52, -132, -6, -73, -40, -83, -45, 2, 63, -40, 72, -6],
    poly [-300, 234, -131, 38, -46, -71, 4, -56, -95, 175, -118, 78, -6],
    poly [-3377, -292, -1408, 1004, -1615, -3171, -221, -1783, -1014, -2020, 2972, -319, -1],
    poly [-144, -12, -60, 43, -69, -135, -9, -76, -43, -86, 127, -14],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_7549 :
    haveI : Fact (Nat.Prime 7549) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7549 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7549 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((7549 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((7549 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7549) := ⟨by norm_num⟩
  have hP : poly [-620, 1] = X - C (620 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7549 : ℕ) : ℤ[X]) = poly [7549] := by simp [poly]
  refine ⟨X - C (620 : ℤ),
    poly [-1108, 1715, -3236, -821, 2653, 1855, 904, -3493, 1285, 3460, -2320, 2541, -1457, 22, 621, 1],
    poly [-91, 141, -266, -67, 218, 152, 74, -287, 106, 284, -191, 209, -120, 2, 51],
    poly [0, -1, -1, -1, 0, -1, 0, 0, -1, -1, -1, -1, 0, 0, -1],
    poly [3611, 3629, 926, 2955, 1485, 3309, 1169, 435, 2455, -1438, 3146, 1741, 95, 3185, -341, 3233],
    poly [7549, -3938, 3629, 926, -656, 1467, 2401, -4489, 4590, 1305, 143, 3526, -3574, 3233],
    poly [-297, -298, -76, -243, -122, -272, -96, -36, -202, 118, -259, -143, -8, -262, 28, -266],
    poly [-620, 324, -299, -76, 54, -121, -197, 369, -378, -107, -12, -290, 294, -266],
    poly [0, 1108, -1715, 3236, -287, 170, -365, 3226, -2710, 2930, 1478, 599, -620, -1],
    poly [0, 91, -141, 266, -24, 14, -30, 265, -223, 241, 121, 49, -51],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_7583 :
    haveI : Fact (Nat.Prime 7583) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7583 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7583 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((7583 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((7583 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7583) := ⟨by norm_num⟩
  have hP : poly [-214, 1] = X - C (214 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7583 : ℕ) : ℤ[X]) = poly [7583] := by simp [poly]
  refine ⟨X - C (214 : ℤ),
    poly [-815, 2264, 1676, 185, -1700, 1374, -3289, 3032, -1793, 1409, 2487, 1429, 3621, 513, 215, 1],
    poly [-23, 64, 47, 5, -48, 39, -93, 86, -51, 40, 70, 40, 102, 14, 6],
    poly [-1, 0, 0, -1, 0, 0, 0, -1, -1, -1, -1, -1],
    poly [-3041, -1815, -3581, -2101, -1598, -1135, -2940, -2913, -3657, -3377, -2667, -325, -2511,
      -2096, -5106, -1364],
    poly [4542, -6357, -1766, -1561, 1729, -1303, -325, -2511, -2096, -5106, -1364],
    poly [86, 51, 101, 59, 45, 32, 83, 82, 103, 95, 75, 9, 71, 59, 144, 38],
    poly [-128, 180, 49, 44, -49, 37, 9, 71, 59, 144, 38],
    poly [815, -3079, 588, 2306, -1194, -2486, -1429, -3621, -513, -215, -1],
    poly [23, -87, 17, 65, -34, -70, -40, -102, -14, -6],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_7753 :
    haveI : Fact (Nat.Prime 7753) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7753 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7753 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((7753 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((7753 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7753) := ⟨by norm_num⟩
  have hP : poly [-924, 1] = X - C (924 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7753 : ℕ) : ℤ[X]) = poly [7753] := by simp [poly]
  refine ⟨X - C (924 : ℤ),
    poly [-1804, 40, 579, 3810, 2278, -1382, 1534, -2289, 1189, 3324, 1623, 3207, -114, 1871, 925, 1],
    poly [-215, 5, 69, 454, 271, -165, 183, -273, 142, 396, 193, 382, -14, 223, 110],
    poly [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [-2531, -1938, -2080, -2399, -4153, -5145, -3770, -4230, -4499, -1336, -1492, -3808, -3005,
      -4204, -4113, -2762],
    poly [5222, -4629, -735, -177, -3966, 1355, 2225, -2154, -1563, -91, -1351, -2762],
    poly [302, 231, 248, 286, 495, 613, 449, 504, 536, 159, 178, 454, 358, 501, 490, 329],
    poly [-622, 552, 87, 21, 473, -162, -265, 257, 186, 11, 161, 329],
    poly [1804, -3648, 1305, -2692, -1186, 284, 638, 3508, 1984, -946, -924, -1],
    poly [215, -435, 156, -321, -141, 34, 76, 418, 236, -113, -110],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8059 :
    haveI : Fact (Nat.Prime 8059) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8059 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8059 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8059 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8059 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8059) := ⟨by norm_num⟩
  have hP : poly [-628, 1] = X - C (628 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8059 : ℕ) : ℤ[X]) = poly [8059] := by simp [poly]
  refine ⟨X - C (628 : ℤ),
    poly [3991, 494, -1167, 3386, -2651, 2665, -2203, 3795, 1007, -1564, 190, 3247, -3973, 122, 629, 1],
    poly [311, 38, -91, 264, -207, 208, -172, 296, 78, -122, 15, 253, -310, 10, 49],
    poly [-1, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    poly [1321, -204, 1526, 3659, 1160, -2373, 2639, 2185, 824, 809, 4261, 160, -578, 3245, 1339, 489],
    poly [9380, -8263, 205, 5184, -1891, -4302, 3612, 738, -3823, 1906, 850, 489],
    poly [-103, 16, -119, -285, -90, 185, -206, -170, -64, -63, -332, -12, 45, -253, -104, -38],
    poly [-731, 645, -17, -404, 148, 335, -282, -57, 298, -149, -66, -38],
    poly [-3991, -494, -2901, 1176, -3078, 2382, 3058, 839, -3964, 507, -628, -1],
    poly [-311, -38, -226, 92, -240, 186, 238, 65, -309, 40, -49],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8093 :
    haveI : Fact (Nat.Prime 8093) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8093 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8093 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8093 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8093 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8093) := ⟨by norm_num⟩
  have hP : poly [-700, 1] = X - C (700 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8093 : ℕ) : ℤ[X]) = poly [8093] := by simp [poly]
  refine ⟨X - C (700 : ℤ),
    poly [659, 3400, 1820, -957, 68, -3688, 3151, -4042, 1740, 3205, 837, -600, -498, -2972, 701, 1],
    poly [57, 294, 157, -83, 6, -319, 273, -350, 151, 277, 72, -52, -43, -257, 61],
    poly [1, 0, -1, 0, -1, 0, 0, 1, -1],
    poly [-1794, -1126, 3777, 1807, -2936, -1197, 2008, 2186, -1814, -4132, 1946, 2579, -1825, -4976,
      -275, 1385],
    poly [9887, -8761, -6697, 2638, 7852, -3041, -3045, 1385],
    poly [155, 97, -327, -156, 254, 103, -174, -189, 157, 357, -169, -223, 158, 430, 23, -120],
    poly [-855, 759, 578, -229, -679, 264, 263, -120],
    poly [659, 2741, -2239, 2575, 1946, -3720, -699, -1],
    poly [57, 237, -194, 223, 168, -322, -60],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8161 :
    haveI : Fact (Nat.Prime 8161) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8161 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8161 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8161 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8161 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8161) := ⟨by norm_num⟩
  have hP : poly [-83, 1] = X - C (83 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8161 : ℕ) : ℤ[X]) = poly [8161] := by simp [poly]
  refine ⟨X - C (83 : ℤ),
    poly [3933, 539, -2255, 1841, 2087, -2433, 69, 1869, -1944, 2828, -3309, 1435, -671, -1188, 84, 1],
    poly [40, 5, -23, 19, 21, -25, 1, 19, -20, 29, -34, 15, -7, -12, 1],
    poly [-1, 1, 0, 0, -1, 0, -1],
    poly [-4306, -2883, -1096, -2746, -1291, -2945, -2080, -988, -3138, -1984, -3150, -3754, -3073,
      -4638, -2887, -1686],
    poly [3855, -2432, 364, -3437, -1201, -1686],
    poly [44, 29, 11, 28, 13, 30, 21, 10, 32, 20, 32, 38, 31, 47, 29, 17],
    poly [-39, 25, -4, 35, 12, 17],
    poly [-3933, -834, -600, 1271, -83, -1],
    poly [-40, -8, -6, 13, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 20 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8263 :
    haveI : Fact (Nat.Prime 8263) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8263 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8263 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8263 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8263 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8263) := ⟨by norm_num⟩
  have hP : poly [-217, 1] = X - C (217 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8263 : ℕ) : ℤ[X]) = poly [8263] := by simp [poly]
  refine ⟨X - C (217 : ℤ),
    poly [-1942, 2885, -1586, 145, -1294, -2938, 2195, -2960, 786, 4078, 1580, 845, 2974, -2271, 218, 1],
    poly [-51, 76, -42, 4, -34, -77, 58, -78, 21, 107, 41, 22, 78, -60, 6],
    poly [-1, 0, 0, -1, 0, -1, 0, 0, 1, -1, 0, -1],
    poly [-2015, 1517, 2371, -24, 955, 1683, 2486, 205, -529, 3542, 1733, 430, -1518, -80, -378, -684],
    poly [6248, -4731, 854, -4410, 4511, -433, 1940, -448, -386, 306, -684],
    poly [53, -40, -62, 1, -25, -44, -65, -5, 14, -93, -45, -11, 40, 2, 10, 18],
    poly [-164, 125, -23, 116, -119, 12, -51, 12, 10, -8, 18],
    poly [1942, 3436, -3792, 211, -3388, -206, -3428, 2802, 2488, -217, -1],
    poly [51, 90, -100, 6, -89, -5, -90, 74, 65, -6],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8297 :
    haveI : Fact (Nat.Prime 8297) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8297 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8297 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8297 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8297 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8297) := ⟨by norm_num⟩
  have hP : poly [-177, 1] = X - C (177 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8297 : ℕ) : ℤ[X]) = poly [8297] := by simp [poly]
  refine ⟨X - C (177 : ℤ),
    poly [375, 799, -558, 2200, -3222, -2737, -2078, -293, 2389, 576, 97, -2812, 1156, -1681, 178, 1],
    poly [8, 17, -12, 47, -69, -58, -44, -6, 51, 12, 2, -60, 25, -36, 4],
    poly [-1, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1],
    poly [-1573, -785, 2407, 175, -822, -312, -731, -1249, 2170, -2217, 102, 1662, -2548, -228, 957,
      -3677],
    poly [6724, -9082, 2407, 1748, -1610, -3504, 3074, 533, -2320, -1185, 4634, -3677],
    poly [34, 17, -51, -3, 18, 7, 16, 27, -46, 48, -2, -35, 55, 5, -20, 79],
    poly [-143, 195, -52, -37, 35, 75, -66, -11, 50, 25, -99, 79],
    poly [-375, -799, 558, -1825, 3646, 1380, -3086, 3967, -2837, 1859, -177, -1],
    poly [-8, -17, 12, -39, 78, 29, -66, 85, -61, 40, -4],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8467 :
    haveI : Fact (Nat.Prime 8467) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8467 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8467 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8467 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8467 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8467) := ⟨by norm_num⟩
  have hP : poly [-478, 1] = X - C (478 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8467 : ℕ) : ℤ[X]) = poly [8467] := by simp [poly]
  refine ⟨X - C (478 : ℤ),
    poly [2781, -809, 388, -938, 3523, 1637, -2937, -77, -3224, 2172, -580, -1436, -127, 354, 479, 1],
    poly [157, -46, 22, -53, 199, 92, -166, -4, -182, 123, -33, -81, -7, 20, 27],
    poly [-1, -1, 0, -1, 0, -1, -1, 0, -1, -1, -1],
    poly [-1315, -2044, 1692, 885, 1397, -19, 722, -2518, -966, 1092, 1486, -1985, -1514, 1020, -1490,
      2012],
    poly [7152, -10511, 3007, 1614, -1024, 1517, -3526, 1020, -1490, 2012],
    poly [74, 115, -96, -50, -79, 1, -41, 142, 54, -62, -84, 112, 85, -58, 84, -114],
    poly [-404, 594, -171, -91, 58, -86, 199, -58, 84, -114],
    poly [-2781, 809, 2393, -2652, 455, 1914, 128, -354, -479, -1],
    poly [-157, 46, 135, -150, 26, 108, 7, -20, -27],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8501 :
    haveI : Fact (Nat.Prime 8501) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8501 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8501 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8501 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8501 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8501) := ⟨by norm_num⟩
  have hP : poly [-354, 1] = X - C (354 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8501 : ℕ) : ℤ[X]) = poly [8501] := by simp [poly]
  refine ⟨X - C (354 : ℤ),
    poly [1705, 2022, -2900, -1377, 3214, -3521, 3304, -3953, 277, -3025, -777, 334, 1802, -1844, 355, 1],
    poly [71, 84, -121, -57, 134, -147, 138, -165, 12, -126, -32, 14, 75, -77, 15],
    poly [0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [1233, -1285, -1100, -1988, -1126, -163, -1385, -620, -4292, -268, -881, -1339, -2541, -1872,
      -3383, -2931],
    poly [8501, -8501, 1233, -1285, -2333, 530, -1311, -508, -962, 750, -3600, 1511, -452, -2931],
    poly [-51, 54, 46, 83, 47, 7, 58, 26, 179, 11, 37, 56, 106, 78, 141, 122],
    poly [-354, 355, -52, 54, 97, -22, 55, 21, 40, -31, 150, -63, 19, 122],
    poly [0, 0, -1705, -2022, -3896, 1694, 365, -1752, 3309, 1114, -3647, 2199, -354, -1],
    poly [0, 0, -71, -84, -162, 71, 15, -73, 138, 46, -152, 92, -15],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8807 :
    haveI : Fact (Nat.Prime 8807) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8807 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8807 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((8807 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((8807 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8807) := ⟨by norm_num⟩
  have hP : poly [-736, 1] = X - C (736 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8807 : ℕ) : ℤ[X]) = poly [8807] := by simp [poly]
  refine ⟨X - C (736 : ℤ),
    poly [-3171, -818, 1016, 4010, 4038, -4051, 521, 2011, -2558, -3342, 2975, -1743, 572, -3601, 737, 1],
    poly [-265, -68, 85, 335, 337, -339, 44, 168, -214, -279, 249, -146, 48, -301, 62],
    poly [-1, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, -1],
    poly [-374, 2617, 1939, 909, 2176, 3841, -644, 726, 3145, 2897, 312, 2594, -538, 2186, 323, 2247],
    poly [8433, -6190, 1939, 909, 2550, 850, 408, -861, -61, 323, 2247],
    poly [31, -219, -162, -76, -182, -321, 54, -61, -263, -242, -26, -217, 45, -183, -27, -188],
    poly [-705, 518, -163, -76, -213, -71, -34, 72, 5, -27, -188],
    poly [3171, 818, -1016, -4010, 1598, -2403, -1858, 165, 3602, -737, -1],
    poly [265, 68, -85, -335, 134, -201, -155, 14, 301, -62],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9011 :
    haveI : Fact (Nat.Prime 9011) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9011 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9011 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((9011 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((9011 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9011) := ⟨by norm_num⟩
  have hP : poly [-255, 1] = X - C (255 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9011 : ℕ) : ℤ[X]) = poly [9011] := by simp [poly]
  refine ⟨X - C (255 : ℤ),
    poly [3039, 3793, 1181, 358, -3603, 4191, -867, -2371, -292, -1662, -1314, 4412, 3339, 2204, 256, 1],
    poly [86, 107, 33, 10, -102, 119, -25, -67, -8, -47, -37, 125, 94, 62, 7],
    poly [1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1],
    poly [2400, -1301, 310, -2546, -755, -960, 276, 1659, -2152, 342, -673, 2150, 1525, -421, 2257, 748],
    poly [6611, -5310, -4011, 4157, 299, 1450, -2571, 732, 1169, -2257, -748],
    poly [-68, 37, -9, 72, 21, 27, -8, -47, 61, -10, 19, -61, -43, 12, -64, -21],
    poly [-187, 151, 113, -118, -8, -41, 73, -21, -33, 64, 21],
    poly [3039, 754, 427, 2970, 3192, 4359, 2208, 3083, 2203, 256, 1],
    poly [86, 21, 12, 84, 90, 123, 62, 87, 62, 7],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9181 :
    haveI : Fact (Nat.Prime 9181) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9181 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9181 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((9181 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((9181 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9181) := ⟨by norm_num⟩
  have hP : poly [-808, 1] = X - C (808 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9181 : ℕ) : ℤ[X]) = poly [9181] := by simp [poly]
  refine ⟨X - C (808 : ℤ),
    poly [-1034, 3987, -745, -160, -1216, -581, 4158, 1630, 4263, 28, 375, 1114, 3217, 1822, 809, 1],
    poly [-91, 351, -66, -14, -107, -51, 366, 143, 375, 2, 33, 98, 283, 160, 71],
    poly [-1, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1],
    poly [46, 1705, 264, -2408, -1775, 896, -771, 1579, -1486, -3251, -1242, 1158, 3888, -1040, -1137,
      -444],
    poly [9227, -7522, -1441, -2672, 633, 2625, -3326, 3791, -347, -693, -444],
    poly [-4, -150, -23, 212, 156, -79, 68, -139, 131, 286, 109, -102, -342, 92, 100, 39],
    poly [-812, 663, 126, 235, -56, -231, 293, -334, 31, 61, 39],
    poly [1034, 4160, -4449, -585, 1056, -1669, 282, -2204, -1014, -808, -1],
    poly [91, 366, -392, -51, 93, -147, 25, -194, -89, -71],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9283 :
    haveI : Fact (Nat.Prime 9283) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9283 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9283 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((9283 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((9283 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9283) := ⟨by norm_num⟩
  have hP : poly [-370, 1] = X - C (370 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9283 : ℕ) : ℤ[X]) = poly [9283] := by simp [poly]
  refine ⟨X - C (370 : ℤ),
    poly [3939, 111, 3011, -1999, -3267, -2869, -1764, -632, -3740, 3678, -2223, -2816, 2978, -1974, 371,
      1],
    poly [157, 4, 120, -80, -130, -114, -70, -25, -149, 147, -89, -112, 119, -79, 15],
    poly [1, -1, -1, 0, 0, 0, 0, 0, -1, -1],
    poly [7043, 2270, 5042, 2942, 3689, 3967, 4319, 958, 2379, 2709, 2459, 3211, 2360, 3286, 3991, 2613],
    poly [2240, 2533, -502, 99, -75, -1631, 673, 3991, 2613],
    poly [-281, -90, -201, -117, -147, -158, -172, -38, -95, -108, -98, -128, -94, -131, -159, -104],
    poly [-89, -101, 20, -4, 3, 65, -27, -159, -104],
    poly [3939, 1516, 2789, -4082, 842, -2607, 1975, -371, -1],
    poly [157, 60, 111, -163, 34, -104, 79, -15],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9419 :
    haveI : Fact (Nat.Prime 9419) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9419 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9419 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((9419 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((9419 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9419) := ⟨by norm_num⟩
  have hP : poly [-685, 1] = X - C (685 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9419 : ℕ) : ℤ[X]) = poly [9419] := by simp [poly]
  refine ⟨X - C (685 : ℤ),
    poly [55, -2970, 3282, -1494, -2546, -1200, 122, 2764, -1261, 3477, -2800, 3351, 4130, -1039, 686, 1],
    poly [4, -216, 239, -109, -185, -87, 9, 201, -92, 253, -204, 244, 300, -76, 50],
    poly [1, 0, 0, 0, -1, 1, 0, 0, 1, 0, 0, -1],
    poly [-2075, -978, -4799, -1862, -3274, -966, -5459, -3238, -2946, -168, -2254, -552, 28, -3615,
      -1049, -894],
    poly [11494, -10516, 3821, -2937, -663, 864, -425, 4537, -2566, -155, -894],
    poly [151, 71, 349, 135, 238, 70, 397, 235, 214, 12, 164, 40, -2, 263, 76, 65],
    poly [-836, 766, -279, 214, 48, -63, 31, -330, 187, 11, 65],
    poly [55, -3025, -3167, 4643, -1107, 4426, 1464, 4251, 1725, -685, -1],
    poly [4, -220, -230, 338, -81, 322, 106, 309, 125, -50],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9521 :
    haveI : Fact (Nat.Prime 9521) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9521 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9521 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((9521 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((9521 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9521) := ⟨by norm_num⟩
  have hP : poly [-382, 1] = X - C (382 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9521 : ℕ) : ℤ[X]) = poly [9521] := by simp [poly]
  refine ⟨X - C (382 : ℤ),
    poly [1969, 55, -1595, 594, 3466, 3972, -2158, 4705, 1757, -1441, 2040, 3071, 1005, 3492, 383, 1],
    poly [79, 2, -64, 24, 139, 159, -87, 189, 70, -58, 82, 123, 40, 140, 15],
    poly [-1, 0, -1, -1, 0, 0, 0, -1, -1, 0, -1, -1, -1],
    poly [-3706, 322, 183, -2235, -1693, -2539, -2940, -3614, 73, -4628, -2771, -3140, -175, -1887,
      -1393, -2937],
    poly [5815, -5493, -3845, -2096, 4431, -3403, -2277, -4684, 2762, -1887, -1393, -2937],
    poly [149, -13, -7, 90, 68, 102, 118, 145, -3, 186, 111, 126, 7, 76, 56, 118],
    poly [-233, 221, 154, 84, -178, 137, 91, 188, -111, 76, 56, 118],
    poly [-1969, 1914, -319, -2244, 692, -1045, 1069, -2689, -1004, -3492, -383, -1],
    poly [-79, 77, -13, -90, 28, -42, 43, -108, -40, -140, -15],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9623 :
    haveI : Fact (Nat.Prime 9623) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9623 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9623 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((9623 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((9623 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9623) := ⟨by norm_num⟩
  have hP : poly [-288, 1] = X - C (288 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9623 : ℕ) : ℤ[X]) = poly [9623] := by simp [poly]
  refine ⟨X - C (288 : ℤ),
    poly [-4043, -415, 2137, 4017, 2687, 4754, -752, -3511, 4532, -3359, 3196, 3319, 212, -3374, 289, 1],
    poly [-121, -12, 64, 120, 80, 142, -23, -105, 136, -101, 96, 99, 6, -101, 9],
    poly [1, 0, 0, 1, 0, 1, 0, 2],
    poly [6291, 7215, -400, 5755, 5342, 362, 7161, 2607, -416, 8428, 5652, 2702, 8372, 573, 3787, 6939],
    poly [3332, -10547, 7615, -12446, -511, 6304, -13878],
    poly [-189, -216, 12, -173, -160, -11, -215, -78, 12, -253, -169, -81, -251, -17, -114, -208],
    poly [-99, 316, -229, 374, 14, -188, 416],
    poly [-4043, 3628, 2552, -2163, 2298, 576, 2],
    poly [-121, 109, 76, -65, 69, 17],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9929 :
    haveI : Fact (Nat.Prime 9929) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9929 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9929 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((9929 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((9929 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9929) := ⟨by norm_num⟩
  have hP : poly [-1070, 1] = X - C (1070 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9929 : ℕ) : ℤ[X]) = poly [9929] := by simp [poly]
  refine ⟨X - C (1070 : ℤ),
    poly [-4649, -2417, -1654, 880, -4277, -635, 2078, -4944, -3670, 1472, -2402, -1422, -2813, 4136,
      1071, 1],
    poly [-501, -260, -178, 95, -461, -68, 224, -533, -395, 159, -259, -153, -303, 446, 115],
    poly [-1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1, -1],
    poly [-1458, 1807, -649, -243, 741, -1912, -3891, -79, -1356, -587, 54, 1363, 427, -2135, 1927, 1207],
    poly [8471, -6664, -2456, 406, -474, 612, -4435, 4218, -293, -3342, 1927, 1207],
    poly [157, -195, 70, 26, -80, 206, 419, 8, 146, 63, -6, -147, -46, 230, -208, -130],
    poly [-913, 719, 264, -44, 51, -66, 478, -455, 32, 360, -208, -130],
    poly [4649, -2232, -763, -2534, -123, 4055, -3476, 4488, 3883, -4135, -1071, -1],
    poly [501, -241, -82, -273, -13, 437, -375, 484, 418, -446, -115],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10099 :
    haveI : Fact (Nat.Prime 10099) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10099 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10099 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((10099 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((10099 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10099) := ⟨by norm_num⟩
  have hP : poly [-47, 1] = X - C (47 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10099 : ℕ) : ℤ[X]) = poly [10099] := by simp [poly]
  refine ⟨X - C (47 : ℤ),
    poly [-1719, 2327, -810, -447, -2588, 3168, 712, 230, -210, 855, 3671, -3145, -5009, 2257, 48, 1],
    poly [-8, 11, -4, -2, -12, 15, 3, 1, -1, 4, 17, -15, -23, 11],
    poly [-1, 0, 1, -1, 0, 0, 0, -1, -1],
    poly [1670, 4284, 3695, 1104, 834, 1258, 2986, 4312, 1332, -1095, -2221, 1193, 2340, 4728, -593,
      2302],
    poly [11769, -7485, -2259, -3535, 2933, 2426, -593, 2302],
    poly [-8, -20, -17, -5, -4, -6, -14, -20, -6, 5, 10, -6, -11, -22, 3, -11],
    poly [-55, 36, 10, 16, -14, -11, 3, -11],
    poly [1719, -4046, 1418, -4697, -5042, -2256, -48, -1],
    poly [8, -19, 7, -22, -23, -10],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10133 :
    haveI : Fact (Nat.Prime 10133) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10133 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10133 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((10133 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((10133 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10133) := ⟨by norm_num⟩
  have hP : poly [-576, 1] = X - C (576 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10133 : ℕ) : ℤ[X]) = poly [10133] := by simp [poly]
  refine ⟨X - C (576 : ℤ),
    poly [2199, 39, -2498, 3215, -4885, 3334, -3108, -3084, 4938, -4020, -3930, 820, 2693, -2036, 577, 1],
    poly [125, 2, -142, 183, -278, 190, -177, -175, 281, -229, -223, 47, 153, -116, 33],
    poly [-1, 0, -1, 0, 1, 0, 0, -1, 0, 0, 0, -1],
    poly [-4766, -1854, -1286, -3959, -3172, -1042, -3466, -3048, -127, 916, -2583, 771, 2149, 1694,
      -928, -827],
    poly [5367, -7221, -4198, 239, 6121, -3455, -2205, 455, 2622, -101, -827],
    poly [271, 105, 73, 225, 180, 59, 197, 173, 7, -52, 147, -44, -122, -96, 53, 47],
    poly [-305, 411, 238, -14, -348, 197, 125, -26, -149, 6, 47],
    poly [-2199, 2160, 338, -3553, 2703, 4174, 1872, -4729, 2613, -576, -1],
    poly [-125, 123, 19, -202, 154, 237, 106, -269, 149, -33],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10303 :
    haveI : Fact (Nat.Prime 10303) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10303 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10303 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((10303 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((10303 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10303) := ⟨by norm_num⟩
  have hP : poly [-1317, 1] = X - C (1317 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10303 : ℕ) : ℤ[X]) = poly [10303] := by simp [poly]
  refine ⟨X - C (1317 : ℤ),
    poly [1017, -2972, 4762, 473, 4217, -1624, 4145, -521, -4882, -35, -4600, 1655, -2729, 4903, 1318, 1],
    poly [130, -380, 609, 60, 539, -208, 530, -67, -624, -4, -588, 212, -349, 627, 168],
    poly [1, 0, -1, -1, 0, -1],
    poly [831, 550, -2157, -39, -718, -476, 682, -2462, 1056, -1609, -993, 1018, -4175, 1970, -3877,
      -2309],
    poly [9472, -10022, 3538, -1568, -2309],
    poly [-106, -70, 276, 5, 92, 61, -87, 315, -135, 206, 127, -130, 534, -252, 496, 295],
    poly [-1211, 1282, -453, 201, 295],
    poly [1017, -3989, -3586, -1317, -1],
    poly [130, -510, -458, -168],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 20 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 19 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10337 :
    haveI : Fact (Nat.Prime 10337) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10337 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10337 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((10337 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((10337 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10337) := ⟨by norm_num⟩
  have hP : poly [-1394, 1] = X - C (1394 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10337 : ℕ) : ℤ[X]) = poly [10337] := by simp [poly]
  refine ⟨X - C (1394 : ℤ),
    poly [3285, 3888, -2600, -4414, 464, -1416, 3195, -235, -15, 875, 2596, 3450, -613, 1275, 1395, 1],
    poly [443, 524, -351, -595, 63, -191, 431, -32, -2, 118, 350, 465, -83, 172, 188],
    poly [1, 0, 0, 0, 1, 1, 0, 0, -1, -1],
    poly [3239, -103, 473, -16, 4114, -792, 35, 1971, -534, 139, 1452, -1224, 2986, 4042, -2023, 2103],
    poly [7098, -6995, -576, 489, -7369, 5009, 1939, -2023, 2103],
    poly [-437, 14, -64, 2, -555, 107, -5, -266, 72, -19, -196, 165, -403, -545, 273, -284],
    poly [-957, 944, 77, -66, 994, -676, -261, 273, -284],
    poly [3285, 603, 3849, -1814, -2174, 2008, -1274, -1395, -1],
    poly [443, 81, 519, -245, -293, 271, -172, -188],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10711 :
    haveI : Fact (Nat.Prime 10711) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10711 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10711 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((10711 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((10711 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10711) := ⟨by norm_num⟩
  have hP : poly [-1091, 1] = X - C (1091 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10711 : ℕ) : ℤ[X]) = poly [10711] := by simp [poly]
  refine ⟨X - C (1091 : ℤ),
    poly [4575, 3244, -1990, 4475, 171, 4153, -4797, 4011, 2193, -2904, -1976, 4691, -2617, 2452, 1092,
      1],
    poly [466, 330, -203, 456, 17, 423, -489, 409, 223, -296, -201, 478, -267, 250, 111],
    poly [0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1],
    poly [1592, 1672, -154, -784, 207, -2865, -1297, 1473, -164, 2122, -2392, -1650, -913, 1277, -3188,
      -1690],
    poly [10711, -10711, 1592, 1672, -1746, -864, 2033, -2235, -3880, 4465, -1498, -1690],
    poly [-162, -170, 16, 80, -21, 292, 132, -150, 17, -216, 244, 168, 93, -130, 325, 172],
    poly [-1091, 1092, -163, -170, 178, 88, -207, 228, 395, -455, 153, 172],
    poly [0, 0, -4575, -3244, -4146, 4905, 5306, 2312, 5068, -1360, -1091, -1],
    poly [0, 0, -466, -330, -422, 500, 540, 235, 516, -139, -111],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10847 :
    haveI : Fact (Nat.Prime 10847) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10847 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10847 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((10847 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((10847 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10847) := ⟨by norm_num⟩
  have hP : poly [-463, 1] = X - C (463 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10847 : ℕ) : ℤ[X]) = poly [10847] := by simp [poly]
  refine ⟨X - C (463 : ℤ),
    poly [3561, 2983, 311, 2484, -1658, -3916, -805, -4289, 4114, -2943, 5382, 4908, 690, -2107, 464, 1],
    poly [152, 127, 13, 106, -71, -167, -34, -183, 176, -126, 230, 209, 29, -90, 20],
    poly [-1, 0, -1, -1, -1, -1, 0, 0, -1, -1],
    poly [-2800, -393, -2590, 240, -527, -2684, -1283, -624, -4371, -3114, 520, 317, -3549, -1566, -1632,
      -5240],
    poly [8047, -8440, -4997, 2437, -3357, -1917, 3674, -1632, -5240],
    poly [120, 17, 111, -10, 23, 115, 55, 27, 187, 133, -22, -13, 152, 67, 70, 224],
    poly [-343, 361, 213, -104, 144, 82, -157, 70, 224],
    poly [-3561, 578, -889, -5156, 3831, -226, 2108, -464, -1],
    poly [-152, 25, -38, -220, 164, -10, 90, -20],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10949 :
    haveI : Fact (Nat.Prime 10949) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10949 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10949 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((10949 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((10949 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10949) := ⟨by norm_num⟩
  have hP : poly [-17, 1] = X - C (17 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10949 : ℕ) : ℤ[X]) = poly [10949] := by simp [poly]
  refine ⟨X - C (17 : ℤ),
    poly [644, 1970, 2048, -4388, 1674, -4410, 4893, 2864, -4340, 3609, -2364, 1149, 5220, 307, 18, 1],
    poly [1, 3, 3, -7, 3, -7, 8, 4, -7, 6, -4, 2, 8],
    poly [0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 1, 0, -1],
    poly [-2964, 726, 299, 1562, -1584, -1125, -1098, 3412, 457, -1649, -3061, -2500, -2467, -1821,
      -1783, -4357],
    poly [10949, -7985, -6654, 4117, -1690, 1445, 85, 5, -3220, 4319, 2574, -4357],
    poly [5, -1, 0, -2, 3, 2, 2, -5, 0, 3, 5, 4, 4, 3, 3, 7],
    poly [-17, 13, 10, -7, 3, -2, 0, 0, 5, -7, -4, 7],
    poly [0, 644, 682, -1248, 4435, 905, -2523, 4360, -4896, -288, -17, -1],
    poly [0, 1, 1, -2, 7, 1, -4, 7, -8],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11119 :
    haveI : Fact (Nat.Prime 11119) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11119 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11119 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((11119 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((11119 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11119) := ⟨by norm_num⟩
  have hP : poly [-8, 1] = X - C (8 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11119 : ℕ) : ℤ[X]) = poly [11119] := by simp [poly]
  refine ⟨X - C (8 : ℤ),
    poly [-1390, 1216, -1238, 1235, 2934, -3803, 5084, 4805, -4959, -620, 4092, 4681, 585, 73, 9, 1],
    poly [-1, 1, -1, 1, 2, -3, 4, 3, -4, 0, 3, 3],
    poly [1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1],
    poly [5215, 4477, 1605, 1246, 2591, 4149, 1564, -149, -1753, 3606, 2886, 2796, 5, 1046, 2566, 2756],
    poly [5904, -5166, 2134, -2513, 3511, -951, 1271, -1231, 1236, -190, 2756],
    poly [-4, -3, -1, -1, -2, -3, -1, 0, 1, -3, -2, -2, 0, -1, -2, -2],
    poly [-4, 4, -2, 2, -3, 1, -1, 1, -1, 0, -2],
    poly [-1390, 3996, -5060, 4927, 616, 77, -4160, -520, -65, -8, -1],
    poly [-1, 3, -4, 4, 0, 0, -3],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11527 :
    haveI : Fact (Nat.Prime 11527) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11527 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11527 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((11527 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((11527 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11527) := ⟨by norm_num⟩
  have hP : poly [-98, 1] = X - C (98 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11527 : ℕ) : ℤ[X]) = poly [11527] := by simp [poly]
  refine ⟨X - C (98 : ℤ),
    poly [5293, 54, -3881, -5215, 1123, -2341, 4681, 283, -5643, -4292, 3132, 3443, 5681, -1824, 99, 1],
    poly [45, 0, -33, -44, 10, -20, 40, 2, -48, -36, 27, 29, 48, -16, 1],
    poly [-1, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [-486, 1391, 2704, 3776, 964, 3523, 2961, 3661, -1272, 442, -11, 102, 1397, 5527, 629, 1520],
    poly [11041, -10136, 3190, 1899, 137, 574, 4460, 516, 225, -4130, 4898, -891, 1520],
    poly [4, -12, -23, -32, -8, -30, -25, -31, 11, -4, 0, -1, -12, -47, -5, -13],
    poly [-94, 87, -28, -16, -1, -5, -38, -4, -2, 35, -42, 8, -13],
    poly [-5293, -54, -2353, -24, 235, -4232, -2278, 212, 2237, 4022, 1923, -98, -1],
    poly [-45, 0, -20, 0, 2, -36, -19, 2, 19, 34, 16, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11731 :
    haveI : Fact (Nat.Prime 11731) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11731 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11731 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((11731 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((11731 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11731) := ⟨by norm_num⟩
  have hP : poly [-444, 1] = X - C (444 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11731 : ℕ) : ℤ[X]) = poly [11731] := by simp [poly]
  refine ⟨X - C (444 : ℤ),
    poly [502, -5151, 5484, 4319, 2599, -2055, -216, 3355, 5556, 3368, -970, -5260, 1547, -1846, 445, 1],
    poly [19, -195, 208, 163, 98, -78, -8, 127, 210, 127, -37, -199, 59, -70, 17],
    poly [-1, -1, 1, 0, 1, 0, 0, -1],
    poly [-1179, 4129, 2450, 676, -332, 1251, 4293, 2239, 1019, 3447, 4615, 4829, 2980, 4429, 4353, 7312],
    poly [10552, -7602, 4808, -8761, 76, -2959, 7312],
    poly [44, -157, -93, -26, 12, -48, -163, -85, -39, -131, -175, -183, -113, -168, -165, -277],
    poly [-400, 288, -182, 332, -3, 112, -277],
    poly [-502, 5151, -4480, -3392, 2291, -444, -1],
    poly [-19, 195, -170, -128, 87, -17],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 22 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 21 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11833 :
    haveI : Fact (Nat.Prime 11833) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11833 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11833 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((11833 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((11833 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11833) := ⟨by norm_num⟩
  have hP : poly [-388, 1] = X - C (388 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11833 : ℕ) : ℤ[X]) = poly [11833] := by simp [poly]
  refine ⟨X - C (388 : ℤ),
    poly [5886, -3919, -1230, 3870, 5591, 4833, 5380, 4314, -4533, 3709, -5236, 17, 488, -2896, 389, 1],
    poly [193, -129, -40, 127, 183, 158, 176, 141, -149, 122, -172, 1, 16, -95, 13],
    poly [1, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, -1],
    poly [4395, 2363, -448, 2564, -234, -2742, 3595, 1629, 831, 158, -2619, 1430, 678, 1408, 7, -1308],
    poly [7438, -9801, 2811, 1383, 766, 4092, -5357, 752, -730, 1401, 1315, -1308],
    poly [-144, -77, 15, -84, 8, 90, -118, -53, -27, -5, 86, -47, -22, -46, 0, 43],
    poly [-244, 322, -93, -45, -25, -134, 176, -25, 24, -46, -43, 43],
    poly [5886, 2028, 2689, -786, -307, 2500, 5252, 471, -3384, 3285, -388, -1],
    poly [193, 66, 88, -26, -10, 82, 172, 15, -111, 108, -13],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11867 :
    haveI : Fact (Nat.Prime 11867) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11867 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11867 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((11867 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((11867 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11867) := ⟨by norm_num⟩
  have hP : poly [-983, 1] = X - C (983 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11867 : ℕ) : ℤ[X]) = poly [11867] := by simp [poly]
  refine ⟨X - C (983 : ℤ),
    poly [2173, 3310, 945, 1679, -3125, 4874, -3665, 3461, 5098, -3870, -2020, 843, -2148, -5821, 984, 1],
    poly [180, 274, 78, 139, -259, 404, -304, 287, 422, -321, -167, 70, -178, -482, 82],
    poly [-1, 0, -1, -1, 0, 1, 0, -1, -1, 0, 0, 0, -1],
    poly [-4175, 1712, 1887, 1356, 4120, 2650, 4737, 2880, 3361, 2444, 1429, -238, 2718, -623, -3234,
      -1957],
    poly [7692, -5980, -4000, 1181, 8826, 2349, -1567, -4913, 3341, 2611, -1277, -1957],
    poly [346, -142, -156, -112, -341, -219, -392, -238, -278, -202, -118, 20, -225, 52, 268, 162],
    poly [-637, 496, 331, -98, -731, -194, 130, 407, -277, -216, 106, 162],
    poly [-2173, -1137, 192, -4044, -5835, -4195, 1879, -2992, -3673, -5062, -983, -1],
    poly [-180, -94, 16, -335, -483, -347, 156, -248, -304, -419, -81],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11969 :
    haveI : Fact (Nat.Prime 11969) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11969 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11969 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((11969 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((11969 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11969) := ⟨by norm_num⟩
  have hP : poly [-441, 1] = X - C (441 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11969 : ℕ) : ℤ[X]) = poly [11969] := by simp [poly]
  refine ⟨X - C (441 : ℤ),
    poly [-1737, -2718, 4852, 11, 5401, -3896, 5365, 5386, 5956, 2619, -754, 5155, -314, 3419, 442, 1],
    poly [-64, -100, 179, 0, 199, -144, 198, 198, 219, 96, -28, 190, -12, 126, 16],
    poly [1, -1, 0, 0, -1, -1],
    poly [4552, -133, 942, 1053, 2356, 3526, 1086, -168, -8, 2625, 3988, 1657, -1768, -2400, 964, 3360],
    poly [7417, -2732, -5760, 964, 3360],
    poly [-168, 5, -35, -39, -87, -130, -40, 6, 0, -97, -147, -61, 65, 88, -36, -124],
    poly [-273, 101, 212, -36, -124],
    poly [-1737, 756, -3418, -442, -1],
    poly [-64, 28, -126, -16],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 20 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 19 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12037 :
    haveI : Fact (Nat.Prime 12037) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12037 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12037 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12037 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12037 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12037) := ⟨by norm_num⟩
  have hP : poly [-1582, 1] = X - C (1582 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12037 : ℕ) : ℤ[X]) = poly [12037] := by simp [poly]
  refine ⟨X - C (1582 : ℤ),
    poly [175, 5661, -3466, 4875, 1677, -4412, 1907, 3486, 4012, -3779, -535, -2496, 3643, 611, 1583, 1],
    poly [23, 744, -456, 641, 220, -580, 251, 458, 527, -497, -70, -328, 479, 80, 208],
    poly [-1, -1, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0, -1],
    poly [-853, 3978, 1143, 3751, 4757, -2775, 3292, 823, -434, 2875, 1576, 198, 608, 1080, 2739, 1302],
    poly [11184, -8059, 1143, 4604, -74, 60, 684, 670, 2267, -357, 1437, 1302],
    poly [112, -523, -150, -493, -625, 365, -433, -108, 57, -378, -207, -26, -80, -142, -360, -171],
    poly [-1470, 1060, -151, -605, 10, -8, -90, -88, -298, 47, -189, -171],
    poly [-175, -5661, 3466, -4700, 3809, -4715, -5603, 5528, -4615, 971, -1582, -1],
    poly [-23, -744, 456, -618, 501, -620, -736, 727, -607, 128, -208],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12071 :
    haveI : Fact (Nat.Prime 12071) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12071 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12071 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12071 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12071 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12071) := ⟨by norm_num⟩
  have hP : poly [-1028, 1] = X - C (1028 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12071 : ℕ) : ℤ[X]) = poly [12071] := by simp [poly]
  refine ⟨X - C (1028 : ℤ),
    poly [-2642, -5768, 3975, -2462, -977, -682, -5907, -1133, -2420, 1348, -2171, -4699, 3659, -4435,
      1029, 1],
    poly [-225, -491, 339, -210, -83, -58, -503, -96, -206, 115, -185, -400, 312, -378, 88],
    poly [0, -1, 0, 0, 0, 1, -1, 0, -1, 0, 0, 0, 0, -1, -1],
    poly [-862, 3153, 374, -2576, 1390, 1934, 2733, 1266, 243, 1381, 2298, -1259, 4456, 2665, 2675, 4953],
    poly [12071, -12933, 4015, -2779, -2950, 4828, -4333, 7593, -2158, -3924, 1781, -2288, 2675, 4953],
    poly [73, -269, -32, 219, -119, -165, -233, -108, -21, -118, -196, 107, -380, -227, -228, -422],
    poly [-1028, 1102, -343, 237, 251, -411, 369, -647, 184, 334, -152, 195, -228, -422],
    poly [0, 2642, 3126, 2328, -5634, -4127, -779, 6023, 5830, 264, -2630, 4436, -1029, -1],
    poly [0, 225, 266, 198, -480, -351, -66, 513, 496, 22, -224, 378, -88],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12241 :
    haveI : Fact (Nat.Prime 12241) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12241 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12241 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12241 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12241 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12241) := ⟨by norm_num⟩
  have hP : poly [-91, 1] = X - C (91 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12241 : ℕ) : ℤ[X]) = poly [12241] := by simp [poly]
  refine ⟨X - C (91 : ℤ),
    poly [4170, -2510, 4815, 860, 4583, 1261, -2811, -838, -2296, 6028, -1817, 3881, 3002, -3868, 92, 1],
    poly [31, -19, 36, 6, 34, 9, -21, -6, -17, 45, -14, 29, 22, -29, 1],
    poly [1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1],
    poly [2804, 279, 2269, 3367, 2841, 5122, 4609, 1644, 2284, 2022, 5113, 5416, 2729, 7004, 3150, 1897],
    poly [9437, -9716, -1990, -1098, -2278, 244, -4281, 1588, 421, -5107, -3150, -1897],
    poly [-21, -2, -17, -25, -21, -38, -34, -12, -17, -15, -38, -40, -20, -52, -23, -14],
    poly [-70, 73, 14, 8, 17, -2, 32, -12, -3, 38, 23, 14],
    poly [4170, 5561, -4916, -3955, -4348, 2239, -4818, -4492, 2910, -3869, 92, 1],
    poly [31, 41, -37, -29, -32, 17, -36, -33, 22, -29, 1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12343 :
    haveI : Fact (Nat.Prime 12343) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12343 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12343 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12343 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12343 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12343) := ⟨by norm_num⟩
  have hP : poly [-783, 1] = X - C (783 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12343 : ℕ) : ℤ[X]) = poly [12343] := by simp [poly]
  refine ⟨X - C (783 : ℤ),
    poly [-2869, -1249, 5563, -2121, -2919, 3417, 162, 5218, -4486, 546, -3956, 2927, 1454, -3277, 784,
      1],
    poly [-182, -79, 353, -135, -185, 217, 10, 331, -285, 35, -251, 186, 92, -208, 50],
    poly [1, -1, 0, 0, -1, 0, 0, 1, 0, 1],
    poly [3544, 648, -1137, 43, 3481, 5046, 2179, -2806, 766, 4144, 6371, 1960, -1624, -2401, 2469, 2223],
    poly [8799, -5903, -1111, -2965, 1286, -1023, 2647, -246, -2223],
    poly [-225, -41, 72, -3, -221, -320, -138, 178, -49, -263, -404, -124, 103, 152, -157, -141],
    poly [-558, 375, 70, 188, -82, 65, -168, 16, 141],
    poly [-2869, 4489, 5192, -2153, -2588, 5514, -4060, 783, 1],
    poly [-182, 285, 329, -137, -164, 350, -258, 50],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 23 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12377 :
    haveI : Fact (Nat.Prime 12377) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12377 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12377 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12377 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12377 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12377) := ⟨by norm_num⟩
  have hP : poly [-110, 1] = X - C (110 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12377 : ℕ) : ℤ[X]) = poly [12377] := by simp [poly]
  refine ⟨X - C (110 : ℤ),
    poly [-3038, 760, 3720, -1879, -5643, -4327, -4090, -1950, 1445, 5414, -4339, -3415, -5882, -166,
      111, 1],
    poly [-27, 7, 33, -17, -50, -38, -36, -17, 13, 48, -39, -30, -52, -1, 1],
    poly [0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 1, 1, 1],
    poly [-66, -2542, 586, -2086, -310, -1194, -977, 2288, -4996, -3712, -1675, -1769, -2670, -4591,
      1355, -5117],
    poly [12377, -12311, 2476, -3062, 5148, -4904, 3556, -1993, -2447, 4591, -1355, 5117],
    poly [1, 23, -5, 19, 3, 11, 9, -20, 45, 33, 15, 16, 24, 41, -12, 46],
    poly [-110, 110, -23, 27, -46, 44, -32, 18, 22, -41, 12, -46],
    poly [0, -3038, 3798, -78, -1801, -804, -4283, -3527, -5883, -166, 111, 1],
    poly [0, -27, 34, -1, -16, -7, -38, -31, -52, -1, 1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12479 :
    haveI : Fact (Nat.Prime 12479) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12479 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12479 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12479 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12479 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12479) := ⟨by norm_num⟩
  have hP : poly [-53, 1] = X - C (53 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12479 : ℕ) : ℤ[X]) = poly [12479] := by simp [poly]
  refine ⟨X - C (53 : ℤ),
    poly [-2590, 3012, -885, 1396, -5860, -5526, -1517, -735, 3047, 2412, 4990, 5745, 1992, 2863, 54, 1],
    poly [-11, 13, -4, 6, -25, -23, -6, -3, 13, 10, 21, 24, 8, 12],
    poly [-1, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0, -1],
    poly [-2789, -958, -688, -212, -2793, 1161, -3238, -3321, -6148, -2905, -1902, 236, -3020, -256,
      -4442, -1931],
    poly [9690, -10648, 270, -2313, -750, 1435, -2092, -2394, -1186, -4695, 4186, -2511, -1931],
    poly [12, 4, 3, 1, 12, -5, 14, 14, 26, 12, 8, -1, 13, 1, 19, 8],
    poly [-41, 46, -2, 10, 3, -6, 9, 10, 5, 20, -18, 11, 8],
    poly [2590, -5602, 3897, 309, 1654, 6153, 587, -2108, -3807, 870, -2809, -53, -1],
    poly [11, -24, 17, 1, 7, 26, 2, -9, -16, 4, -12],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12547 :
    haveI : Fact (Nat.Prime 12547) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12547 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12547 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12547 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12547 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12547) := ⟨by norm_num⟩
  have hP : poly [-1010, 1] = X - C (1010 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12547 : ℕ) : ℤ[X]) = poly [12547] := by simp [poly]
  refine ⟨X - C (1010 : ℤ),
    poly [1528, 486, -807, 5018, 241, -2857, 668, -2869, -6090, -2826, 3488, 4339, -3648, 4804, 1011, 1],
    poly [123, 39, -65, 404, 19, -230, 54, -231, -490, -227, 281, 349, -294, 387, 81],
    poly [-1, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0, -1],
    poly [-2406, -2309, 39, 737, 688, 278, -592, -1214, -4370, -50, -1288, -4221, -1876, 3406, 231,
      -4058],
    poly [10141, -12450, -58, 795, 2299, -2118, -3228, -993, -883, 4289, -4058],
    poly [194, 186, -3, -59, -55, -22, 48, 98, 352, 4, 104, 340, 151, -274, -18, 327],
    poly [-816, 1003, 4, -64, -185, 171, 260, 80, 71, -345, 327],
    poly [-1528, 1042, -235, -4783, 6070, -4255, 766, -5105, -3794, -1010, -1],
    poly [-123, 84, -19, -385, 489, -343, 62, -411, -305, -81],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12853 :
    haveI : Fact (Nat.Prime 12853) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12853 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12853 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((12853 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((12853 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12853) := ⟨by norm_num⟩
  have hP : poly [-27, 1] = X - C (27 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12853 : ℕ) : ℤ[X]) = poly [12853] := by simp [poly]
  refine ⟨X - C (27 : ℤ),
    poly [476, 5254, 5907, 3551, -6057, 4536, 644, 2404, 89, -3329, 4161, -798, -5266, 757, 28, 1],
    poly [1, 11, 12, 7, -13, 10, 1, 5, 0, -7, 9, -2, -11, 2],
    poly [1, 0, -1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1],
    poly [-694, -4528, -4670, -1343, -4076, -1321, -1695, -3613, -3208, -3193, 2520, -4885, -1827, -5046,
      -2309, -6968],
    poly [13547, -9019, -552, -7161, 2591, 572, -2359, 5367, 3749, 2737, -4659, 6968],
    poly [2, 10, 10, 3, 9, 3, 4, 8, 7, 7, -5, 11, 4, 11, 5, 15],
    poly [-29, 20, 1, 15, -6, -1, 5, -12, -8, -6, 10, -15],
    poly [476, 4778, 177, 5719, 2592, 96, 5716, 4496, -6022, 729, 27, 1],
    poly [1, 10, 0, 12, 5, 0, 12, 9, -13, 2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_13159 :
    haveI : Fact (Nat.Prime 13159) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 13159 (uff fact_prime_dezessete.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((13159 : ℕ) : ℤ[X]) * A = Φ17 ∧
        (((13159 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ17 ∧ P = G * QP + RP * Φ17 ∧
          G = C1 * P + C2 * ((13159 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 13159) := ⟨by norm_num⟩
  have hP : poly [-745, 1] = X - C (745 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((13159 : ℕ) : ℤ[X]) = poly [13159] := by simp [poly]
  refine ⟨X - C (745 : ℤ),
    poly [4928, -1901, 3848, 4103, -2432, 1975, -3371, -2601, 5790, 520, -4786, -3751, 1461, 3093, 746,
      1],
    poly [279, -108, 218, 232, -138, 112, -191, -147, 328, 29, -271, -212, 83, 175, 42],
    poly [1, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, -1],
    poly [5226, 3661, 4807, 2530, -1041, 3264, 532, 2171, 4805, -773, -1540, 1603, 1042, 2260, 460, 1694],
    poly [7933, -11594, -1146, 7503, 2006, -3159, 455, 16, 106, -1234, 1694],
    poly [-296, -207, -272, -143, 59, -185, -30, -123, -272, 44, 87, -91, -59, -128, -26, -96],
    poly [-449, 657, 64, -425, -113, 179, -26, -1, -6, 70, -96],
    poly [4928, 6330, 5749, -4673, 294, -1342, -5601, 2377, -2346, -745, -1],
    poly [279, 358, 325, -265, 17, -76, -317, 135, -133, -42],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 25 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)


/-- Fora da lista, um primo `p ≠ 17` tem ordem módulo 17 maior que `log_p 13254`. -/
theorem ordem_grande {p : ℕ} (hple : p ≤ 13254) (hp : p.Prime) (hL : p ∉ primosCertificados)
    {i : ℕ} (hi : i ≤ Nat.log p 13254) (hi1 : 1 ≤ i) : p ^ i % 17 ≠ 1 := by
  intro heq
  have hpow : p ^ i ≤ 13254 := Nat.pow_le_of_le_log (by norm_num) hi
  have h2 := hp.two_le
  have hi15 : i < 15 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 15 ≤ p ^ i := (Nat.pow_le_pow_left h2 15).trans (Nat.pow_le_pow_right (by omega) hc)
    omega
  have hc : condicao p = true := by
    simp only [condicao, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨i, hi15, ⟨hi1, hpow⟩, heq⟩
  have hok := excecoes p hple
  simp only [teste, hc, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.contains_iff_mem,
    beq_iff_eq, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with (hm | h1) | ⟨q, hq, hqp, hmod⟩
  · exact hL hm
  · subst h1; exact Nat.not_prime_one hp
  · have hq2 : 2 ≤ q := by
      simp only [primosPequenos, List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
    rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

set_option maxHeartbeats 0 in
variable (K) in
/-- **`𝓞(ℚ(ζ₁₇))` é principal.** -/
theorem pid_dezessete : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 17
  rw [minkowski_dezessete, ciclotomico_dezessete]
  intro p hple hp hpn
  have hple' : p ≤ 13254 := (Finset.mem_Icc.mp hple).2
  by_cases hL : p ∈ primosCertificados
  · simp only [primosCertificados, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr certificado_2
    · exact Or.inr certificado_67
    · exact Or.inr certificado_101
    · exact Or.inr certificado_103
    · exact Or.inr certificado_137
    · exact Or.inr certificado_239
    · exact Or.inr certificado_307
    · exact Or.inr certificado_409
    · exact Or.inr certificado_443
    · exact Or.inr certificado_613
    · exact Or.inr certificado_647
    · exact Or.inr certificado_919
    · exact Or.inr certificado_953
    · exact Or.inr certificado_1021
    · exact Or.inr certificado_1123
    · exact Or.inr certificado_1259
    · exact Or.inr certificado_1327
    · exact Or.inr certificado_1361
    · exact Or.inr certificado_1429
    · exact Or.inr certificado_1531
    · exact Or.inr certificado_1667
    · exact Or.inr certificado_1871
    · exact Or.inr certificado_1973
    · exact Or.inr certificado_2143
    · exact Or.inr certificado_2347
    · exact Or.inr certificado_2381
    · exact Or.inr certificado_2551
    · exact Or.inr certificado_2687
    · exact Or.inr certificado_2789
    · exact Or.inr certificado_2857
    · exact Or.inr certificado_3061
    · exact Or.inr certificado_3163
    · exact Or.inr certificado_3299
    · exact Or.inr certificado_3469
    · exact Or.inr certificado_3571
    · exact Or.inr certificado_3673
    · exact Or.inr certificado_3877
    · exact Or.inr certificado_3911
    · exact Or.inr certificado_4013
    · exact Or.inr certificado_4217
    · exact Or.inr certificado_4421
    · exact Or.inr certificado_4523
    · exact Or.inr certificado_4591
    · exact Or.inr certificado_4931
    · exact Or.inr certificado_4999
    · exact Or.inr certificado_5101
    · exact Or.inr certificado_5237
    · exact Or.inr certificado_5407
    · exact Or.inr certificado_5441
    · exact Or.inr certificado_5849
    · exact Or.inr certificado_6053
    · exact Or.inr certificado_6121
    · exact Or.inr certificado_6257
    · exact Or.inr certificado_6359
    · exact Or.inr certificado_6427
    · exact Or.inr certificado_6529
    · exact Or.inr certificado_6563
    · exact Or.inr certificado_6733
    · exact Or.inr certificado_6869
    · exact Or.inr certificado_6971
    · exact Or.inr certificado_7039
    · exact Or.inr certificado_7243
    · exact Or.inr certificado_7481
    · exact Or.inr certificado_7549
    · exact Or.inr certificado_7583
    · exact Or.inr certificado_7753
    · exact Or.inr certificado_8059
    · exact Or.inr certificado_8093
    · exact Or.inr certificado_8161
    · exact Or.inr certificado_8263
    · exact Or.inr certificado_8297
    · exact Or.inr certificado_8467
    · exact Or.inr certificado_8501
    · exact Or.inr certificado_8807
    · exact Or.inr certificado_9011
    · exact Or.inr certificado_9181
    · exact Or.inr certificado_9283
    · exact Or.inr certificado_9419
    · exact Or.inr certificado_9521
    · exact Or.inr certificado_9623
    · exact Or.inr certificado_9929
    · exact Or.inr certificado_10099
    · exact Or.inr certificado_10133
    · exact Or.inr certificado_10303
    · exact Or.inr certificado_10337
    · exact Or.inr certificado_10711
    · exact Or.inr certificado_10847
    · exact Or.inr certificado_10949
    · exact Or.inr certificado_11119
    · exact Or.inr certificado_11527
    · exact Or.inr certificado_11731
    · exact Or.inr certificado_11833
    · exact Or.inr certificado_11867
    · exact Or.inr certificado_11969
    · exact Or.inr certificado_12037
    · exact Or.inr certificado_12071
    · exact Or.inr certificado_12241
    · exact Or.inr certificado_12343
    · exact Or.inr certificado_12377
    · exact Or.inr certificado_12479
    · exact Or.inr certificado_12547
    · exact Or.inr certificado_12853
    · exact Or.inr certificado_13159
  · left
    exact orderOf_lt_of _ (fun i hi hi1 => ordem_grande hple' hp hL hi hi1)

set_option backward.isDefEq.respectTransparency false in
/-- **`17` é um primo regular.** -/
theorem regular_dezessete : IsRegularPrime 17 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (pid_dezessete (CyclotomicField _ ℚ))

/-- **Último teorema de Fermat para `n = 17`.** -/
theorem flt_dezessete : FermatLastTheoremFor 17 :=
  @flt_regular 17 fact_prime_dezessete regular_dezessete (by norm_num)

end ATK.FermatDezessete

#print axioms ATK.FermatDezessete.piso_dezessete
#print axioms ATK.FermatDezessete.minkowski_dezessete
#print axioms ATK.FermatDezessete.ciclotomico_dezessete
#print axioms ATK.FermatDezessete.phi_poly
#print axioms ATK.FermatDezessete.teste_0
#print axioms ATK.FermatDezessete.teste_1
#print axioms ATK.FermatDezessete.teste_2
#print axioms ATK.FermatDezessete.teste_3
#print axioms ATK.FermatDezessete.teste_4
#print axioms ATK.FermatDezessete.teste_5
#print axioms ATK.FermatDezessete.teste_6
#print axioms ATK.FermatDezessete.teste_7
#print axioms ATK.FermatDezessete.teste_8
#print axioms ATK.FermatDezessete.teste_9
#print axioms ATK.FermatDezessete.teste_10
#print axioms ATK.FermatDezessete.teste_11
#print axioms ATK.FermatDezessete.teste_12
#print axioms ATK.FermatDezessete.teste_13
#print axioms ATK.FermatDezessete.excecoes
#print axioms ATK.FermatDezessete.certificado_2
#print axioms ATK.FermatDezessete.certificado_67
#print axioms ATK.FermatDezessete.certificado_101
#print axioms ATK.FermatDezessete.certificado_103
#print axioms ATK.FermatDezessete.certificado_137
#print axioms ATK.FermatDezessete.certificado_239
#print axioms ATK.FermatDezessete.certificado_307
#print axioms ATK.FermatDezessete.certificado_409
#print axioms ATK.FermatDezessete.certificado_443
#print axioms ATK.FermatDezessete.certificado_613
#print axioms ATK.FermatDezessete.certificado_647
#print axioms ATK.FermatDezessete.certificado_919
#print axioms ATK.FermatDezessete.certificado_953
#print axioms ATK.FermatDezessete.certificado_1021
#print axioms ATK.FermatDezessete.certificado_1123
#print axioms ATK.FermatDezessete.certificado_1259
#print axioms ATK.FermatDezessete.certificado_1327
#print axioms ATK.FermatDezessete.certificado_1361
#print axioms ATK.FermatDezessete.certificado_1429
#print axioms ATK.FermatDezessete.certificado_1531
#print axioms ATK.FermatDezessete.certificado_1667
#print axioms ATK.FermatDezessete.certificado_1871
#print axioms ATK.FermatDezessete.certificado_1973
#print axioms ATK.FermatDezessete.certificado_2143
#print axioms ATK.FermatDezessete.certificado_2347
#print axioms ATK.FermatDezessete.certificado_2381
#print axioms ATK.FermatDezessete.certificado_2551
#print axioms ATK.FermatDezessete.certificado_2687
#print axioms ATK.FermatDezessete.certificado_2789
#print axioms ATK.FermatDezessete.certificado_2857
#print axioms ATK.FermatDezessete.certificado_3061
#print axioms ATK.FermatDezessete.certificado_3163
#print axioms ATK.FermatDezessete.certificado_3299
#print axioms ATK.FermatDezessete.certificado_3469
#print axioms ATK.FermatDezessete.certificado_3571
#print axioms ATK.FermatDezessete.certificado_3673
#print axioms ATK.FermatDezessete.certificado_3877
#print axioms ATK.FermatDezessete.certificado_3911
#print axioms ATK.FermatDezessete.certificado_4013
#print axioms ATK.FermatDezessete.certificado_4217
#print axioms ATK.FermatDezessete.certificado_4421
#print axioms ATK.FermatDezessete.certificado_4523
#print axioms ATK.FermatDezessete.certificado_4591
#print axioms ATK.FermatDezessete.certificado_4931
#print axioms ATK.FermatDezessete.certificado_4999
#print axioms ATK.FermatDezessete.certificado_5101
#print axioms ATK.FermatDezessete.certificado_5237
#print axioms ATK.FermatDezessete.certificado_5407
#print axioms ATK.FermatDezessete.certificado_5441
#print axioms ATK.FermatDezessete.certificado_5849
#print axioms ATK.FermatDezessete.certificado_6053
#print axioms ATK.FermatDezessete.certificado_6121
#print axioms ATK.FermatDezessete.certificado_6257
#print axioms ATK.FermatDezessete.certificado_6359
#print axioms ATK.FermatDezessete.certificado_6427
#print axioms ATK.FermatDezessete.certificado_6529
#print axioms ATK.FermatDezessete.certificado_6563
#print axioms ATK.FermatDezessete.certificado_6733
#print axioms ATK.FermatDezessete.certificado_6869
#print axioms ATK.FermatDezessete.certificado_6971
#print axioms ATK.FermatDezessete.certificado_7039
#print axioms ATK.FermatDezessete.certificado_7243
#print axioms ATK.FermatDezessete.certificado_7481
#print axioms ATK.FermatDezessete.certificado_7549
#print axioms ATK.FermatDezessete.certificado_7583
#print axioms ATK.FermatDezessete.certificado_7753
#print axioms ATK.FermatDezessete.certificado_8059
#print axioms ATK.FermatDezessete.certificado_8093
#print axioms ATK.FermatDezessete.certificado_8161
#print axioms ATK.FermatDezessete.certificado_8263
#print axioms ATK.FermatDezessete.certificado_8297
#print axioms ATK.FermatDezessete.certificado_8467
#print axioms ATK.FermatDezessete.certificado_8501
#print axioms ATK.FermatDezessete.certificado_8807
#print axioms ATK.FermatDezessete.certificado_9011
#print axioms ATK.FermatDezessete.certificado_9181
#print axioms ATK.FermatDezessete.certificado_9283
#print axioms ATK.FermatDezessete.certificado_9419
#print axioms ATK.FermatDezessete.certificado_9521
#print axioms ATK.FermatDezessete.certificado_9623
#print axioms ATK.FermatDezessete.certificado_9929
#print axioms ATK.FermatDezessete.certificado_10099
#print axioms ATK.FermatDezessete.certificado_10133
#print axioms ATK.FermatDezessete.certificado_10303
#print axioms ATK.FermatDezessete.certificado_10337
#print axioms ATK.FermatDezessete.certificado_10711
#print axioms ATK.FermatDezessete.certificado_10847
#print axioms ATK.FermatDezessete.certificado_10949
#print axioms ATK.FermatDezessete.certificado_11119
#print axioms ATK.FermatDezessete.certificado_11527
#print axioms ATK.FermatDezessete.certificado_11731
#print axioms ATK.FermatDezessete.certificado_11833
#print axioms ATK.FermatDezessete.certificado_11867
#print axioms ATK.FermatDezessete.certificado_11969
#print axioms ATK.FermatDezessete.certificado_12037
#print axioms ATK.FermatDezessete.certificado_12071
#print axioms ATK.FermatDezessete.certificado_12241
#print axioms ATK.FermatDezessete.certificado_12343
#print axioms ATK.FermatDezessete.certificado_12377
#print axioms ATK.FermatDezessete.certificado_12479
#print axioms ATK.FermatDezessete.certificado_12547
#print axioms ATK.FermatDezessete.certificado_12853
#print axioms ATK.FermatDezessete.certificado_13159
#print axioms ATK.FermatDezessete.ordem_grande
#print axioms ATK.FermatDezessete.pid_dezessete
#print axioms ATK.FermatDezessete.regular_dezessete
#print axioms ATK.FermatDezessete.flt_dezessete
