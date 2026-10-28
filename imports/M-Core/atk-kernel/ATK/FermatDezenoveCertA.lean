import ATK.FermatDezenoveBase

/-!
# ATK — Certificados para `𝓞(ℚ(ζ₁₉))` principal (parte A)

Primos 7 a 17443 da lista de `ATK.FermatDezenove`: para cada um, um gerador do ideal
primo e as identidades polinomiais do critério `pid6`, conferidas por reflexão (`ATK.PolyLista`).
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista
  ATK.FermatDezenoveBase

namespace ATK.FermatDezenoveCertA

set_option maxHeartbeats 4000000 in
theorem certificado_7 :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : poly [-1, 0, -2, 1] = (X ^ 3 - 2 * X ^ 2 - 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7 : ℕ) : ℤ[X]) = poly [7] := by simp [poly]
  refine ⟨(X ^ 3 - 2 * X ^ 2 - 1 : ℤ[X]),
    poly [-1, -1, 1, 0, 3, 0, 0, 2, -1, 2, 3, 1, 2, 0, 3, 1],
    poly [0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    poly [-1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1],
    poly [-3, -1, 0, 0, 0, 1, 1, -1, 0, -3, 0, 0, -2, 1, -2, -3, -1, -2],
    poly [4, -5, 1, 0, -3, 3, 1, -2, 1, -2],
    poly [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1],
    poly [0, 0, -1, 2, 0, -1, 1, -1, 0, 1],
    poly [1, 0, -2, 1, -2, 3, -2, -1],
    poly [0, 0, 0, 0, -1, 1, -1, 1, -1],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 3 - 2 * X ^ 2 - 1 : ℤ[X])).natDegree = 3 by compute_degree!]
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
    exact igual_de_listas 24 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11 :
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((11 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((11 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hP : poly [-1, 2, 1, 1] = (X ^ 3 + X ^ 2 + 2 * X - 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11 : ℕ) : ℤ[X]) = poly [11] := by simp [poly]
  refine ⟨(X ^ 3 + X ^ 2 + 2 * X - 1 : ℤ[X]),
    poly [-1, -3, 3, 1, 1, 5, 0, 5, 3, -1, 5, 0, 3, -1, 0, 1],
    poly [0, 0, 1, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1],
    poly [-1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-2, 4, 2, 2, 6, 1, 6, 4, 0, 6, 1, 4, 0, 1, 2, 1, 1, 1],
    poly [9, -7, 4, -2, 4, -1, 0, 1, 0, 0, 1],
    poly [0, -1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    poly [-1, 2, -1, 1, -1, 1],
    poly [1, 3, -4, -4, 2, -4, 1, 1, -1],
    poly [0, 0, -1, 0, 1, 0, 1],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 3 + X ^ 2 + 2 * X - 1 : ℤ[X])).natDegree = 3 by compute_degree!]
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
    exact igual_de_listas 28 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 20 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_37 :
    haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 37 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((37 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((37 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((37 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hP : poly [1, 3, 1] = (X ^ 2 + 3 * X + 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((37 : ℕ) : ℤ[X]) = poly [37] := by simp [poly]
  refine ⟨(X ^ 2 + 3 * X + 1 : ℤ[X]),
    poly [1, -2, 6, -15, 3, 7, 14, -11, -17, -11, 14, 7, 3, -15, 6, -2, 1],
    poly [0, 0, 0, 0, 1, 0, -1, -1, 1, 2, 1, -1, -1, 0, 1],
    poly [-1, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1],
    poly [-6, -9, 6, 1, 1, 6, -9, -6, 0, -21, -1, -3, -17, -10, -17, -3, -1, -21],
    poly [31, -40, 9, -8, 15, 0, -21, 5, 6, -23, 20, -21],
    poly [1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1],
    poly [2, 2, -1, 0, 0, 1, 1, -1, 0, 0, 0, 1],
    poly [-1, 3, -9, -13, 11, 17, 11, -13, -9, 3, -1],
    poly [0, 0, 0, 1, 1, -1, -2, -1, 1, 1],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 2 + 3 * X + 1 : ℤ[X])).natDegree = 2 by compute_degree!]
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
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_113 :
    haveI : Fact (Nat.Prime 113) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 113 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((113 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((113 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((113 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 113) := ⟨by norm_num⟩
  have hP : poly [1, 3, 1] = (X ^ 2 + 3 * X + 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((113 : ℕ) : ℤ[X]) = poly [113] := by simp [poly]
  refine ⟨(X ^ 2 + 3 * X + 1 : ℤ[X]),
    poly [1, -2, 6, -15, 40, 9, 47, -36, -51, -36, 47, 9, 40, -15, 6, -2, 1],
    poly [0, 0, 0, 0, 0, -1, -1, -1, 1, 2, 1, -1, -1, -1],
    poly [0, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, -1, -1, -1],
    poly [5, -11, 32, 32, -11, 5, 0, -1, 7, -16, 45, -2, -35, -2, 45, -16, 7, -1],
    poly [113, -108, -11, 32, 32, -16, 21, -43, -1, 45, -16, 7, -1],
    poly [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1],
    poly [1, 2, -2, -1, 1, 1, 0, 0, -1, 0, 1],
    poly [0, -1, 2, -6, 15, -39, -12, -39, 15, -6, 2, -1],
    poly [0, 0, 0, 0, 0, 0, 1, 1, 1],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 2 + 3 * X + 1 : ℤ[X])).natDegree = 2 by compute_degree!]
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
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 26 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_151 :
    haveI : Fact (Nat.Prime 151) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 151 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((151 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((151 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((151 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 151) := ⟨by norm_num⟩
  have hP : poly [1, 43, 1] = (X ^ 2 + 43 * X + 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((151 : ℕ) : ℤ[X]) = poly [151] := by simp [poly]
  refine ⟨(X ^ 2 + 43 * X + 1 : ℤ[X]),
    poly [1, -42, -6, -1, 50, -34, 54, -22, -13, -22, 54, -34, 50, -1, -6, -42, 1],
    poly [0, 0, 12, 2, 0, -14, 9, -15, 6, 4, 6, -15, 9, -14, 0, 2, 12],
    poly [0, 0, -1, 0, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1],
    poly [-22, -22, 0, -40, -3, -44, 21, -15, -42, -53, -6, -53, -42, -15, 21, -44, -3, -40],
    poly [151, -151, -22, 0, 22, -40, 37, -63, 43, -14, -67, -36, 65, -41, 37, -40],
    poly [11, 5, 5, 11, 0, 10, -1, 17, 7, -1, -4, 9, -4, -1, 7, 17, -1, 10],
    poly [1, 42, -31, -7, 0, 6, -11, 21, -6, 12, 7, -8, -10, 18, -11, 10],
    poly [0, 0, -1, 43, -36, -5, -51, -68, -46, -68, -51, -5, -36, 43, -1],
    poly [0, 0, 0, 0, -12, 10, 2, 15, 20, 14, 20, 15, 2, 10, -12],
    by monicity!, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ((X ^ 2 + 43 * X + 1 : ℤ[X])).natDegree = 2 by compute_degree!]
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
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_191 :
    haveI : Fact (Nat.Prime 191) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 191 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((191 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((191 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((191 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 191) := ⟨by norm_num⟩
  have hP : poly [-5, 1] = X - C (5 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((191 : ℕ) : ℤ[X]) = poly [191] := by simp [poly]
  refine ⟨X - C (5 : ℤ),
    poly [38, -69, -14, -3, -39, -8, -40, 30, 44, 85, 55, 49, 86, 17, -35, 31, 6, 1],
    poly [1, -2, 0, 0, -1, 0, -1, 1, 1, 2, 1, 1, 2, 0, -1, 1],
    poly [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1],
    poly [70, 84, 125, 95, 89, 126, 57, 5, 71, 46, 41, 40, 78, -29, 26, 37, 1, 32],
    poly [191, -121, 14, 41, -30, -6, 107, -55, -11, 36, -31, 32],
    poly [-2, -2, -3, -2, -2, -3, -1, 0, -2, -1, -1, -1, -2, 1, -1, -1, 0, -1],
    poly [-5, 4, -1, -1, 1, 0, -3, 2, 0, -1, 1, -1],
    poly [0, -38, -84, -55, -11, 36, -69, -52, 66, -25, -5, -1],
    poly [0, -1, -2, -1, 0, 1, -2, -1, 2, -1],
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
theorem certificado_227 :
    haveI : Fact (Nat.Prime 227) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 227 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((227 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((227 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((227 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 227) := ⟨by norm_num⟩
  have hP : poly [1, 8, 1] = (X ^ 2 + 8 * X + 1 : ℤ[X]) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((227 : ℕ) : ℤ[X]) = poly [227] := by simp [poly]
  refine ⟨(X ^ 2 + 8 * X + 1 : ℤ[X]),
    poly [1, -7, 56, 14, 60, -39, 26, 59, -43, 59, 26, -39, 60, 14, 56, -7, 1],
    poly [0, 0, 0, -2, -1, -2, 1, -1, -2, 1, -2, -1, 1, -2, -1, -2],
    poly [-1, -1, -1, 0, -1, -1, -1, -1, -1, 0, -1, -1, -1],
    poly [-42, 21, 13, 14, 14, 13, 21, -42, 0, -46, 53, -12, -45, 57, -45, -12, 53, -46],
    poly [185, -206, 13, 56, -49, 21, 20, -42, 1, -12, 53, -46],
    poly [1, 0, 2, 2, 2, 2, 2, 2, 0, 1, 0, 3, 1, 0, 3, 0, 1, 3],
    poly [2, 7, -5, 0, 3, 0, 2, 2, 0, 0, 1, 3],
    poly [-1, 7, -56, -13, -68, 102, -68, -13, -56, 7, -1],
    poly [0, 0, 0, 2, 1, 2, -3, 2, 1, 2],
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
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 27 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_229 :
    haveI : Fact (Nat.Prime 229) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 229 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((229 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((229 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((229 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 229) := ⟨by norm_num⟩
  have hP : poly [-16, 1] = X - C (16 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((229 : ℕ) : ℤ[X]) = poly [229] := by simp [poly]
  refine ⟨X - C (16 : ℤ),
    poly [-43, -60, -104, 65, 4, -100, 8, 72, 76, 19, 87, 34, 45, 60, 18, 44, 17, 1],
    poly [-3, -4, -7, 5, 0, -7, 1, 5, 5, 1, 6, 2, 3, 4, 1, 3, 1],
    poly [1, 0, -1, -1],
    poly [186, -60, 125, 65, 4, 129, 8, 72, 76, 19, 87, 34, 45, 60, 18, 44, 17, 1],
    poly [43, 17, 1],
    poly [-13, 5, -9, -4, 0, -9, 0, -5, -5, -1, -6, -2, -3, -4, -1, -3, -1],
    poly [-3, -1],
    poly [-43, -17, -1],
    poly [-3, -1],
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
    exact igual_de_listas 18 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_419 :
    haveI : Fact (Nat.Prime 419) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 419 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((419 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((419 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((419 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 419) := ⟨by norm_num⟩
  have hP : poly [-7, 1] = X - C (7 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((419 : ℕ) : ℤ[X]) = poly [419] := by simp [poly]
  refine ⟨X - C (7 : ℤ),
    poly [-60, 111, -104, -15, -122, 162, 23, 63, -51, -187, 33, -175, -85, -132, -19, 57, 8, 1],
    poly [-1, 2, -2, 0, -2, 3, 0, 1, -1, -3, 1, -3, -1, -2, 0, 1],
    poly [1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1],
    poly [53, -119, 36, 118, 10, -185, -153, 91, 66, -177, -92, -20, 110, -51, -74, -197, -35, 48],
    poly [366, -247, -155, -82, 161, 23, 123, -162, -83, 48],
    poly [-1, 2, -1, -2, 0, 3, 2, -2, -1, 3, 1, 0, -2, 1, 1, 3, 0, -1],
    poly [-6, 5, 2, 1, -3, 0, -2, 3, 1, -1],
    poly [-60, 171, 204, 89, -47, 113, 76, -49, -7, -1],
    poly [-1, 3, 3, 1, -1, 2, 1, -1],
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
theorem certificado_457 :
    haveI : Fact (Nat.Prime 457) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 457 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((457 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((457 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((457 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 457) := ⟨by norm_num⟩
  have hP : poly [-16, 1] = X - C (16 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((457 : ℕ) : ℤ[X]) = poly [457] := by simp [poly]
  refine ⟨X - C (16 : ℤ),
    poly [-200, 16, -199, 216, 42, -26, 84, 148, 152, 38, 88, 34, 202, -16, -201, -184, 17, 1],
    poly [-7, 1, -7, 8, 1, -1, 3, 5, 5, 1, 3, 1, 7, -1, -7, -6, 1],
    poly [-1, -1, 0, -1],
    poly [8, 237, 337, 229, 108, 129, 216, 250, 195, 163, 161, 218, 193, 220, 136, 245, 109, 329],
    poly [465, -220, 329],
    poly [-1, -9, -12, -8, -4, -5, -8, -9, -7, -6, -6, -8, -7, -8, -5, -9, -4, -12],
    poly [-17, 8, -12],
    poly [200, -16, -1],
    poly [7, -1],
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
theorem certificado_571 :
    haveI : Fact (Nat.Prime 571) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 571 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((571 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((571 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((571 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 571) := ⟨by norm_num⟩
  have hP : poly [-31, 1] = X - C (31 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((571 : ℕ) : ℤ[X]) = poly [571] := by simp [poly]
  refine ⟨X - C (31 : ℤ),
    poly [221, -85, 163, 171, 116, 280, 9, -55, -186, 215, 99, 40, -54, 164, -50, -149, 32, 1],
    poly [12, -5, 9, 9, 6, 15, 0, -3, -10, 12, 5, 2, -3, 9, -3, -8, 2],
    poly [0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [-127, -39, -73, 18, -108, -241, 31, -126, -260, -338, -230, -116, -186, -133, -426, -196, -207,
      -60],
    poly [571, -571, 0, -127, 88, -161, 179, -160, -42, 146, -290, 11, -147, -60],
    poly [7, 2, 4, -1, 6, 13, -2, 7, 14, 18, 12, 6, 10, 7, 23, 10, 11, 3],
    poly [-31, 32, -1, 7, -5, 9, -10, 9, 2, -8, 16, -1, 8, 3],
    poly [0, 0, 0, -221, -265, 102, -273, -193, -172, -245, -100, 181, -31, -1],
    poly [0, 0, 0, -12, -14, 6, -15, -10, -9, -13, -5, 10, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_647 :
    haveI : Fact (Nat.Prime 647) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 647 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((647 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((647 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((647 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 647) := ⟨by norm_num⟩
  have hP : poly [-55, 1] = X - C (55 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((647 : ℕ) : ℤ[X]) = poly [647] := by simp [poly]
  refine ⟨X - C (55 : ℤ),
    poly [-200, -86, 69, 13, -188, -274, -5, 94, -163, 197, -267, 101, -57, 46, -58, -154, 56, 1],
    poly [-17, -7, 6, 1, -16, -23, 0, 8, -14, 17, -23, 9, -5, 4, -5, -13, 5],
    poly [1, 0, 0, 0, -1, -1],
    poly [360, -104, 264, 106, 209, 105, 9, 219, 164, 163, -37, 77, 232, 176, -25, -111, 158, 257],
    poly [287, -183, -368, 158, 257],
    poly [-31, 9, -23, -9, -18, -9, -1, -19, -14, -14, 3, -7, -20, -15, 2, 9, -14, -22],
    poly [-24, 16, 31, -14, -22],
    poly [-200, 114, 155, -56, -1],
    poly [-17, 10, 13, -5],
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
theorem certificado_761 :
    haveI : Fact (Nat.Prime 761) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 761 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((761 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((761 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((761 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 761) := ⟨by norm_num⟩
  have hP : poly [-25, 1] = X - C (25 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((761 : ℕ) : ℤ[X]) = poly [761] := by simp [poly]
  refine ⟨X - C (25 : ℤ),
    poly [-274, -11, -244, -162, 237, -21, 60, 185, 190, 38, 245, -112, 239, -234, 295, -110, 26, 1],
    poly [-9, 0, -8, -5, 8, -1, 2, 6, 6, 1, 8, -4, 8, -8, 10, -4, 1],
    poly [1, 0, 0, -1, 0, 0, 0, -1],
    poly [383, 307, 30, 232, 27, 171, 55, 233, 301, -92, 288, 151, -98, 166, 207, 26, -103, 318],
    poly [378, -685, 277, 181, 129, -421, 318],
    poly [-13, -10, -1, -8, -1, -6, -2, -8, -10, 3, -10, -5, 3, -6, -7, -1, 3, -11],
    poly [-12, 23, -10, -6, -4, 14, -11],
    poly [-274, 263, -233, 356, 136, -25, -1],
    poly [-9, 9, -8, 12, 4, -1],
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
theorem certificado_1103 :
    haveI : Fact (Nat.Prime 1103) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1103 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1103 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((1103 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((1103 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1103) := ⟨by norm_num⟩
  have hP : poly [-17, 1] = X - C (17 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1103 : ℕ) : ℤ[X]) = poly [1103] := by simp [poly]
  refine ⟨X - C (17 : ℤ),
    poly [519, 290, 17, 520, -229, 246, -310, 371, -108, 318, -176, 314, -306, 501, -295, 307, 18, 1],
    poly [8, 4, 0, 8, -4, 4, -5, 6, -2, 5, -3, 5, -5, 8, -5, 5],
    poly [-1, -1, -1, 0, -1],
    poly [246, 520, 601, 476, 274, 327, 395, 399, 529, 342, 331, 525, 212, 518, 536, 18, 831, 230],
    poly [1349, -583, 601, 230],
    poly [-4, -8, -9, -7, -4, -5, -6, -6, -8, -5, -5, -8, -3, -8, -8, 0, -13, -3],
    poly [-21, 10, -10, -3],
    poly [-519, -290, -17, -1],
    poly [-8, -4],
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
theorem certificado_1217 :
    haveI : Fact (Nat.Prime 1217) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1217 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1217 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((1217 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((1217 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1217) := ⟨by norm_num⟩
  have hP : poly [-76, 1] = X - C (76 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1217 : ℕ) : ℤ[X]) = poly [1217] := by simp [poly]
  refine ⟨X - C (76 : ℤ),
    poly [16, -240, 205, 387, -91, 255, -413, 539, -89, 223, 99, -351, -453, -38, -593, -232, 77, 1],
    poly [1, -15, 13, 24, -6, 16, -26, 34, -6, 14, 6, -22, -28, -2, -37, -14, 5],
    poly [1, 0, 0, 0, 0, 1, 1, 0, 0, -1],
    poly [1101, 523, 35, 541, 964, 281, 256, 656, 341, 513, 195, 415, 546, 884, 344, 465, 963, 297],
    poly [116, -639, 488, -506, -423, -418, -498, 666, 297],
    poly [-69, -32, -2, -34, -60, -17, -16, -41, -21, -32, -12, -26, -34, -55, -21, -29, -60, -18],
    poly [-7, 40, -31, 32, 26, 26, 31, -42, -18],
    poly [16, -256, 445, 182, -478, 362, 309, -76, -1],
    poly [1, -16, 28, 11, -30, 23, 19, -5],
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
theorem certificado_1483 :
    haveI : Fact (Nat.Prime 1483) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1483 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1483 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((1483 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((1483 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1483) := ⟨by norm_num⟩
  have hP : poly [-82, 1] = X - C (82 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1483 : ℕ) : ℤ[X]) = poly [1483] := by simp [poly]
  refine ⟨X - C (82 : ℤ),
    poly [-633, 571, 441, -284, 521, -66, 596, -47, -724, -678, 263, -250, -202, 522, 567, -608, 83, 1],
    poly [-35, 32, 24, -16, 29, -4, 33, -3, -40, -37, 15, -14, -11, 29, 31, -34, 5],
    poly [-1, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    poly [-182, 286, -70, -2, 35, -272, -330, 31, 162, 37, -489, 228, 291, 129, -90, 685, 387, 94],
    poly [1301, -1015, -356, 68, 219, -775, 298, 293, 94],
    poly [10, -16, 4, 0, -2, 15, 18, -2, -9, -2, 27, -13, -16, -7, 5, -38, -21, -5],
    poly [-72, 57, 19, -4, -12, 43, -17, -16, -5],
    poly [633, 279, 130, 725, 45, 308, 691, -82, -1],
    poly [35, 15, 7, 40, 2, 17, 38, -5],
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
theorem certificado_1559 :
    haveI : Fact (Nat.Prime 1559) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1559 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1559 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((1559 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((1559 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1559) := ⟨by norm_num⟩
  have hP : poly [-289, 1] = X - C (289 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1559 : ℕ) : ℤ[X]) = poly [1559] := by simp [poly]
  refine ⟨X - C (289 : ℤ),
    poly [-588, -234, 571, -25, 302, -738, 429, 665, 682, -235, -17, 329, -452, 225, 756, -375, 290, 1],
    poly [-109, -43, 106, -5, 56, -137, 80, 123, 126, -44, -3, 61, -84, 42, 140, -70, 54],
    poly [-1, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [-529, 219, 405, 643, 277, 211, 378, 357, 481, 120, -124, -168, 463, 449, 12, 291, 648, 99],
    poly [1030, -811, -343, 986, -180, -357, 549, 99],
    poly [98, -41, -75, -119, -51, -39, -70, -66, -89, -22, 23, 31, -86, -83, -2, -54, -120, -18],
    poly [-191, 151, 63, -183, 34, 66, -102, -18],
    poly [588, -354, -217, 242, 427, 665, -289, -1],
    poly [109, -66, -40, 45, 79, 123, -54],
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
theorem certificado_1597 :
    haveI : Fact (Nat.Prime 1597) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1597 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1597 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((1597 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((1597 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1597) := ⟨by norm_num⟩
  have hP : poly [-3, 1] = X - C (3 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1597 : ℕ) : ℤ[X]) = poly [1597] := by simp [poly]
  refine ⟨X - C (3 : ℤ),
    poly [532, 177, 591, 729, 775, 258, 618, 738, 778, 259, 86, -504, 364, 121, 40, 13, 4, 1],
    poly [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, -1, 1],
    poly [-1, -1, -1, -1, 0, 0, 0, 0, 0, 0, -1],
    poly [-373, 35, 171, -316, 54, -355, 41, 173, 217, -833, 414, -235, 81, -346, 44, 174, -315, -478],
    poly [1224, -1562, 171, -316, 427, -390, -130, 489, 163, -478],
    poly [1, 0, 0, 1, 0, 1, 0, 0, 0, 2, -1, 1, 0, 1, 0, 0, 1, 1],
    poly [-2, 4, -1, 1, -1, 1, 0, -1, 0, 1],
    poly [-532, -177, -591, -729, -243, -81, -27, -9, -3, -1],
    poly [-1, 0, -1, -1],
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
theorem certificado_1787 :
    haveI : Fact (Nat.Prime 1787) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1787 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1787 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((1787 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((1787 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1787) := ⟨by norm_num⟩
  have hP : poly [-36, 1] = X - C (36 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1787 : ℕ) : ℤ[X]) = poly [1787] := by simp [poly]
  refine ⟨X - C (36 : ℤ),
    poly [546, 859, -274, 42, 845, 222, 850, -721, -715, -417, -508, -858, 820, -424, -260, -454, 37, 1],
    poly [11, 17, -6, 1, 17, 4, 17, -15, -14, -8, -10, -17, 17, -9, -5, -9, 1],
    poly [1, 0, 0, -1, 0, -1, 0, -1],
    poly [663, -361, -588, 51, -378, -241, 11, 18, -230, -634, 149, -276, -536, 251, -571, -296, -338,
      -637],
    poly [1124, -763, 227, 24, -595, 299, -637],
    poly [-13, 8, 12, -1, 8, 5, 0, 0, 5, 13, -3, 6, 11, -5, 12, 6, 7, 13],
    poly [-23, 16, -5, 0, 12, -6, 13],
    poly [546, 313, 654, -230, 490, -36, -1],
    poly [11, 6, 13, -5, 10, -1],
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
theorem certificado_1901 :
    haveI : Fact (Nat.Prime 1901) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 1901 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((1901 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((1901 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((1901 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 1901) := ⟨by norm_num⟩
  have hP : poly [-172, 1] = X - C (172 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((1901 : ℕ) : ℤ[X]) = poly [1901] := by simp [poly]
  refine ⟨X - C (172 : ℤ),
    poly [-210, -587, 85, 531, -859, -5, 641, -571, -357, 860, -205, 463, 69, -928, 713, -659, 173, 1],
    poly [-19, -53, 8, 48, -78, 0, 58, -52, -32, 78, -19, 42, 6, -84, 65, -60, 16],
    poly [-1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, -1],
    poly [-366, 715, -395, 328, 78, 806, -295, 417, -242, 141, 729, 644, -97, 175, 265, 155, -133, 219],
    poly [1535, -820, -1110, 357, 831, -382, -378, 462, 69, -352, 219],
    poly [33, -65, 36, -30, -7, -73, 27, -38, 22, -13, -66, -58, 9, -16, -24, -14, 12, -20],
    poly [-139, 75, 100, -33, -75, 35, 34, -42, -6, 32, -20],
    poly [210, 377, -672, -236, -134, 375, 809, 701, 833, -172, -1],
    poly [19, 34, -61, -21, -12, 34, 73, 63, 75, -16],
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
theorem certificado_2053 :
    haveI : Fact (Nat.Prime 2053) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2053 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2053 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2053 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2053 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2053) := ⟨by norm_num⟩
  have hP : poly [-70, 1] = X - C (70 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2053 : ℕ) : ℤ[X]) = poly [2053] := by simp [poly]
  refine ⟨X - C (70 : ℤ),
    poly [-88, 380, 504, -902, 603, -402, -563, -360, -973, 514, -22, 29, 411, -874, 1014, 865, 71, 1],
    poly [-3, 13, 17, -31, 21, -14, -19, -12, -33, 18, -1, 1, 14, -30, 35, 29, 2],
    poly [-1, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1],
    poly [-179, 493, 92, -295, 550, 1002, -282, -359, 1077, 159, -558, -11, 906, -518, -597, 663, 681,
      212],
    poly [1874, -1381, -401, -387, 845, 273, -791, 194, 469, 212],
    poly [6, -17, -3, 10, -19, -34, 10, 12, -37, -5, 19, 0, -31, 18, 20, -23, -23, -7],
    poly [-64, 48, 13, 13, -29, -9, 27, -7, -16, -7],
    poly [88, -468, -124, -647, 548, -960, -219, -795, -70, -1],
    poly [3, -16, -4, -22, 19, -33, -7, -27, -2],
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
theorem certificado_2129 :
    haveI : Fact (Nat.Prime 2129) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2129 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2129 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2129 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2129 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2129) := ⟨by norm_num⟩
  have hP : poly [-23, 1] = X - C (23 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2129 : ℕ) : ℤ[X]) = poly [2129] := by simp [poly]
  refine ⟨X - C (23 : ℤ),
    poly [-648, 990, 43, -461, 813, 313, -79, -744, 523, -255, 174, -733, -865, 888, -54, 553, 24, 1],
    poly [-7, 11, 0, -5, 9, 3, -1, -8, 6, -3, 2, -8, -9, 10, -1, 6],
    poly [-1, 0, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1],
    poly [-1994, 326, -1517, 717, -1500, 1088, -1669, 155, -1617, -213, -1633, 64, -973, -185, -521,
      -1091, -5, -976],
    poly [135, 191, -1843, 2234, -4211, 2914, -2280, 221, 565, -2062, 971, -976],
    poly [22, -4, 17, -8, 17, -12, 19, -2, 18, 2, 18, -1, 11, 2, 6, 12, 0, 11],
    poly [-1, -2, 20, -25, 47, -33, 26, -3, -6, 23, -11, 11],
    poly [648, 491, 947, 504, -626, -490, -299, 635, 583, -530, -23, -1],
    poly [7, 5, 10, 5, -7, -5, -3, 7, 6, -6],
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
theorem certificado_2243 :
    haveI : Fact (Nat.Prime 2243) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2243 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2243 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2243 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2243 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2243) := ⟨by norm_num⟩
  have hP : poly [-226, 1] = X - C (226 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2243 : ℕ) : ℤ[X]) = poly [2243] := by simp [poly]
  refine ⟨X - C (226 : ℤ),
    poly [923, -909, 1048, 352, -981, 214, 785, 857, -552, -985, -580, 186, -287, -1093, 412, -286, 227,
      1],
    poly [93, -92, 106, 35, -99, 22, 79, 86, -56, -99, -58, 19, -29, -110, 42, -29, 23],
    poly [-1, 0, 0, -1, -1, -1],
    poly [-1270, 94, -555, -409, -587, -32, -893, -212, -735, -251, -626, 77, -565, -151, -963, -649,
      -1124, -84],
    poly [973, -879, -649, -1124, -84],
    poly [128, -10, 56, 41, 59, 3, 90, 21, 74, 25, 63, -8, 57, 15, 97, 65, 113, 8],
    poly [-98, 89, 65, 113, 8],
    poly [-923, -411, 286, -227, -1],
    poly [-93, -41, 29, -23],
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
theorem certificado_2281 :
    haveI : Fact (Nat.Prime 2281) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2281 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2281 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2281 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2281 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2281) := ⟨by norm_num⟩
  have hP : poly [-206, 1] = X - C (206 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2281 : ℕ) : ℤ[X]) = poly [2281] := by simp [poly]
  refine ⟨X - C (206 : ℤ),
    poly [609, -750, -1122, -393, 441, -1083, 947, 979, -261, -112, 387, -131, 553, -861, 328, -696, 207,
      1],
    poly [55, -68, -101, -35, 40, -98, 86, 88, -24, -10, 35, -12, 50, -78, 30, -63, 19],
    poly [-1, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1],
    poly [-331, 520, 48, 90, -397, -344, -687, 629, -184, -44, -907, 30, -353, 232, -197, 1030, -326,
      -244],
    poly [1950, -1430, -472, 42, -156, -798, 129, 1274, -326, -244],
    poly [30, -47, -4, -8, 36, 31, 62, -57, 17, 4, 82, -3, 32, -21, 18, -93, 30, 22],
    poly [-176, 130, 42, -4, 14, 72, -12, -115, 30, 22],
    poly [-609, -922, 372, -729, -225, 165, -121, 697, -207, -1],
    poly [-55, -83, 34, -66, -20, 15, -11, 63, -19],
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
theorem certificado_2357 :
    haveI : Fact (Nat.Prime 2357) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2357 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2357 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2357 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2357 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2357) := ⟨by norm_num⟩
  have hP : poly [-51, 1] = X - C (51 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2357 : ℕ) : ℤ[X]) = poly [2357] := by simp [poly]
  refine ⟨X - C (51 : ℤ),
    poly [647, -773, 1094, -71, -556, -242, -698, -291, 364, 839, -76, 322, -271, -791, 955, 296, 52, 1],
    poly [14, -17, 24, -2, -12, -5, -15, -6, 8, 18, -2, 7, -6, -17, 21, 6, 1],
    poly [1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1],
    poly [1387, -342, 1103, -440, 870, -537, -10, 786, -400, 917, -305, 734, 246, 144, 142, -921, 953,
      -27],
    poly [970, -628, -1445, 1543, 77, 1065, -811, -894, 953, -27],
    poly [-30, 8, -24, 10, -19, 12, 0, -17, 9, -20, 7, -16, -5, -3, -3, 20, -21, 1],
    poly [-21, 14, 31, -34, -1, -23, 18, 19, -21, 1],
    poly [647, 937, -490, -1165, -1132, 1087, -903, -295, -52, -1],
    poly [14, 20, -11, -25, -24, 24, -20, -6, -1],
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
theorem certificado_2699 :
    haveI : Fact (Nat.Prime 2699) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2699 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2699 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2699 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2699 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2699) := ⟨by norm_num⟩
  have hP : poly [-43, 1] = X - C (43 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2699 : ℕ) : ℤ[X]) = poly [2699] := by simp [poly]
  refine ⟨X - C (43 : ℤ),
    poly [-816, -19, -126, -1070, 540, -113, -1258, 975, 1278, 218, -1062, -1029, -1091, -402, 430, -806,
      44, 1],
    poly [-13, 0, -2, -17, 9, -2, -20, 16, 20, 3, -17, -16, -17, -6, 7, -13, 1],
    poly [1, 1, 0, 1, 0, 0, 0, 0, -1],
    poly [776, -273, -674, -1311, -196, 81, -603, -54, -104, -419, -1054, -1006, 376, -94, -356, -927,
      64, -980],
    poly [1923, -2426, 1450, 262, 571, -991, 1044, -980],
    poly [-12, 5, 11, 21, 3, -1, 10, 1, 2, 7, 17, 16, -6, 2, 6, 15, -1, 16],
    poly [-31, 39, -24, -4, -9, 16, -17, 16],
    poly [-816, -19, 690, 832, -1236, 850, -43, -1],
    poly [-13, 0, 11, 13, -20, 14, -1],
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
theorem certificado_2851 :
    haveI : Fact (Nat.Prime 2851) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2851 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2851 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2851 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2851 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2851) := ⟨by norm_num⟩
  have hP : poly [-9, 1] = X - C (9 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2851 : ℕ) : ℤ[X]) = poly [2851] := by simp [poly]
  refine ⟨X - C (9 : ℤ),
    poly [1267, 1091, -1146, -761, -1035, 1152, 1395, 1422, 1425, 475, 1003, -839, 857, -1172, 820, 91,
      10, 1],
    poly [4, 3, -4, -2, -3, 4, 4, 4, 4, 1, 3, -3, 3, -4, 3],
    poly [0, -1, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1],
    poly [1165, 1928, 1696, 1987, 1069, 967, 1906, 1060, 966, 322, 884, 1580, 707, 610, 916, 950, 637,
      919],
    poly [2851, -1686, 763, 933, 1054, -1150, 189, 1186, -185, 613, -34, 313, -282, 919],
    poly [-4, -6, -5, -6, -3, -3, -6, -3, -3, -1, -3, -5, -2, -2, -3, -3, -2, -3],
    poly [-9, 6, -3, -3, -3, 4, -1, -4, 1, -2, 0, -1, 1, -3],
    poly [0, -1267, 176, 970, -209, -340, 279, -1236, 813, -860, -729, -81, -9, -1],
    poly [0, -4, 1, 3, -1, -1, 1, -4, 3, -3, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_2927 :
    haveI : Fact (Nat.Prime 2927) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 2927 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((2927 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((2927 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((2927 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 2927) := ⟨by norm_num⟩
  have hP : poly [-289, 1] = X - C (289 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((2927 : ℕ) : ℤ[X]) = poly [2927] := by simp [poly]
  refine ⟨X - C (289 : ℤ),
    poly [1266, -421, -1389, 613, 863, 479, 741, -200, -183, -1216, 1120, 14, 1104, -219, 455, -1072,
      290, 1],
    poly [125, -42, -137, 61, 85, 47, 73, -20, -18, -120, 111, 1, 109, -22, 45, -106, 29],
    poly [-1, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [-1443, -1053, -130, -775, -838, -109, -1018, -535, -270, -2082, 69, -987, -1730, -659, -1344,
      -526, 44, -1534],
    poly [1484, -2537, 923, -645, -63, 729, -2352, -570, 1578, -1534],
    poly [143, 104, 13, 77, 83, 11, 101, 53, 27, 206, -7, 98, 171, 65, 133, 52, -4, 152],
    poly [-146, 251, -92, 64, 6, -72, 233, 56, -156, 152],
    poly [-1266, -1240, 968, 925, -250, 384, 1399, 1362, -289, -1],
    poly [-125, -122, 96, 91, -25, 38, 138, 134, -29],
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
theorem certificado_3041 :
    haveI : Fact (Nat.Prime 3041) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3041 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3041 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((3041 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((3041 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3041) := ⟨by norm_num⟩
  have hP : poly [-72, 1] = X - C (72 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3041 : ℕ) : ℤ[X]) = poly [3041] := by simp [poly]
  refine ⟨X - C (72 : ℤ),
    poly [718, -877, 917, -832, -983, 1000, 394, 639, 1107, -407, 1008, 732, 1235, -1081, 1421, -825, 73,
      1],
    poly [17, -21, 22, -20, -23, 24, 9, 15, 26, -10, 24, 17, 29, -26, 34, -20, 2],
    poly [-1, 1, 0, 0, -1, 0, 0, 0, 0, 0, -1],
    poly [-1090, -7, 895, 992, 1289, 913, 232, -411, -969, -1737, -734, -171, 48, 938, 528, -69, -204,
      -586],
    poly [1951, -868, -181, -805, -890, 410, 597, 135, 382, -586],
    poly [26, 0, -21, -23, -30, -21, -5, 10, 23, 41, 17, 4, -1, -22, -12, 2, 5, 14],
    poly [-46, 21, 4, 19, 21, -10, -14, -3, -9, 14],
    poly [-718, -728, -348, 502, 725, -539, 795, 898, -72, -1],
    poly [-17, -17, -8, 12, 17, -13, 19, 21, -2],
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
theorem certificado_3079 :
    haveI : Fact (Nat.Prime 3079) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3079 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3079 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((3079 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((3079 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3079) := ⟨by norm_num⟩
  have hP : poly [-114, 1] = X - C (114 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3079 : ℕ) : ℤ[X]) = poly [3079] := by simp [poly]
  refine ⟨X - C (114 : ℤ),
    poly [27, -702, 507, -1346, -579, 265, -970, -1494, 338, 138, -620, 1372, -69, -1189, 1340, 795, 115,
      1],
    poly [1, -26, 19, -50, -21, 10, -36, -55, 13, 5, -23, 51, -3, -44, 50, 29, 4],
    poly [-1, 0, 0, 0, -1, 0, -1, -1],
    poly [-494, 528, 645, 565, -354, -173, 1098, 650, 430, 212, -60, 1126, -106, -711, 229, -519, 1203,
      894],
    poly [2585, -2057, 117, -80, -1413, 1203, 894],
    poly [18, -20, -24, -21, 13, 6, -41, -24, -16, -8, 2, -42, 4, 26, -9, 19, -45, -33],
    poly [-96, 77, -5, 3, 52, -45, -33],
    poly [-27, 729, -1209, -1226, -794, -115, -1],
    poly [-1, 27, -45, -45, -29, -4],
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
theorem certificado_3307 :
    haveI : Fact (Nat.Prime 3307) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3307 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3307 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((3307 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((3307 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3307) := ⟨by norm_num⟩
  have hP : poly [-144, 1] = X - C (144 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3307 : ℕ) : ℤ[X]) = poly [3307] := by simp [poly]
  refine ⟨X - C (144 : ℤ),
    poly [-666, -1084, 1623, -1137, -605, -142, 665, -914, -902, 476, -1122, -536, -486, -256, 802, 1039,
      145, 1],
    poly [-29, -47, 71, -50, -26, -6, 29, -40, -39, 21, -49, -23, -21, -11, 35, 45, 6],
    poly [0, 0, 1, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1],
    poly [423, 1046, -718, -1557, -1448, -1608, 963, 223, 126, -1643, -2505, -1179, -1032, 967, -420,
      -1509, -2550, -1386],
    poly [3307, -3307, -423, -200, 2810, -302, -2712, -147, -1999, 1387, 1089, 1041, -1164, -1386],
    poly [-18, -45, 32, 68, 63, 70, -42, -9, -5, 72, 109, 51, 45, -42, 19, 66, 111, 60],
    poly [-144, 145, 17, 9, -122, 14, 118, 6, 87, -61, -47, -45, 51, 60],
    poly [0, 0, -666, 248, 484, 1565, 585, 50, 230, 1058, 237, -894, -144, -1],
    poly [0, 0, -29, 11, 21, 68, 25, 2, 10, 46, 10, -39, -6],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_3877 :
    haveI : Fact (Nat.Prime 3877) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 3877 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((3877 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((3877 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((3877 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 3877) := ⟨by norm_num⟩
  have hP : poly [-317, 1] = X - C (317 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((3877 : ℕ) : ℤ[X]) = poly [3877] := by simp [poly]
  refine ⟨X - C (317 : ℤ),
    poly [1859, 385, -488, 1833, -1682, -42, -1480, 509, 1616, -1487, 1891, -948, 156, -1247, 1586, 5,
      318, 1],
    poly [152, 31, -40, 150, -138, -3, -121, 42, 132, -122, 155, -78, 13, -102, 130, 0, 26],
    poly [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1],
    poly [-192, 52, 65, -840, -1063, -1345, -502, -1331, 611, -80, 1202, -1558, 11, -1256, 758, -1963,
      768, -1168],
    poly [4069, -4121, -13, 1097, -21, 461, 10, 795, -768, 1168],
    poly [16, -4, -5, 69, 87, 110, 41, 109, -50, 7, -98, 128, -1, 103, -62, 161, -63, 96],
    poly [-333, 338, 0, -90, 2, -38, -1, -65, 63, -96],
    poly [1859, -1474, -873, 303, -1112, -1251, 1268, 4, 318, 1],
    poly [152, -121, -71, 25, -91, -102, 104, 0, 26],
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
theorem certificado_4219 :
    haveI : Fact (Nat.Prime 4219) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4219 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4219 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4219 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4219 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4219) := ⟨by norm_num⟩
  have hP : poly [-43, 1] = X - C (43 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4219 : ℕ) : ℤ[X]) = poly [4219] := by simp [poly]
  refine ⟨X - C (43 : ℤ),
    poly [-1668, 648, -868, 1844, -1527, -428, 1658, 431, 10, -1864, -1417, 1635, 38, -1569, 1239, 1893,
      44, 1],
    poly [-17, 7, -9, 19, -16, -4, 17, 4, 0, -19, -14, 17, 0, -16, 13, 19],
    poly [-1, -1, 0, 0, -1, 0, -1, -1],
    poly [-991, -131, -111, -503, -414, 373, 980, 896, 11, 481, -293, -311, -802, -1304, 941, -871, 1736,
      423],
    poly [3228, -4350, 880, -372, -1294, 1736, 423],
    poly [10, 1, 1, 5, 4, -4, -10, -9, 0, -5, 3, 3, 8, 13, -10, 9, -18, -4],
    poly [-33, 45, -10, 4, 13, -18, -4],
    poly [1668, -648, -800, -1196, -1892, -44, -1],
    poly [17, -7, -8, -12, -19],
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
theorem certificado_4409 :
    haveI : Fact (Nat.Prime 4409) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4409 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4409 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4409 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4409 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4409) := ⟨by norm_num⟩
  have hP : poly [-209, 1] = X - C (209 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4409 : ℕ) : ℤ[X]) = poly [4409] := by simp [poly]
  refine ⟨X - C (209 : ℤ),
    poly [-1983, -1444, 415, 888, -270, 505, -1411, -281, 737, 109, -1877, 1531, 598, -2170, -1909, -199,
      210, 1],
    poly [-94, -68, 20, 42, -13, 24, -67, -13, 35, 5, -89, 73, 28, -103, -90, -9, 10],
    poly [-1, 0, 0, 0, -1, -1, -1, 0, -1, 0, -1],
    poly [-1233, 723, -449, -982, 239, 941, -237, 559, 605, -766, 894, -849, -562, -202, -580, -624, 304,
      1975],
    poly [3176, -2453, -1172, -533, -12, 1425, -1627, 1047, -1671, 1975],
    poly [58, -35, 21, 46, -12, -45, 11, -27, -29, 36, -43, 40, 26, 9, 27, 29, -15, -94],
    poly [-151, 117, 55, 25, 0, -68, 77, -50, 79, -94],
    poly [1983, -539, -1859, -473, -1268, 669, 1501, 408, -209, -1],
    poly [94, -26, -88, -22, -60, 32, 71, 19, -10],
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
theorem certificado_4447 :
    haveI : Fact (Nat.Prime 4447) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4447 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4447 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4447 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4447 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4447) := ⟨by norm_num⟩
  have hP : poly [-217, 1] = X - C (217 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4447 : ℕ) : ℤ[X]) = poly [4447] := by simp [poly]
  refine ⟨X - C (217 : ℤ),
    poly [-1496, 1776, 541, -1514, 1530, 1626, -1509, 116, -1393, 219, 1497, 1175, -261, -616, 1944,
      -1610, 218, 1],
    poly [-73, 87, 26, -74, 75, 79, -74, 6, -68, 11, 73, 57, -13, -30, 95, -79, 11],
    poly [0, 0, 0, 0, 1, -1, 0, -1, 0, -1, 0, -1],
    poly [-651, -654, -695, 227, 969, -749, -511, -223, -734, -306, -386, 3, -610, -1576, -1437, 1945,
      731, -1037],
    poly [4447, -4447, 0, 0, 651, -648, 38, -1614, 177, 1768, -1037],
    poly [32, 32, 34, -11, -47, 37, 25, 11, 36, 15, 19, 0, 30, 77, 70, -95, -35, 51],
    poly [-217, 218, -1, 0, -32, 32, -2, 79, -9, -86, 51],
    poly [0, 0, 0, 0, -1496, 321, -60, 676, 1827, -217, -1],
    poly [0, 0, 0, 0, -73, 16, -3, 33, 89, -11],
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
theorem certificado_4523 :
    haveI : Fact (Nat.Prime 4523) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4523 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4523 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4523 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4523 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4523) := ⟨by norm_num⟩
  have hP : poly [-42, 1] = X - C (42 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4523 : ℕ) : ℤ[X]) = poly [4523] := by simp [poly]
  refine ⟨X - C (42 : ℤ),
    poly [-1400, 1582, 1653, 1547, -2117, 1888, 368, -1822, -1228, -1860, -152, -1619, -1977, -1124,
      -996, 1807, 43, 1],
    poly [-13, 15, 15, 14, -20, 18, 3, -17, -11, -17, -1, -15, -18, -10, -9, 17],
    poly [1, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1],
    poly [-517, -637, -1286, -763, -1289, -440, -1389, -227, -1707, -2173, 1262, -2210, -785, -428,
      -2681, 173, -2559, -901],
    poly [5040, -4403, 649, -1040, 406, -2015, 1352, -2854, 2732, -1658, -901],
    poly [5, 6, 12, 7, 12, 4, 13, 2, 16, 20, -12, 21, 7, 4, 25, -2, 24, 8],
    poly [-47, 42, -7, 10, -4, 19, -13, 27, -26, 16, 8],
    poly [-1400, -1541, 71, 1294, -2123, 811, 127, -1720, -1764, -42, -1],
    poly [-13, -14, 1, 12, -20, 8, 1, -16, -16],
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
theorem certificado_4561 :
    haveI : Fact (Nat.Prime 4561) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4561 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4561 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4561 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4561 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4561) := ⟨by norm_num⟩
  have hP : poly [-485, 1] = X - C (485 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4561 : ℕ) : ℤ[X]) = poly [4561] := by simp [poly]
  refine ⟨X - C (485 : ℤ),
    poly [1373, -63, 1213, 689, -497, -396, -2239, 1406, 238, -1570, -370, -1449, 2254, -1011, -1629,
      -1461, 486, 1],
    poly [146, -7, 129, 73, -53, -42, -238, 150, 25, -167, -39, -154, 240, -108, -173, -155, 52],
    poly [-1, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1],
    poly [-1054, 251, 959, 368, -47, -377, 1174, 1638, -1455, -1057, -191, 1212, -365, -1619, 626, 1477,
      670, 358],
    poly [3507, -3256, 708, -591, -415, -330, 497, 715, -1080, -539, 1165, 312, 358],
    poly [112, -27, -102, -39, 5, 40, -125, -174, 155, 112, 20, -129, 39, 172, -67, -157, -71, -38],
    poly [-373, 347, -76, 63, 44, 35, -53, -76, 115, 57, -124, -33, -38],
    poly [-1373, 1436, -1276, 524, 1186, -101, 470, 979, 1328, -317, 1946, -485, -1],
    poly [-146, 153, -136, 56, 126, -11, 50, 104, 141, -34, 207, -52],
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
theorem certificado_4637 :
    haveI : Fact (Nat.Prime 4637) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4637 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4637 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4637 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4637 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4637) := ⟨by norm_num⟩
  have hP : poly [-77, 1] = X - C (77 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4637 : ℕ) : ℤ[X]) = poly [4637] := by simp [poly]
  refine ⟨X - C (77 : ℤ),
    poly [-542, -2175, -1594, -2008, 817, 1757, 1167, 1340, -2271, 2018, -1118, 949, -891, -1216, -1160,
      1370, 78, 1],
    poly [-9, -36, -26, -33, 14, 29, 19, 22, -38, 34, -19, 16, -15, -20, -19, 23, 1],
    poly [-1, 0, -1, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [74, 3086, 3366, 2105, 282, -103, -108, 1819, 2928, 1196, -874, -660, -597, 1090, 1955, 2448,
      708, -1061],
    poly [4711, -1625, 354, 1751, -1543, -1572, 1184, 1822, -157, -1554, 1740, 1769, -1061],
    poly [-1, -51, -55, -34, -4, 2, 2, -30, -48, -19, 15, 11, 10, -18, -32, -40, -11, 18],
    poly [-78, 28, -6, -29, 26, 26, -20, -30, 3, 26, -29, -29, 18],
    poly [542, 1633, -39, 2047, 1231, 16, -602, -1694, -22, -2108, -1292, -77, -1],
    poly [9, 27, -1, 34, 20, 0, -10, -28, 0, -35, -21, -1],
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
theorem certificado_4751 :
    haveI : Fact (Nat.Prime 4751) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4751 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4751 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4751 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4751 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4751) := ⟨by norm_num⟩
  have hP : poly [-110, 1] = X - C (110 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4751 : ℕ) : ℤ[X]) = poly [4751] := by simp [poly]
  refine ⟨X - C (110 : ℤ),
    poly [907, 181, -1726, -1441, 1369, -765, 1116, 658, -2024, -1962, -1184, 1069, 528, 1862, -1322,
      -2042, 111, 1],
    poly [21, 4, -40, -33, 32, -18, 26, 15, -47, -45, -27, 25, 12, 43, -31, -47, 3],
    poly [-1, -1, -1, 0, -1, -1, -1, -1, -1, 0, -1],
    poly [-401, 2230, 915, 1119, 1380, 2203, 1649, 521, 2152, 396, 1503, -85, 678, 2283, 354, 1589, 2680,
      1351],
    poly [4350, -2521, 915, 1520, -1251, 3518, 1445, 260, 1329, 1351],
    poly [9, -52, -21, -26, -32, -51, -38, -12, -50, -9, -35, 2, -16, -53, -8, -37, -62, -31],
    poly [-101, 59, -22, -35, 29, -82, -33, -6, -31, -31],
    poly [-907, -181, 1726, 2348, -2095, -1142, -831, 2152, -110, -1],
    poly [-21, -4, 40, 54, -49, -26, -19, 50, -3],
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
theorem certificado_4789 :
    haveI : Fact (Nat.Prime 4789) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4789 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4789 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4789 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4789 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4789) := ⟨by norm_num⟩
  have hP : poly [-489, 1] = X - C (489 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4789 : ℕ) : ℤ[X]) = poly [4789] := by simp [poly]
  refine ⟨X - C (489 : ℤ),
    poly [-901, 1428, 2275, -818, -413, 528, 716, -2300, 436, -763, 1252, 1736, 2021, 200, 2106, 161,
      490, 1],
    poly [-92, 146, 232, -84, -42, 54, 73, -235, 45, -78, 128, 177, 206, 20, 215, 16, 50],
    poly [-1, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1],
    poly [-3287, -483, -2671, -991, -635, -742, -1369, -1194, -1556, -2066, -1832, -1714, -754, -2603,
      -1980, -970, -870, -1761],
    poly [1502, -1985, -2188, 1680, 356, -3394, -1110, 791, -870, -1761],
    poly [336, 49, 273, 101, 65, 76, 140, 122, 159, 211, 187, 175, 77, 266, 202, 99, 89, 180],
    poly [-153, 203, 223, -172, -36, 347, 113, -81, 89, 180],
    poly [901, -2329, -847, -1696, -405, -40, -1616, -160, -490, -1],
    poly [92, -238, -86, -173, -41, -4, -165, -16, -50],
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
theorem certificado_4903 :
    haveI : Fact (Nat.Prime 4903) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 4903 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((4903 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((4903 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((4903 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 4903) := ⟨by norm_num⟩
  have hP : poly [-230, 1] = X - C (230 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((4903 : ℕ) : ℤ[X]) = poly [4903] := by simp [poly]
  refine ⟨X - C (230 : ℤ),
    poly [-1343, -688, 1340, -1124, -751, 82, 917, -465, 1746, -99, -1919, 418, 1089, 90, 1855, -802,
      231, 1],
    poly [-63, -32, 63, -53, -35, 4, 43, -22, 82, -5, -90, 20, 51, 4, 87, -38, 11],
    poly [0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1],
    poly [-3686, -1954, 100, -1767, -3715, -1677, -517, -1791, -1626, -666, -875, -2091, -2480, -286,
      -447, -938, -3349, -439],
    poly [4903, -1217, 1954, -3786, 3499, 2083, 1542, -3063, 8, 938, 3349, 439],
    poly [173, 91, -5, 83, 174, 78, 24, 84, 76, 31, 41, 98, 116, 13, 21, 44, 157, 20],
    poly [-230, 58, -92, 178, -165, -97, -72, 144, -1, -44, -157, -20],
    poly [0, -1343, -688, -2220, -1779, -1436, 1891, -141, 1854, -802, 231, 1],
    poly [0, -63, -32, -104, -83, -67, 89, -7, 87, -38, 11],
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
theorem certificado_5701 :
    haveI : Fact (Nat.Prime 5701) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 5701 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((5701 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((5701 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((5701 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 5701) := ⟨by norm_num⟩
  have hP : poly [-122, 1] = X - C (122 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((5701 : ℕ) : ℤ[X]) = poly [5701] := by simp [poly]
  refine ⟨X - C (122 : ℤ),
    poly [-1729, 1855, 1604, 901, -273, -563, -285, 1493, 2816, -1519, 81, 1496, 2302, -869, 834, -2096,
      123, 1],
    poly [-37, 40, 34, 19, -6, -12, -6, 32, 60, -33, 2, 32, 49, -19, 18, -45, 3],
    poly [-1, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [-1272, 26, -1926, -1942, -1101, -767, 918, 1072, -609, 452, -801, -858, -2494, -3442, -646,
      -810, 684, 1257],
    poly [4429, -4403, -1952, -16, -431, 1632, -1539, 164, -1494, -573, 1257],
    poly [27, -1, 41, 41, 23, 16, -20, -23, 13, -10, 17, 18, 53, 73, 13, 17, -15, -27],
    poly [-95, 95, 41, 0, 9, -35, 33, -4, 32, 12, -27],
    poly [1729, 2117, 251, 703, -2798, 2407, 1702, 2771, 2219, -122, -1],
    poly [37, 45, 5, 15, -60, 52, 36, 59, 47, -3],
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
theorem certificado_6043 :
    haveI : Fact (Nat.Prime 6043) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6043 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6043 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((6043 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((6043 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6043) := ⟨by norm_num⟩
  have hP : poly [-694, 1] = X - C (694 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6043 : ℕ) : ℤ[X]) = poly [6043] := by simp [poly]
  refine ⟨X - C (694 : ℤ),
    poly [1280, 533, 1899, -154, -1019, 312, 758, -2080, -1283, -176, 2969, 2007, 595, 1098, -2184,
      -1109, 695, 1],
    poly [147, 61, 218, -18, -117, 36, 87, -239, -147, -20, 341, 230, 68, 126, -251, -127, 80],
    poly [-1, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1],
    poly [-273, -1327, 204, -1544, -14, -482, 301, 1199, -71, -38, 23, 502, -2275, -999, -2669, 1752,
      -880, 2129],
    poly [5770, -7097, 1531, -2021, 476, 790, -2292, 2632, -3009, 2129],
    poly [31, 152, -24, 177, 1, 55, -35, -138, 8, 4, -3, -58, 261, 114, 306, -202, 101, -245],
    poly [-663, 816, -177, 232, -55, -91, 263, -303, 346, -245],
    poly [-1280, 747, -1366, 773, 1612, 2066, 1074, 1804, -694, -1],
    poly [-147, 86, -157, 89, 185, 237, 123, 207, -80],
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
theorem certificado_6271 :
    haveI : Fact (Nat.Prime 6271) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6271 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6271 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((6271 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((6271 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6271) := ⟨by norm_num⟩
  have hP : poly [-5, 1] = X - C (5 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6271 : ℕ) : ℤ[X]) = poly [6271] := by simp [poly]
  refine ⟨X - C (5 : ℤ),
    poly [1254, 2759, 3060, 1866, 373, -2434, -487, -2606, 1987, -857, -2680, 718, -2365, 781, 156, 31,
      6, 1],
    poly [1, 2, 2, 1, 0, -2, 0, -2, 2, -1, -2, 1, -2, 1],
    poly [1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1],
    poly [257, -2200, -183, -2288, -2709, -1539, -1305, -4, -998, -2451, 1021, -793, -2410, -225, 212,
      -2209, -1439, -1285],
    poly [6014, -3814, -2017, 2105, 421, -1427, 2223, -3318, 3099, 1617, -2185, -437, 2421, -770, -154,
      -1285],
    poly [0, 2, 0, 2, 2, 1, 1, 0, 1, 2, -1, 1, 2, 0, 0, 2, 1, 1],
    poly [-5, 4, 1, -2, 0, 1, -2, 3, -3, -1, 2, 0, -2, 1, 0, 1],
    poly [1254, 1505, 301, -1194, -1493, -1553, -2819, -1818, -2872, -3083, -3125, -625, -125, -25, -5,
      -1],
    poly [1, 1, 0, -1, -1, -1, -2, -1, -2, -2, -2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6689 :
    haveI : Fact (Nat.Prime 6689) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6689 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6689 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((6689 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((6689 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6689) := ⟨by norm_num⟩
  have hP : poly [-83, 1] = X - C (83 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6689 : ℕ) : ℤ[X]) = poly [6689] := by simp [poly]
  refine ⟨X - C (83 : ℤ),
    poly [-1773, -1472, -2919, 126, 888, 736, -1200, -2271, -1478, -179, 1932, -1105, -1061, -3317,
      -3183, 284, 84, 1],
    poly [-22, -18, -36, 2, 11, 9, -15, -28, -18, -2, 24, -14, -13, -41, -39, 4, 1],
    poly [-1, 0, 0, 0, -1, 0, 0, -1, -1, 0, -1],
    poly [-1447, 1598, 2360, 2208, 272, -799, -6, 1293, 3404, 367, 411, -1845, -1711, 1756, 1556, 1473,
      1472, -301],
    poly [5242, -3644, 762, -152, -3383, 1974, 1555, -300, 1773, -301],
    poly [18, -20, -29, -27, -3, 10, 0, -16, -42, -4, -5, 23, 21, -22, -19, -18, -18, 4],
    poly [-65, 46, -10, 2, 42, -25, -19, 4, -22, 4],
    poly [1773, -301, 1447, -3045, 1011, -149, -3306, -201, -83, -1],
    poly [22, -4, 18, -38, 13, -2, -41, -2, -1],
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
theorem certificado_6803 :
    haveI : Fact (Nat.Prime 6803) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6803 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6803 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((6803 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((6803 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6803) := ⟨by norm_num⟩
  have hP : poly [-637, 1] = X - C (637 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6803 : ℕ) : ℤ[X]) = poly [6803] := by simp [poly]
  refine ⟨X - C (637 : ℤ),
    poly [1634, -1546, -2918, 743, -1494, 553, 2831, 1820, 665, -3299, -2579, -2140, 1652, 3057, -102,
      -1773, 638, 1],
    poly [153, -145, -273, 70, -140, 52, 265, 170, 62, -309, -241, -200, 155, 286, -10, -166, 60],
    poly [-1, 0, 0, -1, 0, -1, -1, -1, 0, -1],
    poly [-2969, -2162, -1018, 511, -1174, -3099, -635, 565, -971, -1454, -1380, 158, -2627, -3144,
      -1938, 328, -1484, 19],
    poly [3834, -5996, 1144, -1440, -878, -3750, 1831, -1503, 19],
    poly [278, 202, 95, -48, 110, 290, 59, -53, 91, 136, 129, -15, 246, 294, 181, -31, 139, -2],
    poly [-359, 562, -108, 135, 82, 351, -172, 141, -2],
    poly [-1634, 3180, 1372, 1508, -1386, -2309, 2410, -637, -1],
    poly [-153, 298, 128, 141, -130, -216, 226, -60],
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
theorem certificado_6841 :
    haveI : Fact (Nat.Prime 6841) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6841 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6841 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((6841 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((6841 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6841) := ⟨by norm_num⟩
  have hP : poly [-18, 1] = X - C (18 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6841 : ℕ) : ℤ[X]) = poly [6841] := by simp [poly]
  refine ⟨X - C (18 : ℤ),
    poly [380, -359, -20, 1139, -1457, -81, -3045, 1351, 75, -756, 338, 1919, 3147, 1695, -666, 343, 19,
      1],
    poly [1, -1, 0, 3, -4, 0, -8, 4, 0, -2, 1, 5, 8, 4, -2, 1],
    poly [0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    poly [-1620, -1710, -1715, 185, -3510, -1815, -2861, -2159, -2120, -3258, -1801, -1340, 1346, -25,
      1039, 338, -81, 1796],
    poly [6841, -5221, 1710, 95, -1895, 3415, 2090, 976, 154, 3049, -2491, 2522, -620, -2215, 1877,
      -1796],
    poly [4, 4, 4, -1, 9, 4, 7, 5, 5, 8, 4, 3, -4, 0, -3, -1, 0, -5],
    poly [-18, 15, -5, 0, 5, -9, -5, -2, 0, -8, 7, -7, 2, 6, -5, 5],
    poly [0, 380, -359, -400, 1498, -1057, -1959, -869, 2232, 124, 767, 2703, -990, 325, 18, 1],
    poly [0, 1, -1, -1, 4, -3, -5, -2, 6, 0, 2, 7, -3, 1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_6917 :
    haveI : Fact (Nat.Prime 6917) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 6917 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((6917 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((6917 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((6917 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 6917) := ⟨by norm_num⟩
  have hP : poly [-124, 1] = X - C (124 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((6917 : ℕ) : ℤ[X]) = poly [6917] := by simp [poly]
  refine ⟨X - C (124 : ℤ),
    poly [-1283, -1126, -288, 2731, 2588, -1039, 661, 2906, -1148, -846, -732, 273, 3126, -2485, -801,
      1667, 125, 1],
    poly [-23, -20, -5, 49, 46, -19, 12, 52, -21, -15, -13, 5, 56, -45, -14, 30, 2],
    poly [-1, 0, 0, 0, 0, 1, 0, -1, 0, -1],
    poly [-1892, -1461, -1848, -345, -1839, -2632, -3252, -3257, -2755, -1970, -4697, -3436, -4151,
      -1535, 48, -2561, -2080, -570],
    poly [5025, -6486, -387, 1503, -1494, 1099, -1051, -1510, -570],
    poly [34, 26, 33, 6, 33, 47, 58, 58, 49, 35, 84, 61, 74, 27, -1, 46, 37, 10],
    poly [-90, 117, 6, -27, 27, -20, 19, 27, 10],
    poly [1283, -157, -838, -3019, 143, 2344, -1543, -124, -1],
    poly [23, -3, -15, -54, 3, 42, -28, -2],
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
theorem certificado_7069 :
    haveI : Fact (Nat.Prime 7069) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7069 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7069 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7069 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7069 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7069) := ⟨by norm_num⟩
  have hP : poly [-70, 1] = X - C (70 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7069 : ℕ) : ℤ[X]) = poly [7069] := by simp [poly]
  refine ⟨X - C (70 : ℤ),
    poly [-101, -3233, -1460, 888, -2310, -134, 503, 1219, 2845, -2585, 367, 1621, 1033, -1803, 1590,
      -2098, 71, 1],
    poly [-1, -32, -14, 9, -23, -1, 5, 12, 28, -26, 4, 16, 10, -18, 16, -21, 1],
    poly [1, 0, -1, 0, 0, -1, -1, -1],
    poly [1520, -478, 2725, 1054, 1939, -573, 199, 412, 718, 3348, 356, 2131, -2388, 678, -692, 2318,
      2361, -365],
    poly [5549, -5071, -1683, -327, 2318, 2361, -365],
    poly [-15, 5, -27, -10, -19, 6, -2, -4, -7, -33, -3, -21, 24, -7, 7, -23, -23, 4],
    poly [-55, 51, 16, 3, -23, -23, 4],
    poly [-101, -3132, 1874, -1589, 2098, -71, -1],
    poly [-1, -31, 19, -16, 21, -1],
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
theorem certificado_7297 :
    haveI : Fact (Nat.Prime 7297) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7297 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7297 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7297 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7297 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7297) := ⟨by norm_num⟩
  have hP : poly [-292, 1] = X - C (292 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7297 : ℕ) : ℤ[X]) = poly [7297] := by simp [poly]
  refine ⟨X - C (292 : ℤ),
    poly [2424, 733, -1197, -254, -2125, 1742, -2518, -1533, -3054, -1135, 2695, 559, -2647, -2608,
      -2283, -2007, 293, 1],
    poly [97, 29, -48, -10, -85, 70, -101, -61, -122, -45, 108, 22, -106, -104, -91, -80, 12],
    poly [-1, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1],
    poly [745, 4521, 1935, 2276, 253, 421, 1821, 1326, 4498, -689, -132, -355, 219, 2570, 2703, 1379, 75,
      1370],
    poly [8042, -2776, 1190, -2245, -937, 1921, -1018, 1246, 1399, 2674, -1295, 1370],
    poly [-30, -181, -77, -91, -10, -17, -73, -53, -180, 28, 5, 14, -9, -103, -108, -55, -3, -55],
    poly [-322, 112, -48, 90, 37, -77, 41, -50, -56, -107, 52, -55],
    poly [-2424, -733, 3621, 987, -1496, -305, 2323, 2332, -17, 2299, -292, -1],
    poly [-97, -29, 145, 39, -60, -12, 93, 93, -1, 92, -12],
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
theorem certificado_7411 :
    haveI : Fact (Nat.Prime 7411) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7411 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7411 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7411 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7411 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7411) := ⟨by norm_num⟩
  have hP : poly [-373, 1] = X - C (373 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7411 : ℕ) : ℤ[X]) = poly [7411] := by simp [poly]
  refine ⟨X - C (373 : ℤ),
    poly [2722, -2973, 2416, -73, 1331, -3692, 3030, 3505, 69, 179, -2801, 1125, 1215, 798, 1989, -1306,
      374, 1],
    poly [137, -150, 122, -4, 67, -186, 153, 176, 3, 9, -141, 57, 61, 40, 100, -66, 19],
    poly [-1, 0, -1, 0, -1, 0, 0, 0, -1, -1],
    poly [-4022, -2185, -74, -2691, -1188, -1482, -1602, -1046, -2634, -711, -2951, -4924, 18, -1141,
      -3429, -733, -2355, -4227],
    poly [3389, -5574, -1911, -780, -408, -1074, 3494, -2355, -4227],
    poly [203, 110, 4, 136, 60, 75, 81, 53, 133, 36, 149, 248, -1, 58, 173, 37, 119, 213],
    poly [-170, 281, 96, 39, 21, 54, -176, 119, 213],
    poly [-2722, -1716, -700, 773, -2104, -1615, 1307, -374, -1],
    poly [-137, -86, -35, 39, -106, -81, 66, -19],
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
theorem certificado_7487 :
    haveI : Fact (Nat.Prime 7487) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7487 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7487 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7487 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7487 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7487) := ⟨by norm_num⟩
  have hP : poly [-634, 1] = X - C (634 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7487 : ℕ) : ℤ[X]) = poly [7487] := by simp [poly]
  refine ⟨X - C (634 : ℤ),
    poly [-1547, 1084, -1687, 1627, -210, 3011, -444, 389, 1276, 3344, -1896, 245, 3118, 371, 3378,
      -1707, 635, 1],
    poly [-131, 92, -143, 138, -18, 255, -38, 33, 108, 283, -161, 21, 264, 31, 286, -145, 54],
    poly [-1, -1, -1, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1, 0, -1],
    poly [4588, 4548, 2564, 2986, 4451, 2245, 3635, 5196, 1762, 5134, 3179, 3542, 3578, 6861, 1989, 4414,
      4902, 3651],
    poly [12075, -2939, 2564, -1602, -97, -319, 649, 745, -483, 6087, -2057, 4384, -1174, 3163, 1251,
      3651],
    poly [-389, -385, -217, -253, -377, -190, -308, -440, -149, -435, -269, -300, -303, -581, -168, -374,
      -415, -309],
    poly [-1023, 250, -218, 136, 8, 27, -55, -63, 41, -516, 175, -372, 100, -268, -106, -309],
    poly [1547, -1084, 1687, -3174, 1294, 2789, 2071, -599, 1735, -2241, -346, -2138, 1768, 2341, -634,
      -1],
    poly [131, -92, 143, -269, 110, 236, 175, -51, 147, -190, -29, -181, 150, 198, -54],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_7639 :
    haveI : Fact (Nat.Prime 7639) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7639 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7639 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7639 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7639 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7639) := ⟨by norm_num⟩
  have hP : poly [-250, 1] = X - C (250 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7639 : ℕ) : ℤ[X]) = poly [7639] := by simp [poly]
  refine ⟨X - C (250 : ℤ),
    poly [275, 1040, -3082, -104, -1681, -3429, 3653, -3591, 2369, -1885, -802, -706, 3450, -1239, -2755,
      1639, 251, 1],
    poly [9, 34, -101, -3, -55, -112, 120, -118, 78, -62, -26, -23, 113, -41, -90, 54, 8],
    poly [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 1, 1],
    poly [1608, 2470, 2229, -247, 782, 450, 82, 1975, 852, -3522, 5, 233, -1355, -78, 141, 1028, 1551,
      2867],
    poly [6031, -8501, 241, 2476, -2637, -530, 609, 583, 94, 4706, -1551, -2867],
    poly [-53, -81, -73, 8, -26, -15, -3, -65, -28, 115, -1, -8, 44, 2, -5, -34, -51, -94],
    poly [-197, 279, -9, -81, 87, 17, -20, -19, -3, -154, 51, 94],
    poly [275, 765, 3517, 2978, -1302, -983, 2960, 3373, -3256, 1637, 251, 1],
    poly [9, 25, 115, 97, -43, -32, 97, 110, -107, 54, 8],
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
theorem certificado_7753 :
    haveI : Fact (Nat.Prime 7753) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7753 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7753 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7753 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7753 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7753) := ⟨by norm_num⟩
  have hP : poly [-310, 1] = X - C (310 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7753 : ℕ) : ℤ[X]) = poly [7753] := by simp [poly]
  refine ⟨X - C (310 : ℤ),
    poly [-2576, -1784, -631, 98, 1776, -1870, 2670, -1567, 145, -1200, -329, 2750, 2935, -1191, -404,
      3375, 311, 1],
    poly [-103, -71, -25, 4, 71, -75, 107, -63, 6, -48, -13, 110, 117, -48, -16, 135, 12],
    poly [-1, 0, -1, -1, -1, 0, 0, 0, 0, 0, -1, 0, -1],
    poly [-2616, -4075, -2254, -1923, -2097, -647, -2393, -3349, -551, -3193, -1851, -2697, -3400, -126,
      -1566, -5072, -4283, -3105],
    poly [5137, -9212, -795, -3744, -2428, 2143, 232, 651, 2328, -3894, -1178, -3105],
    poly [105, 163, 90, 77, 84, 26, 96, 134, 22, 128, 74, 108, 136, 5, 63, 203, 171, 124],
    poly [-205, 369, 31, 150, 97, -86, -9, -26, -93, 156, 47, 124],
    poly [2576, -792, 1423, 1055, -1047, 972, -347, -2277, 3469, -3065, -310, -1],
    poly [103, -32, 57, 42, -42, 39, -14, -91, 139, -123, -12],
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
theorem certificado_7829 :
    haveI : Fact (Nat.Prime 7829) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7829 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7829 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7829 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7829 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7829) := ⟨by norm_num⟩
  have hP : poly [-86, 1] = X - C (86 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7829 : ℕ) : ℤ[X]) = poly [7829] := by simp [poly]
  refine ⟨X - C (86 : ℤ),
    poly [2640, 850, -2266, 3524, 132, -1364, 2260, 1938, -1343, 1623, 383, 1461, -2532, 1154, 1561,
      -346, 87, 1],
    poly [29, 9, -25, 39, 1, -15, 25, 21, -15, 18, 4, 16, -28, 13, 17, -4, 1],
    poly [1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1],
    poly [4155, 3384, 3284, 1098, 2165, 3725, 3379, 826, -23, 2243, 1359, 2077, 1175, 2439, 633, 612,
      1249, 2804],
    poly [3674, -2903, -671, 2086, 902, -1264, 1806, 21, -637, -1555, 2804],
    poly [-46, -37, -36, -12, -24, -41, -37, -9, 0, -25, -15, -23, -13, -27, -7, -7, -14, -31],
    poly [-40, 32, 7, -23, -10, 14, -20, 0, 7, 17, -31],
    poly [2640, 3399, -1326, 1077, 3836, 3686, 407, -1907, 433, -86, -1],
    poly [29, 37, -15, 12, 42, 40, 4, -21, 5, -1],
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
theorem certificado_7867 :
    haveI : Fact (Nat.Prime 7867) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 7867 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((7867 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((7867 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((7867 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 7867) := ⟨by norm_num⟩
  have hP : poly [-228, 1] = X - C (228 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((7867 : ℕ) : ℤ[X]) = poly [7867] := by simp [poly]
  refine ⟨X - C (228 : ℤ),
    poly [-3899, 811, 3523, -3504, -1016, -315, 3035, -2402, 300, 1485, 3871, 224, -3760, -51, 1794,
      -2856, 229, 1],
    poly [-113, 24, 102, -102, -29, -9, 88, -70, 9, 43, 112, 6, -109, -1, 52, -83, 7],
    poly [-1, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1],
    poly [-1761, -9, 2483, 3046, 3290, 2739, 2081, 1181, 763, -550, 1480, 2248, -647, 893, 2832, 2806,
      3703, 291],
    poly [6106, -6115, 731, 2315, 975, 1764, 317, -897, 3412, 291],
    poly [51, 0, -72, -88, -95, -79, -60, -34, -22, 16, -43, -65, 19, -26, -82, -81, -107, -8],
    poly [-177, 178, -22, -67, -28, -51, -9, 26, -99, -8],
    poly [3899, 3157, 1187, 2317, -1301, 1616, 3216, 3085, -228, -1],
    poly [113, 91, 34, 67, -38, 47, 93, 89, -7],
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
theorem certificado_8171 :
    haveI : Fact (Nat.Prime 8171) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8171 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8171 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8171 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8171 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8171) := ⟨by norm_num⟩
  have hP : poly [-692, 1] = X - C (692 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8171 : ℕ) : ℤ[X]) = poly [8171] := by simp [poly]
  refine ⟨X - C (692 : ℤ),
    poly [-3932, 3147, -822, -320, -3838, -3111, 3774, -3100, -2000, 741, 804, 3390, -1353, 3564, -3549,
      -2532, 693, 1],
    poly [-333, 267, -70, -27, -325, -263, 320, -263, -169, 63, 68, 287, -115, 302, -301, -214, 59],
    poly [-1, 0, 0, 0, -1, 0, -1, -1, 0, 0, -1],
    poly [-2880, -2034, -1159, -650, -1157, -957, 1027, -1190, 23, -2325, -1431, 247, -4025, -1953,
      -1336, -2079, 1663, -764],
    poly [5291, -7325, 875, 509, -3387, 1046, -21, -3742, 2427, -764],
    poly [244, 172, 98, 55, 98, 81, -87, 101, -2, 197, 121, -21, 341, 165, 113, 176, -141, 65],
    poly [-448, 621, -75, -43, 287, -89, 2, 317, -206, 65],
    poly [3932, 1092, 3969, -502, -721, 365, 1016, 3225, -692, -1],
    poly [333, 92, 336, -43, -61, 31, 86, 273, -59],
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
theorem certificado_8209 :
    haveI : Fact (Nat.Prime 8209) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8209 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8209 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8209 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8209 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8209) := ⟨by norm_num⟩
  have hP : poly [-144, 1] = X - C (144 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8209 : ℕ) : ℤ[X]) = poly [8209] := by simp [poly]
  refine ⟨X - C (144 : ℤ),
    poly [57, -3192, 1403, 2176, -840, -1317, 1245, 2973, 2985, 2301, 244, 2567, 1500, -3353, 2371,
      -3746, 145, 1],
    poly [1, -56, 25, 38, -15, -23, 22, 52, 52, 40, 4, 45, 26, -59, 42, -66, 3],
    poly [0, 1, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, -1],
    poly [-1410, -3130, -3598, -1549, -3416, -3714, -3146, -2686, -4279, -3777, 445, -2148, -2109, -4332,
      -756, 637, -4883, -2185],
    poly [8209, -6799, 1720, 468, -2049, 1867, -1112, -878, 792, 5520, -2698, -2185],
    poly [25, 55, 63, 27, 60, 65, 55, 47, 75, 66, -8, 38, 37, 76, 13, -11, 86, 38],
    poly [-144, 120, -31, -8, 36, -33, 20, 15, -14, -97, 48, 38],
    poly [0, 57, -3249, -3614, 773, -3016, -534, -2341, 2093, 3891, -144, -1],
    poly [0, 1, -57, -63, 14, -53, -9, -41, 37, 68, -3],
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
theorem certificado_8513 :
    haveI : Fact (Nat.Prime 8513) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8513 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8513 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8513 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8513 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8513) := ⟨by norm_num⟩
  have hP : poly [-534, 1] = X - C (534 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8513 : ℕ) : ℤ[X]) = poly [8513] := by simp [poly]
  refine ⟨X - C (534 : ℤ),
    poly [2471, 451, 3253, 580, -525, -2743, 4076, 1554, 1900, -1766, -912, 78, -2981, -3736, -2478,
      -3751, 535, 1],
    poly [155, 28, 204, 36, -33, -172, 256, 97, 119, -111, -57, 5, -187, -234, -155, -235, 34],
    poly [0, 0, 1, 0, -1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, -1],
    poly [-4630, -5372, -2185, -2737, -9338, -662, -3324, -6071, -3095, -1559, -8730, -4742, -1036,
      -7087, -3894, -2246, -5240, -4863],
    poly [8513, -8513, 4630, 742, -7817, -190, 9788, -9228, -8569, 6051, -3193, -1648, 2994, -377, -4863],
    poly [291, 337, 137, 172, 586, 41, 209, 381, 194, 98, 548, 297, 65, 445, 244, 141, 329, 305],
    poly [-534, 535, -292, -46, 491, 11, -614, 580, 537, -380, 201, 103, -188, 24, 305],
    poly [0, 0, 2471, -2020, 331, -653, -3907, 455, -3060, -755, 1258, -1273, -4227, -534, -1],
    poly [0, 0, 155, -127, 21, -41, -245, 29, -192, -47, 79, -80, -265, -33],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_8627 :
    haveI : Fact (Nat.Prime 8627) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8627 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8627 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8627 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8627 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8627) := ⟨by norm_num⟩
  have hP : poly [-74, 1] = X - C (74 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8627 : ℕ) : ℤ[X]) = poly [8627] := by simp [poly]
  refine ⟨X - C (74 : ℤ),
    poly [3614, 3896, 2734, 853, 711, -3721, 1815, 724, 1059, -1851, -1424, -369, -5, -4197, -3321,
      -3076, 75, 1],
    poly [31, 33, 23, 7, 6, -32, 16, 6, 9, -16, -12, -3, 0, -36, -28, -26, 1],
    poly [-1, 0, -1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-5973, -4305, -2184, -6702, -934, -3654, -8354, -490, -3648, -4157, -2182, -5303, -1498, -1330,
      -4592, -206, -3411, -6602],
    poly [2654, -6959, -3852, -2850, 7889, -1265, -600, 3023, -3340, -4386, 3205, 3191, -6602],
    poly [52, 37, 19, 58, 8, 32, 72, 4, 32, 36, 19, 46, 13, 12, 40, 2, 30, 57],
    poly [-22, 60, 33, 24, -68, 11, 5, -26, 29, 38, -28, -27, 57],
    poly [-3614, -282, -2452, 1599, 1304, 1300, 3515, -4266, 875, 245, 3151, -74, -1],
    poly [-31, -2, -21, 14, 11, 11, 30, -37, 8, 2, 27, -1],
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
theorem certificado_8741 :
    haveI : Fact (Nat.Prime 8741) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8741 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8741 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8741 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8741 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8741) := ⟨by norm_num⟩
  have hP : poly [-1227, 1] = X - C (1227 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8741 : ℕ) : ℤ[X]) = poly [8741] := by simp [poly]
  refine ⟨X - C (1227 : ℤ),
    poly [3968, 1485, 2922, 38, 1781, -312, 762, -4003, -3266, 553, 3655, 2247, 3692, 4028, -588, 3305,
      1228, 1],
    poly [557, 208, 410, 5, 250, -44, 107, -562, -458, 78, 513, 315, 518, 565, -83, 464, 172],
    poly [-2, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, -1],
    poly [-4495, 25, 1197, 913, 236, 3085, 366, 2964, -261, -285, -1204, 391, -85, 627, -1246, 968, 521,
      -206],
    poly [-249, 299, 2344, -568, -1354, 1203, -918, 1873, -2214, 447, 727, -206],
    poly [631, -4, -168, -128, -33, -433, -51, -416, 37, 40, 169, -55, 12, -88, 175, -136, -73, 29],
    poly [35, -42, -329, 80, 190, -169, 129, -263, 311, -63, -102, 29],
    poly [805, -3775, -2874, -2973, -3486, 218, 335, 4125, 3893, -2077, -1227, -1],
    poly [113, -530, -403, -417, -489, 31, 47, 579, 546, -292, -172],
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
theorem certificado_8779 :
    haveI : Fact (Nat.Prime 8779) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8779 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8779 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8779 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8779 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8779) := ⟨by norm_num⟩
  have hP : poly [-1475, 1] = X - C (1475 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8779 : ℕ) : ℤ[X]) = poly [8779] := by simp [poly]
  refine ⟨X - C (1475 : ℤ),
    poly [3833, -789, -685, -4262, 2360, 323, 3613, -313, 839, 1060, -3249, -151, 3202, 3609, -2539, -91,
      1476, 1],
    poly [644, -133, -115, -716, 397, 54, 607, -53, 141, 178, -546, -25, 538, 606, -427, -15, 248],
    poly [-1, 0, 0, 0, 0, 0, 0, -1, 1, -1, -1],
    poly [-2393, -4079, -2985, 75, -161, 190, -2006, -3799, -5187, -5057, -2944, 944, -3797, -4074,
      -4592, -3152, -681, 517],
    poly [6386, -10465, 1094, 3060, -236, 351, -2196, -4186, -681, 517],
    poly [402, 685, 501, -13, 27, -32, 337, 638, 871, 849, 494, -159, 638, 684, 771, 529, 114, -87],
    poly [-1073, 1759, -185, -514, 40, -59, 369, 703, 114, -87],
    poly [-3833, -4157, -104, 3577, 2157, 2037, -3290, 93, -1476, -1],
    poly [-644, -698, -17, 601, 362, 342, -553, 16, -248],
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
theorem certificado_8893 :
    haveI : Fact (Nat.Prime 8893) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8893 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8893 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8893 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8893 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8893) := ⟨by norm_num⟩
  have hP : poly [-842, 1] = X - C (842 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8893 : ℕ) : ℤ[X]) = poly [8893] := by simp [poly]
  refine ⟨X - C (842 : ℤ),
    poly [2651, 320, -834, -772, 3833, -2826, -2422, 2627, 1693, -3420, -1789, -3572, 978, -2164, 3430,
      -1633, 843, 1],
    poly [251, 30, -79, -73, 363, -268, -229, 249, 160, -324, -169, -338, 93, -205, 325, -155, 80],
    poly [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    poly [-473, -463, -294, -3663, -1016, -1636, -3221, 1118, -2922, -54, 393, -1835, -359, -315, -1350,
      3391, 809, -1919],
    poly [9366, -8903, -169, 3842, -2184, 441, 4785, -3617, 2013, -663, -2728, 1919],
    poly [45, 44, 28, 347, 96, 155, 305, -106, 277, 5, -37, 174, 34, 30, 128, -321, -76, 182],
    poly [-887, 844, 15, -364, 207, -42, -453, 343, -191, 63, 258, -182],
    poly [2651, -2331, -1154, 2713, -3968, -1251, -688, 823, -2988, -2475, 842, 1],
    poly [251, -221, -109, 257, -376, -118, -65, 78, -283, -234, 80],
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
theorem certificado_8969 :
    haveI : Fact (Nat.Prime 8969) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 8969 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((8969 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((8969 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((8969 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 8969) := ⟨by norm_num⟩
  have hP : poly [-112, 1] = X - C (112 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((8969 : ℕ) : ℤ[X]) = poly [8969] := by simp [poly]
  refine ⟨X - C (112 : ℤ),
    poly [2002, 3141, 989, 4173, -2205, 3664, 3316, 430, 2166, -2303, 2542, -1659, -4179, 283, 483, 3688,
      113, 1],
    poly [25, 39, 12, 52, -28, 46, 41, 5, 27, -29, 32, -21, -52, 4, 6, 46, 1],
    poly [0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, -1],
    poly [2008, 104, 87, -1755, -330, -1038, -724, -1522, -408, 2645, -1572, 1033, -3188, -1544, -1209,
      796, -4071, -671],
    poly [8969, -8969, 2008, 104, -1921, -1859, 1591, 821, -2315, -335, -2005, 4867, -3400, -671],
    poly [-25, -1, -1, 22, 4, 13, 9, 19, 5, -33, 20, -13, 40, 19, 15, -10, 51, 8],
    poly [-112, 113, -26, -1, 24, 23, -20, -10, 29, 4, 25, -61, 43, 8],
    poly [0, 0, -2002, -3141, 1013, -1032, 1192, -2632, 4461, 200, 3205, -3575, -112, -1],
    poly [0, 0, -25, -39, 13, -13, 15, -33, 56, 2, 40, -45, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9007 :
    haveI : Fact (Nat.Prime 9007) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9007 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9007 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((9007 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((9007 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9007) := ⟨by norm_num⟩
  have hP : poly [-730, 1] = X - C (730 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9007 : ℕ) : ℤ[X]) = poly [9007] := by simp [poly]
  refine ⟨X - C (730 : ℤ),
    poly [1641, 1853, -3773, -3682, 106, -1172, -2605, -1879, -4321, 3893, -809, -3826, 2228, 2335,
      -2119, 2218, 731, 1],
    poly [133, 150, -306, -298, 9, -95, -211, -152, -350, 316, -66, -310, 181, 189, -172, 180, 59],
    poly [-1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1],
    poly [-1812, -630, -3787, -2175, 591, 1113, 176, -2404, -1914, -4381, -177, 421, 866, 188, -4082,
      -4458, 82, -1269],
    poly [7195, -9637, -3787, -363, -591, 4270, 376, -4540, 1351, -1269],
    poly [147, 51, 307, 176, -48, -90, -14, 195, 155, 355, 14, -34, -70, -15, 331, 361, -7, 103],
    poly [-583, 782, 306, 29, 48, -346, -30, 368, -110, 103],
    poly [-1641, -1853, 3773, -3684, 106, -4454, 4337, -1487, -730, -1],
    poly [-133, -150, 306, -299, 9, -361, 352, -121, -59],
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
theorem certificado_9311 :
    haveI : Fact (Nat.Prime 9311) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9311 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9311 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((9311 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((9311 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9311) := ⟨by norm_num⟩
  have hP : poly [-403, 1] = X - C (403 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9311 : ℕ) : ℤ[X]) = poly [9311] := by simp [poly]
  refine ⟨X - C (403 : ℤ),
    poly [1109, 280, -2148, -375, -2011, -3332, -170, 3419, -985, 4087, 3083, -801, -4438, -2668, -977,
      4526, 404, 1],
    poly [48, 12, -93, -16, -87, -144, -7, 148, -43, 177, 133, -35, -192, -115, -42, 196, 17],
    poly [-1, 0, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1],
    poly [-809, 2516, 2247, 2616, 3079, 1717, 3793, 1326, -205, 3072, 169, -2010, 2952, 2895, 931, 233,
      1502, 142],
    poly [8502, -5986, -1078, 3694, -615, 2332, 2270, -3460, 199, 1964, 698, -1269, 1360, 142],
    poly [35, -109, -97, -113, -133, -74, -164, -57, 9, -133, -7, 87, -128, -125, -40, -10, -65, -6],
    poly [-368, 260, 46, -160, 27, -101, -98, 150, -9, -85, -30, 55, -59, -6],
    poly [-1109, 829, 1319, -944, 2955, 377, 902, -4041, 1769, 1691, -3808, -4122, -403, -1],
    poly [-48, 36, 57, -41, 128, 16, 39, -175, 77, 73, -165, -178, -17],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9349 :
    haveI : Fact (Nat.Prime 9349) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9349 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9349 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((9349 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((9349 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9349) := ⟨by norm_num⟩
  have hP : poly [-123, 1] = X - C (123 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9349 : ℕ) : ℤ[X]) = poly [9349] := by simp [poly]
  refine ⟨X - C (123 : ℤ),
    poly [76, 3649, 3222, -1722, 62, -4636, -2850, 1649, -3711, 1642, -3179, -1394, 3181, 1394, -3029,
      -3445, 124, 1],
    poly [1, 48, 42, -23, 1, -61, -37, 22, -49, 22, -42, -18, 42, 18, -40, -45, 2],
    poly [-1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    poly [-4113, -42, -921, 440, -157, -1530, -21, -2517, 199, -539, -545, -89, 2651, 89, -1528, -173,
      -314, 1053],
    poly [5236, -5278, -879, 1361, -597, -1373, 1509, 1617, -1355, 141, -1367, 1053],
    poly [54, 0, 12, -6, 2, 20, 0, 33, -3, 7, 7, 1, -35, -1, 20, 2, 4, -14],
    poly [-69, 70, 11, -18, 8, 18, -20, -21, 18, -2, 18, -14],
    poly [-76, -3573, 427, -4405, -1784, -4651, -1786, -4423, -416, 3569, -123, -1],
    poly [-1, -47, 6, -58, -23, -61, -23, -58, -5, 47, -2],
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
theorem certificado_9463 :
    haveI : Fact (Nat.Prime 9463) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9463 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9463 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((9463 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((9463 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9463) := ⟨by norm_num⟩
  have hP : poly [-86, 1] = X - C (86 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9463 : ℕ) : ℤ[X]) = poly [9463] := by simp [poly]
  refine ⟨X - C (86 : ℤ),
    poly [3191, 2898, 1024, 342, 114, -989, -1552, -2989, 2386, -2283, 1734, -3611, -42, 4731, 55, -1980,
      87, 1],
    poly [29, 26, 9, 3, 1, -9, -14, -27, 22, -21, 16, -33, 0, 43, 0, -18, 1],
    poly [0, -1, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, -1],
    poly [3847, 1581, 2655, 1127, 3530, 587, 4404, 3238, 4985, 4015, 4884, 4564, 3680, 4550, 1039, 448,
      3192, 363],
    poly [9463, -5616, 1581, -1192, 3393, 2456, -1732, 420, 3526, 3888, 3232, 1358, 676, 448, 3192, 363],
    poly [-35, -14, -24, -10, -32, -5, -40, -29, -45, -36, -44, -41, -33, -41, -9, -4, -29, -3],
    poly [-86, 52, -15, 11, -31, -22, 16, -4, -32, -35, -29, -12, -6, -4, -29, -3],
    poly [0, -3191, -2898, 2167, -635, -1988, 3498, 4222, 2910, 3665, -1938, -4644, -54, 1980, -87, -1],
    poly [0, -29, -26, 20, -6, -18, 32, 38, 26, 33, -18, -42, 0, 18, -1],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_9539 :
    haveI : Fact (Nat.Prime 9539) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9539 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9539 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((9539 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((9539 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9539) := ⟨by norm_num⟩
  have hP : poly [-681, 1] = X - C (681 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9539 : ℕ) : ℤ[X]) = poly [9539] := by simp [poly]
  refine ⟨X - C (681 : ℤ),
    poly [-1905, 3429, -3875, -594, 1666, -4662, -2206, 2364, -893, 4411, -2809, -1671, 866, -2422, 1061,
      -2968, 682, 1],
    poly [-136, 245, -277, -42, 119, -333, -157, 169, -64, 315, -201, -119, 62, -173, 76, -212, 49],
    poly [-1, 0, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1],
    poly [-4730, -1025, -1860, 478, -345, -3764, -1822, -3444, -2718, -2843, -2493, -3473, -729, -781,
      -4451, -3714, -1962, -3052],
    poly [4809, -5834, -835, 2338, -5553, -4444, 4812, -119, -2489, -662, -1962, -3052],
    poly [338, 73, 133, -34, 25, 269, 130, 246, 194, 203, 178, 248, 52, 56, 318, 265, 140, 218],
    poly [-343, 417, 59, -167, 397, 317, -344, 9, 178, 47, 140, 218],
    poly [1905, 4205, -2235, -3281, -355, 2899, -486, -547, -379, 2969, -682, -1],
    poly [136, 300, -160, -234, -25, 207, -35, -39, -27, 212, -49],
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
theorem certificado_9767 :
    haveI : Fact (Nat.Prime 9767) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 9767 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((9767 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((9767 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((9767 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 9767) := ⟨by norm_num⟩
  have hP : poly [-423, 1] = X - C (423 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((9767 : ℕ) : ℤ[X]) = poly [9767] := by simp [poly]
  refine ⟨X - C (423 : ℤ),
    poly [3856, 494, 3557, 932, 4320, -1329, 805, -4085, 1445, -874, 4385, 1973, 4461, 1927, -3736, 3547,
      424, 1],
    poly [167, 21, 154, 40, 187, -58, 35, -177, 63, -38, 190, 85, 193, 83, -162, 154, 18],
    poly [1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, 1],
    poly [2925, 5010, 3491, 555, 1818, 5423, 2984, 2147, 6509, 5411, 421, 871, 4197, 3212, 2009, 1452,
      504, 3134],
    poly [6842, -11852, -1406, 3776, 2341, -2188, -1760, -1505, 1682, -504, -3134],
    poly [-127, -217, -151, -24, -79, -235, -129, -93, -282, -234, -18, -38, -182, -139, -87, -63, -22,
      -136],
    poly [-296, 514, 60, -164, -101, 95, 76, 65, -73, 22, 136],
    poly [3856, -3362, -2848, -76, 46, -1570, -1620, -4160, 3546, 424, 1],
    poly [167, -146, -123, -3, 2, -68, -70, -180, 154, 18],
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
theorem certificado_10223 :
    haveI : Fact (Nat.Prime 10223) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10223 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10223 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((10223 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((10223 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10223) := ⟨by norm_num⟩
  have hP : poly [-311, 1] = X - C (311 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10223 : ℕ) : ℤ[X]) = poly [10223] := by simp [poly]
  refine ⟨X - C (311 : ℤ),
    poly [-2301, -1388, 3710, -1796, -4805, 2680, -90, -4931, -1002, 2495, 3591, 406, 1612, -4038, -1032,
      5026, 312, 1],
    poly [-70, -42, 113, -55, -146, 82, -3, -150, -30, 76, 109, 12, 49, -123, -31, 153, 9],
    poly [-1, -1, 0, 0, 0, 0, 0, -1, 0, -1],
    poly [-78, 4458, 4111, 3058, 2956, 3383, 4502, 3125, 3778, 3550, 295, 3999, 921, 2982, 1871, 1210,
      3476, 3812],
    poly [10145, -5765, 4189, -1400, -1155, 325, 1546, -336, 3812],
    poly [2, -136, -125, -93, -90, -103, -137, -95, -115, -108, -9, -122, -28, -91, -57, -37, -106, -116],
    poly [-309, 176, -128, 43, 35, -10, -47, 10, -116],
    poly [2301, 1388, 4212, 408, -1708, -4476, -4715, -311, -1],
    poly [70, 42, 128, 12, -52, -136, -143, -9],
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
theorem certificado_10337 :
    haveI : Fact (Nat.Prime 10337) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10337 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10337 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((10337 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((10337 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10337) := ⟨by norm_num⟩
  have hP : poly [-1617, 1] = X - C (1617 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10337 : ℕ) : ℤ[X]) = poly [10337] := by simp [poly]
  refine ⟨X - C (1617 : ℤ),
    poly [-2979, 2063, 2520, -561, 396, -1713, 472, -2723, -251, 3893, -3846, 3520, 1383, 2852, -3885,
      1046, 1618, 1],
    poly [-466, 323, 394, -88, 62, -268, 74, -426, -39, 609, -602, 551, 216, 446, -608, 164, 253],
    poly [0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, -1],
    poly [-6039, 497, -3667, -3823, -3382, -2442, -3509, 1694, -4069, -2289, -2550, -4794, -1631, -6398,
      -4253, -2564, -5152, -3402],
    poly [10337, -10337, 0, -6039, 6536, -4164, -6195, 6977, -3224, -1223, -395, 1713, 2588, -1750,
      -3402],
    poly [945, -78, 574, 598, 529, 382, 549, -265, 637, 358, 399, 750, 255, 1001, 665, 401, 806, 532],
    poly [-1617, 1618, -1, 945, -1023, 652, 969, -1092, 505, 191, 62, -268, -405, 274, 532],
    poly [0, 0, 0, 2979, -5042, -457, -4277, 4338, 1652, 896, -5120, 4932, 572, -1617, -1],
    poly [0, 0, 0, 466, -789, -71, -669, 679, 258, 140, -801, 772, 89, -253],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_10831 :
    haveI : Fact (Nat.Prime 10831) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 10831 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((10831 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((10831 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((10831 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 10831) := ⟨by norm_num⟩
  have hP : poly [-107, 1] = X - C (107 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((10831 : ℕ) : ℤ[X]) = poly [10831] := by simp [poly]
  refine ⟨X - C (107 : ℤ),
    poly [-4960, 1472, -3934, -138, 3744, 946, -2623, 3822, -2090, 4738, 3081, 5090, 5210, 4705, 1866,
      726, 108, 1],
    poly [-49, 15, -39, -1, 37, 9, -26, 38, -21, 47, 30, 50, 51, 46, 18, 7, 1],
    poly [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    poly [3518, 4057, 2240, 1312, 1607, 2622, 607, 3220, -1007, 1889, 4143, 6391, 541, 790, 1096, 2516,
      5566, 2659],
    poly [7313, -11370, 1817, -2590, -834, 802, 2943, -2908, -306, -1420, -3050, 2907, 2659],
    poly [-35, -40, -22, -13, -16, -26, -6, -32, 10, -19, -41, -63, -5, -8, -11, -25, -55, -26],
    poly [-72, 113, -19, 26, 8, -8, -29, 29, 3, 14, 30, -29, -26],
    poly [-4960, -4399, -5406, -1164, -517, 2627, 227, -504, -2839, -1140, -618, -107, -1],
    poly [-49, -43, -53, -11, -5, 26, 2, -5, -28, -11, -6, -1],
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
theorem certificado_11059 :
    haveI : Fact (Nat.Prime 11059) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11059 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11059 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((11059 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((11059 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11059) := ⟨by norm_num⟩
  have hP : poly [-550, 1] = X - C (550 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11059 : ℕ) : ℤ[X]) = poly [11059] := by simp [poly]
  refine ⟨X - C (550 : ℤ),
    poly [-5248, 1217, 525, -3739, 2205, -1122, 943, 243, -1769, 600, 2796, 3926, -4517, 32, -3197, 4458,
      551, 1],
    poly [-261, 61, 26, -186, 110, -56, 47, 12, -88, 30, 139, 195, -225, 2, -159, 222, 27],
    poly [-1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
    poly [-1144, 181, -2330, 2270, 1273, -76, -1868, 4925, 373, -1083, -402, 1429, 246, -4039, 2287,
      2017, 609, -1163],
    poly [9915, -10878, -1186, 2089, 3603, -2346, -4285, 6326, -270, -1408, -1772, 1163],
    poly [57, -9, 116, -113, -63, 4, 93, -245, -18, 54, 20, -71, -12, 201, -114, -100, -30, 58],
    poly [-493, 542, 58, -104, -179, 117, 213, -315, 14, 70, 88, -58],
    poly [5248, -1217, 5286, 4956, -1680, -2617, -4549, 3229, 3404, 3907, 550, 1],
    poly [261, -61, 263, 246, -84, -130, -226, 161, 169, 194, 27],
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
theorem certificado_11173 :
    haveI : Fact (Nat.Prime 11173) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11173 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11173 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((11173 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((11173 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11173) := ⟨by norm_num⟩
  have hP : poly [-264, 1] = X - C (264 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11173 : ℕ) : ℤ[X]) = poly [11173] := by simp [poly]
  refine ⟨X - C (264 : ℤ),
    poly [-2497, -2972, -4709, 4299, -5147, 5567, -910, 4525, 525, 1187, 597, 2203, 1278, 4364, 736,
      2923, 265, 1],
    poly [-59, -70, -111, 102, -122, 132, -22, 107, 12, 28, 14, 52, 30, 103, 17, 69, 6],
    poly [-1, 1, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [-5620, -5472, -4625, -1363, -1266, -4863, -3480, -2586, -4868, -4792, -4961, -2380, -4444,
      -7499, -4675, -3310, -2670, -2329],
    poly [5553, -5405, 699, 2415, -3165, -3694, -640, -341, -2329],
    poly [133, 129, 109, 32, 30, 115, 82, 61, 115, 113, 117, 56, 105, 177, 110, 78, 63, 55],
    poly [-131, 128, -17, -57, 75, 87, 15, 8, 55],
    poly [2497, -2022, 1262, 428, -3892, 2186, -2658, -264, -1],
    poly [59, -48, 30, 10, -92, 52, -63, -6],
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
theorem certificado_11287 :
    haveI : Fact (Nat.Prime 11287) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11287 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11287 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((11287 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((11287 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11287) := ⟨by norm_num⟩
  have hP : poly [-2161, 1] = X - C (2161 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11287 : ℕ) : ℤ[X]) = poly [11287] := by simp [poly]
  refine ⟨X - C (2161 : ℤ),
    poly [4941, 5241, 1538, 1834, -4679, -3183, -1934, 746, -1483, -4106, -1339, -4529, 609, -1786, 3133,
      -735, 2162, 1],
    poly [946, 1003, 294, 351, -896, -609, -370, 143, -284, -786, -256, -867, 117, -342, 600, -141, 414],
    poly [0, -1, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0, 0, -1],
    poly [777, -800, 3127, 2173, -2079, 1946, 2115, 2324, -3228, 1794, -3082, 2776, -1734, 1638, 198,
      4428, -3765, 2666],
    poly [11287, -10510, -1577, 4704, -2531, -325, 3848, -5660, 8938, -7137, 4106, -4230, 8193, -6431,
      2666],
    poly [-149, 153, -599, -416, 398, -373, -405, -445, 618, -344, 590, -532, 332, -314, -38, -848, 721,
      -511],
    poly [-2161, 2013, 301, -901, 485, 62, -737, 1084, -1712, 1367, -787, 810, -1569, 1232, -511],
    poly [0, -4941, -300, -1238, -596, -1071, 4554, 4964, -5414, -4557, 4918, -3868, 2897, -2161, -1],
    poly [0, -946, -57, -237, -114, -205, 872, 950, -1037, -872, 942, -741, 555, -414],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_11743 :
    haveI : Fact (Nat.Prime 11743) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11743 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11743 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((11743 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((11743 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11743) := ⟨by norm_num⟩
  have hP : poly [-560, 1] = X - C (560 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11743 : ℕ) : ℤ[X]) = poly [11743] := by simp [poly]
  refine ⟨X - C (560 : ℤ),
    poly [-692, 1907, 3736, 1160, 3504, 5018, -4164, -5145, -2903, -1515, -3945, 5487, 3323, -2804,
      -3465, -2900, 561, 1],
    poly [-33, 91, 178, 55, 167, 239, -199, -245, -138, -72, -188, 262, 158, -134, -165, -138, 27],
    poly [-1, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1],
    poly [-2223, -2206, -2185, 604, 4740, 1560, -3059, -5311, -1876, 3058, 173, 63, -5599, -1541, 18,
      -1510, -2016, 122],
    poly [9520, -13949, 38, 587, 4719, 994, -4989, -2169, 2156, -1632, -2016, 122],
    poly [106, 105, 104, -29, -226, -74, 146, 253, 89, -146, -8, -3, 267, 73, -1, 72, 96, -6],
    poly [-454, 666, -3, -28, -225, -47, 238, 103, -103, 78, 96, -6],
    poly [692, -1907, -4428, 1439, -1675, 3457, -3328, -656, 4025, 2901, -561, -1],
    poly [33, -91, -211, 69, -80, 165, -159, -31, 192, 138, -27],
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
theorem certificado_11933 :
    haveI : Fact (Nat.Prime 11933) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11933 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11933 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((11933 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((11933 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11933) := ⟨by norm_num⟩
  have hP : poly [-83, 1] = X - C (83 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11933 : ℕ) : ℤ[X]) = poly [11933] := by simp [poly]
  refine ⟨X - C (83 : ℤ),
    poly [-5032, -4230, -1920, -742, -3747, -5796, 5681, 2225, -1986, 1270, 1453, 3468, -102, -5177,
      -5957, -4960, 84, 1],
    poly [-35, -29, -13, -5, -26, -40, 40, 15, -14, 9, 10, 24, -1, -36, -41, -34, 1],
    poly [-1, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [-445, 3719, 2619, 4331, 3489, 2760, -2137, -2196, -759, -1173, 3854, 1758, 3458, 1897, -1141,
      -2184, -40, 1136],
    poly [11488, -7769, -1100, 1712, -1287, 2990, -1833, 553, 1862, 2179, -2144, -1176, 1136],
    poly [3, -26, -18, -30, -24, -19, 15, 15, 5, 8, -27, -12, -24, -13, 8, 15, 0, -8],
    poly [-80, 55, 7, -12, 9, -21, 13, -4, -13, -15, 15, 8, -8],
    poly [5032, -802, -2310, -1178, -3896, -5654, -2656, -32, -863, 996, 5044, -83, -1],
    poly [35, -6, -16, -8, -27, -39, -18, 0, -6, 7, 35, -1],
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
theorem certificado_11971 :
    haveI : Fact (Nat.Prime 11971) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 11971 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((11971 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((11971 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((11971 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 11971) := ⟨by norm_num⟩
  have hP : poly [-385, 1] = X - C (385 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((11971 : ℕ) : ℤ[X]) = poly [11971] := by simp [poly]
  refine ⟨X - C (385 : ℤ),
    poly [-4322, 2725, 5635, 1134, 687, -3916, -2280, 5622, 4803, -3470, -1999, -938, -189, 4819, 5827,
      4959, 386, 1],
    poly [-139, 88, 181, 36, 22, -126, -73, 181, 154, -112, -64, -30, -6, 155, 187, 159, 12],
    poly [-1, 0, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1],
    poly [-4350, 1391, -1890, 3263, -3502, 3321, -4217, 1609, -5403, -695, -3419, 2917, -2539, -501,
      -2921, 493, -4442, -1190],
    poly [7621, -6230, -3281, 803, -1024, -808, -994, 1521, 1683, -4442, -1190],
    poly [140, -45, 61, -105, 113, -107, 136, -52, 174, 22, 110, -94, 82, 16, 94, -16, 143, 38],
    poly [-245, 201, 105, -26, 33, 26, 32, -49, -54, 143, 38],
    poly [4322, 4924, -2910, -3148, 5371, -5956, 140, -5441, -4958, -386, -1],
    poly [139, 158, -94, -101, 173, -192, 5, -175, -159, -12],
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
theorem certificado_12161 :
    haveI : Fact (Nat.Prime 12161) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12161 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12161 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((12161 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((12161 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12161) := ⟨by norm_num⟩
  have hP : poly [-1953, 1] = X - C (1953 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12161 : ℕ) : ℤ[X]) = poly [12161] := by simp [poly]
  refine ⟨X - C (1953 : ℤ),
    poly [2553, 3040, 151, -5959, 2469, -1406, 4576, -5415, -9, 1208, -4738, -1528, -144, 5355, 202,
      -2391, 1954, 1],
    poly [410, 488, 24, -957, 397, -226, 735, -870, -1, 194, -761, -245, -23, 860, 32, -384, 314],
    poly [-1, -1, 0, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [470, 4499, 6668, 2466, 4170, 7496, 4596, 2247, 3871, 4700, 4277, 1867, 1131, 7345, 947, 2818,
      5428, 6326],
    poly [12631, -7662, 6198, -2033, -2498, 5500, 4455, -2610, -898, 6326],
    poly [-76, -723, -1071, -396, -670, -1204, -738, -361, -622, -755, -687, -300, -182, -1180, -152,
      -453, -872, -1016],
    poly [-2029, 1231, -996, 327, 401, -884, -715, 419, 144, -1016],
    poly [-2553, -3040, 2402, -3162, -2318, 5055, -2594, 4345, -1953, -1],
    poly [-410, -488, 386, -508, -372, 812, -417, 698, -314],
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
theorem certificado_12503 :
    haveI : Fact (Nat.Prime 12503) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12503 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12503 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((12503 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((12503 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12503) := ⟨by norm_num⟩
  have hP : poly [-983, 1] = X - C (983 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12503 : ℕ) : ℤ[X]) = poly [12503] := by simp [poly]
  refine ⟨X - C (983 : ℤ),
    poly [-3307, 569, 2926, -4347, -386, -4503, -3655, 9, 1450, 3194, -5784, -1405, 1474, -4959, 1216,
      4542, 984, 1],
    poly [-260, 45, 230, -342, -30, -354, -287, 1, 114, 251, -455, -110, 116, -390, 96, 357, 77],
    poly [-1, 0, -1, 0, 1, -1, 0, 0, 0, 0, 0, -1],
    poly [-416, -798, -1269, 4009, 4167, 1547, 1786, 4470, 3328, 2640, 2970, 6519, 2745, 121, -365, 5320,
      1103, -3671],
    poly [12087, -12885, -887, 4896, 103, 2624, 486, -5685, 4217, 4774, -3671],
    poly [33, 63, 100, -315, -327, -121, -140, -351, -261, -207, -233, -512, -215, -9, 29, -418, -86,
      289],
    poly [-950, 1014, 69, -385, -8, -206, -38, 447, -332, -375, 289],
    poly [3307, -3876, 950, 3397, 2878, 6070, 6175, 3326, -3558, -983, -1],
    poly [260, -305, 75, 267, 226, 477, 485, 261, -280, -77],
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
theorem certificado_12541 :
    haveI : Fact (Nat.Prime 12541) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12541 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12541 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((12541 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((12541 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12541) := ⟨by norm_num⟩
  have hP : poly [-41, 1] = X - C (41 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12541 : ℕ) : ℤ[X]) = poly [12541] := by simp [poly]
  refine ⟨X - C (41 : ℤ),
    poly [2447, -3305, 837, -1509, -4625, -4701, 5697, -5061, -3794, 6025, -5053, 1712, 1877, -566,
      -4602, 1723, 42, 1],
    poly [8, -11, 3, -5, -15, -15, 19, -17, -12, 20, -17, 6, 6, -2, -15, 6],
    poly [-1, -1, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, -1],
    poly [379, 1000, -1126, -3319, -4596, -2486, 1236, -1732, -275, -3910, -634, -3307, 3663, 3833, 1696,
      1338, -506, -2998],
    poly [12920, -11541, -1126, -3698, -5596, -981, 5176, 738, 397, -5802, 1461, -503, 2202, 4336, -506,
      -2998],
    poly [-1, -3, 4, 11, 15, 8, -4, 6, 1, 13, 2, 11, -12, -12, -5, -4, 2, 10],
    poly [-42, 39, 3, 12, 18, 3, -17, -2, -1, 19, -5, 2, -7, -14, 2, 10],
    poly [-2447, 3305, -837, 3956, 1320, 3091, -1454, -3706, -1008, -4001, 6020, 2288, 4644, -1722, -42,
      -1],
    poly [-8, 11, -3, 13, 4, 10, -5, -12, -3, -13, 20, 7, 15, -6],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_12959 :
    haveI : Fact (Nat.Prime 12959) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 12959 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((12959 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((12959 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((12959 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 12959) := ⟨by norm_num⟩
  have hP : poly [-298, 1] = X - C (298 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((12959 : ℕ) : ℤ[X]) = poly [12959] := by simp [poly]
  refine ⟨X - C (298 : ℤ),
    poly [1609, 4528, -985, 5476, 2845, -1469, -6267, 3110, -207, -2262, -312, -1784, -4833, 2506, -296,
      -1610, 299, 1],
    poly [37, 104, -23, 126, 65, -34, -144, 72, -5, -52, -7, -41, -111, 58, -7, -37, 7],
    poly [1, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1],
    poly [3482, -768, -4870, -883, -1261, -2132, -265, 2220, -4773, -1448, 694, 1310, -4950, -1753,
      -1003, -2566, -1745, -916],
    poly [9477, -8709, 4102, -3987, 3860, -3379, -2487, 734, -1737, -829, -916],
    poly [-80, 18, 112, 20, 29, 49, 6, -51, 110, 33, -16, -30, 114, 40, 23, 59, 40, 21],
    poly [-218, 201, -95, 92, -89, 78, 57, -17, 40, 19, 21],
    poly [1609, 2919, -5513, 6461, -4240, 5726, -894, -1612, 1908, -298, -1],
    poly [37, 67, -127, 149, -98, 132, -21, -37, 44, -7],
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
theorem certificado_13187 :
    haveI : Fact (Nat.Prime 13187) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 13187 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((13187 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((13187 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((13187 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 13187) := ⟨by norm_num⟩
  have hP : poly [-1037, 1] = X - C (1037 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((13187 : ℕ) : ℤ[X]) = poly [13187] := by simp [poly]
  refine ⟨X - C (1037 : ℤ),
    poly [-2467, 3838, -2387, 3393, -5681, 287, -6536, 922, 3943, 6095, 718, 1781, -11, -3230, -5929,
      -4927, 1038, 1],
    poly [-194, 302, -188, 267, -447, 23, -514, 73, 310, 479, 56, 140, -1, -254, -466, -387, 82],
    poly [-1, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1, -1],
    poly [-2302, 2261, -2516, 1803, 1680, 1540, -978, -1807, -2965, 1828, -2580, 2159, -3597, -1250,
      -294, -2315, -3436, 327],
    poly [10885, -8624, -4777, 2017, 2138, -354, -2976, 1065, 3142, -2642, -3436, 327],
    poly [181, -178, 198, -142, -132, -121, 77, 142, 233, -144, 203, -170, 283, 98, 23, 182, 270, -26],
    poly [-856, 679, 375, -159, -168, 28, 234, -84, -247, 208, 270, -26],
    poly [2467, -6305, 6225, -3313, 5236, -6048, -5919, -1697, -6220, 4928, -1038, -1],
    poly [194, -496, 490, -261, 412, -476, -465, -133, -489, 388, -82],
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
theorem certificado_13339 :
    haveI : Fact (Nat.Prime 13339) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 13339 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((13339 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((13339 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((13339 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 13339) := ⟨by norm_num⟩
  have hP : poly [-287, 1] = X - C (287 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((13339 : ℕ) : ℤ[X]) = poly [13339] := by simp [poly]
  refine ⟨X - C (287 : ℤ),
    poly [2045, -4873, 3097, 4705, -2261, -2843, 176, 2278, -1154, 972, 1816, -3433, 6216, 2392, 5818,
      2623, 288, 1],
    poly [44, -105, 67, 101, -49, -61, 4, 49, -25, 21, 39, -74, 134, 51, 125, 56, 6],
    poly [1, 0, 0, 0, 0, -1, 0, 1, 1, 0, 0, 0, 0, -1],
    poly [1073, -5616, 914, -597, -5250, -572, -3019, -1029, -2184, -1212, -1441, -1, 3118, 805, -4455,
      1011, 1123, -1154],
    poly [12266, -6650, -6530, 1511, 4653, -3605, -4242, 3467, 5260, -5466, -112, 2277, -1154],
    poly [-23, 121, -20, 13, 113, 12, 65, 22, 47, 26, 31, 0, -67, -17, 96, -22, -24, 25],
    poly [-264, 144, 140, -33, -100, 78, 91, -75, -113, 118, 2, -49, 25],
    poly [2045, 6421, -5369, 1608, 6373, -2627, -3402, -3823, 3426, -3195, -2335, -287, -1],
    poly [44, 138, -116, 35, 137, -57, -73, -82, 74, -69, -50, -6],
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
theorem certificado_13567 :
    haveI : Fact (Nat.Prime 13567) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 13567 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((13567 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((13567 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((13567 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 13567) := ⟨by norm_num⟩
  have hP : poly [-328, 1] = X - C (328 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((13567 : ℕ) : ℤ[X]) = poly [13567] := by simp [poly]
  refine ⟨X - C (328 : ℤ),
    poly [-4674, 5487, -66, -1117, -2237, -255, -2648, 5245, -5113, 2218, -2930, 3176, -2348, -3523,
      -838, -623, 329, 1],
    poly [-113, 133, -2, -27, -54, -6, -64, 127, -124, 54, -71, 77, -57, -85, -20, -15, 8],
    poly [-1, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0, -1],
    poly [1486, 746, 1571, 4593, 6174, 1753, 540, 1984, -5126, 1884, 2319, 459, 3266, 3895, -198, -1410,
      4708, 1004],
    poly [15053, -14307, 825, 3022, 3067, -3675, -1128, 5291, -1021, 4916, -5114, 3704, 1004],
    poly [-36, -18, -38, -111, -149, -42, -13, -48, 124, -46, -56, -11, -79, -94, 5, 34, -114, -24],
    poly [-364, 347, -21, -73, -74, 89, 27, -128, 25, -119, 124, -90, -24],
    poly [4674, 3406, 5553, 1051, 5794, 6098, -2215, -1289, 3636, -113, 951, -328, -1],
    poly [113, 82, 134, 25, 140, 147, -54, -31, 88, -3, 23, -8],
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
theorem certificado_13681 :
    haveI : Fact (Nat.Prime 13681) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 13681 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((13681 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((13681 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((13681 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 13681) := ⟨by norm_num⟩
  have hP : poly [-652, 1] = X - C (652 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((13681 : ℕ) : ℤ[X]) = poly [13681] := by simp [poly]
  refine ⟨X - C (652 : ℤ),
    poly [4973, -4189, 707, 5079, 2232, 528, 5981, 3954, 1328, -4929, 538, -2706, -193, -6589, 6075,
      1646, 653, 1],
    poly [237, -200, 34, 242, 106, 25, 285, 188, 63, -235, 26, -129, -9, -314, 290, 78, 31],
    poly [-1, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1],
    poly [-986, 4594, 322, -1615, -338, -2875, -256, -231, -1427, -4954, -4225, -4077, -1307, 250, 735,
      -3314, -6069, -135],
    poly [12695, -8101, -4272, -2923, 5871, -1229, -3590, -635, -3442, 2135, -1885, 2620, -5934, -135],
    poly [47, -219, -15, 77, 16, 137, 12, 11, 68, 236, 201, 194, 62, -12, -35, 158, 289, 6],
    poly [-605, 387, 203, 139, -280, 59, 171, 30, 164, -102, 90, -125, 283, 6],
    poly [-4973, -4519, -4896, 4336, -6645, 5970, -1040, 502, 2204, -2011, -5081, -994, -652, -1],
    poly [-237, -215, -233, 207, -317, 285, -50, 24, 105, -96, -242, -47, -31],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_13757 :
    haveI : Fact (Nat.Prime 13757) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 13757 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((13757 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((13757 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((13757 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 13757) := ⟨by norm_num⟩
  have hP : poly [-225, 1] = X - C (225 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((13757 : ℕ) : ℤ[X]) = poly [13757] := by simp [poly]
  refine ⟨X - C (225 : ℤ),
    poly [-428, -4771, -6380, 6575, -6513, 4679, -6338, -2963, -2948, 3472, -168, -3547, -5274, -1552,
      -4348, -4177, 226, 1],
    poly [-7, -78, -104, 108, -107, 77, -104, -48, -48, 57, -3, -58, -86, -25, -71, -68, 4],
    poly [-1, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1],
    poly [-4565, -4891, -6849, -5696, -7464, -7533, -9551, -6564, -7529, -7839, -2949, -1093, -4631,
      -5625, -4590, -1834, -5368, -4650],
    poly [9192, -14083, -6523, -3738, -4052, -5439, -7524, -5699, -4183, -1914, 1663, -8165, -4907, 60,
      -1834, -5368, -4650],
    poly [75, 80, 112, 93, 122, 123, 156, 107, 123, 128, 48, 18, 76, 92, 75, 30, 88, 76],
    poly [-150, 231, 106, 61, 66, 89, 123, 93, 68, 31, -27, 134, 80, -1, 30, 88, 76],
    poly [428, 4343, 2037, 5573, 5283, 5404, 2164, 4901, 6564, 2964, 3376, 871, 1777, 4349, 4177, -226,
      -1],
    poly [7, 71, 33, 91, 86, 88, 35, 80, 107, 48, 55, 14, 29, 71, 68, -4],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 34 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_14251 :
    haveI : Fact (Nat.Prime 14251) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14251 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14251 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14251 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14251 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14251) := ⟨by norm_num⟩
  have hP : poly [-31, 1] = X - C (31 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14251 : ℕ) : ℤ[X]) = poly [14251] := by simp [poly]
  refine ⟨X - C (31 : ℤ),
    poly [-3218, 1735, -6380, 1633, -6843, -6197, 6236, -1178, -3256, -6541, -3429, 6785, -1620, -512,
      2282, 993, 32, 1],
    poly [-7, 4, -14, 4, -15, -13, 14, -3, -7, -14, -7, 15, -4, -1, 5, 2],
    poly [1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1],
    poly [2647, -1405, -1076, 3072, -1851, 3047, 3205, -1387, -156, -576, 1709, 1323, -988, 1236, 4066,
      4617, -3640, 3449],
    poly [11604, -12846, 1076, -425, -2201, -2718, 943, -3536, 5054, 3381, -7706, -1168, 3640, -3449],
    poly [-6, 3, 2, -7, 4, -7, -7, 3, 0, 1, -4, -3, 2, -3, -9, -10, 8, -8],
    poly [-25, 29, -3, 1, 5, 6, -2, 8, -11, -7, 17, 2, -8, 8],
    poly [-3218, 1735, -6380, 4851, 2455, 1918, -1777, -6953, -3902, -1505, 2250, 992, 32, 1],
    poly [-7, 4, -14, 11, 5, 4, -4, -15, -8, -3, 5, 2],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_14327 :
    haveI : Fact (Nat.Prime 14327) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14327 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14327 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14327 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14327 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14327) := ⟨by norm_num⟩
  have hP : poly [-516, 1] = X - C (516 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14327 : ℕ) : ℤ[X]) = poly [14327] := by simp [poly]
  refine ⟨X - C (516 : ℤ),
    poly [-4026, 5462, -5959, 2765, -4215, 3879, -3602, -6754, -2984, 2743, -6825, -2290, 3022, -1077,
      1053, -5440, 517, 1],
    poly [-145, 197, -215, 100, -152, 140, -130, -243, -107, 99, -246, -82, 109, -39, 38, -196, 19],
    poly [-1, 0, 0, 1, 0, 0, 0, 1, 0, 1, -1],
    poly [760, 8869, 4470, 2268, 5429, 9239, 4082, 1823, 4734, 4934, 7822, 1386, 7593, 10687, 2641, 2792,
      8984, 8996],
    poly [15087, -6218, -4399, -2962, -4948, 8209, -2955, -6180, -9008, 8996],
    poly [-28, -320, -161, -82, -196, -333, -147, -66, -171, -178, -282, -50, -274, -385, -95, -101,
      -324, -324],
    poly [-544, 225, 158, 107, 178, -296, 107, 223, 324, -324],
    poly [4026, 4839, -2906, 1577, 2141, -5188, 1878, 6473, -515, -1],
    poly [145, 174, -105, 57, 77, -187, 68, 233, -19],
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
theorem certificado_14479 :
    haveI : Fact (Nat.Prime 14479) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14479 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14479 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14479 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14479 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14479) := ⟨by norm_num⟩
  have hP : poly [-1068, 1] = X - C (1068 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14479 : ℕ) : ℤ[X]) = poly [14479] := by simp [poly]
  refine ⟨X - C (1068 : ℤ),
    poly [6765, -4820, -7122, 983, 2631, 2741, -2980, -2782, 4295, -4036, 2911, 5290, -2476, 4702, -6381,
      -2148, 1069, 1],
    poly [499, -356, -525, 73, 194, 202, -220, -205, 317, -298, 215, 390, -183, 347, -471, -158, 79],
    poly [-1, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, 0, 0, -1, -1],
    poly [-6719, -2265, -2776, -6342, -4366, -7889, -7228, -4882, -6588, -5261, -5436, -8839, -9154,
      -6592, -7159, -8339, -3568, -5692],
    poly [7760, -10025, -511, -3566, -4743, 931, 150, -7939, -1995, 1747, -3591, -2647, -3568, -5692],
    poly [496, 167, 205, 468, 322, 582, 533, 360, 486, 388, 401, 652, 675, 486, 528, 615, 263, 420],
    poly [-572, 740, 37, 263, 350, -69, -11, 586, 147, -129, 265, 195, 263, 420],
    poly [-6765, -2894, 2302, 6374, 6066, -3004, -6456, -589, -3905, -6850, -7029, 2149, -1069, -1],
    poly [-499, -213, 170, 470, 447, -222, -476, -43, -288, -505, -518, 159, -79],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_14593 :
    haveI : Fact (Nat.Prime 14593) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14593 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14593 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14593 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14593 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14593) := ⟨by norm_num⟩
  have hP : poly [-685, 1] = X - C (685 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14593 : ℕ) : ℤ[X]) = poly [14593] := by simp [poly]
  refine ⟨X - C (685 : ℤ),
    poly [5262, -461, -5987, 2569, 302, 6775, 5911, -737, 1618, -935, -7202, 4165, -6875, 5465, -3358,
      2935, 686, 1],
    poly [247, -22, -281, 121, 14, 318, 277, -35, 76, -44, -338, 196, -323, 257, -158, 138, 32],
    poly [-1, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0, -1],
    poly [-4457, -2674, -1521, 2081, 4664, -999, -1199, 505, -5841, -1973, 1846, 829, -3348, -1032,
      -2669, 1355, 1510, 3108],
    poly [10136, -12810, 1153, 3602, 2583, -10120, 1583, -1600, -961, 3147, -916, -155, -1598, 3108],
    poly [209, 125, 71, -98, -219, 47, 56, -24, 274, 92, -87, -39, 157, 48, 125, -64, -71, -146],
    poly [-476, 602, -55, -169, -121, 475, -75, 75, 45, -148, 43, 7, 75, -146],
    poly [-5262, 5723, 5526, 6037, 2267, 2858, 6587, 6912, -5188, 5084, 6292, -2249, -685, -1],
    poly [-247, 269, 259, 283, 106, 134, 309, 324, -244, 239, 295, -106, -32],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_14669 :
    haveI : Fact (Nat.Prime 14669) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14669 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14669 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14669 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14669 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14669) := ⟨by norm_num⟩
  have hP : poly [-1125, 1] = X - C (1125 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14669 : ℕ) : ℤ[X]) = poly [14669] := by simp [poly]
  refine ⟨X - C (1125 : ℤ),
    poly [2334, -3023, 2227, -2658, 1119, 1670, 6508, -4923, 6789, -672, 1199, 5647, -5002, 478, 1526,
      5217, 1126, 1],
    poly [179, -232, 171, -204, 86, 128, 499, -378, 521, -52, 92, 433, -384, 37, 117, 400, 86],
    poly [0, -1, 0, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1],
    poly [3751, 6310, 3887, -3065, -1011, 1716, 3244, 1459, 1653, 3596, 1355, -4984, 3890, 4602, 391,
      635, 3230, 4797],
    poly [14669, -10918, 2559, -2423, -6952, 5805, 9037, 1664, -7409, -2145, 8052, 1372, -4406, 635,
      3230, 4797],
    poly [-288, -484, -298, 235, 77, -132, -249, -112, -127, -276, -104, 382, -299, -353, -30, -49, -248,
      -368],
    poly [-1125, 838, -197, 186, 533, -446, -693, -127, 568, 164, -618, -105, 338, -49, -248, -368],
    poly [0, -2334, 5357, -5250, 4885, -6111, 2472, -4731, -5937, -5247, -4451, 648, -1525, -5217, -1126,
      -1],
    poly [0, -179, 411, -403, 375, -469, 190, -363, -455, -402, -341, 50, -117, -400, -86],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_14783 :
    haveI : Fact (Nat.Prime 14783) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14783 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14783 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14783 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14783 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14783) := ⟨by norm_num⟩
  have hP : poly [-1931, 1] = X - C (1931 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14783 : ℕ) : ℤ[X]) = poly [14783] := by simp [poly]
  refine ⟨X - C (1931 : ℤ),
    poly [-5313, 2248, -6353, 5570, 7314, 4245, 4297, -304, 5665, -5356, -4466, -6456, 5302, 2598, 5322,
      5377, 1932, 1],
    poly [-694, 294, -830, 728, 955, 554, 561, -40, 740, -700, -583, -843, 693, 339, 695, 702, 252],
    poly [-1, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1],
    poly [2043, 5780, 6892, 1748, 5443, 5154, 7129, 4374, 2229, 3537, 4931, 4970, 5215, 5996, 1426, 9485,
      601, 2028],
    poly [16826, -9003, 6892, 1748, 3400, 1417, 3974, 3738, -6315, 7858, 2362, -1461, 825, 7457, 601,
      2028],
    poly [-267, -755, -900, -228, -711, -673, -931, -571, -291, -462, -644, -649, -681, -783, -186,
      -1239, -78, -265],
    poly [-2198, 1177, -901, -228, -444, -185, -519, -488, 825, -1027, -308, 191, -108, -974, -78, -265],
    poly [5313, -2248, 6353, -5570, 2156, 3316, -3428, -308, -4961, 5609, -1911, 2778, -3390, -5376,
      -1932, -1],
    poly [694, -294, 830, -728, 282, 433, -448, -40, -648, 733, -250, 363, -443, -702, -252],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_14821 :
    haveI : Fact (Nat.Prime 14821) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14821 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14821 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14821 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14821 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14821) := ⟨by norm_num⟩
  have hP : poly [-937, 1] = X - C (937 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14821 : ℕ) : ℤ[X]) = poly [14821] := by simp [poly]
  refine ⟨X - C (937 : ℤ),
    poly [6327, 6919, -3773, 1467, 2564, -1927, 773, 6486, -6067, 5846, -2920, -620, 1502, 3434, 6995,
      4468, 938, 1],
    poly [400, 437, -239, 93, 162, -122, 49, 410, -384, 370, -185, -39, 95, 217, 442, 282, 59],
    poly [0, -1, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0, -1],
    poly [6834, 973, 1378, 2976, 352, 2880, 83, 428, -3700, -446, -2135, -1773, 5108, -1702, 521, 729,
      3782, -786],
    poly [14821, -7987, 973, -5456, 8837, -6887, 7143, -4532, -4671, 7177, -5322, 5816, -5276, 4360,
      -3839, 4568, -786],
    poly [-432, -61, -87, -188, -22, -182, -5, -27, 234, 28, 135, 112, -323, 108, -33, -46, -239, 50],
    poly [-937, 506, -62, 345, -559, 436, -452, 287, 295, -454, 337, -368, 334, -276, 243, -289, 50],
    poly [0, -6327, -6919, -4721, -875, -6929, -7062, -4041, 1182, -236, 4745, -596, 31, -3464, -3531,
      -937, -1],
    poly [0, -400, -437, -298, -55, -438, -446, -255, 75, -15, 300, -38, 2, -219, -223, -59],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 34 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 33 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_14897 :
    haveI : Fact (Nat.Prime 14897) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 14897 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((14897 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((14897 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((14897 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 14897) := ⟨by norm_num⟩
  have hP : poly [-711, 1] = X - C (711 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((14897 : ℕ) : ℤ[X]) = poly [14897] := by simp [poly]
  refine ⟨X - C (711 : ℤ),
    poly [4819, 6481, -3008, 5590, 385, -3268, 7182, 492, 2494, -6785, 2819, 6122, -1039, 6368, 5247,
      -265, 712, 1],
    poly [230, 309, -144, 267, 18, -156, 343, 23, 119, -324, 135, 292, -50, 304, 250, -13, 34],
    poly [0, 0, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1],
    poly [119, 7641, 3524, 543, 5274, -1005, 1689, 9487, 1159, 1273, 3096, 7289, 1554, 4584, 2074, 1400,
      1860, 4773],
    poly [14897, -14897, 119, 7641, 3405, -7098, 1750, -1548, -3704, 2970, 3587, -5233, -2913, 4773],
    poly [-6, -365, -168, -26, -252, 48, -81, -453, -55, -61, -148, -348, -74, -219, -99, -67, -89, -228],
    poly [-711, 712, -7, -365, -162, 339, -84, 74, 177, -142, -171, 250, 139, -228],
    poly [0, 0, -4819, -6481, -7070, 891, -3393, -6039, -1978, -2098, -4801, 978, -711, -1],
    poly [0, 0, -230, -309, -337, 43, -162, -288, -94, -100, -229, 47, -34],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_15277 :
    haveI : Fact (Nat.Prime 15277) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15277 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15277 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15277 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15277 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15277) := ⟨by norm_num⟩
  have hP : poly [-1764, 1] = X - C (1764 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15277 : ℕ) : ℤ[X]) = poly [15277] := by simp [poly]
  refine ⟨X - C (1764 : ℤ),
    poly [-6019, 2664, 3024, 530, 6435, -949, -4452, -6749, -6707, 1659, 3621, 3778, 1587, -1991, 2597,
      -3047, 1765, 1],
    poly [-695, 308, 349, 61, 743, -110, -514, -779, -774, 192, 418, 436, 183, -230, 300, -352, 204],
    poly [-1, -1, -1, -1, 0, -1, -1, 0, 0, -1],
    poly [-2892, 5940, 1788, 4072, 2168, -258, 2460, 435, 3006, 2254, -2042, 4295, 29, 3612, -1435, 6625,
      13, -1030],
    poly [12385, -9337, 1788, 4072, 5060, -9090, 6612, 1043, -1030],
    poly [334, -686, -206, -470, -250, 30, -284, -50, -347, -260, 236, -496, -3, -417, 166, -765, -1,
      119],
    poly [-1430, 1079, -207, -470, -584, 1050, -764, -120, 119],
    poly [6019, -2664, -3024, -530, 2823, -5645, 4812, -1764, -1],
    poly [695, -308, -349, -61, 326, -652, 556, -204],
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
theorem certificado_15391 :
    haveI : Fact (Nat.Prime 15391) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15391 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15391 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15391 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15391 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15391) := ⟨by norm_num⟩
  have hP : poly [-1711, 1] = X - C (1711 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15391 : ℕ) : ℤ[X]) = poly [15391] := by simp [poly]
  refine ⟨X - C (1711 : ℤ),
    poly [-1925, 1681, 1890, 4049, 4554, 7046, 2154, 4346, 6812, -1957, 1645, -5846, -4654, -3313, -7576,
      4943, 1712, 1],
    poly [-214, 187, 210, 450, 506, 783, 239, 483, 757, -218, 183, -650, -517, -368, -842, 550, 190],
    poly [-1, -1, -1, 0, 0, -1, 0, 0, -1],
    poly [-4361, 4200, 364, 3744, -149, 1243, 2809, 723, 2224, -1859, 3167, -2722, 4120, 274, -205, 1180,
      4662, -2964],
    poly [11030, -11191, 364, 8105, -4349, -3482, 7626, -2964],
    poly [485, -467, -40, -416, 17, -138, -312, -80, -247, 207, -352, 303, -458, -30, 23, -131, -518,
      330],
    poly [-1226, 1245, -41, -901, 484, 387, -848, 330],
    poly [1925, -1681, -1890, -5974, -2873, -3231, -1711, -1],
    poly [214, -187, -210, -664, -319, -359, -190],
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
theorem certificado_15467 :
    haveI : Fact (Nat.Prime 15467) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15467 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15467 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15467 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15467 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15467) := ⟨by norm_num⟩
  have hP : poly [-1205, 1] = X - C (1205 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15467 : ℕ) : ℤ[X]) = poly [15467] := by simp [poly]
  refine ⟨X - C (1205 : ℤ),
    poly [2734, -1461, 6622, -5424, -903, -3184, -131, 5147, 5806, -1728, -5816, 3602, 7345, -2330, 550,
      -667, 1206, 1],
    poly [213, -114, 516, -423, -70, -248, -10, 401, 452, -135, -453, 281, 572, -182, 43, -52, 94],
    poly [-1, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, -1],
    poly [-3544, 3410, 117, 1385, -719, -2107, 3270, -3798, 1831, 1810, -2644, 2063, 1669, -3825, -1686,
      -3186, -941, 1628],
    poly [11923, -8513, -3293, 1268, -5648, 2022, 5494, -2139, 1500, -2245, -2569, 1628],
    poly [276, -266, -9, -108, 56, 164, -255, 296, -143, -141, 206, -161, -130, 298, 131, 248, 73, -127],
    poly [-929, 664, 256, -99, 440, -158, -428, 167, -117, 175, 200, -127],
    poly [-2734, 4195, 7384, -3421, -7255, 3742, 5792, 2880, -1217, 1873, -1205, -1],
    poly [-213, 327, 575, -267, -565, 292, 451, 224, -95, 146, -94],
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
theorem certificado_15581 :
    haveI : Fact (Nat.Prime 15581) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15581 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15581 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15581 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15581 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15581) := ⟨by norm_num⟩
  have hP : poly [-302, 1] = X - C (302 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15581 : ℕ) : ℤ[X]) = poly [15581] := by simp [poly]
  refine ⟨X - C (302 : ℤ),
    poly [1393, -7012, -178, 51, -7326, 956, -5930, 3953, -5043, -739, 2474, -1488, 1904, -2109, -5579,
      -1979, 303, 1],
    poly [27, -136, -3, 1, -142, 19, -115, 77, -98, -14, 48, -29, 37, -41, -108, -38, 6],
    poly [-1, 0, -1, 0, 0, 0, 0, 0, 0, -1, 1],
    poly [-3817, 143, -463, 2321, 3878, 736, -719, 566, 2376, 5168, -4419, -2645, 3552, 3005, 1507, 367,
      -875, -260],
    poly [11764, -11621, -4423, 6744, 951, -358, 102, -1857, 355, 260],
    poly [74, -3, 9, -45, -75, -14, 14, -11, -46, -100, 86, 51, -69, -58, -29, -7, 17, 5],
    poly [-228, 226, 85, -131, -18, 7, -2, 36, -7, -5],
    poly [-1393, -7176, 7354, -7405, 543, 7070, -1318, -2584, 301, 1],
    poly [-27, -139, 143, -144, 11, 137, -26, -50, 6],
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
theorem certificado_15619 :
    haveI : Fact (Nat.Prime 15619) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15619 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15619 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15619 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15619 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15619) := ⟨by norm_num⟩
  have hP : poly [-186, 1] = X - C (186 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15619 : ℕ) : ℤ[X]) = poly [15619] := by simp [poly]
  refine ⟨X - C (186 : ℤ),
    poly [3107, 2200, -6790, -1632, -2444, 5781, 3390, -2417, -13, -3359, 6028, 1292, 2946, 2619, 3373,
      3545, 187, 1],
    poly [37, 26, -81, -19, -29, 69, 40, -29, 0, -40, 72, 15, 35, 31, 40, 42, 2],
    poly [1, -1, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, -1],
    poly [6364, 7070, 188, 151, 5777, 3456, -1175, 2243, 3437, -4618, 629, 4436, -330, 820, 4521, 1098,
      -180, 3340],
    poly [9255, -9961, 7588, -481, -4957, 1065, 2273, -2423, -97, 4618, -3520, 3340],
    poly [-76, -84, -2, -2, -69, -41, 14, -27, -41, 55, -8, -53, 4, -10, -54, -13, 2, -40],
    poly [-110, 119, -91, 6, 59, -13, -27, 29, 1, -55, 42, -40],
    poly [3107, -4014, 7536, -4578, -5063, 2408, -155, -2604, -14, -3359, -186, -1],
    poly [37, -48, 90, -55, -60, 29, -2, -31, 0, -40, -2],
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
theorem certificado_15733 :
    haveI : Fact (Nat.Prime 15733) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15733 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15733 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15733 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15733 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15733) := ⟨by norm_num⟩
  have hP : poly [-1885, 1] = X - C (1885 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15733 : ℕ) : ℤ[X]) = poly [15733] := by simp [poly]
  refine ⟨X - C (1885 : ℤ),
    poly [-3614, -6220, -237, 5183, 5478, 1764, -383, -3272, 2594, -5766, 4287, -7401, -4728, -4568,
      7284, -547, 1886, 1],
    poly [-433, -745, -28, 621, 656, 211, -46, -392, 311, -691, 514, -887, -566, -547, 873, -66, 226],
    poly [-1, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, 0, 0, -1],
    poly [1394, 4750, 3191, 1379, -2261, -4433, -3274, 374, -8, 3948, -365, 3856, -2460, 99, -2679,
      -4717, -7005, -279],
    poly [17127, -12377, -1559, -418, 1110, -375, -2212, -410, -2838, 2778, 2038, 2288, -6726, -279],
    poly [-167, -569, -382, -165, 271, 531, 392, -45, 1, -473, 44, -462, 295, -12, 321, 565, 839, 33],
    poly [-2052, 1484, 186, 50, -133, 45, 265, 49, 340, -333, -244, -274, 806, 33],
    poly [3614, 2606, -5983, -1806, 5925, 337, 6477, 788, 159, -3881, -7831, 2433, -1885, -1],
    poly [433, 312, -717, -216, 710, 40, 776, 94, 19, -465, -938, 292, -226],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_15809 :
    haveI : Fact (Nat.Prime 15809) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15809 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15809 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15809 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15809 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15809) := ⟨by norm_num⟩
  have hP : poly [-2657, 1] = X - C (2657 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15809 : ℕ) : ℤ[X]) = poly [15809] := by simp [poly]
  refine ⟨X - C (2657 : ℤ),
    poly [5230, 1900, -3718, 5300, -593, -7753, 3335, 507, -6277, -1353, -1012, 1975, -743, 2106, -6086,
      -4316, 2658, 1],
    poly [879, 319, -625, 891, -100, -1303, 561, 85, -1055, -227, -170, 332, -125, 354, -1023, -725, 447],
    poly [1, 0, -1, 1, -1, 0, 0, -1],
    poly [5054, 5282, -1483, -1075, -700, -1634, -1795, 2358, 3734, 349, -2181, -2414, -1117, -2366, 787,
      -616, 1698, -6637],
    poly [10755, -16037, 11819, -5234, -2314, 8335, -6637],
    poly [-849, -887, 250, 181, 118, 275, 302, -396, -627, -58, 367, 406, 188, 398, -132, 104, -285,
      1116],
    poly [-1808, 2696, -1987, 880, 389, -1401, 1116],
    poly [5230, -3330, 4961, 1769, 6974, -2657, -1],
    poly [879, -560, 834, 297, 1172, -447],
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
theorem certificado_15923 :
    haveI : Fact (Nat.Prime 15923) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 15923 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((15923 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((15923 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((15923 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 15923) := ⟨by norm_num⟩
  have hP : poly [-102, 1] = X - C (102 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((15923 : ℕ) : ℤ[X]) = poly [15923] := by simp [poly]
  refine ⟨X - C (102 : ℤ),
    poly [-5776, 6656, 1158, -4828, 4792, -1358, 455, -4991, 2761, 2837, -4031, 6517, -5556, 3536, 4874,
      -5416, 103, 1],
    poly [-37, 43, 7, -31, 31, -9, 3, -32, 18, 18, -26, 42, -36, 23, 31, -35, 1],
    poly [-1, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [588, 5277, 3918, 4373, 5158, 1263, 2942, 3739, 5464, 1266, 4347, -1711, 6035, 3301, 7333, 816,
      596, 3716],
    poly [16511, -10646, 3330, -316, 6517, 220, -3120, 3716],
    poly [-4, -34, -25, -28, -33, -8, -19, -24, -35, -8, -28, 11, -39, -21, -47, -5, -4, -24],
    poly [-106, 69, -22, 2, -42, -1, 20, -24],
    poly [5776, -6656, -6934, 1337, 5633, 5519, -102, -1],
    poly [37, -43, -44, 9, 36, 35, -1],
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
theorem certificado_16189 :
    haveI : Fact (Nat.Prime 16189) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 16189 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((16189 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((16189 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((16189 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 16189) := ⟨by norm_num⟩
  have hP : poly [-410, 1] = X - C (410 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((16189 : ℕ) : ℤ[X]) = poly [16189] := by simp [poly]
  refine ⟨X - C (410 : ℤ),
    poly [-6752, -8032, -5666, 7212, -7840, -4402, -6052, 7369, -61, 2290, -5167, -7041, -491, -3239,
      -5141, 6621, 411, 1],
    poly [-171, -203, -143, 183, -199, -111, -153, 187, -2, 58, -131, -178, -12, -82, -130, 168, 10],
    poly [1, 0, 0, 0, -1, 0, 0, 1, 1, 0, -1],
    poly [3819, 630, -128, -2420, -1320, -4871, -5314, -1485, -1910, -6057, 369, 2201, 3469, 1024, 5164,
      41, 5438, 4543],
    poly [12370, -13000, 758, 2292, 2719, 362, -315, -9940, 895, 4543],
    poly [-97, -16, 3, 61, 33, 123, 134, 37, 48, 153, -10, -56, -88, -26, -131, -1, -138, -115],
    poly [-313, 330, -20, -58, -69, -9, 8, 252, -23, -115],
    poly [-6752, -1280, 2366, -3311, 7889, 4718, -4016, -6209, -410, -1],
    poly [-171, -32, 60, -84, 200, 119, -102, -157, -10],
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
theorem certificado_16417 :
    haveI : Fact (Nat.Prime 16417) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 16417 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((16417 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((16417 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((16417 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 16417) := ⟨by norm_num⟩
  have hP : poly [-554, 1] = X - C (554 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((16417 : ℕ) : ℤ[X]) = poly [16417] := by simp [poly]
  refine ⟨X - C (554 : ℤ),
    poly [-3882, -3000, 6188, -137, 6045, 2915, 835, 3439, -705, 947, -5036, -987, 6162, -2567, -3857,
      -4452, 555, 1],
    poly [-131, -101, 209, -5, 204, 98, 28, 116, -24, 32, -170, -33, 208, -87, -130, -150, 19],
    poly [-1, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0, -1, -1],
    poly [-3089, 6240, 5516, 2255, 560, 3787, 4830, -1243, -1817, 2627, -32, 4023, 1630, 4026, -3141,
      1380, 2129, 3938],
    poly [13328, -7088, -724, -6350, 7634, -586, 4022, 837, -1332, -2558, 2129, 3938],
    poly [104, -211, -186, -76, -19, -128, -163, 42, 61, -89, 1, -136, -55, -136, 106, -47, -72, -133],
    poly [-450, 240, 24, 214, -258, 20, -136, -28, 45, 86, -72, -133],
    poly [3882, -882, 7229, -6210, -7064, -2176, -5012, -2439, 4411, 4453, -555, -1],
    poly [131, -30, 244, -210, -238, -73, -169, -82, 149, 150, -19],
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
theorem certificado_16493 :
    haveI : Fact (Nat.Prime 16493) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 16493 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((16493 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((16493 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((16493 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 16493) := ⟨by norm_num⟩
  have hP : poly [-310, 1] = X - C (310 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((16493 : ℕ) : ℤ[X]) = poly [16493] := by simp [poly]
  refine ⟨X - C (310 : ℤ),
    poly [-6544, 1841, 1070, 2504, 2083, 1390, 1973, 7242, 715, 4897, -6475, 8066, -240, 6224, 2095,
      -2547, 311, 1],
    poly [-123, 35, 20, 47, 39, 26, 37, 136, 13, 92, -122, 152, -5, 117, 39, -48, 6],
    poly [-1, -1, 1, 0, 0, 0, 0, -1, -1],
    poly [1243, 4386, 5407, 7166, 5948, 1475, 5238, 6261, 4615, 3120, 189, 1084, 2949, 2689, 28, 3052,
      508, 10502],
    poly [17736, -12107, 2921, -363, -480, -7450, 508, 10502],
    poly [-24, -83, -102, -135, -112, -28, -99, -118, -87, -59, -4, -21, -56, -51, -1, -58, -10, -198],
    poly [-334, 228, -55, 7, 9, 140, -10, -198],
    poly [6544, -1841, 2335, 7722, -1784, 2548, -311, -1],
    poly [123, -35, 44, 145, -34, 48, -6],
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
theorem certificado_16607 :
    haveI : Fact (Nat.Prime 16607) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 16607 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((16607 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((16607 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((16607 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 16607) := ⟨by norm_num⟩
  have hP : poly [-1357, 1] = X - C (1357 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((16607 : ℕ) : ℤ[X]) = poly [16607] := by simp [poly]
  refine ⟨X - C (1357 : ℤ),
    poly [8175, 4118, 5914, 4202, 101, -3757, -1300, 7195, -5563, -873, 3940, -352, -3843, 4256, 7040,
      -570, 1358, 1],
    poly [668, 336, 483, 343, 8, -307, -106, 588, -455, -71, 322, -29, -314, 348, 575, -47, 111],
    poly [1, 1, -1, 0, 0, 1, 0, 0, -1],
    poly [-3753, -12714, -10016, -12070, -10297, -6661, -4431, -195, -3900, -6693, -8543, -13770, -12856,
      -11656, -6919, -4370, -660, -5528],
    poly [20360, -3893, 2510, -9605, 2979, -3710, 4868, -5528],
    poly [307, 1039, 818, 986, 841, 544, 362, 16, 319, 547, 698, 1125, 1050, 952, 565, 357, 54, 452],
    poly [-1664, 319, -205, 785, -244, 303, -398, 452],
    poly [8175, 4118, 6171, 4141, -7609, 1928, -1357, -1],
    poly [668, 336, 504, 338, -622, 158, -111],
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
theorem certificado_16759 :
    haveI : Fact (Nat.Prime 16759) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 16759 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((16759 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((16759 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((16759 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 16759) := ⟨by norm_num⟩
  have hP : poly [-841, 1] = X - C (841 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((16759 : ℕ) : ℤ[X]) = poly [16759] := by simp [poly]
  refine ⟨X - C (841 : ℤ),
    poly [3846, -6432, 5034, -273, -2013, 3186, 1319, -7810, -7781, -2002, -5602, -2936, 136, 319, 379,
      4245, 842, 1],
    poly [193, -323, 253, -14, -101, 160, 66, -392, -390, -100, -281, -147, 7, 16, 19, 213, 42],
    poly [0, -1, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1, -1],
    poly [1339, -3442, -339, -2069, -1812, -1453, -7929, -5107, 1313, -4000, 577, -5615, -5722, 3584,
      -6827, -3372, -1415, -3246],
    poly [16759, -15420, -4781, 3103, -1730, 1596, -4422, -2034, -2350, 4999, -3581, -3372, -1415, -3246],
    poly [-67, 173, 17, 104, 91, 73, 398, 256, -66, 201, -29, 282, 287, -180, 343, 169, 71, 163],
    poly [-841, 775, 239, -156, 87, -80, 222, 102, 118, -251, 180, 169, 71, 163],
    poly [0, -3846, -6481, 5293, 5307, -2106, 5079, 3314, 4109, 523, -378, -4245, -842, -1],
    poly [0, -193, -325, 266, 266, -106, 255, 166, 206, 26, -19, -213, -42],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 30 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_16987 :
    haveI : Fact (Nat.Prime 16987) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 16987 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((16987 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((16987 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((16987 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 16987) := ⟨by norm_num⟩
  have hP : poly [-752, 1] = X - C (752 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((16987 : ℕ) : ℤ[X]) = poly [16987] := by simp [poly]
  refine ⟨X - C (752 : ℤ),
    poly [6212, -5255, 1258, 5536, -1732, -4362, -8296, 2406, -8287, -2541, -7006, 6790, 5453, 4254,
      -4851, 5686, 753, 1],
    poly [275, -233, 56, 245, -77, -193, -367, 107, -367, -112, -310, 301, 241, 188, -215, 252, 33],
    poly [1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, -1],
    poly [-1804, -6776, -3078, -8630, -3216, -724, -5871, -2241, -10052, -2992, 722, -2300, -271, -65,
      -5712, -4703, -4408, -2352],
    poly [18791, -12015, -3698, 5552, -5414, -2492, 6951, 1342, 4113, 296, -2352],
    poly [80, 300, 136, 382, 142, 32, 260, 99, 445, 132, -32, 102, 12, 3, 253, 208, 195, 104],
    poly [-832, 533, 163, -246, 240, 110, -308, -59, -182, -13, 104],
    poly [6212, 5520, 6513, 4278, -7268, -2630, 2278, -765, -4180, -751, -1],
    poly [275, 244, 288, 189, -322, -116, 101, -34, -185, -33],
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
theorem certificado_17291 :
    haveI : Fact (Nat.Prime 17291) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 17291 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((17291 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((17291 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((17291 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 17291) := ⟨by norm_num⟩
  have hP : poly [-1984, 1] = X - C (1984 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((17291 : ℕ) : ℤ[X]) = poly [17291] := by simp [poly]
  refine ⟨X - C (1984 : ℤ),
    poly [5325, 6940, 692, 3408, -4016, 1558, -8636, -2035, 243, 8175, -5103, -2652, 478, 1752, -4226,
      -4107, 1985, 1],
    poly [611, 796, 79, 391, -461, 179, -991, -233, 28, 938, -586, -304, 55, 201, -485, -471, 228],
    poly [-1, -1, -1, -1, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [-1213, 8469, -3710, 8215, 142, 3441, 3922, 1665, 2945, -401, 7319, -974, -1963, 7998, -2830,
      8076, -3196, 3143],
    poly [16078, -8822, -3710, 8215, 1355, -5028, 7632, -7763, 11272, -6339, 3143],
    poly [139, -972, 426, -943, -16, -395, -450, -191, -338, 46, -840, 112, 225, -918, 325, -927, 367,
      -361],
    poly [-1845, 1013, 425, -943, -155, 577, -876, 891, -1294, 728, -361],
    poly [-5325, -6940, -692, -3408, -7950, 5382, -7963, 118, 6092, -1984, -1],
    poly [-611, -796, -79, -391, -912, 618, -914, 14, 699, -228],
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
theorem certificado_17443 :
    haveI : Fact (Nat.Prime 17443) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 17443 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((17443 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((17443 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((17443 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 17443) := ⟨by norm_num⟩
  have hP : poly [-353, 1] = X - C (353 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((17443 : ℕ) : ℤ[X]) = poly [17443] := by simp [poly]
  refine ⟨X - C (353 : ℤ),
    poly [8005, -3881, -8016, 3288, -8391, 4967, -233, 6769, 118, 5337, 3227, -8490, -4916, -8266, -1407,
      2862, 354, 1],
    poly [162, -79, -162, 67, -170, 101, -5, 137, 2, 108, 65, -172, -99, -167, -28, 58, 7],
    poly [0, 0, -1, 0, 0, 0, 1, 0, 0, -1, 0, -1, 0, 0, 0, -1],
    poly [150, 2967, 6681, -1017, -4646, 2904, 5149, 214, -3506, -107, 1978, 4504, 311, 4944, 1597, 1884,
      6925, -621],
    poly [17443, -17443, 150, 2817, 3714, -7698, -3779, 4733, -1469, 2913, 2726, -287, -5041, 7546, -621],
    poly [-3, -60, -135, 21, 94, -59, -104, -4, 71, 2, -40, -91, -6, -100, -32, -38, -140, 13],
    poly [-353, 354, -4, -57, -75, 156, 76, -96, 30, -59, -55, 6, 102, -153, 13],
    poly [0, 0, -8005, -5557, 4135, 6139, 2241, -7801, 1065, -3703, 6858, 4269, -2508, -353, -1],
    poly [0, 0, -162, -112, 84, 124, 45, -158, 22, -75, 139, 86, -51, -7],
    monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_X_sub_C, orderOf_eq_one_iff]
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  · rw [← hP, hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)
  · rw [hc, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 32 0 (by decide +kernel)
  · rw [← hP, phi_poly, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 31 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

end ATK.FermatDezenoveCertA

#print axioms ATK.FermatDezenoveCertA.certificado_7
#print axioms ATK.FermatDezenoveCertA.certificado_11
#print axioms ATK.FermatDezenoveCertA.certificado_37
#print axioms ATK.FermatDezenoveCertA.certificado_113
#print axioms ATK.FermatDezenoveCertA.certificado_151
#print axioms ATK.FermatDezenoveCertA.certificado_191
#print axioms ATK.FermatDezenoveCertA.certificado_227
#print axioms ATK.FermatDezenoveCertA.certificado_229
#print axioms ATK.FermatDezenoveCertA.certificado_419
#print axioms ATK.FermatDezenoveCertA.certificado_457
#print axioms ATK.FermatDezenoveCertA.certificado_571
#print axioms ATK.FermatDezenoveCertA.certificado_647
#print axioms ATK.FermatDezenoveCertA.certificado_761
#print axioms ATK.FermatDezenoveCertA.certificado_1103
#print axioms ATK.FermatDezenoveCertA.certificado_1217
#print axioms ATK.FermatDezenoveCertA.certificado_1483
#print axioms ATK.FermatDezenoveCertA.certificado_1559
#print axioms ATK.FermatDezenoveCertA.certificado_1597
#print axioms ATK.FermatDezenoveCertA.certificado_1787
#print axioms ATK.FermatDezenoveCertA.certificado_1901
#print axioms ATK.FermatDezenoveCertA.certificado_2053
#print axioms ATK.FermatDezenoveCertA.certificado_2129
#print axioms ATK.FermatDezenoveCertA.certificado_2243
#print axioms ATK.FermatDezenoveCertA.certificado_2281
#print axioms ATK.FermatDezenoveCertA.certificado_2357
#print axioms ATK.FermatDezenoveCertA.certificado_2699
#print axioms ATK.FermatDezenoveCertA.certificado_2851
#print axioms ATK.FermatDezenoveCertA.certificado_2927
#print axioms ATK.FermatDezenoveCertA.certificado_3041
#print axioms ATK.FermatDezenoveCertA.certificado_3079
#print axioms ATK.FermatDezenoveCertA.certificado_3307
#print axioms ATK.FermatDezenoveCertA.certificado_3877
#print axioms ATK.FermatDezenoveCertA.certificado_4219
#print axioms ATK.FermatDezenoveCertA.certificado_4409
#print axioms ATK.FermatDezenoveCertA.certificado_4447
#print axioms ATK.FermatDezenoveCertA.certificado_4523
#print axioms ATK.FermatDezenoveCertA.certificado_4561
#print axioms ATK.FermatDezenoveCertA.certificado_4637
#print axioms ATK.FermatDezenoveCertA.certificado_4751
#print axioms ATK.FermatDezenoveCertA.certificado_4789
#print axioms ATK.FermatDezenoveCertA.certificado_4903
#print axioms ATK.FermatDezenoveCertA.certificado_5701
#print axioms ATK.FermatDezenoveCertA.certificado_6043
#print axioms ATK.FermatDezenoveCertA.certificado_6271
#print axioms ATK.FermatDezenoveCertA.certificado_6689
#print axioms ATK.FermatDezenoveCertA.certificado_6803
#print axioms ATK.FermatDezenoveCertA.certificado_6841
#print axioms ATK.FermatDezenoveCertA.certificado_6917
#print axioms ATK.FermatDezenoveCertA.certificado_7069
#print axioms ATK.FermatDezenoveCertA.certificado_7297
#print axioms ATK.FermatDezenoveCertA.certificado_7411
#print axioms ATK.FermatDezenoveCertA.certificado_7487
#print axioms ATK.FermatDezenoveCertA.certificado_7639
#print axioms ATK.FermatDezenoveCertA.certificado_7753
#print axioms ATK.FermatDezenoveCertA.certificado_7829
#print axioms ATK.FermatDezenoveCertA.certificado_7867
#print axioms ATK.FermatDezenoveCertA.certificado_8171
#print axioms ATK.FermatDezenoveCertA.certificado_8209
#print axioms ATK.FermatDezenoveCertA.certificado_8513
#print axioms ATK.FermatDezenoveCertA.certificado_8627
#print axioms ATK.FermatDezenoveCertA.certificado_8741
#print axioms ATK.FermatDezenoveCertA.certificado_8779
#print axioms ATK.FermatDezenoveCertA.certificado_8893
#print axioms ATK.FermatDezenoveCertA.certificado_8969
#print axioms ATK.FermatDezenoveCertA.certificado_9007
#print axioms ATK.FermatDezenoveCertA.certificado_9311
#print axioms ATK.FermatDezenoveCertA.certificado_9349
#print axioms ATK.FermatDezenoveCertA.certificado_9463
#print axioms ATK.FermatDezenoveCertA.certificado_9539
#print axioms ATK.FermatDezenoveCertA.certificado_9767
#print axioms ATK.FermatDezenoveCertA.certificado_10223
#print axioms ATK.FermatDezenoveCertA.certificado_10337
#print axioms ATK.FermatDezenoveCertA.certificado_10831
#print axioms ATK.FermatDezenoveCertA.certificado_11059
#print axioms ATK.FermatDezenoveCertA.certificado_11173
#print axioms ATK.FermatDezenoveCertA.certificado_11287
#print axioms ATK.FermatDezenoveCertA.certificado_11743
#print axioms ATK.FermatDezenoveCertA.certificado_11933
#print axioms ATK.FermatDezenoveCertA.certificado_11971
#print axioms ATK.FermatDezenoveCertA.certificado_12161
#print axioms ATK.FermatDezenoveCertA.certificado_12503
#print axioms ATK.FermatDezenoveCertA.certificado_12541
#print axioms ATK.FermatDezenoveCertA.certificado_12959
#print axioms ATK.FermatDezenoveCertA.certificado_13187
#print axioms ATK.FermatDezenoveCertA.certificado_13339
#print axioms ATK.FermatDezenoveCertA.certificado_13567
#print axioms ATK.FermatDezenoveCertA.certificado_13681
#print axioms ATK.FermatDezenoveCertA.certificado_13757
#print axioms ATK.FermatDezenoveCertA.certificado_14251
#print axioms ATK.FermatDezenoveCertA.certificado_14327
#print axioms ATK.FermatDezenoveCertA.certificado_14479
#print axioms ATK.FermatDezenoveCertA.certificado_14593
#print axioms ATK.FermatDezenoveCertA.certificado_14669
#print axioms ATK.FermatDezenoveCertA.certificado_14783
#print axioms ATK.FermatDezenoveCertA.certificado_14821
#print axioms ATK.FermatDezenoveCertA.certificado_14897
#print axioms ATK.FermatDezenoveCertA.certificado_15277
#print axioms ATK.FermatDezenoveCertA.certificado_15391
#print axioms ATK.FermatDezenoveCertA.certificado_15467
#print axioms ATK.FermatDezenoveCertA.certificado_15581
#print axioms ATK.FermatDezenoveCertA.certificado_15619
#print axioms ATK.FermatDezenoveCertA.certificado_15733
#print axioms ATK.FermatDezenoveCertA.certificado_15809
#print axioms ATK.FermatDezenoveCertA.certificado_15923
#print axioms ATK.FermatDezenoveCertA.certificado_16189
#print axioms ATK.FermatDezenoveCertA.certificado_16417
#print axioms ATK.FermatDezenoveCertA.certificado_16493
#print axioms ATK.FermatDezenoveCertA.certificado_16607
#print axioms ATK.FermatDezenoveCertA.certificado_16759
#print axioms ATK.FermatDezenoveCertA.certificado_16987
#print axioms ATK.FermatDezenoveCertA.certificado_17291
#print axioms ATK.FermatDezenoveCertA.certificado_17443
