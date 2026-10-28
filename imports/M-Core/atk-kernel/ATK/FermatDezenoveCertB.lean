import ATK.FermatDezenoveBase

/-!
# ATK — Certificados para `𝓞(ℚ(ζ₁₉))` principal (parte B)

Primos 17519 a 39103 da lista de `ATK.FermatDezenove`: para cada um, um gerador do ideal
primo e as identidades polinomiais do critério `pid6`, conferidas por reflexão (`ATK.PolyLista`).
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista
  ATK.FermatDezenoveBase

namespace ATK.FermatDezenoveCertB

set_option maxHeartbeats 4000000 in
theorem certificado_17519 :
    haveI : Fact (Nat.Prime 17519) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 17519 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((17519 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((17519 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((17519 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 17519) := ⟨by norm_num⟩
  have hP : poly [-968, 1] = X - C (968 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((17519 : ℕ) : ℤ[X]) = poly [17519] := by simp [poly]
  refine ⟨X - C (968 : ℤ),
    poly [-6823, 5350, 4150, -2077, -5323, 8754, -552, -6534, -2450, 7472, -5657, 7342, 822, -4397, 2493,
      -8033, 969, 1],
    poly [-377, 296, 229, -115, -294, 484, -31, -361, -135, 413, -313, 406, 45, -243, 138, -444, 54],
    poly [-1, -1, -1, 0, 0, 0, 0, -1, 0, -1, -1],
    poly [1215, 4673, 514, 4437, 2034, 4149, -862, 6173, 3918, -265, -2423, 7022, -2144, 1068, 275, 3007,
      3227, -2347],
    poly [18734, -12846, 514, 3222, -2639, 3635, -5299, 5354, 3227, -2347],
    poly [-67, -258, -28, -245, -112, -229, 48, -341, -216, 15, 134, -388, 119, -59, -15, -166, -178,
      130],
    poly [-1035, 711, -29, -178, 146, -201, 293, -296, -178, 130],
    poly [6823, -5350, -4150, -4746, -6846, -4604, -1525, 8034, -969, -1],
    poly [377, -296, -229, -262, -378, -254, -84, 444, -54],
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
theorem certificado_17747 :
    haveI : Fact (Nat.Prime 17747) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 17747 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((17747 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((17747 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((17747 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 17747) := ⟨by norm_num⟩
  have hP : poly [-1564, 1] = X - C (1564 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((17747 : ℕ) : ℤ[X]) = poly [17747] := by simp [poly]
  refine ⟨X - C (1564 : ℤ),
    poly [-4641, 1336, 2032, 2214, -4980, 7520, 5077, 7447, 3477, 93, 1044, -4368, 8292, 3035, 7423,
      -1425, 1565, 1],
    poly [-409, 118, 179, 195, -439, 663, 447, 656, 306, 8, 92, -385, 731, 267, 654, -126, 138],
    poly [0, -1, -1, 0, 0, -1, 0, -1, -1, 0, 0, 0, -1, 0, -1, -1],
    poly [6535, 5847, 7299, 2171, 1850, 2837, 4778, -2517, 2664, 500, 2178, -1157, -3508, -94, -3791,
      -219, 1735, 1532],
    poly [17747, -11212, 5847, 764, -3676, 1086, -22, 10915, -4635, -1671, 328, -3994, -1751, 1735, 1532],
    poly [-576, -515, -643, -191, -163, -250, -421, 222, -235, -44, -192, 102, 309, 8, 334, 19, -153,
      -135],
    poly [-1564, 989, -516, -67, 324, -96, 2, -962, 409, 147, -29, 352, 154, -153, -135],
    poly [0, 4641, -1336, -6673, -878, -6094, 6464, -6112, -1445, 2121, -6024, -5859, 1426, -1565, -1],
    poly [0, 409, -118, -588, -77, -537, 570, -539, -127, 187, -531, -516, 126, -138],
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
theorem certificado_18013 :
    haveI : Fact (Nat.Prime 18013) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 18013 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((18013 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((18013 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((18013 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 18013) := ⟨by norm_num⟩
  have hP : poly [-171, 1] = X - C (171 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((18013 : ℕ) : ℤ[X]) = poly [18013] := by simp [poly]
  refine ⟨X - C (171 : ℤ),
    poly [-5899, -2984, 8199, -4903, 182, 4952, 6876, 8362, 1945, -6625, 1436, -1045, 8105, -1006, 3997,
      -6613, 172, 1],
    poly [-56, -28, 78, -47, 2, 47, 65, 79, 18, -63, 14, -10, 77, -10, 38, -63, 2],
    poly [-1, 0, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1],
    poly [-1896, -327, -3478, -1811, -3276, 929, 2323, -6412, 1016, -6841, -7835, 797, -1786, 95, 106,
      -7057, -3096, -18],
    poly [16117, -16444, -3151, 1667, -3361, 5774, -1757, -7068, 4067, -3979, -3078, -18],
    poly [18, 3, 33, 17, 31, -9, -22, 61, -10, 65, 74, -8, 17, -1, -1, 67, 29],
    poly [-153, 157, 29, -16, 32, -55, 17, 67, -39, 38, 29],
    poly [5899, -2915, 6830, -4911, 814, -7685, 4906, -6397, 7231, 6784, -171, -1],
    poly [56, -28, 65, -47, 8, -73, 47, -61, 69, 64, -2],
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
theorem certificado_18089 :
    haveI : Fact (Nat.Prime 18089) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 18089 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((18089 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((18089 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((18089 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 18089) := ⟨by norm_num⟩
  have hP : poly [-290, 1] = X - C (290 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((18089 : ℕ) : ℤ[X]) = poly [18089] := by simp [poly]
  refine ⟨X - C (290 : ℤ),
    poly [-8795, 5833, -7964, 6522, -8024, 3403, 1384, 7677, 2272, 3189, 510, 8672, -1779, -8115, -1026,
      -6054, 291, 1],
    poly [-141, 94, -128, 105, -129, 55, 22, 123, 36, 51, 8, 139, -29, -130, -16, -97, 5],
    poly [-1, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, -1],
    poly [52, 5167, 4249, -1867, 4599, 1253, 3986, 440, -1194, 8531, -2975, 9710, 1333, 2115, 5985, -863,
      7347, 3009],
    poly [18141, -12922, 4197, -7034, 350, 3120, -613, -813, -5232, 2976, -863, 7347, 3009],
    poly [-1, -83, -68, 30, -74, -20, -64, -7, 19, -137, 48, -156, -21, -34, -96, 14, -118, -48],
    poly [-291, 208, -68, 113, -6, -50, 10, 13, 84, -48, 14, -118, -48],
    poly [8795, -5833, -831, -689, 60, 3119, 8681, -4274, 8406, 1027, 6054, -291, -1],
    poly [141, -94, -13, -11, 1, 50, 139, -69, 135, 16, 97, -5],
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
theorem certificado_18127 :
    haveI : Fact (Nat.Prime 18127) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 18127 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((18127 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((18127 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((18127 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 18127) := ⟨by norm_num⟩
  have hP : poly [-1742, 1] = X - C (1742 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((18127 : ℕ) : ℤ[X]) = poly [18127] := by simp [poly]
  refine ⟨X - C (1742 : ℤ),
    poly [-2487, -6349, -3833, -356, 364, -3569, 3640, 4820, 2906, -7938, -3990, 7979, -7779, -7351,
      5719, -9029, 1743, 1],
    poly [-239, -610, -368, -34, 35, -343, 350, 463, 279, -763, -383, 767, -748, -706, 550, -868, 168],
    poly [-1, 0, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1],
    poly [-10369, -3351, -5886, -2235, -3825, -6469, -1996, -7623, -7928, -5129, -4784, 1262, -7746,
      -5670, -8853, -3475, -6115, -9821],
    poly [7758, -11109, -12904, 300, 2893, -11897, 3183, -5378, 2640, 3706, -9821],
    poly [997, 322, 566, 215, 368, 622, 192, 733, 762, 493, 460, -121, 745, 545, 851, 334, 588, 944],
    poly [-745, 1068, 1240, -29, -278, 1144, -306, 517, -254, -356, 944],
    poly [2487, 3862, -29, 2872, 626, 427, -5057, 3379, -7355, -1742, -1],
    poly [239, 371, -3, 276, 60, 41, -486, 325, -707, -167],
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
theorem certificado_18583 :
    haveI : Fact (Nat.Prime 18583) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 18583 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((18583 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((18583 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((18583 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 18583) := ⟨by norm_num⟩
  have hP : poly [-312, 1] = X - C (312 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((18583 : ℕ) : ℤ[X]) = poly [18583] := by simp [poly]
  refine ⟨X - C (312 : ℤ),
    poly [-2442, -663, -4767, 8085, 5982, -636, 5418, -2782, 5292, 5437, 6450, 8657, 9081, 3841, -7135,
      4742, 313, 1],
    poly [-41, -11, -80, 136, 100, -11, 91, -47, 89, 91, 108, 145, 152, 64, -120, 80, 5],
    poly [0, -1, 0, 0, 0, -1, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, -1, -1],
    poly [6717, 842, 168, 8147, -702, 2069, 4639, -475, -1087, 9632, 1983, -960, 3855, -954, -76, 6955,
      5965, 4175],
    poly [18583, -11866, -5875, -674, 7979, -2132, 3613, 2738, 3033, -1314, 6071, 2865, -2744, -4251,
      6955, 5965, 4175],
    poly [-113, -14, -3, -137, 12, -35, -78, 8, 18, -162, -33, 16, -65, 16, 1, -117, -100, -70],
    poly [-312, 200, 98, 11, -134, 36, -61, -46, -51, 22, -102, -48, 46, 71, -117, -100, -70],
    poly [0, 2442, -1779, 4104, 5731, 4545, 7281, -1287, 115, 4527, -1951, -4652, -3529, 7136, -4742,
      -313, -1],
    poly [0, 41, -30, 69, 96, 76, 122, -22, 2, 76, -33, -78, -59, 120, -80, -5],
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
theorem certificado_18773 :
    haveI : Fact (Nat.Prime 18773) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 18773 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((18773 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((18773 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((18773 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 18773) := ⟨by norm_num⟩
  have hP : poly [-2153, 1] = X - C (2153 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((18773 : ℕ) : ℤ[X]) = poly [18773] := by simp [poly]
  refine ⟨X - C (2153 : ℤ),
    poly [-8423, 6588, 8086, -8489, -4913, 3843, -3486, 8744, -4190, -7553, -5645, -4249, 2361, -2327,
      9041, 632, 2154, 1],
    poly [-966, 756, 927, -974, -563, 441, -400, 1003, -481, -866, -647, -487, 271, -267, 1037, 72, 247],
    poly [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1],
    poly [6840, 5823, 120, 3858, 6711, 8090, 2920, 9370, 8658, 69, 6064, 2579, 9396, 2380, 4016, 4662,
      1750, 10285],
    poly [18773, -18773, -6840, 1017, 5703, -3738, -2853, -8219, 6187, -747, -3026, -1104, -13197, 8535,
      -10285],
    poly [-785, -668, -14, -443, -770, -928, -335, -1075, -993, -8, -696, -296, -1078, -273, -461, -535,
      -201, -1180],
    poly [-2153, 2154, 784, -117, -654, 429, 327, 943, -710, 86, 347, 127, 1514, -979, 1180],
    poly [0, 0, -8423, -3762, 1498, 2198, 3576, 333, 7682, -5045, 8037, -8210, -1521, 2153, 1],
    poly [0, 0, -966, -431, 172, 252, 410, 38, 881, -579, 922, -942, -174, 247],
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
theorem certificado_19001 :
    haveI : Fact (Nat.Prime 19001) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 19001 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((19001 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((19001 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((19001 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 19001) := ⟨by norm_num⟩
  have hP : poly [-670, 1] = X - C (670 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((19001 : ℕ) : ℤ[X]) = poly [19001] := by simp [poly]
  refine ⟨X - C (670 : ℤ),
    poly [-3942, -488, -8537, -6025, -3242, 3767, 5791, 3979, 5451, -6231, 1749, -6747, 784, 8424, 8719,
      -6453, 671, 1],
    poly [-139, -17, -301, -212, -114, 133, 204, 140, 192, -220, 62, -238, 28, 297, 307, -228, 24],
    poly [1, 0, 0, -1, 0, -1, -1],
    poly [4424, 914, -2778, -1876, 621, 1277, 3093, -1612, -3746, 1469, -83, 255, 2581, -5810, -2391,
      3598, -6007, 76],
    poly [14577, -15491, 3692, 3522, -6007, 76],
    poly [-156, -32, 98, 66, -22, -45, -109, 57, 132, -52, 3, -9, -91, 205, 84, -127, 212, -3],
    poly [-514, 547, -131, -124, 212, -3],
    poly [-3942, 3454, -8049, 6454, -671, -1],
    poly [-139, 122, -284, 228, -24],
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
theorem certificado_19267 :
    haveI : Fact (Nat.Prime 19267) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 19267 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((19267 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((19267 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((19267 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 19267) := ⟨by norm_num⟩
  have hP : poly [-364, 1] = X - C (364 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((19267 : ℕ) : ℤ[X]) = poly [19267] := by simp [poly]
  refine ⟨X - C (364 : ℤ),
    poly [6934, -2257, -7099, 4215, 8163, -8129, -1822, 1530, -5236, -4937, 2633, -4439, -1706, 6400,
      1235, -2008, 365, 1],
    poly [131, -43, -134, 80, 154, -154, -34, 29, -99, -93, 50, -84, -32, 121, 23, -38, 7],
    poly [-1, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0, -1],
    poly [-5666, -3035, -540, 896, 4711, 5092, 2817, -2006, -6836, -1662, -3024, 254, 5662, 172, -3760,
      -2077, 3803, 855],
    poly [13601, -16636, -3171, 4067, 644, -1218, 1000, 2120, -5025, 2948, 855],
    poly [107, 57, 10, -17, -89, -96, -53, 38, 129, 31, 57, -5, -107, -3, 71, 39, -72, -16],
    poly [-257, 315, 59, -77, -12, 23, -19, -40, 95, -56, -16],
    poly [-6934, 9191, -2092, -2123, -6040, 7235, -3156, -3608, 2372, -364, -1],
    poly [-131, 174, -40, -40, -114, 137, -60, -68, 45, -7],
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
theorem certificado_19381 :
    haveI : Fact (Nat.Prime 19381) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 19381 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((19381 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((19381 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((19381 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 19381) := ⟨by norm_num⟩
  have hP : poly [-931, 1] = X - C (931 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((19381 : ℕ) : ℤ[X]) = poly [19381] := by simp [poly]
  refine ⟨X - C (931 : ℤ),
    poly [2394, 7934, 1778, 9682, 3362, -3119, 7595, -658, 7785, 9626, 1759, -2975, -7664, -3797, 2723,
      -4452, 932, 1],
    poly [115, 381, 85, 465, 161, -150, 365, -32, 374, 462, 84, -143, -368, -182, 131, -214, 45],
    poly [1, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, -1],
    poly [7952, 3006, 1939, -1955, -1980, -273, 2560, 3708, 7498, 4546, -2431, -5915, 951, -1165, 6098,
      3233, 1169, 230],
    poly [11429, -14435, 1067, 3894, 25, -1707, 5119, -6094, 3095, 2064, 939, 230],
    poly [-382, -144, -93, 94, 95, 13, -123, -178, -360, -218, 117, 284, -46, 56, -293, -155, -56, -11],
    poly [-549, 694, -52, -187, -1, 82, -246, 293, -149, -99, -45, -11],
    poly [2394, 5540, -6156, 7904, -6320, -6481, 8320, 5588, -7176, 5384, -931, -1],
    poly [115, 266, -296, 380, -304, -311, 400, 268, -345, 259, -45],
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
theorem certificado_19457 :
    haveI : Fact (Nat.Prime 19457) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 19457 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((19457 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((19457 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((19457 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 19457) := ⟨by norm_num⟩
  have hP : poly [-3556, 1] = X - C (3556 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((19457 : ℕ) : ℤ[X]) = poly [19457] := by simp [poly]
  refine ⟨X - C (3556 : ℤ),
    poly [5105, -2997, -7869, -2355, 2954, 4110, -1799, 5296, -5202, 2510, -5739, 458, 1855, -8568, 5409,
      1643, 3557, 1],
    poly [933, -548, -1438, -430, 540, 751, -329, 968, -951, 459, -1049, 84, 339, -1566, 989, 300, 650],
    poly [-1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0, -1],
    poly [-2675, -5614, -3366, 224, 1768, -267, -1630, -9121, -571, -6270, -1090, -2927, -3316, -2085,
      -1729, -9608, -4932, -2173],
    poly [16782, -22396, 2248, 915, -4070, -2726, 4475, -5032, 5120, -6849, -2759, -2173],
    poly [489, 1026, 615, -41, -323, 49, 298, 1667, 104, 1146, 199, 535, 606, 381, 316, 1756, 901, 397],
    poly [-3067, 4094, -412, -167, 744, 498, -818, 920, -936, 1252, 504, 397],
    poly [-5105, 8102, 4872, 8838, -2312, -7639, 5267, -3566, -7322, 1913, -3556, -1],
    poly [-933, 1481, 890, 1615, -423, -1396, 963, -652, -1338, 350, -650],
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
theorem certificado_19571 :
    haveI : Fact (Nat.Prime 19571) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 19571 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((19571 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((19571 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((19571 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 19571) := ⟨by norm_num⟩
  have hP : poly [-2995, 1] = X - C (2995 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((19571 : ℕ) : ℤ[X]) = poly [19571] := by simp [poly]
  refine ⟨X - C (2995 : ℤ),
    poly [6051, 8791, 5688, -6219, 2187, 2510, 5137, 812, 4960, -4566, 665, -5809, 6794, -5343, 5252,
      9503, 2996, 1],
    poly [926, 1345, 870, -952, 335, 384, 786, 124, 759, -699, 102, -889, 1040, -818, 804, 1454, 458],
    poly [1, -1, 0, -1, -1, 0, 0, -1, 0, -1, -1],
    poly [7842, -3996, -2118, 4855, 6308, 1584, -6723, 606, 713, -901, -516, -1202, 732, 1556, 6137,
      -958, -7887, -1590],
    poly [11729, 109, -13716, 2747, 1524, -3783, 12434, 632, -7887, -1590],
    poly [-1200, 612, 324, -743, -965, -242, 1029, -93, -109, 138, 79, 184, -112, -238, -939, 147, 1207,
      243],
    poly [-1795, -16, 2099, -421, -233, 579, -1903, -96, 1207, 243],
    poly [6051, -3311, -5843, 4716, -8049, -7720, -2257, -9502, -2996, -1],
    poly [926, -507, -894, 722, -1232, -1181, -345, -1454, -458],
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
theorem certificado_19609 :
    haveI : Fact (Nat.Prime 19609) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 19609 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((19609 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((19609 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((19609 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 19609) := ⟨by norm_num⟩
  have hP : poly [-25, 1] = X - C (25 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((19609 : ℕ) : ℤ[X]) = poly [19609] := by simp [poly]
  refine ⟨X - C (25 : ℤ),
    poly [-8628, 4361, 8018, 9733, 1958, 1647, 4772, 4897, 4902, 8824, 2706, 4030, -4545, -4888, -3333,
      651, 26, 1],
    poly [-11, 6, 10, 12, 2, 2, 6, 6, 6, 11, 3, 5, -6, -6, -4, 1],
    poly [1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1],
    poly [6929, 2500, 7029, 2504, 2323, 9375, 7304, 2515, -814, 3759, 6295, 3259, 6275, 7180, 11138,
      1884, 6220, 3256],
    poly [12680, -15180, -4529, -2404, 4610, -18510, 4096, -2059, 702, -9254, 4336, -2964, -3256],
    poly [-9, -3, -9, -3, -3, -12, -9, -3, 1, -5, -8, -4, -8, -9, -14, -2, -8, -4],
    poly [-16, 20, 5, 3, -6, 24, -6, 3, -1, 12, -6, 4, 4],
    poly [-8628, -6620, 3657, -6913, 5214, -5282, 9201, 368, -1554, -3984, 625, 25, 1],
    poly [-11, -8, 5, -9, 7, -7, 12, 0, -2, -5, 1],
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
theorem certificado_19913 :
    haveI : Fact (Nat.Prime 19913) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 19913 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((19913 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((19913 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((19913 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 19913) := ⟨by norm_num⟩
  have hP : poly [-1656, 1] = X - C (1656 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((19913 : ℕ) : ℤ[X]) = poly [19913] := by simp [poly]
  refine ⟨X - C (1656 : ℤ),
    poly [-8742, -5212, 8811, -6464, -3936, -7590, 9507, 4503, 8396, 9685, 7365, -2641, 2716, -1766,
      5374, -4001, 1657, 1],
    poly [-727, -433, 733, -538, -327, -631, 791, 374, 698, 805, 612, -220, 226, -147, 447, -333, 138],
    poly [1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 1],
    poly [-2246, -2560, 446, -6262, -3813, -1130, -3858, 3740, -4312, -2441, 5268, -8159, 142, 4512,
      -5995, 480, -7729, -4355],
    poly [22159, -19599, -3006, 4462, -2763, 323, -1734, -4835, 7729, 4355],
    poly [187, 213, -37, 521, 317, 94, 321, -311, 359, 203, -438, 679, -12, -375, 499, -40, 643, 362],
    poly [-1843, 1631, 249, -371, 230, -27, 144, 402, -643, -362],
    poly [-8742, 3530, -5890, -6533, -1002, 2236, 3717, -4002, 1657, 1],
    poly [-727, 294, -490, -543, -83, 186, 309, -333, 138],
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
theorem certificado_20369 :
    haveI : Fact (Nat.Prime 20369) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 20369 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((20369 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((20369 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((20369 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 20369) := ⟨by norm_num⟩
  have hP : poly [-541, 1] = X - C (541 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((20369 : ℕ) : ℤ[X]) = poly [20369] := by simp [poly]
  refine ⟨X - C (541 : ℤ),
    poly [-8622, -656, -2072, -9793, 6006, -2888, 2329, 8551, 2689, -3986, 6958, -3451, -4035, -8140,
      -128, 8057, 542, 1],
    poly [-229, -17, -55, -260, 160, -77, 62, 227, 71, -106, 185, -92, -107, -216, -3, 214, 14],
    poly [1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1],
    poly [3623, -4917, -2862, -5682, 864, -2023, -2819, -1578, 4599, -2242, 3280, -8758, 30, -2514, 531,
      -1120, 1889, -4619],
    poly [16746, -11829, -2055, -803, -1629, 5749, 6478, -2105, -531, 1120, -1889, 4619],
    poly [-96, 131, 76, 151, -23, 54, 75, 42, -122, 60, -87, 233, -1, 67, -14, 30, -50, 123],
    poly [-445, 315, 54, 21, 43, -153, -172, 56, 14, -30, 50, -123],
    poly [-8622, 7966, -1416, 4026, -5226, 9403, -4576, -8141, -128, 8057, 542, 1],
    poly [-229, 212, -38, 107, -139, 250, -122, -216, -3, 214, 14],
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
theorem certificado_20407 :
    haveI : Fact (Nat.Prime 20407) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 20407 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((20407 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((20407 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((20407 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 20407) := ⟨by norm_num⟩
  have hP : poly [-2663, 1] = X - C (2663 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((20407 : ℕ) : ℤ[X]) = poly [20407] := by simp [poly]
  refine ⟨X - C (2663 : ℤ),
    poly [728, 1326, -5471, 4251, 7864, 10103, -7736, 204, -4935, 1776, -6559, 442, 5464, 2301, -1026,
      -7403, 2664, 1],
    poly [95, 173, -714, 555, 1026, 1318, -1010, 27, -644, 232, -856, 58, 713, 300, -134, -966, 348],
    poly [-1, 0, -1, -1, -1, -1, 0, 0, 0, 0, -1, -1],
    poly [-3602, 6558, -2588, 3018, 3250, -2390, 1723, 7288, -3446, -4975, 6159, 2186, -3264, 5378, -642,
      -5587, 2741, 836],
    poly [16805, -10247, -12748, 12164, -2356, -2622, 10965, -3383, -6423, 2741, 836],
    poly [470, -856, 338, -394, -424, 312, -225, -951, 450, 649, -804, -285, 426, -702, 84, 729, -358,
      -109],
    poly [-2193, 1338, 1663, -1588, 308, 342, -1431, 442, 838, -358, -109],
    poly [-728, -598, 6069, 9359, 1858, -6490, -9704, 3690, 7404, -2664, -1],
    poly [-95, -78, 792, 1221, 242, -847, -1266, 482, 966, -348],
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
theorem certificado_20483 :
    haveI : Fact (Nat.Prime 20483) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 20483 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((20483 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((20483 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((20483 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 20483) := ⟨by norm_num⟩
  have hP : poly [-4045, 1] = X - C (4045 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((20483 : ℕ) : ℤ[X]) = poly [20483] := by simp [poly]
  refine ⟨X - C (4045 : ℤ),
    poly [-9130, -220, 10087, -6388, 4014, -5397, -1642, -7034, 5138, -5260, -295, 1276, 6406, -1315,
      8441, 154, 4046, 1],
    poly [-1803, -43, 1992, -1262, 793, -1066, -324, -1389, 1015, -1039, -58, 252, 1265, -260, 1667, 30,
      799],
    poly [-1, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, -1, -1, 0, -1, -1],
    poly [-10952, -4706, -3398, -2947, -2400, -6142, -4958, -10062, -10757, -6377, 207, -5478, -5606,
      -6715, -13283, -4899, -3950, -3889],
    poly [9531, -14237, -9644, 6697, -9097, -7997, -1667, -841, -8157, 2778, -5766, -13222, -1010, -3950,
      -3889],
    poly [2163, 929, 671, 582, 474, 1213, 979, 1987, 2124, 1259, -41, 1082, 1107, 1326, 2623, 967, 780,
      768],
    poly [-1882, 2812, 1904, -1323, 1797, 1579, 329, 166, 1611, -549, 1139, 2611, 199, 780, 768],
    poly [9130, -8910, -1177, 7565, 8904, 5623, -3761, -8422, 9452, 1881, -2577, -4396, -153, -4046, -1],
    poly [1803, -1760, -232, 1494, 1758, 1110, -743, -1663, 1867, 371, -509, -868, -30, -799],
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
theorem certificado_20521 :
    haveI : Fact (Nat.Prime 20521) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 20521 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((20521 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((20521 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((20521 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 20521) := ⟨by norm_num⟩
  have hP : poly [-2160, 1] = X - C (2160 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((20521 : ℕ) : ℤ[X]) = poly [20521] := by simp [poly]
  refine ⟨X - C (2160 : ℤ),
    poly [-10251, -5211, 8472, -8651, 110, 9225, -5544, 1375, 7468, 887, -8417, -2113, -438, -6090, 6562,
      9494, 2161, 1],
    poly [-1079, -548, 892, -911, 12, 971, -584, 145, 786, 93, -886, -222, -46, -641, 691, 999, 227],
    poly [-1, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1],
    poly [-8538, -9511, -10528, -11127, -15697, -13324, -5086, -1263, -6800, -5501, -7581, -8342, -11373,
      -13360, -4744, -4512, -6716, -6299],
    poly [11983, -21494, -9555, -1572, -5587, 1774, -4870, 5223, 1684, -4015, -13160, -6644, 1555, -4512,
      -6716, -6299],
    poly [899, 1001, 1108, 1171, 1652, 1402, 535, 133, 716, 579, 798, 878, 1197, 1406, 499, 475, 707,
      663],
    poly [-1261, 2263, 1005, 165, 588, -187, 513, -550, -177, 423, 1385, 699, -164, 475, 707, 663],
    poly [10251, -5040, -3432, -8438, -1923, 8008, -4262, -553, -5007, 6515, 9931, 8251, -6561, -9494,
      -2161, -1],
    poly [1079, -531, -361, -888, -202, 843, -449, -58, -527, 686, 1045, 868, -691, -999, -227],
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
theorem certificado_20749 :
    haveI : Fact (Nat.Prime 20749) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 20749 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((20749 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((20749 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((20749 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 20749) := ⟨by norm_num⟩
  have hP : poly [-80, 1] = X - C (80 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((20749 : ℕ) : ℤ[X]) = poly [20749] := by simp [poly]
  refine ⟨X - C (80 : ℤ),
    poly [-2853, -8854, 8967, -3519, -44, -3891, -3161, 4629, 7320, 7613, -7167, 8210, -5344, 1230, -244,
      6481, 81, 1],
    poly [-11, -34, 35, -14, 0, -15, -12, 18, 28, 29, -28, 32, -21, 5, -1, 25],
    poly [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, -1],
    poly [2843, 1063, 6228, 10183, 6342, 3441, 5739, 5249, -2538, 3330, 291, 3106, 4438, 7567, 12534,
      11818, 2472, 799],
    poly [17906, -18969, -5165, -3955, 998, 1838, -5683, -8630, 7673, 874, 799],
    poly [-11, -4, -24, -39, -24, -13, -22, -20, 10, -13, -1, -12, -17, -29, -48, -45, -9, -3],
    poly [-69, 74, 19, 15, -4, -7, 22, 33, -30, -3, -3],
    poly [-2853, -6001, -2928, 8263, 622, 8048, -8199, -7624, -6320, -79, -1],
    poly [-11, -23, -11, 32, 2, 31, -32, -29, -24],
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
theorem certificado_20939 :
    haveI : Fact (Nat.Prime 20939) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 20939 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((20939 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((20939 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((20939 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 20939) := ⟨by norm_num⟩
  have hP : poly [-1463, 1] = X - C (1463 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((20939 : ℕ) : ℤ[X]) = poly [20939] := by simp [poly]
  refine ⟨X - C (1463 : ℤ),
    poly [-7056, -1250, 9202, -9583, 8266, 2725, -1458, 7284, 4542, 4626, -9901, 4931, 6401, -7023, 1269,
      6055, 1464, 1],
    poly [-493, -87, 643, -670, 578, 190, -102, 509, 317, 323, -692, 345, 447, -491, 89, 423, 102],
    poly [0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, -1],
    poly [9576, 7679, 2468, 2536, 747, 3780, 4970, 5071, 5801, 5687, -3015, 9760, 7765, 2053, 5756, 2252,
      6987, -1497],
    poly [20939, -20939, 9576, -1897, -5211, 68, -1789, -6543, -6489, 7209, -3703, 3504, -4735, 8484,
      -1497],
    poly [-669, -536, -172, -177, -52, -264, -347, -354, -405, -397, 211, -682, -542, -143, -402, -157,
      -488, 105],
    poly [-1463, 1464, -670, 133, 364, -5, 125, 457, 453, -504, 259, -245, 331, -593, 105],
    poly [0, 0, 7056, -5806, -10452, -2154, 3090, -1515, 2933, 7516, 8292, 4786, -4591, -1463, -1],
    poly [0, 0, 493, -406, -730, -150, 216, -106, 205, 525, 579, 334, -321, -102],
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
theorem certificado_21319 :
    haveI : Fact (Nat.Prime 21319) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 21319 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((21319 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((21319 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((21319 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 21319) := ⟨by norm_num⟩
  have hP : poly [-716, 1] = X - C (716 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((21319 : ℕ) : ℤ[X]) = poly [21319] := by simp [poly]
  refine ⟨X - C (716 : ℤ),
    poly [-5032, 916, -624, 10212, 2962, -2229, -7566, -1410, -925, 9229, 2514, 3249, -7737, -9122,
      -7129, 1717, 717, 1],
    poly [-169, 31, -21, 343, 99, -75, -254, -47, -31, 310, 84, 109, -260, -306, -239, 58, 24],
    poly [0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, -1],
    poly [-2282, 5635, -1232, 2123, -165, -1121, 6381, 496, -733, -2551, -4876, -145, -7076, -5984,
      -11342, -4263, -6784, -7651],
    poly [21319, -21319, -2282, 5635, 1050, -5794, 6702, -2194, 3034, 402, -2441, -5650, 8746, -13863,
      -5130, 867, -7651],
    poly [77, -189, 42, -71, 6, 38, -214, -16, 25, 86, 164, 5, 238, 201, 381, 143, 228, 257],
    poly [-716, 717, 76, -189, -35, 195, -225, 74, -102, -13, 82, 190, -294, 466, 172, -29, 257],
    poly [0, 0, 5032, -916, -4408, -4264, -4502, 8033, 1232, 627, -148, 6461, 277, 8129, -1001, -716, -1],
    poly [0, 0, 169, -31, -148, -143, -151, 270, 41, 21, -5, 217, 9, 273, -34, -24],
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
theorem certificado_21433 :
    haveI : Fact (Nat.Prime 21433) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 21433 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((21433 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((21433 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((21433 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 21433) := ⟨by norm_num⟩
  have hP : poly [-94, 1] = X - C (94 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((21433 : ℕ) : ℤ[X]) = poly [21433] := by simp [poly]
  refine ⟨X - C (94 : ℤ),
    poly [228, -8890, -8987, -8304, 7436, -1973, -21, 5016, -7471, 10409, 6039, -4952, -6665, -1895,
      3628, 8931, 95, 1],
    poly [1, -39, -39, -36, 33, -9, 0, 22, -33, 46, 26, -22, -29, -8, 16, 39],
    poly [1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, -1],
    poly [-158, -7000, -11633, -5526, -4777, -4085, -11830, -3476, -651, -1761, -5877, -10481, -10986,
      -3011, 494, -5625, -3638, -6581],
    poly [21591, -14591, 4633, -5949, 6093, 4099, 8480, -4470, -9624, 8106, -4930, 9524, -6581],
    poly [1, 31, 51, 24, 21, 18, 52, 15, 3, 8, 26, 46, 48, 13, -2, 25, 16, 29],
    poly [-95, 65, -21, 26, -27, -18, -37, 20, 42, -36, 22, -42, 29],
    poly [228, -9118, -97, 911, 6622, -9278, -6483, -753, 220, -7294, -8742, -93, -1],
    poly [1, -40, 0, 4, 29, -41, -28, -3, 1, -32, -38],
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
theorem certificado_21661 :
    haveI : Fact (Nat.Prime 21661) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 21661 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((21661 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((21661 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((21661 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 21661) := ⟨by norm_num⟩
  have hP : poly [-4942, 1] = X - C (4942 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((21661 : ℕ) : ℤ[X]) = poly [21661] := by simp [poly]
  refine ⟨X - C (4942 : ℤ),
    poly [5790, -8743, 6003, -7336, 4009, -7389, 7625, 2158, 9367, 10004, 4144, -9243, -1571, 4260,
      -9392, -5301, 4943, 1],
    poly [1321, -1995, 1370, -1674, 915, -1686, 1740, 492, 2137, 2282, 945, -2109, -358, 972, -2143,
      -1209, 1128],
    poly [1, 1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, 1],
    poly [-1121, -8831, -11252, -8329, -15258, -12520, -9688, -9591, -8035, -6299, -7035, -12812, -8566,
      -7671, -12742, -2307, -8428, -5234],
    poly [22782, -12830, 10131, -1623, -2583, 9480, 895, -5071, 10435, -6121, 3194, 5234],
    poly [256, 2015, 2567, 1900, 3481, 2856, 2210, 2188, 1833, 1437, 1605, 2923, 1954, 1750, 2907, 526,
      1923, 1194],
    poly [-5198, 2928, -2312, 371, 589, -2163, -204, 1157, -2381, 1397, -729, -1194],
    poly [5790, -8743, 213, -4383, -3332, -7671, -5831, -8009, -4091, -10244, 4942, 1],
    poly [1321, -1995, 49, -1000, -760, -1750, -1330, -1827, -933, -2337, 1128],
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
theorem certificado_21737 :
    haveI : Fact (Nat.Prime 21737) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 21737 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((21737 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((21737 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((21737 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 21737) := ⟨by norm_num⟩
  have hP : poly [-616, 1] = X - C (616 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((21737 : ℕ) : ℤ[X]) = poly [21737] := by simp [poly]
  refine ⟨X - C (616 : ℤ),
    poly [-3070, 5888, 9643, -4854, 6732, -7717, -930, -10623, -10180, 2136, -10124, 160, 9916, 7250,
      -4258, 10544, 617, 1],
    poly [-87, 167, 273, -138, 191, -219, -26, -301, -288, 61, -287, 5, 281, 205, -121, 299, 17],
    poly [-1, 0, 0, 0, -1, 0, 0, 1, -1, -1],
    poly [-2216, -1655, 3392, -799, 1135, 4314, 3931, 1919, -1613, 1910, -7506, -4416, 4552, -4467, 141,
      -4086, -3987, -4375],
    poly [19521, -21176, 5047, -4191, -282, 3740, 4664, -3987, -4375],
    poly [63, 47, -96, 23, -32, -122, -111, -54, 46, -54, 213, 125, -129, 127, -4, 116, 113, 124],
    poly [-553, 601, -144, 119, 8, -106, -132, 113, 124],
    poly [3070, -8958, -3755, -7240, -8516, 5491, -10542, -617, -1],
    poly [87, -254, -106, -205, -241, 156, -299, -17],
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
theorem certificado_21851 :
    haveI : Fact (Nat.Prime 21851) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 21851 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((21851 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((21851 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((21851 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 21851) := ⟨by norm_num⟩
  have hP : poly [-4164, 1] = X - C (4164 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((21851 : ℕ) : ℤ[X]) = poly [21851] := by simp [poly]
  refine ⟨X - C (4164 : ℤ),
    poly [-4917, 7251, 9269, -10430, -4930, 8883, -7355, -6047, 1195, -7021, -2594, 1369, -3652, -279,
      -147, -6633, 4165, 1],
    poly [-937, 1382, 1766, -1988, -939, 1693, -1402, -1152, 228, -1338, -494, 261, -696, -53, -28,
      -1264, 794],
    poly [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    poly [-603, 6182, 1550, -5252, 3195, -1657, 2351, 85, 2173, -1101, 4828, 8487, -5434, 4192, 5968,
      -1840, -1569, -1973],
    poly [22454, -28636, 4632, 6802, -8447, 5455, -10190, 113, 9949, -4553, -11677, 9222, 3749, -7808,
      271, -404, 1973],
    poly [115, -1178, -295, 1001, -609, 316, -448, -16, -414, 210, -920, -1617, 1036, -799, -1137, 351,
      299, 376],
    poly [-4279, 5458, -884, -1296, 1610, -1040, 1942, -22, -1896, 868, 2225, -1758, -714, 1488, -52, 77,
      -376],
    poly [-4917, -9683, 2018, 2152, 5500, 8896, -8987, -6357, 6495, 6687, -5776, 791, -131, 6486, -10798,
      4164, 1],
    poly [-937, -1845, 385, 410, 1048, 1695, -1713, -1211, 1238, 1274, -1101, 151, -25, 1236, -2058, 794],
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
theorem certificado_22003 :
    haveI : Fact (Nat.Prime 22003) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 22003 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((22003 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((22003 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((22003 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 22003) := ⟨by norm_num⟩
  have hP : poly [-928, 1] = X - C (928 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((22003 : ℕ) : ℤ[X]) = poly [22003] := by simp [poly]
  refine ⟨X - C (928 : ℤ),
    poly [-1636, 6234, 9799, -10659, 8619, -4875, 9953, -748, 6804, -3810, -7947, 845, -5405, 990,
      -10218, 3996, 929, 1],
    poly [-69, 263, 413, -450, 364, -206, 420, -32, 287, -161, -335, 36, -228, 42, -431, 169, 39],
    poly [1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1],
    poly [9382, 240, 5968, 3698, 8485, 6949, 2395, 11068, 8161, 4957, -73, -31, 2672, 2177, 6468, 7587,
      12022, 6692],
    poly [12621, -12861, -15110, 2030, -1373, -1922, -7345, -2782, 3269, 1355, -5523, -1777, 9845, 224,
      -7587, -12022, -6692],
    poly [-396, -10, -252, -156, -358, -293, -101, -467, -344, -209, 3, 1, -113, -92, -273, -320, -507,
      -282],
    poly [-532, 543, 637, -86, 58, 81, 310, 117, -138, -57, 233, 75, -415, -9, 320, 507, 282],
    poly [-1636, 7870, 1929, 7779, 8710, -8384, -9991, 2953, -9552, -4942, -10011, -9400, 61, -10219,
      3996, 929, 1],
    poly [-69, 332, 81, 328, 367, -354, -421, 125, -403, -208, -422, -396, 3, -431, 169, 39],
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
theorem certificado_22079 :
    haveI : Fact (Nat.Prime 22079) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 22079 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((22079 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((22079 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((22079 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 22079) := ⟨by norm_num⟩
  have hP : poly [-2127, 1] = X - C (2127 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((22079 : ℕ) : ℤ[X]) = poly [22079] := by simp [poly]
  refine ⟨X - C (2127 : ℤ),
    poly [-6550, -9553, -6814, 5488, -4762, -23, -2647, 9694, -10054, 1407, 2357, -1421, 3238, 6510,
      -599, 62, 2128, 1],
    poly [-631, -920, -656, 529, -459, -2, -255, 934, -969, 136, 227, -137, 312, 627, -58, 6, 205],
    poly [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1],
    poly [16087, 2870, 3279, 10670, 2473, 8251, 10745, 7985, 12686, 4031, 12653, 8671, 1870, 10742,
      10414, 3677, 12248, 5401],
    poly [5992, -8862, -409, -7391, -7890, -8648, 10314, -5040, -3895, -5013, -3677, -12248, -5401],
    poly [-1550, -276, -316, -1028, -238, -795, -1035, -769, -1222, -388, -1219, -835, -180, -1035,
      -1003, -354, -1180, -520],
    poly [-577, 854, 39, 712, 760, 833, -994, 486, 375, 483, 354, 1180, 520],
    poly [-6550, -3003, 2739, -9777, 5279, -4814, -2888, 5303, 4383, -600, 62, 2128, 1],
    poly [-631, -289, 264, -942, 509, -464, -278, 511, 422, -58, 6, 205],
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
theorem certificado_22193 :
    haveI : Fact (Nat.Prime 22193) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 22193 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((22193 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((22193 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((22193 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 22193) := ⟨by norm_num⟩
  have hP : poly [-2668, 1] = X - C (2668 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((22193 : ℕ) : ℤ[X]) = poly [22193] := by simp [poly]
  refine ⟨X - C (2668 : ℤ),
    poly [-11005, 8364, 444, -7245, -2781, 10430, -11051, -9620, 3698, 5716, -1387, -6156, -2556, 939,
      2945, -3060, 2669, 1],
    poly [-1323, 1006, 53, -871, -334, 1254, -1329, -1156, 445, 687, -167, -740, -307, 113, 354, -368,
      321],
    poly [-1, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1],
    poly [-8605, -9099, -8284, -5181, -11693, -15056, -6947, -5455, -8815, -12077, -2113, -3906, -6294,
      -9722, -6762, -11286, -19007, -11615],
    poly [13588, -14082, 1309, -6317, -10109, 3964, 14575, -4524, -7721, 7392, 11615],
    poly [1035, 1094, 996, 623, 1406, 1810, 835, 656, 1060, 1452, 254, 470, 757, 1169, 813, 1357, 2285,
      1396],
    poly [-1633, 1693, -158, 760, 1215, -477, -1752, 544, 928, -889, -1396],
    poly [11005, -8181, 5096, 10774, -9329, -827, -2005, 6005, -5729, 2668, 1],
    poly [1323, -984, 613, 1295, -1122, -99, -241, 722, -689, 321],
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
theorem certificado_22307 :
    haveI : Fact (Nat.Prime 22307) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 22307 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((22307 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((22307 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((22307 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 22307) := ⟨by norm_num⟩
  have hP : poly [-2488, 1] = X - C (2488 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((22307 : ℕ) : ℤ[X]) = poly [22307] := by simp [poly]
  refine ⟨X - C (2488 : ℤ),
    poly [9710, -5008, 8130, -10424, -2416, 2106, -6338, 6677, 182, 4743, -3172, 3863, -1953, -9917,
      4461, -8713, 2489, 1],
    poly [1083, -559, 907, -1163, -269, 235, -707, 745, 20, 529, -354, 431, -218, -1106, 498, -972, 278],
    poly [1, 0, 0, -1, 0, 0, 1, 1, -1],
    poly [2240, 1165, -261, -6448, -3429, -6521, -8423, -10199, -8550, -3914, -3948, -8413, 4236, 4788,
      -1452, 3136, 735, 3630],
    poly [20067, -21232, 1426, 8427, -4094, 1666, -6525, 3630],
    poly [-250, -130, 29, 719, 382, 727, 939, 1137, 953, 436, 440, 938, -473, -534, 162, -350, -82, -405],
    poly [-2238, 2369, -160, -940, 457, -186, 728, -405],
    poly [9710, 7589, -9169, -5957, 419, -8616, -2487, -1],
    poly [1083, 846, -1023, -664, 47, -961, -277],
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
theorem certificado_22573 :
    haveI : Fact (Nat.Prime 22573) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 22573 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((22573 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((22573 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((22573 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 22573) := ⟨by norm_num⟩
  have hP : poly [-419, 1] = X - C (419 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((22573 : ℕ) : ℤ[X]) = poly [22573] := by simp [poly]
  refine ⟨X - C (419 : ℤ),
    poly [8943, 7833, 2443, -10715, 10803, 10154, -9673, -7727, -7022, 8603, 1098, 8784, 7671, 6537,
      -9951, -4603, 420, 1],
    poly [166, 145, 45, -199, 201, 188, -180, -143, -130, 160, 20, 163, 142, 121, -185, -85, 8],
    poly [1, 0, 0, 1, -1, 0, 0, 1, 0, 1],
    poly [4455, 4735, 6298, 1076, -2115, 2726, 4677, 5813, 4415, 1287, 7044, 11206, 13317, 5672, 1290,
      2788, 14536, 6914],
    poly [18118, -22853, -1563, 767, 7366, -6124, 4834, -7622, -6914],
    poly [-83, -88, -117, -20, 39, -51, -87, -108, -82, -24, -131, -208, -247, -105, -24, -52, -270,
      -128],
    poly [-336, 425, 28, -14, -137, 114, -90, 142, 128],
    poly [8943, -1110, -5390, -4215, -11108, -4929, -5022, 419, 1],
    poly [166, -21, -100, -78, -206, -91, -93, 8],
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
theorem certificado_22877 :
    haveI : Fact (Nat.Prime 22877) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 22877 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((22877 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((22877 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((22877 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 22877) := ⟨by norm_num⟩
  have hP : poly [-252, 1] = X - C (252 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((22877 : ℕ) : ℤ[X]) = poly [22877] := by simp [poly]
  refine ⟨X - C (252 : ℤ),
    poly [-4993, 888, -9347, -5484, -2836, -4278, 2071, -4894, -8099, 3236, 1193, 3636, 8094, 7567, 7111,
      -4874, 253, 1],
    poly [-55, 10, -103, -60, -31, -47, 23, -54, -89, 36, 13, 40, 89, 83, 78, -54, 3],
    poly [-1, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0, -1],
    poly [-3903, -378, 7534, 3571, 4917, -343, -727, 3629, -2890, 1714, -1899, 8345, 3665, -6158, -4109,
      529, 6539, -155],
    poly [18974, -19352, 4009, -4341, 12783, -5214, -3379, 11879, -8214, 2056, -6165, 6694, -155],
    poly [43, 4, -83, -39, -54, 4, 8, -40, 32, -19, 21, -92, -40, 68, 45, -6, -72, 2],
    poly [-209, 214, -45, 48, -141, 58, 37, -131, 91, -23, 68, -74, 2],
    poly [4993, -5881, -7649, -4751, 1706, -10070, 9129, 10113, 4670, 10640, 5126, -252, -1],
    poly [55, -65, -84, -52, 19, -111, 101, 111, 51, 117, 56, -3],
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
theorem certificado_23029 :
    haveI : Fact (Nat.Prime 23029) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23029 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23029 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23029 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23029 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23029) := ⟨by norm_num⟩
  have hP : poly [-507, 1] = X - C (507 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23029 : ℕ) : ℤ[X]) = poly [23029] := by simp [poly]
  refine ⟨X - C (507 : ℤ),
    poly [6995, -9434, -3289, 7579, 4648, 11183, 11423, -9289, -4288, -5232, -11275, 1295, -1133, 10354,
      6970, 4238, 508, 1],
    poly [154, -208, -72, 167, 102, 246, 251, -205, -94, -115, -248, 29, -25, 228, 153, 93, 11],
    poly [0, -1, -1, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1],
    poly [-3701, 198, -6971, 6051, -3144, -4116, 1469, -8422, 7, -6608, 56, -3928, -938, -5656, -3803,
      -211, -1612, -11971],
    poly [23029, -26730, 198, -3270, 5853, 3827, -13868, 4811, -7576, 4391, 5641, -10118, 3592, -1401,
      -10359, 11971],
    poly [82, -4, 154, -133, 70, 91, -32, 186, 0, 146, -1, 87, 21, 125, 84, 5, 36, 264],
    poly [-507, 590, -5, 72, -129, -84, 306, -106, 167, -97, -124, 223, -79, 31, 228, -264],
    poly [0, -6995, 9434, 10284, 6016, -7937, -10599, 2659, 7727, -1302, 11035, 3383, 2732, 3730, 507, 1],
    poly [0, -154, 208, 226, 132, -175, -233, 59, 170, -29, 243, 74, 60, 82, 11],
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
theorem certificado_23143 :
    haveI : Fact (Nat.Prime 23143) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23143 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23143 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23143 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23143 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23143) := ⟨by norm_num⟩
  have hP : poly [-318, 1] = X - C (318 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23143 : ℕ) : ℤ[X]) = poly [23143] := by simp [poly]
  refine ⟨X - C (318 : ℤ),
    poly [7496, 8684, -9652, -9273, -3668, 8940, -7759, 10601, -7681, 4488, -7773, -170, 8951, 2357,
      -2467, 8871, 319, 1],
    poly [103, 119, -133, -127, -50, 123, -107, 146, -106, 62, -107, -2, 123, 32, -34, 122, 4],
    poly [-1, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0, 0, 0, -1],
    poly [-8143, 3694, 3804, -10751, -2573, 946, 5542, -9290, -7590, 1003, -5156, -7577, -3873, 2543,
      -639, -8800, -893, -2542],
    poly [15000, -11306, -8033, -10861, 20125, -10926, -9924, 8702, 1782, -12504, -7309, 640, 8161,
      -7907, 1649, -2542],
    poly [112, -51, -52, 148, 35, -13, -76, 128, 104, -14, 71, 104, 53, -35, 9, 121, 12, 35],
    poly [-206, 156, 110, 149, -277, 151, 136, -120, -24, 172, 100, -9, -112, 109, -23, 35],
    poly [-7496, -1188, 10840, -9063, 11543, 5349, 3219, 8525, 10070, 250, -6913, -4825, 11338, -8552,
      -318, -1],
    poly [-103, -16, 149, -125, 159, 73, 44, 117, 138, 3, -95, -66, 156, -118, -4],
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
theorem certificado_23333 :
    haveI : Fact (Nat.Prime 23333) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23333 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23333 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23333 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23333 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23333) := ⟨by norm_num⟩
  have hP : poly [-1778, 1] = X - C (1778 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23333 : ℕ) : ℤ[X]) = poly [23333] := by simp [poly]
  refine ⟨X - C (1778 : ℤ),
    poly [-6286, 6020, -10692, 6175, 6985, -11282, 7382, 10962, -1503, -4279, -1131, 813, -5695, 11099,
      -3642, -10225, 1779, 1],
    poly [-479, 459, -815, 471, 532, -860, 563, 835, -115, -326, -86, 62, -434, 846, -278, -779, 136],
    poly [-1, -1, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, -1],
    poly [5338, 7152, 119, 6716, 12717, 5542, 6181, 9659, 9346, 1800, 3633, -631, 5482, 2349, 1363, 9945,
      10501, 5567],
    poly [28671, -16181, -5219, -436, 12598, 4164, 616, -1102, 8067, 6553, -8582, -556, 4934, 5567],
    poly [-407, -545, -9, -512, -969, -422, -471, -736, -712, -137, -277, 48, -418, -179, -104, -758,
      -800, -424],
    poly [-2185, 1234, 397, 33, -960, -317, -47, 84, -615, -499, 654, 42, -376, -424],
    poly [6286, -6020, 4406, -155, 5656, 410, -6417, 5495, -8317, 8591, -6583, -11329, -1778, -1],
    poly [479, -459, 336, -12, 431, 31, -489, 419, -634, 655, -502, -863, -135],
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
theorem certificado_23371 :
    haveI : Fact (Nat.Prime 23371) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23371 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23371 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23371 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23371 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23371) := ⟨by norm_num⟩
  have hP : poly [-957, 1] = X - C (957 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23371 : ℕ) : ℤ[X]) = poly [23371] := by simp [poly]
  refine ⟨X - C (957 : ℤ),
    poly [464, -4493, 5197, -3731, 2194, 10772, 3650, -10424, -597, -2980, 4295, -5881, -5159, 10398,
      -9782, 5338, 958, 1],
    poly [19, -184, 213, -153, 90, 441, 149, -427, -24, -122, 176, -241, -211, 426, -401, 219, 39],
    poly [1, 0, 0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 1],
    poly [-1065, 2304, 4945, -5187, -1510, -1555, -4046, 6599, -1400, -5853, 3691, -7606, -902, -3215,
      -5049, 4571, 4752, -9119],
    poly [24436, -26740, -2641, 11197, -7046, -2596, 11558, -10953, 9620, 181, -13871, 9119],
    poly [44, -94, -202, 213, 62, 64, 166, -270, 58, 240, -151, 312, 37, 132, 207, -187, -194, 374],
    poly [-1001, 1096, 107, -459, 289, 106, -473, 449, -394, -7, 568, -374],
    poly [464, -4957, 9690, -8464, 968, -5103, 6857, -3192, 8251, 4380, 957, 1],
    poly [19, -203, 397, -347, 40, -209, 281, -131, 338, 179, 39],
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
theorem certificado_23447 :
    haveI : Fact (Nat.Prime 23447) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23447 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23447 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23447 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23447 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23447) := ⟨by norm_num⟩
  have hP : poly [-188, 1] = X - C (188 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23447 : ℕ) : ℤ[X]) = poly [23447] := by simp [poly]
  refine ⟨X - C (188 : ℤ),
    poly [4864, 4391, 7257, -5449, -9757, 6184, 8389, -1452, 9845, -2442, -4877, -1772, -4624, 10327,
      -2190, -11361, 189, 1],
    poly [39, 35, 58, -44, -78, 50, 67, -12, 79, -20, -39, -14, -37, 83, -18, -91, 2],
    poly [1, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [7103, -4458, 2340, -2862, 353, 1742, -1618, -1137, 3979, -2978, 1849, -6232, 2580, 2128, -3362,
      -6135, -288, 1115],
    poly [16344, -11886, -6798, 5202, 3888, -5847, -1403, 1115],
    poly [-57, 36, -19, 23, -3, -14, 13, 9, -32, 24, -15, 50, -21, -17, 27, 49, 2, -9],
    poly [-131, 96, 54, -42, -31, 47, 11, -9],
    poly [4864, -473, 2866, 10741, -9172, 11550, -188, -1],
    poly [39, -4, 23, 86, -74, 93, -2],
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
theorem certificado_23561 :
    haveI : Fact (Nat.Prime 23561) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23561 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23561 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23561 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23561 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23561) := ⟨by norm_num⟩
  have hP : poly [-1684, 1] = X - C (1684 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23561 : ℕ) : ℤ[X]) = poly [23561] := by simp [poly]
  refine ⟨X - C (1684 : ℤ),
    poly [6282, 7433, 10078, 4693, -333, 1259, -9821, -4455, 2124, -1160, -10508, -384, -8213, 1758,
      -10926, 10221, 1685, 1],
    poly [449, 531, 720, 335, -24, 90, -702, -318, 152, -83, -751, -27, -587, 126, -781, 731, 120],
    poly [-1, -1, -1, 0, 1, 0, -1, 0, 0, 0, 0, -1],
    poly [507, -3732, 1736, 3698, 817, 4411, -1659, 8383, -2664, 7445, -398, 3277, 6707, -5799, 4519,
      3154, 1880, -5592],
    poly [24068, -27293, 1736, 3191, 4042, 6914, -10318, 1365, 1274, 7472, -5592],
    poly [-36, 267, -124, -264, -58, -315, 119, -599, 191, -532, 29, -234, -479, 415, -323, -225, -134,
      400],
    poly [-1720, 1952, -125, -228, -289, -494, 738, -98, -91, -534, 400],
    poly [-6282, -7433, -10078, 1589, -9513, 9970, 10877, -2414, -8536, -1684, -1],
    poly [-449, -531, -720, 114, -680, 713, 777, -173, -610, -120],
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
theorem certificado_23599 :
    haveI : Fact (Nat.Prime 23599) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23599 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23599 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23599 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23599 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23599) := ⟨by norm_num⟩
  have hP : poly [-229, 1] = X - C (229 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23599 : ℕ) : ℤ[X]) = poly [23599] := by simp [poly]
  refine ⟨X - C (229 : ℤ),
    poly [-1958, 10915, -11082, 10566, -10053, -4166, 6268, -694, 7932, 756, -8447, 1715, 4954, -1215,
      2571, 5473, 230, 1],
    poly [-19, 106, -108, 103, -98, -40, 61, -7, 77, 7, -82, 17, 48, -12, 25, 53, 2],
    poly [1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1],
    poly [11979, 9455, -346, -4717, 3302, 11169, 4608, -3974, -5042, 4125, 17871, 6080, -876, -4101,
      5881, 10665, 8934, -5707],
    poly [11620, -21075, 9801, -7608, -5495, 1934, 10932, -11416, -4275, -4784, 1731, 14641, -5707],
    poly [-116, -91, 4, 46, -32, -108, -44, 39, 49, -40, -173, -58, 9, 40, -57, -103, -86, 56],
    poly [-113, 205, -96, 74, 53, -19, -106, 111, 41, 46, -17, -142, 56],
    poly [-1958, -10726, 1602, -3909, -7746, 7489, 8483, -5940, 3787, 2902, -5243, -229, -1],
    poly [-19, -104, 16, -38, -75, 73, 82, -58, 37, 28, -51, -2],
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
theorem certificado_23789 :
    haveI : Fact (Nat.Prime 23789) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23789 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23789 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23789 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23789 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23789) := ⟨by norm_num⟩
  have hP : poly [-258, 1] = X - C (258 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23789 : ℕ) : ℤ[X]) = poly [23789] := by simp [poly]
  refine ⟨X - C (258 : ℤ),
    poly [-6731, 4953, 3523, -11051, -2809, -1855, -3511, 6994, -8548, 2272, -10226, 7429, -6610, 10578,
      -6690, -4544, 259, 1],
    poly [-73, 54, 38, -120, -30, -20, -38, 76, -93, 25, -111, 81, -72, 115, -73, -49, 3],
    poly [-1, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1],
    poly [-10386, -2681, -346, -7990, -4147, 4443, -7326, -7095, 1481, -9366, -12082, 263, -519, -6792,
      -4880, -5057, -6994, -8569],
    poly [13403, -16084, -8051, 61, -4208, -1735, 2114, 3512, -6994, -8569],
    poly [113, 29, 4, 87, 45, -48, 80, 77, -16, 102, 131, -3, 6, 74, 53, 55, 76, 93],
    poly [-145, 175, 87, -1, 46, 19, -23, -38, 76, 93],
    poly [6731, -11684, 8161, 2890, -81, 8667, 6949, 4545, -259, -1],
    poly [73, -127, 89, 31, -1, 94, 75, 49, -3],
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
theorem certificado_23827 :
    haveI : Fact (Nat.Prime 23827) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 23827 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((23827 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((23827 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((23827 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 23827) := ⟨by norm_num⟩
  have hP : poly [-135, 1] = X - C (135 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((23827 : ℕ) : ℤ[X]) = poly [23827] := by simp [poly]
  refine ⟨X - C (135 : ℤ),
    poly [-353, -5827, -8162, 1528, -8990, -4832, 9495, -8225, 3116, 3553, -8975, 463, -3703, 2973, 728,
      -5466, 136, 1],
    poly [-2, -33, -46, 9, -51, -27, 54, -47, 18, 20, -51, 3, -21, 17, 4, -31, 1],
    poly [1, -1, -1, 0, 1, -1, 0, -1],
    poly [3763, -2210, -13903, -19461, -27621, -25034, -17249, -9249, 3165, 1139, 771, -9998, -22962,
      -24470, -32600, -19423, -14207, -7638],
    poly [20064, -14091, 9483, -12108, -12854, -6569, -7638],
    poly [-21, 13, 79, 110, 156, 141, 97, 52, -18, -6, -4, 57, 130, 138, 184, 109, 80, 43],
    poly [-114, 81, -54, 69, 72, 37, 43],
    poly [-353, -5121, 3492, -6328, 5601, -135, -1],
    poly [-2, -29, 20, -36, 32, -1],
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
theorem certificado_24169 :
    haveI : Fact (Nat.Prime 24169) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 24169 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((24169 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((24169 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((24169 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 24169) := ⟨by norm_num⟩
  have hP : poly [-611, 1] = X - C (611 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((24169 : ℕ) : ℤ[X]) = poly [24169] := by simp [poly]
  refine ⟨X - C (611 : ℤ),
    poly [4905, -5965, -5429, -88, 1503, 4235, -6599, 10709, -3503, 2961, 6769, 11166, 2629, -8263, 3507,
      11398, 612, 1],
    poly [124, -151, -137, -2, 38, 107, -167, 271, -89, 75, 171, 282, 66, -209, 89, 288, 15],
    poly [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1],
    poly [4589, -3117, -5503, 31, -2452, -4513, 2050, 3643, -3435, 7471, -462, -1187, 2095, 439, 2335,
      7520, 883, -275],
    poly [19580, -16463, 2386, -5534, -2106, 5178, 3529, -4741, 4027, -6362, -1158, 275],
    poly [-116, 79, 139, -1, 62, 114, -52, -92, 87, -189, 12, 30, -53, -11, -59, -190, -22, 7],
    poly [-495, 417, -61, 140, 53, -131, -89, 120, -102, 161, 29, -7],
    poly [4905, -10870, 536, 5341, 6496, -3233, 3001, -984, -7280, 10787, 611, 1],
    poly [124, -275, 14, 135, 164, -82, 76, -25, -184, 273, 15],
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
theorem certificado_24359 :
    haveI : Fact (Nat.Prime 24359) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 24359 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((24359 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((24359 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((24359 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 24359) := ⟨by norm_num⟩
  have hP : poly [-321, 1] = X - C (321 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((24359 : ℕ) : ℤ[X]) = poly [24359] := by simp [poly]
  refine ⟨X - C (321 : ℤ),
    poly [1973, 6684, -7340, -9812, -4356, -2366, -6837, -3512, -11166, 11955, -5730, 4687, 10942, -4519,
      2566, 5927, 322, 1],
    poly [26, 88, -97, -129, -57, -31, -90, -46, -147, 158, -76, 62, 144, -60, 34, 78, 4],
    poly [-1, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1],
    poly [-10920, 884, -1204, 1749, -2719, -5313, -2741, -10625, 3465, -2486, -2201, -4249, -7139, -5175,
      -7066, -3050, -9943, -2376],
    poly [13439, -12555, -2088, -7967, -3584, 7122, -7483, 2405, -5980, 8784, -11583, 4517, -7567, -2376],
    poly [144, -12, 16, -23, 36, 70, 36, 140, -46, 33, 29, 56, 94, 68, 93, 40, 131, 31],
    poly [-177, 166, 27, 105, 47, -94, 99, -32, 79, -116, 153, -60, 100, 31],
    poly [-1973, -4711, -10335, 499, -12140, 7323, -5365, -11020, -12100, 1480, 3040, -5606, -321, -1],
    poly [-26, -62, -136, 7, -160, 97, -71, -145, -159, 20, 40, -74, -4],
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
theorem certificado_24473 :
    haveI : Fact (Nat.Prime 24473) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 24473 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((24473 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((24473 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((24473 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 24473) := ⟨by norm_num⟩
  have hP : poly [-4586, 1] = X - C (4586 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((24473 : ℕ) : ℤ[X]) = poly [24473] := by simp [poly]
  refine ⟨X - C (4586 : ℤ),
    poly [-9675, -6075, -1154, 9536, -12085, -56, 11404, -259, 5219, -3649, 789, -11676, -7607, 7384,
      -6162, -10797, 4587, 1],
    poly [-1813, -1138, -216, 1787, -2265, -10, 2137, -49, 978, -684, 148, -2188, -1425, 1384, -1155,
      -2023, 860],
    poly [0, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0, -1],
    poly [11278, 821, 728, 6454, -1368, -8702, 6548, 2581, -4480, 8961, 1114, -3365, 3993, 686, -8328,
      2994, 2196, -9459],
    poly [24473, -13195, 821, 728, -4824, 9089, -8609, 822, -875, 13311, -17474, 9812, 333, -8661, 11655,
      -9459],
    poly [-2113, -153, -136, -1209, 257, 1631, -1227, -483, 840, -1679, -208, 631, -748, -128, 1561,
      -561, -411, 1773],
    poly [-4586, 2474, -154, -136, 904, -1703, 1614, -154, 164, -2494, 3275, -1839, -62, 1623, -2184,
      1773],
    poly [0, 9675, 6075, 1154, 5262, -8788, 4977, -714, -6564, 10410, 10355, 1838, -9221, -9090, -4586,
      -1],
    poly [0, 1813, 1138, 216, 986, -1647, 933, -134, -1230, 1951, 1940, 344, -1728, -1703, -859],
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
theorem certificado_24967 :
    haveI : Fact (Nat.Prime 24967) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 24967 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((24967 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((24967 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((24967 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 24967) := ⟨by norm_num⟩
  have hP : poly [-874, 1] = X - C (874 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((24967 : ℕ) : ℤ[X]) = poly [24967] := by simp [poly]
  refine ⟨X - C (874 : ℤ),
    poly [-3228, -11973, -3156, -4260, 2309, 10058, 6896, 11463, -1758, -10543, -6011, -7377, 2334,
      -9110, 818, -9226, 875, 1],
    poly [-113, -419, -110, -149, 81, 352, 241, 401, -62, -369, -210, -258, 82, -319, 29, -323, 31],
    poly [1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1],
    poly [3052, -7057, -7040, -2098, -3235, -3322, -9521, 3641, -3257, 563, -2175, -2121, -2578, -4721,
      -6466, 3216, -1972, 4021],
    poly [21915, -17910, 7040, 2098, 3235, 6374, -588, -3624, 11251, -11809, 2105, 3916, 4494, 805, 1972,
      -4021],
    poly [-107, 247, 246, 73, 113, 116, 333, -128, 114, -20, 76, 74, 90, 165, 226, -113, 69, -141],
    poly [-767, 628, -247, -73, -113, -223, 21, 127, -394, 414, -74, -137, -157, -28, -69, 141],
    poly [-3228, -11973, -3156, -4260, 2309, -11681, -9326, 2646, 2574, -8367, 2390, 117, -57, -9227,
      875, 1],
    poly [-113, -419, -110, -149, 81, -409, -326, 93, 90, -293, 84, 4, -2, -323, 31],
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
theorem certificado_25309 :
    haveI : Fact (Nat.Prime 25309) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 25309 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((25309 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((25309 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((25309 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 25309) := ⟨by norm_num⟩
  have hP : poly [-3962, 1] = X - C (3962 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((25309 : ℕ) : ℤ[X]) = poly [25309] := by simp [poly]
  refine ⟨X - C (3962 : ℤ),
    poly [-12284, 8627, -6999, 11982, 2769, 12125, -12249, 8314, -4923, 2094, -3532, 5563, -10692, 898,
      9333, 9827, 3963, 1],
    poly [-1923, 1351, -1096, 1876, 433, 1898, -1918, 1302, -771, 328, -553, 871, -1674, 141, 1461, 1538,
      620],
    poly [-1, -1, 0, -1, 0, 0, 0, -1, -1],
    poly [1461, 4304, 1296, 2164, 9587, 5392, 3136, 3787, 3027, 6208, 4516, -1323, -1893, 6820, 5551,
      7499, -5583, 7279],
    poly [26770, -21005, -165, -679, 11134, 220, -5583, 7279],
    poly [-229, -674, -203, -339, -1501, -844, -491, -593, -474, -972, -707, 207, 296, -1068, -869,
      -1174, 874, -1140],
    poly [-4191, 3289, 25, 106, -1743, -34, 874, -1140],
    poly [12284, -8627, -5285, 8929, -5370, -9826, -3963, -1],
    poly [1923, -1351, -827, 1398, -841, -1538, -620],
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
theorem certificado_25423 :
    haveI : Fact (Nat.Prime 25423) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 25423 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((25423 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((25423 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((25423 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 25423) := ⟨by norm_num⟩
  have hP : poly [-3241, 1] = X - C (3241 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((25423 : ℕ) : ℤ[X]) = poly [25423] := by simp [poly]
  refine ⟨X - C (3241 : ℤ),
    poly [7350, 8725, -4594, 11506, -4852, 1081, -6024, -3116, 3827, -3262, 9161, -5896, -3265, 5788,
      -1771, 7624, 3242, 1],
    poly [937, 1112, -586, 1467, -619, 138, -768, -397, 488, -416, 1168, -752, -416, 738, -226, 972, 413],
    poly [-1, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, -1, 0, -1],
    poly [-1388, 5789, 7564, 3313, 3296, 1131, -917, 1467, -4486, -2919, -3750, 2580, 1170, -7914, -1312,
      6495, 4756, -1363],
    poly [24035, -18246, 387, 2926, 1758, -6416, -3453, 7396, -6226, -1688, 376, 6119, -1363],
    poly [177, -738, -964, -422, -420, -144, 117, -187, 572, 372, 478, -329, -149, 1009, 167, -828, -606,
      174],
    poly [-3064, 2327, -50, -373, -224, 818, 440, -943, 794, 215, -48, -780, 174],
    poly [-7350, -1375, 5969, 7948, 4254, 3390, -9310, -10216, -11942, 6154, -4383, -3241, -1],
    poly [-937, -175, 761, 1013, 542, 432, -1187, -1302, -1522, 785, -559, -413],
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
theorem certificado_25537 :
    haveI : Fact (Nat.Prime 25537) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 25537 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((25537 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((25537 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((25537 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 25537) := ⟨by norm_num⟩
  have hP : poly [-561, 1] = X - C (561 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((25537 : ℕ) : ℤ[X]) = poly [25537] := by simp [poly]
  refine ⟨X - C (561 : ℤ),
    poly [11107, -10632, -7894, -4293, -9658, 1576, -680, 4915, -7229, -10255, -7165, -6067, 5133, -2540,
      4502, 8839, 562, 1],
    poly [244, -234, -173, -94, -212, 35, -15, 108, -159, -225, -157, -133, 113, -56, 99, 194, 12],
    poly [-1, -1, -1, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0, -1],
    poly [-766, 3375, 1425, 4699, 5069, 6936, 6211, 14631, 10185, 3349, 9300, 1299, -354, -1586, -5594,
      271, 2603, -4403],
    poly [24771, -22162, 1425, 5465, 1694, 4745, 4887, 10987, 7948, 2973, -2536, 41, 4279, -3262, -6735,
      7006, -4403],
    poly [17, -74, -31, -103, -111, -152, -136, -321, -223, -73, -204, -28, 8, 35, 123, -6, -57, 97],
    poly [-544, 488, -32, -120, -37, -104, -107, -241, -174, -65, 56, -1, -94, 72, 148, -154, 97],
    poly [-11107, 10632, 7894, -10137, -974, 4960, 7019, -6679, -12439, 4803, -11235, -12174, -1797,
      3775, -8278, -561, -1],
    poly [-244, 234, 173, -223, -21, 109, 154, -147, -273, 106, -247, -267, -39, 83, -182, -12],
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
theorem certificado_25841 :
    haveI : Fact (Nat.Prime 25841) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 25841 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((25841 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((25841 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((25841 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 25841) := ⟨by norm_num⟩
  have hP : poly [-146, 1] = X - C (146 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((25841 : ℕ) : ℤ[X]) = poly [25841] := by simp [poly]
  refine ⟨X - C (146 : ℤ),
    poly [-177, -5665, 4917, -8462, 827, -8844, 10736, -12139, -3977, -6399, 4204, -5458, -10126, -9450,
      6838, -4378, 147, 1],
    poly [-1, -32, 28, -48, 5, -50, 61, -69, -22, -36, 24, -31, -57, -53, 39, -25, 1],
    poly [-1, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1, -1, -1],
    poly [-6751, 12849, -6486, 8072, 738, -5330, 5956, -12020, 10512, -6679, -248, 1035, -4443, 7909,
      -2272, 4561, -525, 3688],
    poly [19090, -12992, 265, -4777, 473, 6198, -14117, 7868, -9529, 12122, -5960, 4561, -525, 3688],
    poly [38, -73, 37, -46, -4, 30, -34, 68, -60, 38, 1, -6, 25, -45, 13, -26, 3, -21],
    poly [-108, 74, -2, 27, -3, -35, 80, -45, 54, -69, 34, -26, 3, -21],
    poly [177, 5665, -5094, 2797, 4267, 5870, 5350, -9167, 5601, 9596, -6837, 4378, -147, -1],
    poly [1, 32, -29, 16, 24, 33, 30, -52, 32, 54, -39, 25, -1],
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
theorem certificado_26107 :
    haveI : Fact (Nat.Prime 26107) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 26107 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((26107 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((26107 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((26107 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 26107) := ⟨by norm_num⟩
  have hP : poly [-1071, 1] = X - C (1071 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((26107 : ℕ) : ℤ[X]) = poly [26107] := by simp [poly]
  refine ⟨X - C (1071 : ℤ),
    poly [-4729, 5529, 8805, -6549, -12048, 11860, 3375, 4269, 2661, -4434, -9194, 11107, -7010, 871,
      -10676, -595, 1072, 1],
    poly [-194, 227, 361, -269, -494, 487, 138, 175, 109, -182, -377, 456, -288, 36, -438, -24, 44],
    poly [1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -1],
    poly [6871, -3385, 2797, -2365, -3418, 3382, -3242, 262, -7267, -1960, 6016, -95, 1435, 5166, 733,
      997, -3683, 3333],
    poly [19236, -15851, -6182, 5162, 1053, -6800, -247, 6752, 1347, -7016, 3333],
    poly [-282, 139, -115, 97, 140, -139, 133, -11, 298, 80, -247, 4, -59, -212, -30, -41, 151, -137],
    poly [-789, 651, 253, -212, -43, 279, 10, -277, -55, 288, -137],
    poly [-4729, 10258, 3276, 10753, -5499, -2199, 12893, 11152, 1668, -1071, -1],
    poly [-194, 421, 134, 441, -226, -90, 529, 457, 68, -44],
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
theorem certificado_26183 :
    haveI : Fact (Nat.Prime 26183) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 26183 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((26183 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((26183 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((26183 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 26183) := ⟨by norm_num⟩
  have hP : poly [-903, 1] = X - C (903 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((26183 : ℕ) : ℤ[X]) = poly [26183] := by simp [poly]
  refine ⟨X - C (903 : ℤ),
    poly [-6553, -8242, -850, 376, -3827, -1570, -4844, 10694, 5521, -12346, -4421, 7215, 13027, 2798,
      641, 4640, 904, 1],
    poly [-226, -284, -29, 13, -132, -54, -167, 369, 190, -426, -152, 249, 449, 96, 22, 160, 31],
    poly [1, 0, 0, 1, 0, 1, 0, -1, 0, -1],
    poly [9481, 6215, -4372, 3967, 5513, 3630, -3476, 10463, 243, 4697, -2286, 5999, -5938, 5705, 5022,
      6616, 5081, 498],
    poly [16702, -22917, 10587, -17820, 1720, 2989, 2033, 4583, 498],
    poly [-327, -214, 151, -137, -190, -125, 120, -361, -8, -162, 79, -207, 205, -197, -173, -228, -175,
      -17],
    poly [-576, 791, -366, 615, -60, -103, -70, -158, -17],
    poly [-6553, -1689, 7392, -5327, -5892, 3096, -3737, -903, -1],
    poly [-226, -58, 255, -184, -203, 107, -129, -31],
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
theorem certificado_26297 :
    haveI : Fact (Nat.Prime 26297) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 26297 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((26297 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((26297 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((26297 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 26297) := ⟨by norm_num⟩
  have hP : poly [-935, 1] = X - C (935 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((26297 : ℕ) : ℤ[X]) = poly [26297] := by simp [poly]
  refine ⟨X - C (935 : ℤ),
    poly [225, 2194, 6218, -5084, -12943, -6567, 5168, -5507, 3341, 11113, -1985, -199, -7594, -430,
      -8213, 7360, 936, 1],
    poly [8, 78, 221, -181, -460, -233, 184, -196, 119, 395, -71, -7, -270, -15, -292, 262, 33],
    poly [-1, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, -1, -1],
    poly [-10319, -2680, -12150, -11457, -9600, -6673, -7823, -12043, -9235, -9907, -16489, -8171,
      -12634, -7745, -3296, -5035, -8215, -2734],
    poly [15978, -18658, -9470, -9626, -823, 1096, -9927, -11989, 4912, -11045, -13090, -10333, 470,
      -562, -5035, -8215, -2734],
    poly [367, 95, 432, 407, 341, 237, 278, 428, 328, 352, 586, 290, 449, 275, 117, 179, 292, 97],
    poly [-568, 664, 336, 342, 29, -39, 353, 426, -175, 393, 465, 367, -17, 20, 179, 292, 97],
    poly [-225, -1969, -4024, 11077, 5665, -12369, -4457, 3314, -9559, -5804, -8950, -11344, 1366, 8214,
      -7360, -936, -1],
    poly [-8, -70, -143, 394, 201, -440, -158, 118, -340, -206, -318, -403, 49, 292, -262, -33],
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
theorem certificado_26449 :
    haveI : Fact (Nat.Prime 26449) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 26449 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((26449 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((26449 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((26449 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 26449) := ⟨by norm_num⟩
  have hP : poly [-2479, 1] = X - C (2479 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((26449 : ℕ) : ℤ[X]) = poly [26449] := by simp [poly]
  refine ⟨X - C (2479 : ℤ),
    poly [8354, -8500, 1789, 6733, -8554, 3272, -4117, -8377, 5758, -9696, -4549, 3487, -1695, -8280,
      -11110, 11753, 2480, 1],
    poly [783, -797, 168, 631, -802, 307, -386, -785, 540, -909, -426, 327, -159, -776, -1041, 1102, 232],
    poly [1, -1, -1, 1, -1, 0, 0, 0, 0, -1],
    poly [483, 12198, 6388, 9213, 1671, 6021, 7047, 5319, -123, -3486, 2178, 2383, 8998, -751, 5924,
      -2534, 10319, -7152],
    poly [25966, -37681, 18008, 2597, -6675, 8458, -12853, 17471, -7152],
    poly [-45, -1143, -598, -863, -156, -564, -660, -498, 12, 327, -204, -223, -843, 71, -555, 238, -967,
      671],
    poly [-2434, 3533, -1689, -243, 626, -793, 1205, -1638, 671],
    poly [8354, 1241, -7660, -6586, -2830, -3586, -9273, -2479, -1],
    poly [783, 116, -718, -617, -265, -336, -869, -232],
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
theorem certificado_26981 :
    haveI : Fact (Nat.Prime 26981) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 26981 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((26981 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((26981 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((26981 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 26981) := ⟨by norm_num⟩
  have hP : poly [-196, 1] = X - C (196 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((26981 : ℕ) : ℤ[X]) = poly [26981] := by simp [poly]
  refine ⟨X - C (196 : ℤ),
    poly [-10875, 8204, 8439, 869, -3850, -5113, -6909, -4165, -4151, 13194, -11083, 12608, 10664, -4213,
      13469, 11632, 197, 1],
    poly [-79, 60, 61, 6, -28, -37, -50, -30, -30, 96, -81, 92, 77, -31, 98, 84, 1],
    poly [0, -1, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 1, -1],
    poly [-3763, 3789, 1625, -4443, 1583, -2516, -6529, 7354, -697, -1977, 219, 3534, 7543, 4122, 7546,
      9766, 4271, 9061],
    poly [26981, -30744, 7552, -2164, -2305, -1526, -1935, 2055, 7857, -7715, 10285, -13851, 9061],
    poly [27, -28, -12, 32, -12, 18, 47, -54, 5, 14, -2, -26, -55, -30, -55, -71, -31, -66],
    poly [-196, 224, -56, 16, 17, 11, 14, -15, -57, 56, -75, 101, -66],
    poly [0, 10875, 7902, -235, -3305, -3183, 1498, -5774, -7463, 9598, -11239, -195, -1],
    poly [0, 79, 57, -2, -24, -23, 11, -42, -54, 70, -82, -1],
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
theorem certificado_27361 :
    haveI : Fact (Nat.Prime 27361) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 27361 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((27361 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((27361 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((27361 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 27361) := ⟨by norm_num⟩
  have hP : poly [-1106, 1] = X - C (1106 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((27361 : ℕ) : ℤ[X]) = poly [27361] := by simp [poly]
  refine ⟨X - C (1106 : ℤ),
    poly [4923, 10840, -6447, 4744, -10856, 12978, 2164, -5020, 11400, 134, 1905, 11431, 11687, 10005,
      108, -6902, 1107, 1],
    poly [199, 438, -261, 192, -439, 525, 87, -203, 461, 5, 77, 462, 472, 404, 4, -279, 45],
    poly [-1, -1, -1, 0, -1, -1, -1, -1, 0, 0, -1, -1, -1, -1],
    poly [-4299, 9625, 1078, -3259, 6212, 3623, -956, -4003, 2550, 750, -2814, 4357, -2786, 3318, -4296,
      -5144, 10688, -6120],
    poly [23062, -17736, 1078, 1040, -7712, 12170, 3381, -13474, 9438, -4296, -5144, 10688, -6120],
    poly [174, -389, -43, 132, -251, -146, 39, 162, -103, -30, 114, -176, 113, -134, 174, 208, -432, 248],
    poly [-932, 718, -44, -42, 312, -492, -136, 545, -382, 174, 208, -432, 248],
    poly [-4923, -10840, 6447, 179, -10588, -2904, 9027, -10580, -10004, -108, 6902, -1107, -1],
    poly [-199, -438, 261, 7, -428, -117, 365, -428, -404, -4, 279, -45],
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
theorem certificado_27437 :
    haveI : Fact (Nat.Prime 27437) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 27437 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((27437 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((27437 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((27437 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 27437) := ⟨by norm_num⟩
  have hP : poly [-1516, 1] = X - C (1516 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((27437 : ℕ) : ℤ[X]) = poly [27437] := by simp [poly]
  refine ⟨X - C (1516 : ℤ),
    poly [11601, 6885, 7823, -8863, -2612, -4472, 7906, -11451, 4698, -15, -6443, -8981, -5544, -12220,
      8842, -4935, 1517, 1],
    poly [641, 380, 432, -490, -144, -247, 437, -633, 260, -1, -356, -496, -306, -675, 489, -273, 84],
    poly [-1, 0, -1, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [1558, 8183, 2595, -4648, 9301, 10378, -64, 3223, 8166, 7753, -2509, -2190, 1086, -3545, -960,
      -904, 7928, -2346],
    poly [28995, -20812, -4030, -618, 8361, -6166, 5065, 12547, -2904, -3332, -4201, 7689, -2402, -8832,
      10274, -2346],
    poly [-86, -452, -143, 257, -514, -573, 4, -178, -451, -428, 139, 121, -60, 196, 53, 50, -438, 130],
    poly [-1602, 1151, 222, 34, -462, 341, -280, -693, 161, 184, 232, -425, 133, 488, -568, 130],
    poly [-11601, 4716, -12539, -6035, -7189, -8891, -2793, -13105, -8913, -10340, -224, -7891, 13659,
      6452, -1516, -1],
    poly [-641, 261, -693, -333, -397, -491, -154, -724, -492, -571, -12, -436, 755, 356, -84],
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
theorem certificado_27551 :
    haveI : Fact (Nat.Prime 27551) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 27551 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((27551 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((27551 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((27551 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 27551) := ⟨by norm_num⟩
  have hP : poly [-189, 1] = X - C (189 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((27551 : ℕ) : ℤ[X]) = poly [27551] := by simp [poly]
  refine ⟨X - C (189 : ℤ),
    poly [-3207, -11533, 11455, 7495, 8786, -11178, -7202, -12283, 3142, -10479, 2860, -5670, -3237,
      2461, 9634, 8360, 190, 1],
    poly [-22, -79, 79, 51, 60, -77, -49, -84, 22, -72, 20, -39, -22, 17, 66, 57, 1],
    poly [1, 0, -1, 1, 0, 0, 0, -1, 0, 0, -1],
    poly [-103, 188, -3309, -4931, 454, -4328, 5705, 1968, 2094, -7089, -4951, -8584, -5542, -2902, 5421,
      363, 6896, -8084],
    poly [27654, -27842, 3394, 2016, -9173, 6657, -3026, -6533, 14980, -8084],
    poly [1, -1, 23, 34, -3, 30, -39, -13, -14, 49, 34, 59, 38, 20, -37, -2, -47, 56],
    poly [-190, 192, -24, -14, 63, -46, 21, 45, -103, 56],
    poly [-3207, -8326, -1356, 1159, -2472, 6984, -1275, -8170, -189, -1],
    poly [-22, -57, -9, 8, -17, 48, -9, -56, -1],
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
theorem certificado_27779 :
    haveI : Fact (Nat.Prime 27779) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 27779 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((27779 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((27779 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((27779 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 27779) := ⟨by norm_num⟩
  have hP : poly [-2294, 1] = X - C (2294 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((27779 : ℕ) : ℤ[X]) = poly [27779] := by simp [poly]
  refine ⟨X - C (2294 : ℤ),
    poly [4759, -3437, -389, -5183, 2904, -9214, -8856, 9720, -686, -8489, 13244, 7114, 11834, -5214,
      11538, -13279, 2295, 1],
    poly [393, -284, -32, -428, 240, -761, -731, 803, -57, -701, 1094, 587, 977, -431, 953, -1097, 190],
    poly [-1, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, -1],
    poly [-8986, 3507, -3620, -4386, 1959, 1877, 3209, -2167, -2242, -6444, -10006, -3638, -2061, -6674,
      1183, 254, 4504, 1866],
    poly [18793, -15286, -7127, -766, -2641, 3425, -2288, -776, -1623, -7691, 7540, -1378, -6928, -3321,
      -1612, 4504, 1866],
    poly [742, -290, 299, 362, -162, -155, -265, 179, 185, 532, 826, 300, 170, 551, -98, -21, -372, -154],
    poly [-1552, 1263, 588, 63, 218, -283, 189, 64, 134, 635, -623, 114, 572, 274, 133, -372, -154],
    poly [-4759, 8196, -3048, 4794, -12846, -12224, 31, -8634, 4065, 11869, 13156, -297, -8065, -9243,
      13280, -2295, -1],
    poly [-393, 677, -252, 396, -1061, -1009, 3, -713, 336, 980, 1086, -25, -666, -763, 1097, -190],
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
theorem certificado_27817 :
    haveI : Fact (Nat.Prime 27817) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 27817 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((27817 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((27817 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((27817 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 27817) := ⟨by norm_num⟩
  have hP : poly [-222, 1] = X - C (222 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((27817 : ℕ) : ℤ[X]) = poly [27817] := by simp [poly]
  refine ⟨X - C (222 : ℤ),
    poly [-6641, 8240, -840, 6136, -9370, -6182, -3411, 11763, 1306, -12399, -10080, 7598, -8361, -9310,
      2840, -6127, 223, 1],
    poly [-53, 66, -7, 49, -75, -49, -27, 94, 10, -99, -80, 61, -67, -74, 23, -49, 2],
    poly [-1, -1, -1, 0, -1, 0, 0, -1, -1, 0, -1],
    poly [-5518, 12250, 9824, 4801, -359, 2625, 13665, 4693, 5655, -3613, 6620, 7042, 27, 6887, -99,
      4631, 11168, 1048],
    poly [22299, -15567, 9824, 10319, -18127, 10569, 6438, -5489, 10120, 1048],
    poly [44, -98, -78, -38, 3, -21, -109, -37, -45, 29, -53, -56, 0, -55, 1, -37, -89, -8],
    poly [-178, 125, -79, -82, 145, -85, -51, 44, -81, -8],
    poly [6641, -8240, 840, -12777, -3566, -9539, -9190, 6349, -222, -1],
    poly [53, -66, 7, -102, -28, -76, -73, 51, -2],
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
theorem certificado_27893 :
    haveI : Fact (Nat.Prime 27893) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 27893 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((27893 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((27893 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((27893 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 27893) := ⟨by norm_num⟩
  have hP : poly [-2591, 1] = X - C (2591 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((27893 : ℕ) : ℤ[X]) = poly [27893] := by simp [poly]
  refine ⟨X - C (2591 : ℤ),
    poly [-2982, 2561, -8762, 4475, 8614, -5487, 7975, 13632, 7541, 2522, -13488, -2492, 13305, 8682,
      2038, -6340, 2592, 1],
    poly [-277, 238, -814, 416, 800, -510, 741, 1266, 700, 234, -1253, -231, 1236, 806, 189, -589, 241],
    poly [1, 0, 1, 1, 1, 0, 0, 0, 0, 0, -1],
    poly [9556, -1098, -1199, 4442, 6425, 6415, 4488, 4132, 2474, -4621, 8876, 7331, 2486, 3270, -1854,
      3742, 11000, 9388],
    poly [18337, -17239, -9455, -4543, -784, 5124, -5596, -7258, 1612, 9388],
    poly [-888, 102, 111, -413, -597, -596, -417, -384, -230, 429, -825, -681, -231, -304, 172, -348,
      -1022, -872],
    poly [-1703, 1602, 878, 422, 73, -476, 520, 674, -150, -872],
    poly [-2982, 5543, 13588, -12095, -4623, -6644, -8378, 8932, -2591, -1],
    poly [-277, 515, 1262, -1124, -429, -617, -778, 830, -241],
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
theorem certificado_28349 :
    haveI : Fact (Nat.Prime 28349) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 28349 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((28349 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((28349 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((28349 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 28349) := ⟨by norm_num⟩
  have hP : poly [-1801, 1] = X - C (1801 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((28349 : ℕ) : ℤ[X]) = poly [28349] := by simp [poly]
  refine ⟨X - C (1801 : ℤ),
    poly [13962, 4242, 8219, -11313, 5440, 7653, 10157, 3626, -9285, 11155, -11091, -4083, 10969, 6082,
      2333, 13617, 1802, 1],
    poly [887, 269, 522, -719, 346, 486, 645, 230, -590, 709, -705, -259, 697, 386, 148, 865, 114],
    poly [-1, -1, 0, -1, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [7957, 12054, 18022, 10517, 17423, 10800, 6688, 11707, 15157, 11208, 8341, 8607, 8434, 14195,
      5226, 12871, 7366, 14037],
    poly [36306, -16295, 10065, 6420, 3498, 14208, -14143, 13781, 2298, 6392, 5505, -6671, 14037],
    poly [-506, -766, -1145, -668, -1107, -686, -425, -744, -963, -712, -530, -547, -536, -902, -332,
      -818, -468, -892],
    poly [-2307, 1036, -640, -408, -222, -903, 899, -876, -146, -406, -350, 424, -892],
    poly [-13962, -4242, 5743, 1593, 12499, -8556, -3814, 11646, -5550, 11283, -11815, -1801, -1],
    poly [-887, -269, 365, 101, 794, -544, -242, 740, -353, 717, -751, -114],
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
theorem certificado_28387 :
    haveI : Fact (Nat.Prime 28387) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 28387 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((28387 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((28387 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((28387 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 28387) := ⟨by norm_num⟩
  have hP : poly [-406, 1] = X - C (406 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((28387 : ℕ) : ℤ[X]) = poly [28387] := by simp [poly]
  refine ⟨X - C (406 : ℤ),
    poly [8600, -3265, 12857, 5765, -6698, 14177, 8565, 13865, -5000, 2295, 565, 3777, 1128, -12233,
      10178, -5079, 407, 1],
    poly [123, -47, 184, 82, -96, 203, 122, 198, -72, 33, 8, 54, 16, -175, 146, -73, 6],
    poly [-1, -1, 0, 0, 1, -1, 0, 0, -1, 0, -1],
    poly [12989, 10434, 11896, 14137, 16310, 7156, 14405, 10857, 7632, 8533, 9584, -1950, 6272, 9089,
      -3000, 9206, 12732, 6448],
    poly [41376, -17953, -1093, 3703, -8575, 8563, -5922, 2922, 6284, 6448],
    poly [-186, -149, -170, -202, -233, -102, -206, -155, -109, -122, -137, 28, -90, -130, 43, -132,
      -182, -92],
    poly [-592, 258, 15, -53, 123, -123, 85, -42, -90, -92],
    poly [-8600, 3265, -4257, -9030, -232, -490, 12724, 5485, -406, -1],
    poly [-123, 47, -61, -129, -3, -7, 182, 78, -6],
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
theorem certificado_28463 :
    haveI : Fact (Nat.Prime 28463) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 28463 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((28463 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((28463 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((28463 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 28463) := ⟨by norm_num⟩
  have hP : poly [-363, 1] = X - C (363 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((28463 : ℕ) : ℤ[X]) = poly [28463] := by simp [poly]
  refine ⟨X - C (363 : ℤ),
    poly [10507, -7028, -7782, 1782, -12776, -12032, -1915, 8071, -213, -79, -13330, 2394, -10422,
      -11163, 4125, -10182, 364, 1],
    poly [134, -90, -99, 23, -163, -153, -24, 103, -3, -1, -170, 31, -133, -142, 53, -130, 5],
    poly [0, -1, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1],
    poly [-702, 3295, -10259, 1230, -2110, -3609, 6345, -7271, 1003, -7913, 766, 5965, 569, -1955, -9803,
      -8178, -4253, -1341],
    poly [28463, -29165, 3295, -9557, -2767, 11444, -15098, 10387, -9067, 1308, 3771, -1401, 4936, -2966,
      -3925, -2912, -1341],
    poly [9, -42, 131, -16, 27, 46, -81, 93, -13, 101, -10, -76, -7, 25, 125, 104, 54, 17],
    poly [-363, 373, -43, 122, 35, -146, 193, -133, 116, -17, -48, 18, -63, 38, 50, 37, 17],
    poly [0, -10507, 7028, -10174, 9146, 12022, -6867, -2136, 14108, 2548, 1340, 9805, -13538, 14155,
      10546, -363, -1],
    poly [0, -134, 90, -130, 117, 153, -88, -27, 180, 32, 17, 125, -173, 181, 134, -5],
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
theorem certificado_28729 :
    haveI : Fact (Nat.Prime 28729) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 28729 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((28729 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((28729 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((28729 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 28729) := ⟨by norm_num⟩
  have hP : poly [-3932, 1] = X - C (3932 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((28729 : ℕ) : ℤ[X]) = poly [28729] := by simp [poly]
  refine ⟨X - C (3932 : ℤ),
    poly [-14138, -800, -5312, 11141, 4942, -13070, -12870, -712, 3485, -13443, -208, 4245, -13209, 4249,
      -14115, 8355, 3933, 1],
    poly [-1935, -109, -727, 1525, 676, -1789, -1761, -97, 477, -1840, -28, 581, -1808, 582, -1932, 1144,
      538],
    poly [-1, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0, -1],
    poly [-4915, 2266, -1042, 1266, -4374, 9010, -5921, 293, 543, 1376, -560, 7009, 2006, 390, -7063,
      395, 6169, -8837],
    poly [23814, -21548, -8223, 9489, -8948, 10777, -13390, 16290, -7458, -5774, 15006, -8837],
    poly [673, -310, 143, -173, 599, -1233, 811, -40, -74, -188, 77, -959, -274, -53, 967, -54, -844,
      1210],
    poly [-3259, 2950, 1125, -1299, 1225, -1475, 1833, -2230, 1021, 790, -2054, 1210],
    poly [14138, -13338, -10079, -1062, 10711, -13032, -7339, 10366, -6259, -4422, -3932, -1],
    poly [1935, -1826, -1379, -145, 1466, -1784, -1004, 1419, -857, -605, -538],
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
theorem certificado_28843 :
    haveI : Fact (Nat.Prime 28843) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 28843 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((28843 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((28843 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((28843 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 28843) := ⟨by norm_num⟩
  have hP : poly [-2085, 1] = X - C (2085 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((28843 : ℕ) : ℤ[X]) = poly [28843] := by simp [poly]
  refine ⟨X - C (2085 : ℤ),
    poly [9642, 2467, -10540, -6410, 4313, -13541, -297, -10984, 5874, -8657, 8794, -12529, -9067, 10523,
      -12293, -5982, 2086, 1],
    poly [697, 178, -762, -463, 312, -979, -21, -794, 425, -626, 636, -906, -655, 761, -889, -432, 151],
    poly [-1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1],
    poly [5917, 5657, 3236, 12531, 5342, 11951, 2160, 3843, 14966, 5274, 4218, 4591, 13500, 7376, 13363,
      1552, 11050, 7859],
    poly [34760, -23186, -2681, 6874, 2106, -6497, -2922, -5687, 3511, 8620, -17357, 3191, 7859],
    poly [-428, -409, -234, -906, -386, -864, -156, -278, -1082, -381, -305, -332, -976, -533, -966,
      -112, -799, -568],
    poly [-2513, 1677, 193, -497, -152, 470, 211, 411, -254, -623, 1255, -231, -568],
    poly [-9642, -2467, -8661, 8877, 13990, -12070, -2565, 13279, -2041, 8396, 8069, -2085, -1],
    poly [-697, -178, -626, 642, 1011, -873, -185, 960, -148, 607, 583, -151],
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
theorem certificado_29033 :
    haveI : Fact (Nat.Prime 29033) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 29033 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((29033 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((29033 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((29033 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 29033) := ⟨by norm_num⟩
  have hP : poly [-364, 1] = X - C (364 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((29033 : ℕ) : ℤ[X]) = poly [29033] := by simp [poly]
  refine ⟨X - C (364 : ℤ),
    poly [-12682, -2986, 6931, 3369, 5433, -6685, 13541, 13118, -9296, -1541, 12598, -13445, -11363,
      1564, -7573, -12304, 365, 1],
    poly [-159, -37, 87, 42, 68, -84, 170, 164, -117, -19, 158, -169, -142, 20, -95, -154, 5],
    poly [1, -1, 0, 0, 1, -1, 0, 0, 0, -1, 0, -1],
    poly [13628, 10475, 2570, 2309, 2069, 6854, 11254, 10628, -2295, -496, -5516, 213, 14825, 6570, 9658,
      6157, -2068, 4051],
    poly [15405, -12252, 4752, -7644, -13649, 11756, 5137, -2618, 12276, -6119, 4051],
    poly [-171, -131, -32, -29, -26, -86, -141, -133, 29, 6, 69, -3, -186, -82, -121, -77, 26, -51],
    poly [-193, 154, -60, 96, 171, -148, -64, 33, -154, 77, -51],
    poly [-12682, -6655, 221, -13479, -7056, 8196, 3532, -5095, 12668, -364, -1],
    poly [-159, -83, 3, -169, -88, 103, 44, -64, 159, -5],
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
theorem certificado_29147 :
    haveI : Fact (Nat.Prime 29147) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 29147 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((29147 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((29147 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((29147 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 29147) := ⟨by norm_num⟩
  have hP : poly [-472, 1] = X - C (472 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((29147 : ℕ) : ℤ[X]) = poly [29147] := by simp [poly]
  refine ⟨X - C (472 : ℤ),
    poly [-7225, -5573, 9004, -9429, 13936, 6637, -1715, -10625, 348, 433, 2471, 7786, -7085, -14218,
      10900, -9919, 473, 1],
    poly [-117, -90, 146, -153, 226, 107, -28, -172, 6, 7, 40, 126, -115, -230, 177, -161, 8],
    poly [1, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, -1],
    poly [12587, 15022, 3109, 2775, 8826, 6801, 7970, 1365, -6121, 4361, 12905, 9959, 2419, 1662, 11973,
      9216, -2708, 4924],
    poly [16560, -31582, -674, 10486, 8297, -9554, -7554, 14681, 4292, -2708, 4924],
    poly [-204, -243, -50, -45, -143, -110, -129, -22, 99, -71, -209, -161, -39, -27, -194, -149, 44,
      -80],
    poly [-268, 512, 10, -170, -134, 155, 122, -238, -69, 44, -80],
    poly [-7225, 1652, 7352, -9556, 7143, -11162, 4299, -10427, 9920, -473, -1],
    poly [-117, 27, 119, -155, 116, -181, 70, -169, 161, -8],
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
theorem certificado_29527 :
    haveI : Fact (Nat.Prime 29527) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 29527 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((29527 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((29527 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((29527 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 29527) := ⟨by norm_num⟩
  have hP : poly [-8403, 1] = X - C (8403 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((29527 : ℕ) : ℤ[X]) = poly [29527] := by simp [poly]
  refine ⟨X - C (8403 : ℤ),
    poly [7857, -13162, -11390, 2750, -14656, 4749, -12435, 4809, -11423, -3712, 365, 4171, 11280, -8576,
      8875, -9771, 8404, 1],
    poly [2236, -3746, -3241, 783, -4171, 1352, -3539, 1369, -3251, -1056, 104, 1187, 3210, -2441, 2526,
      -2781, 2392],
    poly [1, 0, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1],
    poly [15317, -7827, 7315, 904, -931, 7488, -115, 3535, -3798, 4406, 3019, 5215, -4989, 2034, 8286,
      -10277, 5361, -558],
    poly [14210, -6383, -15142, 21728, -5992, -1104, -6810, 18563, -15638, 5919, -558],
    poly [-4359, 2228, -2082, -257, 265, -2131, 33, -1006, 1081, -1254, -859, -1484, 1420, -579, -2358,
      2925, -1526, 159],
    poly [-4044, 1817, 4309, -6184, 1706, 314, 1938, -5283, 4451, -1685, 159],
    poly [7857, 8508, 1772, 6283, -4244, 1268, -12077, 10881, -11352, -8403, -1],
    poly [2236, 2421, 504, 1788, -1208, 361, -3437, 3097, -3231, -2391],
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
theorem certificado_29641 :
    haveI : Fact (Nat.Prime 29641) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 29641 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((29641 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((29641 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((29641 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 29641) := ⟨by norm_num⟩
  have hP : poly [-384, 1] = X - C (384 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((29641 : ℕ) : ℤ[X]) = poly [29641] := by simp [poly]
  refine ⟨X - C (384 : ℤ),
    poly [9340, 7203, -11251, -13306, 2667, -2000, -14131, 1507, 13435, -3207, -4331, 915, -152, 6252,
      8430, -364, 385, 1],
    poly [121, 93, -146, -172, 35, -26, -183, 20, 174, -42, -56, 12, -2, 81, 109, -5, 5],
    poly [-1, -1, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1],
    poly [999, 7254, 7965, 6809, 14525, 4356, 13052, 8752, 7197, 6807, 3564, 82, 5785, 4642, 9502, -2527,
      8943, 1717],
    poly [30640, -22387, 6966, -445, 7559, 3802, -762, 3240, 2860, -4860, 12029, -11470, 7226, 1717],
    poly [-13, -94, -103, -88, -188, -56, -169, -113, -93, -88, -46, -1, -75, -60, -123, 33, -116, -22],
    poly [-397, 291, -91, 6, -98, -49, 10, -42, -37, 63, -156, 149, -94, -22],
    poly [-9340, -7203, -9050, -9132, 6383, -9169, 5611, -1452, 6403, 2178, -8794, 749, -384, -1],
    poly [-121, -93, -117, -118, 83, -119, 73, -19, 83, 28, -114, 10, -5],
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
theorem certificado_29717 :
    haveI : Fact (Nat.Prime 29717) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 29717 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((29717 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((29717 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((29717 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 29717) := ⟨by norm_num⟩
  have hP : poly [-4371, 1] = X - C (4371 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((29717 : ℕ) : ℤ[X]) = poly [29717] := by simp [poly]
  refine ⟨X - C (4371 : ℤ),
    poly [3073, 9750, -3941, -10770, -5455, 5900, -257, -9525, 2153, 13795, -12520, -6482, 11869, -7605,
      -14041, 1982, 4372, 1],
    poly [452, 1434, -580, -1584, -802, 868, -38, -1401, 317, 2029, -1842, -953, 1746, -1119, -2065, 292,
      643],
    poly [0, -1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0, 0, -1, 0, -1],
    poly [271, -436, 2834, -1530, 6675, -7274, 6089, 10484, -3833, 11148, 6168, 5453, 3590, -6792, 10753,
      1606, -1945, 4139],
    poly [29717, -29446, -707, 3270, -4364, 8205, -13678, 12927, 6958, -15682, 19529, -13994, 3063, 7690,
      -6084, 4139],
    poly [-40, 64, -417, 225, -982, 1070, -896, -1542, 564, -1640, -907, -802, -528, 999, -1582, -236,
      286, -609],
    poly [-4371, 4332, 103, -481, 642, -1207, 2012, -1902, -1023, 2307, -2873, 2059, -451, -1131, 895,
      -609],
    poly [0, -3073, -6677, 13691, 6829, -5315, -14428, -3593, -13435, 11915, -3451, -4046, 11652, 2389,
      -4371, -1],
    poly [0, -452, -982, 2014, 1004, -782, -2122, -528, -1976, 1753, -508, -595, 1714, 351, -643],
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
theorem certificado_29983 :
    haveI : Fact (Nat.Prime 29983) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 29983 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((29983 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((29983 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((29983 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 29983) := ⟨by norm_num⟩
  have hP : poly [-1602, 1] = X - C (1602 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((29983 : ℕ) : ℤ[X]) = poly [29983] := by simp [poly]
  refine ⟨X - C (1602 : ℤ),
    poly [3163, 12916, -13299, 1751, 11605, -4260, -14807, 4258, -2524, 11097, 13445, -7478, -510, -2789,
      9768, -10531, 1603, 1],
    poly [169, 690, -711, 94, 620, -228, -791, 228, -135, 593, 718, -400, -27, -149, 522, -563, 86],
    poly [1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [7917, 2251, -6025, -4196, -2604, -956, 3462, 1406, -1777, -8236, 3158, 3502, -5182, -2118,
      -9041, 818, -879, -225],
    poly [22066, -24317, 8276, -1829, -1592, 6269, -10084, 1697, -654, -225],
    poly [-423, -120, 322, 224, 139, 51, -185, -75, 95, 440, -169, -187, 277, 113, 483, -44, 47, 12],
    poly [-1179, 1300, -443, 98, 85, -335, 539, -91, 35, 12],
    poly [3163, 9753, 3768, -14933, 9854, 10955, 9683, 12134, -1602, -1],
    poly [169, 521, 201, -798, 527, 585, 517, 648, -86],
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
theorem certificado_30059 :
    haveI : Fact (Nat.Prime 30059) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 30059 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((30059 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((30059 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((30059 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 30059) := ⟨by norm_num⟩
  have hP : poly [-1506, 1] = X - C (1506 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((30059 : ℕ) : ℤ[X]) = poly [30059] := by simp [poly]
  refine ⟨X - C (1506 : ℤ),
    poly [7884, 12440, 13441, -2985, 5427, -4627, -4474, -8366, -14077, 13124, 1346, 6847, 12100, -11309,
      13046, -14941, 1507, 1],
    poly [395, 623, 673, -150, 272, -232, -224, -419, -705, 658, 67, 343, 606, -567, 654, -749, 76],
    poly [1, 0, 1, 0, 0, 0, 1, 1, 0, -1],
    poly [13986, 4774, 9638, 17146, 10245, 10939, 10181, 4512, 1175, 8458, 1976, 5764, 19818, 15556,
      11202, 10760, 8644, 8443],
    poly [16073, -20847, -18850, 1704, 2037, -8202, -6327, 201, 8443],
    poly [-701, -239, -483, -859, -513, -548, -510, -226, -59, -424, -99, -289, -993, -779, -561, -539,
      -433, -423],
    poly [-805, 1045, 944, -86, -102, 411, 317, -10, -423],
    poly [7884, 4556, 8885, -11870, 9413, 3579, -13610, -1506, -1],
    poly [395, 228, 445, -595, 472, 179, -682, -75],
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
theorem certificado_30097 :
    haveI : Fact (Nat.Prime 30097) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 30097 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((30097 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((30097 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((30097 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 30097) := ⟨by norm_num⟩
  have hP : poly [-195, 1] = X - C (195 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((30097 : ℕ) : ℤ[X]) = poly [30097] := by simp [poly]
  refine ⟨X - C (195 : ℤ),
    poly [-4939, 10007, 360, -2622, -13287, 12125, -12594, 3794, 13293, 7631, 3126, -5386, -645, -312,
      -10960, 8124, 196, 1],
    poly [-32, 65, 2, -17, -86, 79, -82, 25, 86, 49, 20, -35, -4, -2, -71, 53, 1],
    poly [-1, -1, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1],
    poly [2433, 10317, 3875, -634, 1195, 5526, -2632, 4889, 11410, 14839, 6059, 11416, 14376, 6674, 9104,
      2171, 10470, 7117],
    poly [32530, -19780, 1442, -10951, -247, 14044, -7836, 2738, 9429, 12205, -3796, 1987, 2171, 10470,
      7117],
    poly [-16, -67, -25, 4, -8, -36, 17, -32, -74, -96, -39, -74, -93, -43, -59, -14, -68, -46],
    poly [-211, 129, -10, 71, 1, -91, 51, -18, -61, -79, 25, -13, -14, -68, -46],
    poly [4939, -10007, -5299, 12629, -11511, 404, 13893, -3633, -5575, 8769, 508, 10961, -8124, -196,
      -1],
    poly [32, -65, -34, 82, -75, 3, 90, -24, -36, 57, 3, 71, -53, -1],
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
theorem certificado_30211 :
    haveI : Fact (Nat.Prime 30211) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 30211 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((30211 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((30211 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((30211 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 30211) := ⟨by norm_num⟩
  have hP : poly [-316, 1] = X - C (316 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((30211 : ℕ) : ℤ[X]) = poly [30211] := by simp [poly]
  refine ⟨X - C (316 : ℤ),
    poly [8700, -2745, -6701, 170, 10039, 9401, 1177, 10329, -6086, -2983, 9551, -4750, 5052, 13305,
      -6459, 9540, 317, 1],
    poly [91, -29, -70, 2, 105, 98, 12, 108, -64, -31, 100, -50, 53, 139, -68, 100, 3],
    poly [-1, 0, 0, 0, 0, -1, 0, -1, 0, 1, 0, -1],
    poly [-848, 5268, -2361, -3628, -7743, -7278, -4504, 285, -3046, 4305, 7292, 1852, -10785, -6714,
      -17122, -9889, -7476, -3931],
    poly [29363, -24095, -7629, -1267, -4115, -383, 8890, -3688, 1518, -3545, -3931],
    poly [9, -55, 25, 38, 81, 76, 47, -3, 32, -45, -76, -19, 113, 70, 179, 103, 78, 41],
    poly [-307, 253, 79, 13, 43, 4, -93, 39, -16, 37, 41],
    poly [-8700, 11445, 3956, -6871, -9869, -8062, -10542, -13896, -9222, -316, -1],
    poly [-91, 120, 41, -72, -103, -84, -110, -145, -96, -3],
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
theorem certificado_30553 :
    haveI : Fact (Nat.Prime 30553) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 30553 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((30553 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((30553 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((30553 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 30553) := ⟨by norm_num⟩
  have hP : poly [-1998, 1] = X - C (1998 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((30553 : ℕ) : ℤ[X]) = poly [30553] := by simp [poly]
  refine ⟨X - C (1998 : ℤ),
    poly [-5031, 12445, 2667, -121, -2722, -11669, 11096, -1386, -11913, 5652, -14662, -14611, -2454,
      -7693, 2137, -8440, 1999, 1],
    poly [-329, 814, 174, -8, -178, -763, 726, -91, -779, 370, -959, -955, -160, -503, 140, -552, 131],
    poly [1, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1],
    poly [10596, 4087, 10124, 12589, 9486, 10876, 7329, 5324, 659, -4252, 5884, 7143, 16701, 12577,
      10220, 6717, 12205, 2421],
    poly [19957, -24044, -6037, -13061, 9612, -7427, 1082, -5488, 9784, 2421],
    poly [-693, -267, -662, -823, -620, -711, -479, -348, -43, 278, -385, -467, -1092, -822, -668, -439,
      -798, -158],
    poly [-1305, 1573, 394, 854, -629, 486, -71, 359, -640, -158],
    poly [-5031, -13077, -9778, -7819, 14875, 11828, -10576, 10439, -1998, -1],
    poly [-329, -855, -639, -511, 973, 773, -692, 683, -131],
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
theorem certificado_30781 :
    haveI : Fact (Nat.Prime 30781) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 30781 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((30781 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((30781 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((30781 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 30781) := ⟨by norm_num⟩
  have hP : poly [-4011, 1] = X - C (4011 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((30781 : ℕ) : ℤ[X]) = poly [30781] := by simp [poly]
  refine ⟨X - C (4011 : ℤ),
    poly [-7866, -12012, 3412, -10106, 5661, 12234, 3372, 13845, -6274, 13574, -14071, -1876, 10398,
      -2315, 4696, -6330, 4012, 1],
    poly [-1025, -1565, 445, -1317, 738, 1594, 439, 1804, -818, 1769, -1834, -244, 1355, -302, 612, -825,
      523],
    poly [0, -1, -1, 0, 0, -1, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, -1],
    poly [10565, 6155, 7282, 7336, 1166, 9583, 7774, -998, 9452, -6899, 9934, -1550, 7541, 13084, -2355,
      16297, -98, 9222],
    poly [30781, -20216, 6155, -3283, 1181, 4449, -2163, 7735, 38, 1663, 9798, 6009, -2257, 7075, -98,
      9222],
    poly [-1377, -802, -949, -956, -152, -1249, -1013, 130, -1232, 899, -1295, 202, -983, -1705, 307,
      -2124, 13, -1202],
    poly [-4011, 2635, -803, 428, -154, -580, 282, -1008, -5, -217, -1277, -783, 294, -922, 13, -1202],
    poly [0, 7866, 12012, -11278, -1906, 5617, 12587, -13135, -11008, 5891, -9714, -4016, -684, 6331,
      -4012, -1],
    poly [0, 1025, 1565, -1470, -248, 732, 1640, -1712, -1434, 768, -1266, -523, -89, 825, -523],
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
theorem certificado_30971 :
    haveI : Fact (Nat.Prime 30971) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 30971 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((30971 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((30971 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((30971 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 30971) := ⟨by norm_num⟩
  have hP : poly [-1773, 1] = X - C (1773 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((30971 : ℕ) : ℤ[X]) = poly [30971] := by simp [poly]
  refine ⟨X - C (1773 : ℤ),
    poly [7948, -12887, 12727, 5038, 11427, -6876, -5419, -2501, 2514, 2971, -5658, 7840, 9280, -7541,
      14931, -13739, 1774, 1],
    poly [455, -738, 729, 288, 654, -394, -310, -143, 144, 170, -324, 449, 531, -432, 855, -787, 102],
    poly [-1, 0, 0, 1, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1],
    poly [-7549, 1076, -11601, -3468, -8075, 639, -7077, -2889, 4712, -14586, -2474, -10782, -8970,
      -9231, -9860, 3101, -1381, 4905],
    poly [23422, -22346, -12677, 15682, -13232, 13842, -14773, 4743, -5657, -8056, 4482, -6286, 4905],
    poly [432, -62, 664, 198, 462, -37, 405, 165, -270, 835, 141, 617, 513, 528, 564, -178, 79, -281],
    poly [-1341, 1280, 725, -898, 758, -793, 846, -272, 324, 461, -257, 360, -281],
    poly [-7948, -10136, 5357, -15334, 3747, 4998, 3741, -1308, -10272, 2300, -15458, -1773, -1],
    poly [-455, -580, 307, -878, 215, 286, 214, -75, -588, 132, -885, -101],
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
theorem certificado_31123 :
    haveI : Fact (Nat.Prime 31123) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 31123 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((31123 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((31123 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((31123 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 31123) := ⟨by norm_num⟩
  have hP : poly [-3571, 1] = X - C (3571 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((31123 : ℕ) : ℤ[X]) = poly [31123] := by simp [poly]
  refine ⟨X - C (3571 : ℤ),
    poly [-7260, 7502, -7990, -1388, -288, -12899, -4893, 12026, 1485, 5282, -3476, -2267, -1613, -15392,
      9513, -4817, 3572, 1],
    poly [-833, 861, -917, -159, -33, -1480, -561, 1380, 170, 606, -399, -260, -185, -1766, 1092, -553,
      410],
    poly [-1, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1],
    poly [-6812, -7485, -7154, -565, -476, -7919, -14571, -5195, -1436, -5967, -4016, -721, -12608,
      -8149, -3729, -2342, -16574, -12534],
    poly [24311, -31796, -6481, -896, -253, -7335, -647, -4459, -4420, -1387, 14232, -4040, -12534],
    poly [782, 859, 821, 65, 55, 909, 1672, 596, 165, 685, 461, 83, 1447, 935, 428, 269, 1902, 1438],
    poly [-2789, 3649, 743, 103, 29, 842, 74, 512, 507, 159, -1633, 464, 1438],
    poly [7260, -14762, -8371, -14104, -370, -2362, 653, -13779, -6218, -14330, 8389, -3571, -1],
    poly [833, -1694, -960, -1618, -42, -271, 75, -1581, -713, -1644, 963, -410],
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
theorem certificado_31237 :
    haveI : Fact (Nat.Prime 31237) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 31237 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((31237 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((31237 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((31237 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 31237) := ⟨by norm_num⟩
  have hP : poly [-505, 1] = X - C (505 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((31237 : ℕ) : ℤ[X]) = poly [31237] := by simp [poly]
  refine ⟨X - C (505 : ℤ),
    poly [5134, 11206, 12084, 2560, 12871, -8325, 13468, -12097, 11976, -5234, 12670, -7212, -15540,
      8196, 3109, 5635, 506, 1],
    poly [83, 181, 195, 41, 208, -135, 218, -196, 194, -85, 205, -117, -251, 133, 50, 91, 8],
    poly [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [-1857, 4696, 3843, 9965, 4039, 3285, 933, -12618, -6583, -3169, -6688, 4872, 6132, 3351, 5696,
      -7289, -2057, 675],
    poly [29380, -22827, -7406, 6975, -13905, 11725, -2451, -5077, 13660, -5232, -2732, 675],
    poly [30, -76, -62, -161, -65, -53, -15, 204, 106, 51, 108, -79, -99, -54, -92, 118, 33, -11],
    poly [-475, 370, 119, -113, 225, -190, 40, 82, -221, 85, 44, -11],
    poly [-5134, -938, 5194, 10402, 6268, -5802, -12630, -5592, 2525, -5129, -505, -1],
    poly [-83, -15, 84, 168, 101, -94, -204, -90, 41, -83, -8],
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
theorem certificado_31541 :
    haveI : Fact (Nat.Prime 31541) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 31541 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((31541 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((31541 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((31541 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 31541) := ⟨by norm_num⟩
  have hP : poly [-4067, 1] = X - C (4067 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((31541 : ℕ) : ℤ[X]) = poly [31541] := by simp [poly]
  refine ⟨X - C (4067 : ℤ),
    poly [5801, 8447, -12073, -11287, 2572, 4522, -15750, -2726, -14255, -1446, 4141, -13439, -3912,
      -10207, 14151, -14468, 4068, 1],
    poly [748, 1089, -1557, -1455, 332, 583, -2031, -351, -1838, -186, 534, -1733, -504, -1316, 1825,
      -1866, 525],
    poly [-1, -1, 0, 0, -1, -1, -1, -1, -1, 0, -1],
    poly [-3328, -692, 5257, 962, -1133, 8677, 831, 1814, 8352, -6304, 10157, -5497, -3182, 3969, -2567,
      487, 10275, 3887],
    poly [28213, -32233, 8585, 1654, -9718, 7023, 7221, -5901, 6388, 3887],
    poly [429, 89, -678, -124, 146, -1119, -107, -234, -1077, 813, -1310, 709, 410, -512, 331, -63,
      -1325, -501],
    poly [-3638, 4157, -1108, -213, 1253, -906, -931, 761, -824, -501],
    poly [-5801, -8447, -13667, -11807, 11095, 7285, -1146, -13006, -4067, -1],
    poly [-748, -1089, -1762, -1522, 1431, 939, -148, -1677, -524],
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
theorem certificado_31769 :
    haveI : Fact (Nat.Prime 31769) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 31769 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((31769 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((31769 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((31769 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 31769) := ⟨by norm_num⟩
  have hP : poly [-92, 1] = X - C (92 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((31769 : ℕ) : ℤ[X]) = poly [31769] := by simp [poly]
  refine ⟨X - C (92 : ℤ),
    poly [-6561, -6287, 12363, 825, 5534, -9954, 2309, -11025, -3573, -3492, -12124, -2549, 11713, -6779,
      -6980, 8557, 93, 1],
    poly [-19, -18, 36, 2, 16, -29, 7, -32, -10, -10, -35, -7, 34, -20, -20, 25],
    poly [-1, -1, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1],
    poly [5075, 8238, 15524, 6625, 11708, 3821, 8915, 9661, 11741, -2049, -127, -2178, 11267, 1399, 2673,
      6140, 6523, 9635],
    poly [36844, -23531, 10449, 3462, -653, 4482, -6617, 14086, 7300, -7277, 9485, -4386, 6168, -383,
      -3112, 9635],
    poly [-15, -24, -45, -19, -34, -11, -26, -28, -34, 6, 0, 6, -33, -4, -8, -18, -19, -28],
    poly [-107, 69, -31, -10, 2, -13, 19, -41, -21, 21, -28, 13, -18, 1, 9, -28],
    poly [6561, 6287, 12845, -551, 6555, -7871, -10445, -3912, 9281, -1971, 4813, -293, 15536, -8464,
      -92, -1],
    poly [19, 18, 37, -2, 19, -23, -30, -11, 27, -6, 14, -1, 45, -25],
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
theorem certificado_31883 :
    haveI : Fact (Nat.Prime 31883) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 31883 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((31883 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((31883 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((31883 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 31883) := ⟨by norm_num⟩
  have hP : poly [-310, 1] = X - C (310 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((31883 : ℕ) : ℤ[X]) = poly [31883] := by simp [poly]
  refine ⟨X - C (310 : ℤ),
    poly [-3394, -12867, 5718, -13249, -15470, 2727, 5974, -5226, -13490, -4466, 15310, -10544, 14879,
      -6740, 13040, 762, 311, 1],
    poly [-33, -125, 56, -129, -150, 27, 58, -51, -131, -43, 149, -103, 145, -66, 127, 7, 3],
    poly [1, -1, -1, 0, 0, 0, 0, 0, 0, -1, -1],
    poly [23527, 7250, 16351, 10518, 12659, 9889, 13994, 13493, 2898, 7492, 8741, 7408, 10592, 8751,
      9465, 9673, 14199, 7837],
    poly [8356, 7921, -1851, -1343, 1127, -922, -4734, 1836, 14199, 7837],
    poly [-229, -70, -159, -102, -123, -96, -136, -131, -28, -73, -85, -72, -103, -85, -92, -94, -138,
      -76],
    poly [-81, -77, 18, 13, -11, 9, 46, -18, -138, -76],
    poly [-3394, -6079, -431, 3804, -1839, 7502, -12729, -761, -311, -1],
    poly [-33, -59, -4, 37, -18, 73, -124, -7, -3],
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
theorem certificado_32377 :
    haveI : Fact (Nat.Prime 32377) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 32377 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((32377 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((32377 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((32377 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 32377) := ⟨by norm_num⟩
  have hP : poly [-8, 1] = X - C (8 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((32377 : ℕ) : ℤ[X]) = poly [32377] := by simp [poly]
  refine ⟨X - C (8 : ℤ),
    poly [4047, 8600, 5122, -3407, -426, 12088, 5558, 12836, -10537, 6777, 847, 8200, 5072, 4681, 585,
      73, 9, 1],
    poly [1, 2, 1, -1, 0, 3, 1, 3, -3, 2, 0, 2, 1, 1],
    poly [-1, 0, -1, -1, 1, -1, -1],
    poly [477, 12678, 10156, 17935, 6766, 9417, -2393, 4225, -3042, 8191, 5548, 17359, 6694, 9408, 1653,
      12825, -1967, -3816],
    poly [32854, -20176, -2045, 20457, -1967, -3816],
    poly [0, -3, -2, -4, -1, -2, 1, -1, 1, -2, -1, -4, -1, -2, 0, -3, 1, 1],
    poly [-8, 6, 0, -5, 1, 1],
    poly [-4047, -4553, -569, -71, -9, -1],
    poly [-1, -1],
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
theorem certificado_32491 :
    haveI : Fact (Nat.Prime 32491) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 32491 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((32491 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((32491 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((32491 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 32491) := ⟨by norm_num⟩
  have hP : poly [-2639, 1] = X - C (2639 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((32491 : ℕ) : ℤ[X]) = poly [32491] := by simp [poly]
  refine ⟨X - C (2639 : ℤ),
    poly [-12041, 9611, 13559, -15397, -13672, -4696, 10254, -9427, 1006, 14553, -3331, 5773, 2403, 5492,
      -2054, 13887, 2640, 1],
    poly [-978, 781, 1101, -1251, -1110, -381, 833, -766, 82, 1182, -271, 469, 195, 446, -167, 1128, 214],
    poly [-1, 1, -1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, -1],
    poly [-7272, -6179, -4221, -16409, -10270, -7596, -8543, -7029, -4406, -2115, -1043, 7982, -4388,
      -12814, -887, 1900, -3036, -11373],
    poly [25219, -24126, -6407, -5781, 19192, -17611, 7434, 89, -554, -2787, 4936, 8337, -11373],
    poly [591, 502, 343, 1333, 834, 617, 694, 571, 358, 172, 85, -648, 357, 1041, 72, -154, 247, 924],
    poly [-2048, 1960, 520, 469, -1559, 1431, -604, -7, 45, 226, -401, -677, 924],
    poly [12041, -1202, -2746, -789, -12977, -6838, 7877, 5728, -7545, 15941, -11247, -2639, -1],
    poly [978, -98, -223, -64, -1054, -555, 640, 465, -613, 1295, -914, -214],
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
theorem certificado_32719 :
    haveI : Fact (Nat.Prime 32719) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 32719 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((32719 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((32719 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((32719 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 32719) := ⟨by norm_num⟩
  have hP : poly [-1526, 1] = X - C (1526 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((32719 : ℕ) : ℤ[X]) = poly [32719] := by simp [poly]
  refine ⟨X - C (1526 : ℤ),
    poly [-4181, -12996, 5802, 9202, -8163, -7767, 11959, 1766, -15029, 12769, -14400, -7621, 724, 12715,
      -11141, 7154, 1527, 1],
    poly [-195, -606, 271, 429, -381, -362, 558, 82, -701, 596, -672, -355, 34, 593, -520, 334, 71],
    poly [1, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0, -1],
    poly [14427, -122, -4870, 4175, -1844, -6372, 6361, 9221, -8273, 8997, 4034, -2423, -5965, 6640,
      -2164, -2813, -605, 4285],
    poly [18292, -18170, 4748, 5382, 5897, -14769, 5991, 44, 2077, -4890, 4285],
    poly [-673, 6, 227, -195, 86, 297, -297, -430, 386, -420, -188, 113, 278, -310, 101, 131, 28, -200],
    poly [-853, 848, -222, -251, -275, 689, -280, -2, -97, 228, -200],
    poly [-4181, -8815, -13921, 7581, -4369, -9587, 1709, -15951, -5628, -1526, -1],
    poly [-195, -411, -649, 354, -204, -447, 80, -744, -262, -71],
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
theorem certificado_32833 :
    haveI : Fact (Nat.Prime 32833) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 32833 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((32833 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((32833 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((32833 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 32833) := ⟨by norm_num⟩
  have hP : poly [-300, 1] = X - C (300 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((32833 : ℕ) : ℤ[X]) = poly [32833] := by simp [poly]
  refine ⟨X - C (300 : ℤ),
    poly [10616, -5984, 4905, 12274, -8824, 13651, -16371, -12750, -5843, -14466, -11102, -1022, -7555,
      3477, 3076, -8198, 301, 1],
    poly [97, -55, 45, 112, -81, 125, -150, -116, -53, -132, -101, -9, -69, 32, 28, -75, 3],
    poly [-1, 0, 0, 1, 0, -1, 0, 0, 0, 0, -1, -1],
    poly [-9085, 6754, -2277, -1541, -663, 3061, 9, -6130, -8011, -1779, -2196, -7779, -2216, 7543,
      -5886, -4508, 10162, 361],
    poly [23748, -16994, -9031, 9821, -14961, 3670, 12051, -16048, -4869, 10162, 361],
    poly [83, -62, 21, 14, 6, -28, 0, 56, 73, 16, 20, 71, 20, -69, 54, 41, -93, -3],
    poly [-217, 156, 82, -90, 137, -34, -110, 147, 44, -93, -3],
    poly [-10616, -16233, -10889, 3247, 4498, 10631, -11675, -2775, 8199, -301, -1],
    poly [-97, -148, -99, 30, 41, 97, -107, -25, 75, -3],
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
theorem certificado_32909 :
    haveI : Fact (Nat.Prime 32909) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 32909 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((32909 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((32909 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((32909 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 32909) := ⟨by norm_num⟩
  have hP : poly [-1069, 1] = X - C (1069 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((32909 : ℕ) : ℤ[X]) = poly [32909] := by simp [poly]
  refine ⟨X - C (1069 : ℤ),
    poly [-10159, -12816, 13010, -4113, 304, -15269, 5096, -5752, 1657, 6805, 12936, 1028, 1140, -12867,
      -11464, -7984, 1070, 1],
    poly [-330, -416, 423, -134, 10, -496, 166, -187, 54, 221, 420, 33, 37, -418, -372, -259, 35],
    poly [0, 1, -1, 0, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, -1],
    poly [-9410, -4955, 3515, -6790, -11756, -11853, -10006, -4463, -425, -15906, -15274, -12041, -11176,
      -10344, -15669, -9948, -7603, -10864],
    poly [32909, -23499, -13865, -4015, 18775, -5339, -14279, 2511, 4774, -8800, 5143, -2345, 3261,
      -10864],
    poly [306, 161, -114, 221, 382, 385, 325, 145, 14, 517, 496, 391, 363, 336, 509, 323, 247, 353],
    poly [-1069, 764, 450, 130, -610, 174, 464, -82, -155, 286, -167, 76, -106, 353],
    poly [0, -10159, 7502, -4426, -10040, -11369, -9831, 5686, 8779, 2471, 3481, 9054, -1069, -1],
    poly [0, -330, 244, -144, -326, -369, -319, 185, 285, 80, 113, 294, -35],
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
theorem certificado_33023 :
    haveI : Fact (Nat.Prime 33023) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 33023 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((33023 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((33023 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((33023 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 33023) := ⟨by norm_num⟩
  have hP : poly [-7562, 1] = X - C (7562 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((33023 : ℕ) : ℤ[X]) = poly [33023] := by simp [poly]
  refine ⟨X - C (7562 : ℤ),
    poly [13114, -13121, -945, -10804, -4923, 13371, -15073, 4758, -2851, -13931, -12011, 5658, -16240,
      -13876, -6775, -4429, 7563, 1],
    poly [3003, -3005, -216, -2474, -1127, 3062, -3452, 1090, -653, -3190, -2750, 1296, -3719, -3177,
      -1551, -1014, 1732],
    poly [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1],
    poly [4132, 7827, -3662, 12158, -836, 3800, 2639, 4390, -7239, -4747, 7935, 15, 5560, 5076, 11836,
      -5072, 10018, -6426],
    poly [28891, -36718, 11489, -15820, 12994, -8768, -2534, 9738, -4191, 10502, -13186, 16908, -15090,
      16444, -6426],
    poly [-946, -1792, 839, -2784, 192, -870, -604, -1005, 1658, 1087, -1817, -3, -1273, -1162, -2710,
      1162, -2294, 1472],
    poly [-6616, 8409, -2632, 3623, -2976, 2008, 580, -2230, 960, -2405, 3020, -3872, 3456, -3766, 1472],
    poly [13114, 6788, 12176, -9859, 5881, -1615, 11367, -1016, 15555, -5199, 7100, 2346, 11992, -7562,
      -1],
    poly [3003, 1554, 2788, -2258, 1347, -370, 2603, -233, 3562, -1191, 1626, 537, 2746, -1732],
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
theorem certificado_33289 :
    haveI : Fact (Nat.Prime 33289) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 33289 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((33289 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((33289 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((33289 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 33289) := ⟨by norm_num⟩
  have hP : poly [-228, 1] = X - C (228 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((33289 : ℕ) : ℤ[X]) = poly [33289] := by simp [poly]
  refine ⟨X - C (228 : ℤ),
    poly [146, 12119, -4911, -15206, -10141, 16016, -7960, -2809, 10792, -10903, -5888, -5720, 3041,
      -11083, -12897, -14365, 229, 1],
    poly [1, 83, -34, -104, -69, 110, -55, -19, 74, -75, -40, -39, 21, -76, -88, -98, 2],
    poly [-1, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, -1, 0, -1],
    poly [-15155, 401, -7123, -7156, -2338, -6697, -2774, -9619, -8919, -11252, -3524, 14, -17199, -776,
      -1726, 3818, -6670, -6716],
    poly [18134, -17733, -7524, -33, 19973, -19915, 11447, -21967, 11438, -5498, 3772, 46, -6716],
    poly [104, -3, 49, 49, 16, 46, 19, 66, 61, 77, 24, 0, 118, 5, 12, -26, 46, 46],
    poly [-124, 122, 51, 0, -137, 137, -79, 151, -79, 38, -26, 0, 46],
    poly [-146, -11973, -16259, 10295, -4919, -14184, 6946, -15592, 12780, -1696, 14593, -228, -1],
    poly [-1, -82, -111, 71, -34, -97, 48, -107, 88, -12, 100, -2],
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
theorem certificado_33403 :
    haveI : Fact (Nat.Prime 33403) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 33403 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((33403 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((33403 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((33403 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 33403) := ⟨by norm_num⟩
  have hP : poly [-26, 1] = X - C (26 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((33403 : ℕ) : ℤ[X]) = poly [33403] := by simp [poly]
  refine ⟨X - C (26 : ℤ),
    poly [14132, -16158, 16080, 12181, -2101, 10197, 10670, 6834, 4117, -12689, -5627, 2353, -2479, 7613,
      -15124, 703, 27, 1],
    poly [11, -13, 13, 9, -2, 8, 8, 5, 3, -10, -4, 2, -2, 6, -12, 1],
    poly [1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1],
    poly [-25181, -9448, -17836, -25867, -1766, -20110, -23385, -4240, -30483, -4513, -13792, -23142,
      2193, -18673, -22045, -1619, -26528, -13354],
    poly [58584, -23955, -7345, 16419, -16070, -5757, 21619, 9311, 16546, -7072, 24909, -13174, -13354],
    poly [20, 7, 14, 20, 1, 16, 18, 3, 24, 3, 11, 18, -2, 15, 17, 1, 21, 10],
    poly [-46, 20, 5, -13, 13, 4, -17, -7, -13, 6, -20, 11, 10],
    poly [14132, -16158, 1948, -5064, 15222, -1984, 12771, 10769, 10692, 15828, -676, -26, -1],
    poly [11, -13, 2, -4, 12, -2, 10, 8, 8, 12, -1],
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
theorem certificado_33479 :
    haveI : Fact (Nat.Prime 33479) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 33479 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((33479 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((33479 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((33479 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 33479) := ⟨by norm_num⟩
  have hP : poly [-3098, 1] = X - C (3098 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((33479 : ℕ) : ℤ[X]) = poly [33479] := by simp [poly]
  refine ⟨X - C (3098 : ℤ),
    poly [12352, 4251, -928, -8289, -14181, 13936, -9581, 8599, -7108, -5049, 6223, 13640, -2600, -12288,
      -58, -7770, 3099, 1],
    poly [1143, 393, -86, -767, -1312, 1290, -887, 796, -658, -467, 576, 1262, -241, -1137, -5, -719,
      287],
    poly [0, 0, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, -1],
    poly [7232, -460, -2278, -10751, -7609, -15432, -6130, -4506, -10233, -11456, -3989, -1728, -8114,
      -4766, -12697, -8539, -11369, -7285],
    poly [33479, -33479, 7232, -7692, -1818, -1241, -4550, -2409, -6863, 2948, -14791, 10761, -8242,
      -4455, -4084, -7285],
    poly [-669, 43, 211, 995, 704, 1428, 567, 417, 947, 1060, 369, 160, 751, 441, 1175, 790, 1052, 674],
    poly [-3098, 3099, -670, 712, 168, 115, 421, 223, 635, -273, 1369, -996, 763, 412, 378, 674],
    poly [0, 0, -12352, 8101, 5179, -4991, 13993, -1811, 5500, -7109, 16078, -10380, -10810, 10868,
      -3098, -1],
    poly [0, 0, -1143, 750, 479, -462, 1295, -168, 509, -658, 1488, -961, -1000, 1006, -287],
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
theorem certificado_34429 :
    haveI : Fact (Nat.Prime 34429) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 34429 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((34429 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((34429 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((34429 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 34429) := ⟨by norm_num⟩
  have hP : poly [-854, 1] = X - C (854 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((34429 : ℕ) : ℤ[X]) = poly [34429] := by simp [poly]
  refine ⟨X - C (854 : ℤ),
    poly [13183, -15143, -10419, -4850, 16080, 9896, 5696, 12464, -4541, 5155, -16765, -8002, 13093, 741,
      -12013, 7162, 855, 1],
    poly [327, -376, -258, -120, 399, 245, 141, 309, -113, 128, -416, -198, 325, 18, -298, 178, 21],
    poly [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1],
    poly [4649, 502, -2849, 977, 1304, -5912, -4711, -154, 3520, 10781, 1638, -2122, -11802, 5764, 2640,
      9248, 1354, -10911],
    poly [29780, -34931, 7498, -5124, -4655, 14387, 891, -5764, -2640, -9248, -1354, 10911],
    poly [-115, -12, 71, -24, -32, 147, 117, 4, -87, -267, -40, 53, 293, -143, -65, -229, -33, 271],
    poly [-739, 867, -187, 127, 115, -357, -22, 143, 65, 229, 33, -271],
    poly [13183, -15143, 10827, -10953, 11356, -8856, 13092, 741, -12013, 7162, 855, 1],
    poly [327, -376, 269, -272, 282, -220, 325, 18, -298, 178, 21],
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
theorem certificado_34543 :
    haveI : Fact (Nat.Prime 34543) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 34543 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((34543 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((34543 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((34543 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 34543) := ⟨by norm_num⟩
  have hP : poly [-2450, 1] = X - C (2450 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((34543 : ℕ) : ℤ[X]) = poly [34543] := by simp [poly]
  refine ⟨X - C (2450 : ℤ),
    poly [12083, -8088, 17240, -4547, -4429, -13960, -17249, -712, 13972, 48, -15213, -7084, 10501, 4939,
      -10093, -5531, 2451, 1],
    poly [857, -574, 1223, -323, -314, -990, -1223, -50, 991, 3, -1079, -502, 745, 350, -716, -392, 174],
    poly [1, 0, 0, 0, 0, 1, -1, 0, 0, 0, -1, 0, -1],
    poly [5218, -2901, -3144, -3130, 423, 6473, -2689, -8558, -10210, -14948, -3445, 6838, 8520, -3802,
      2594, -7583, -11972, -3190],
    poly [29325, -26424, 243, -14, -3553, -11268, 22499, -2007, 1395, 1199, -8782, -3190],
    poly [-370, 206, 223, 222, -30, -459, 191, 607, 724, 1060, 244, -485, -604, 270, -184, 538, 849, 226],
    poly [-2080, 1875, -18, 1, 252, 799, -1596, 143, -99, -85, 623, 226],
    poly [12083, 14372, -9215, 12756, 118, 2552, -1000, -7050, 2112, 7981, -2450, -1],
    poly [857, 1019, -654, 905, 8, 181, -71, -500, 150, 566, -174],
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
theorem certificado_34847 :
    haveI : Fact (Nat.Prime 34847) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 34847 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((34847 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((34847 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((34847 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 34847) := ⟨by norm_num⟩
  have hP : poly [-1746, 1] = X - C (1746 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((34847 : ℕ) : ℤ[X]) = poly [34847] := by simp [poly]
  refine ⟨X - C (1746 : ℤ),
    poly [5728, -13229, -10785, -1523, -17125, 3423, -17202, -8532, -13317, 5421, 2917, -11135, 16998,
      3702, -12352, -16273, 1747, 1],
    poly [287, -663, -540, -76, -858, 172, -862, -427, -667, 272, 146, -558, 852, 185, -619, -815, 88],
    poly [-1, 0, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1],
    poly [-8737, -3493, -3011, -10994, -3634, 3156, -712, -7500, -15088, -5233, -2533, 3935, -2408,
      -15125, -2379, -7002, -10178, -8184],
    poly [26110, -29603, -8255, -11476, 4349, 4533, -12746, 4623, 3176, -1994, -8184],
    poly [438, 175, 151, 551, 182, -158, 36, 376, 756, 262, 127, -197, 121, 758, 119, 351, 510, 410],
    poly [-1308, 1484, 413, 575, -218, -227, 639, -232, -159, 100, 410],
    poly [-5728, -15890, -8172, 3967, -8460, -13297, -16054, -3921, -16827, -1746, -1],
    poly [-287, -796, -409, 199, -424, -666, -804, -196, -843, -87],
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
theorem certificado_34961 :
    haveI : Fact (Nat.Prime 34961) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 34961 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((34961 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((34961 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((34961 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 34961) := ⟨by norm_num⟩
  have hP : poly [-638, 1] = X - C (638 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((34961 : ℕ) : ℤ[X]) = poly [34961] := by simp [poly]
  refine ⟨X - C (638 : ℤ),
    poly [-10028, 11985, 14595, 1886, -11121, -5826, -13325, -12186, 12420, 6650, 5545, 7242, -1249,
      15999, -8085, -11849, 639, 1],
    poly [-183, 219, 266, 34, -203, -106, -243, -222, 227, 121, 101, 132, -23, 292, -148, -216, 12],
    poly [-1, -1, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0, 0, -1],
    poly [9737, 6300, 11610, 14687, 280, 20697, -4204, 14991, 7185, 6296, 6459, -2144, 10720, 4822,
      13690, 1210, 12150, 10852],
    poly [44698, -28661, 1873, 8387, -1593, 2573, 826, 7108, 3282, 23332, -10940, 1298, 10852],
    poly [-178, -115, -212, -268, -5, -378, 77, -274, -131, -115, -118, 39, -196, -88, -250, -22, -222,
      -198],
    poly [-816, 524, -35, -153, 29, -47, -15, -130, -60, -426, 200, -24, -198],
    poly [10028, -11985, 10338, 10099, 783, -14301, -406, -5864, 10238, -3765, 12488, -638, -1],
    poly [183, -219, 189, 184, 14, -261, -7, -107, 187, -69, 228, -12],
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
theorem certificado_35227 :
    haveI : Fact (Nat.Prime 35227) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 35227 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((35227 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((35227 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((35227 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 35227) := ⟨by norm_num⟩
  have hP : poly [-4969, 1] = X - C (4969 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((35227 : ℕ) : ℤ[X]) = poly [35227] := by simp [poly]
  refine ⟨X - C (4969 : ℤ),
    poly [3729, 12953, -1791, -10762, 11674, 11955, -14311, 543, -13179, 6555, 7672, -835, 17468, 280,
      16419, 1804, 4970, 1],
    poly [526, 1827, -253, -1518, 1647, 1686, -2019, 77, -1859, 925, 1082, -118, 2464, 39, 2316, 254,
      701],
    poly [-1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, -1],
    poly [-11760, -16335, -6028, -8174, -2269, -5139, -11917, 5486, -2167, 2000, -1636, -5387, -3027,
      3283, 4929, -3507, -3374, -6153],
    poly [23467, -39802, 10307, -2146, 5905, 8890, -2203, -4664, -10082, 8569, -2912, 8932, -6153],
    poly [1659, 2304, 850, 1153, 320, 725, 1681, -774, 306, -282, 231, 760, 427, -463, -695, 495, 476,
      868],
    poly [-3310, 5615, -1455, 303, -833, -1254, 311, 658, 1422, -1209, 411, -1260, 868],
    poly [-3729, -9224, 14744, 8971, 12791, 3448, 263, 1900, -4473, 17446, 8135, -4968, -1],
    poly [-526, -1301, 2080, 1265, 1804, 486, 37, 268, -631, 2461, 1147, -701],
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
theorem certificado_35531 :
    haveI : Fact (Nat.Prime 35531) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 35531 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((35531 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((35531 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((35531 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 35531) := ⟨by norm_num⟩
  have hP : poly [-2321, 1] = X - C (2321 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((35531 : ℕ) : ℤ[X]) = poly [35531] := by simp [poly]
  refine ⟨X - C (2321 : ℤ),
    poly [-7394, 3579, -14863, -7033, 7988, 3356, 6232, -11693, 17018, 8427, 16001, -14230, -16723,
      -9376, -12557, -11349, 2322, 1],
    poly [-483, 234, -971, -459, 522, 219, 407, -764, 1112, 550, 1045, -930, -1092, -612, -820, -741,
      152],
    poly [1, 0, -1, 0, 0, 0, 1, 0, 1, -1],
    poly [6389, -9575, -13409, -8267, -6489, -6427, -9902, -15139, -8727, 3247, -4249, -1313, -1970,
      7919, 4387, 4064, -3621, -12442],
    poly [29142, -19567, 10223, -21106, -5612, 5080, -1136, 21263, -12442],
    poly [-417, 626, 876, 540, 424, 420, 647, 989, 570, -212, 278, 86, 129, -517, -286, -265, 237, 813],
    poly [-1904, 1279, -668, 1379, 366, -332, 74, -1389, 813],
    poly [-7394, 10973, -11048, -3143, -2068, -12462, 15992, -2320, -1],
    poly [-483, 717, -722, -205, -135, -814, 1045, -152],
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
theorem certificado_35569 :
    haveI : Fact (Nat.Prime 35569) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 35569 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((35569 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((35569 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((35569 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 35569) := ⟨by norm_num⟩
  have hP : poly [-2151, 1] = X - C (2151 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((35569 : ℕ) : ℤ[X]) = poly [35569] := by simp [poly]
  refine ⟨X - C (2151 : ℤ),
    poly [-13080, -12590, -5810, 3073, -11210, 11107, 2684, -12963, -11697, 7998, -7669, 16549, 10475,
      -11868, 12165, 4983, 2152, 1],
    poly [-791, -761, -351, 186, -678, 672, 162, -784, -707, 484, -464, 1001, 633, -718, 736, 301, 130],
    poly [-1, 0, 0, -1, 0, 0, 0, 1, -1, 0, 0, -1, -1],
    poly [-9722, -14307, -16773, -10970, -11976, -9926, -14952, -23520, -15041, -13863, -7000, -15116,
      1069, -5819, -4582, -8517, -9974, -2550],
    poly [25847, -40154, -2466, -3919, -5591, -416, 777, 148, 5392, -5967, -9974, -2550],
    poly [588, 865, 1014, 663, 724, 600, 904, 1422, 909, 838, 423, 914, -65, 352, 277, 515, 603, 154],
    poly [-1563, 2429, 148, 237, 338, 25, -47, -9, -326, 361, 603, 154],
    poly [13080, -490, -6780, 4197, 13793, 6472, -460, 16850, -10013, -4982, -2152, -1],
    poly [791, -30, -410, 254, 834, 391, -28, 1019, -606, -301, -130],
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
theorem certificado_35759 :
    haveI : Fact (Nat.Prime 35759) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 35759 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((35759 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((35759 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((35759 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 35759) := ⟨by norm_num⟩
  have hP : poly [-1210, 1] = X - C (1210 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((35759 : ℕ) : ℤ[X]) = poly [35759] := by simp [poly]
  refine ⟨X - C (1210 : ℤ),
    poly [-14806, 5987, -17845, -4625, -14071, 17661, 4152, -10015, -4323, -12534, -4000, 13857, 2553,
      -12351, -12186, -808, 1211, 1],
    poly [-501, 203, -604, -156, -476, 598, 140, -339, -146, -424, -135, 469, 86, -418, -412, -27, 41],
    poly [-1, 0, -1, 0, 0, 0, 1, 0, -1, 1, -1],
    poly [-3563, -12816, -20005, -5796, 2461, -4418, -13260, -14213, 474, 5717, 786, -23481, -14251,
      9990, 9153, -10855, -21747, -15609],
    poly [32196, -45012, -10752, 4956, 1068, 7330, 2978, 1421, 9471, -15609],
    poly [121, 434, 677, 196, -83, 150, 449, 481, -16, -193, -26, 795, 482, -338, -309, 368, 736, 528],
    poly [-1089, 1524, 363, -168, -36, -248, -101, -48, -320, 528],
    poly [14806, 14966, 2879, 1746, -2481, -9193, 8149, 3228, -1209, -1],
    poly [501, 506, 97, 59, -84, -311, 276, 109, -41],
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
theorem certificado_35797 :
    haveI : Fact (Nat.Prime 35797) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 35797 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((35797 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((35797 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((35797 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 35797) := ⟨by norm_num⟩
  have hP : poly [-1674, 1] = X - C (1674 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((35797 : ℕ) : ℤ[X]) = poly [35797] := by simp [poly]
  refine ⟨X - C (1674 : ℤ),
    poly [3229, -6285, 595, 15012, -1381, -12147, -7620, 15670, -14040, -16410, 11559, 15489, -2343,
      15609, 3944, 11785, 1675, 1],
    poly [151, -294, 28, 702, -65, -568, -356, 733, -657, -767, 541, 724, -110, 730, 184, 551, 78],
    poly [-1, 0, -1, 1, 0, -1],
    poly [-5922, 618, 3188, 9562, 11191, 13309, 11514, 8455, 5994, 5629, 2913, 2612, 8022, 8068, 2722,
      10802, 16495, -2341],
    poly [29875, -29257, -3352, 18836, -2341],
    poly [277, -29, -149, -447, -523, -622, -538, -395, -280, -263, -136, -122, -375, -377, -127, -505,
      -771, 110],
    poly [-1397, 1369, 156, -881, 110],
    poly [-3229, 9514, -10109, -1674, -1],
    poly [-151, 445, -473, -78],
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
theorem certificado_35911 :
    haveI : Fact (Nat.Prime 35911) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 35911 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((35911 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((35911 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((35911 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 35911) := ⟨by norm_num⟩
  have hP : poly [-1242, 1] = X - C (1242 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((35911 : ℕ) : ℤ[X]) = poly [35911] := by simp [poly]
  refine ⟨X - C (1242 : ℤ),
    poly [9397, 10937, 11690, 10216, -252, 7315, 3996, -14020, -2122, -16685, 10916, -6439, 6645, 15561,
      12272, -366, 1243, 1],
    poly [325, 378, 404, 353, -9, 253, 138, -485, -73, -577, 378, -223, 230, 538, 424, -13, 43],
    poly [-1, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0, -1],
    poly [-14110, -5852, -2607, -7433, -13104, -14641, -7674, -10820, -2611, -5756, -6944, -11629,
      -13570, -16781, -8254, -19032, -7186, 52],
    poly [21801, -27653, 3245, -4826, -19781, 6721, -3898, -13824, 14041, -20373, 3540, -11794, -7238,
      52],
    poly [488, 202, 90, 257, 453, 506, 265, 374, 90, 199, 240, 402, 469, 580, 285, 658, 248, -2],
    poly [-754, 957, -113, 167, 684, -233, 135, 478, -486, 705, -123, 408, 250, -2],
    poly [-9397, -1540, -753, 1474, 1071, -9107, -6831, 8553, -3723, -1680, -13880, 1608, -1242, -1],
    poly [-325, -53, -26, 51, 37, -315, -236, 296, -129, -58, -480, 56, -43],
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
theorem certificado_36671 :
    haveI : Fact (Nat.Prime 36671) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 36671 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((36671 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((36671 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((36671 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 36671) := ⟨by norm_num⟩
  have hP : poly [-495, 1] = X - C (495 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((36671 : ℕ) : ℤ[X]) = poly [36671] := by simp [poly]
  refine ⟨X - C (495 : ℤ),
    poly [-12520, 5605, 10457, -6350, -11792, -10914, 17017, -18190, 12261, -9606, 1240, 447, 9928, 8021,
      5202, -11176, 496, 1],
    poly [-169, 76, 141, -86, -159, -147, 230, -246, 166, -130, 17, 6, 134, 108, 70, -151, 7],
    poly [1, 0, 0, 0, -1, -1, -1, 0, 0, 0, -1, -1],
    poly [18079, -2924, 7257, 4981, 2828, 453, 5634, 755, 9561, -9016, 11097, 6100, 4386, -2359, 3554,
      -4435, 11773, -1381],
    poly [18592, -15668, -10181, 2276, 20232, -549, 2076, -8219, -3054, 11773, -1381],
    poly [-244, 40, -98, -67, -38, -6, -76, -10, -129, 122, -150, -82, -59, 32, -48, 60, -159, 19],
    poly [-251, 212, 137, -31, -273, 8, -28, 111, 41, -159, 19],
    poly [-12520, 18125, 4852, -16807, 7078, -4727, 17474, -4706, 11177, -496, -1],
    poly [-169, 245, 65, -227, 96, -64, 236, -64, 151, -7],
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
theorem certificado_36709 :
    haveI : Fact (Nat.Prime 36709) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 36709 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((36709 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((36709 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((36709 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 36709) := ⟨by norm_num⟩
  have hP : poly [-2740, 1] = X - C (2740 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((36709 : ℕ) : ℤ[X]) = poly [36709] := by simp [poly]
  refine ⟨X - C (2740 : ℤ),
    poly [-17832, 12011, 2014, -5586, 842, -17269, -6839, 13127, 6248, -15311, -2042, -15448, 14477,
      -1656, 3121, -15004, 2741, 1],
    poly [-1331, 897, 150, -417, 63, -1289, -510, 980, 466, -1143, -152, -1153, 1081, -124, 233, -1120,
      205],
    poly [1, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, -1],
    poly [-7892, 4270, 282, -8401, -5095, -7157, 5677, -19050, -2406, 1137, 3724, -8105, -12919, 6184,
      -8640, -8699, 3774, 2479],
    poly [44601, -48871, 3988, 16575, -15468, 6050, -4151, 13529, -2420, -12473, 1295, 2479],
    poly [589, -319, -21, 627, 380, 534, -424, 1422, 179, -85, -278, 605, 964, -462, 645, 649, -282,
      -185],
    poly [-3329, 3649, -299, -1237, 1155, -452, 310, -1010, 181, 931, -97, -185],
    poly [-17832, -6866, -9997, 11277, -438, 8601, 2830, 7517, -18124, 17745, -2740, -1],
    poly [-1331, -512, -746, 842, -33, 642, 211, 561, -1353, 1325, -205],
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
theorem certificado_36899 :
    haveI : Fact (Nat.Prime 36899) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 36899 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((36899 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((36899 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((36899 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 36899) := ⟨by norm_num⟩
  have hP : poly [-702, 1] = X - C (702 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((36899 : ℕ) : ℤ[X]) = poly [36899] := by simp [poly]
  refine ⟨X - C (702 : ℤ),
    poly [-18029, 17320, 4913, 848, -5623, 3356, 9834, 16361, -16166, -9642, 14441, 16315, 3177, -7144,
      -2796, 13820, 703, 1],
    poly [-343, 330, 93, 16, -107, 64, 187, 311, -308, -183, 275, 310, 60, -136, -53, 263, 13],
    poly [0, 1, 1, 2, 1, 0, -1],
    poly [-21254, -13505, -6398, -24522, -4574, -16635, -18597, -5354, -20736, -9930, -15276, -18122,
      -2147, -22466, -20445, -3149, -7014, -23787],
    poly [36899, -15645, 13505, 27652, 16773, -23787],
    poly [405, 257, 122, 467, 87, 317, 354, 102, 395, 189, 291, 345, 41, 428, 389, 60, 134, 453],
    poly [-702, 298, -258, -527, -319, 453],
    poly [0, -18029, 17320, -13116, -702, -1],
    poly [0, -343, 330, -250, -13],
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
theorem certificado_37013 :
    haveI : Fact (Nat.Prime 37013) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 37013 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((37013 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((37013 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((37013 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 37013) := ⟨by norm_num⟩
  have hP : poly [-7319, 1] = X - C (7319 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((37013 : ℕ) : ℤ[X]) = poly [37013] := by simp [poly]
  refine ⟨X - C (7319 : ℤ),
    poly [-13902, 2380, -16764, 3831, -17047, -7057, 1147, 16102, 18491, -7305, -4340, -17392, 8443,
      -7539, -264, 17270, 7320, 1],
    poly [-2749, 471, -3315, 758, -3371, -1395, 227, 3184, 3656, -1445, -858, -3439, 1670, -1491, -52,
      3415, 1447],
    poly [-1, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1],
    poly [-9132, -7606, -1603, -12212, -1725, -5658, -14023, -9407, -18317, -2626, -20966, -1089, -10093,
      -5735, -11100, -14135, -11885, -8370],
    poly [27881, -35487, 6003, -19741, 2881, -5536, -11445, 10497, -22097, 6274, -18493, -6520, -5335,
      -2250, -3515, -8370],
    poly [1806, 1504, 317, 2415, 341, 1119, 2773, 1860, 3622, 519, 4146, 215, 1996, 1134, 2195, 2795,
      2350, 1655],
    poly [-5513, 7018, -1188, 3904, -570, 1095, 2263, -2076, 4370, -1241, 3657, 1289, 1055, 445, 695,
      1655],
    poly [13902, -16282, -17869, -6693, 18498, 6774, 11076, 4472, 1806, -10913, 3761, -45, 17533, -9950,
      -7319, -1],
    poly [2749, -3220, -3533, -1323, 3658, 1339, 2190, 884, 357, -2158, 744, -9, 3467, -1968, -1447],
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
theorem certificado_37507 :
    haveI : Fact (Nat.Prime 37507) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 37507 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((37507 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((37507 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((37507 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 37507) := ⟨by norm_num⟩
  have hP : poly [-1499, 1] = X - C (1499 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((37507 : ℕ) : ℤ[X]) = poly [37507] := by simp [poly]
  refine ⟨X - C (1499 : ℤ),
    poly [15238, -13076, -7365, -15343, -6766, 8803, 156, 1051, 15589, 1887, -8506, 5474, 17994, -1164,
      11459, -1919, 1500, 1],
    poly [609, -523, -294, -613, -270, 352, 6, 42, 623, 75, -340, 219, 719, -47, 458, -77, 60],
    poly [-1, -1, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0, -1, -1],
    poly [-4832, -1057, 11231, 1631, 9131, 7960, -1674, -1180, 10155, 7160, -1049, 1848, 3101, 950,
      -3230, 4724, -13211, 4317],
    poly [32675, -38564, 16063, -2144, 1675, 13785, -16630, 10648, -3774, 9981, 407, -13211, 4317],
    poly [193, 42, -449, -65, -365, -318, 67, 47, -406, -286, 42, -74, -124, -38, 129, -189, 528, -173],
    poly [-1306, 1542, -643, 86, -67, -551, 665, -426, 151, -399, -16, 528, -173],
    poly [-15238, 13076, -14904, -12971, -9792, -7588, -8137, -6536, -755, -9959, 1920, -1500, -1],
    poly [-609, 523, -596, -518, -391, -303, -325, -261, -30, -398, 77, -60],
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
theorem certificado_37811 :
    haveI : Fact (Nat.Prime 37811) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 37811 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((37811 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((37811 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((37811 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 37811) := ⟨by norm_num⟩
  have hP : poly [-482, 1] = X - C (482 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((37811 : ℕ) : ℤ[X]) = poly [37811] := by simp [poly]
  refine ⟨X - C (482 : ℤ),
    poly [10904, -8528, -14844, 989, 2983, 1732, -7135, -4094, -2911, -8792, -9824, 13237, -757, -15377,
      -10073, 5941, 483, 1],
    poly [139, -109, -189, 13, 38, 22, -91, -52, -37, -112, -125, 169, -10, -196, -128, 76, 6],
    poly [-1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    poly [-14506, -4495, -4082, -7925, 1559, 1108, 3382, 11702, -989, -6585, -14755, -11791, -2842, 7453,
      11632, 6071, -5629, -3143],
    poly [23305, -13294, -9598, -4256, 13327, 4571, 7220, -4378, -3075, -8557, 2486, 3143],
    poly [185, 57, 52, 101, -20, -14, -43, -149, 13, 84, 188, 150, 36, -95, -148, -77, 72, 40],
    poly [-297, 170, 122, 54, -170, -58, -92, 56, 39, 109, -32, -40],
    poly [-10904, -7475, -13116, 15662, 13839, 14149, -912, 155, -15532, 5459, 482, 1],
    poly [-139, -95, -167, 200, 176, 180, -12, 2, -198, 70, 6],
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
theorem certificado_37963 :
    haveI : Fact (Nat.Prime 37963) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 37963 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((37963 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((37963 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((37963 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 37963) := ⟨by norm_num⟩
  have hP : poly [-440, 1] = X - C (440 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((37963 : ℕ) : ℤ[X]) = poly [37963] := by simp [poly]
  refine ⟨X - C (440 : ℤ),
    poly [-8024, -7352, -5970, -1998, 18373, 6599, -16033, -209, -14668, -18756, 17127, -7036, -13907,
      13428, -746, 4226, 441, 1],
    poly [-93, -85, -69, -23, 213, 76, -186, -2, -170, -217, 199, -82, -161, 156, -9, 49, 5],
    poly [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, -1, 0, 0, 2, 1],
    poly [3651, -8161, 5962, 9359, 9453, 4449, 17207, 1188, 7450, -9274, -3445, -1965, -8864, -16386,
      -11744, -6039, -12497, -11994],
    poly [37963, -37963, 0, -3651, 8161, -2311, -17520, -3491, 1259, 4058, -7211, -5452, 24491, 11994],
    poly [-42, 95, -69, -108, -109, -51, -199, -13, -86, 108, 40, 23, 103, 190, 136, 70, 145, 139],
    poly [-440, 441, -1, 42, -95, 27, 203, 40, -15, -47, 84, 63, -284, -139],
    poly [0, 0, 0, -8024, -7352, 2054, 5354, -13620, 573, 4229, 2598, 4665, 442, 1],
    poly [0, 0, 0, -93, -85, 24, 62, -158, 7, 49, 30, 54, 5],
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
theorem certificado_38039 :
    haveI : Fact (Nat.Prime 38039) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 38039 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((38039 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((38039 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((38039 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 38039) := ⟨by norm_num⟩
  have hP : poly [-2586, 1] = X - C (2586 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((38039 : ℕ) : ℤ[X]) = poly [38039] := by simp [poly]
  refine ⟨X - C (2586 : ℤ),
    poly [5369, 12770, -10483, -9124, -2107, -17770, 10687, -10322, 1364, -14459, -1859, -17917, 1111,
      12533, 6683, -4881, 2587, 1],
    poly [365, 868, -713, -620, -143, -1208, 727, -702, 93, -983, -126, -1218, 76, 852, 454, -332, 176],
    poly [-1, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [-13661, -6944, -9545, -5089, -2822, -1865, -4733, -12236, -11930, -19167, -1533, 592, 3167,
      -13851, -13887, -10798, -10635, -10885],
    poly [24378, -31322, -16262, -2488, 6383, -10849, -3089, -163, 250, -10885],
    poly [929, 472, 649, 346, 192, 127, 322, 832, 811, 1303, 104, -40, -215, 942, 944, 734, 723, 740],
    poly [-1657, 2130, 1105, 169, -434, 738, 210, 11, -17, 740],
    poly [-5369, -7401, 17884, -14129, 8835, -5851, -11564, 7468, -2586, -1],
    poly [-365, -503, 1216, -961, 601, -398, -786, 508, -176],
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
theorem certificado_38153 :
    haveI : Fact (Nat.Prime 38153) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 38153 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((38153 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((38153 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((38153 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 38153) := ⟨by norm_num⟩
  have hP : poly [-1553, 1] = X - C (1553 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((38153 : ℕ) : ℤ[X]) = poly [38153] := by simp [poly]
  refine ⟨X - C (1553 : ℤ),
    poly [11866, -5520, 3485, 16708, -2274, -17174, -14776, -7306, -16907, -16299, 18243, -17603, 1389,
      12088, -7215, 9724, 1554, 1],
    poly [483, -225, 142, 680, -93, -699, -601, -297, -688, -663, 743, -717, 57, 492, -294, 396, 63],
    poly [1, -1, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1],
    poly [16186, 15312, 8580, -1890, 8962, 5505, 11792, -635, -3198, 1419, 3805, 1055, 11740, 5949, 8402,
      11843, 4647, 5969],
    poly [21967, -21093, 5858, 3738, -21322, 14309, -9744, 2528, 7196, -1322, 5969],
    poly [-659, -623, -349, 77, -365, -224, -480, 26, 130, -58, -155, -43, -478, -242, -342, -482, -189,
      -243],
    poly [-894, 859, -239, -152, 868, -583, 397, -103, -293, 54, -243],
    poly [11866, 8901, -11762, 4218, 5948, 4082, 17298, 16938, -8170, -1553, -1],
    poly [483, 362, -479, 172, 242, 166, 704, 689, -333, -63],
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
theorem certificado_38609 :
    haveI : Fact (Nat.Prime 38609) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 38609 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((38609 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((38609 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((38609 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 38609) := ⟨by norm_num⟩
  have hP : poly [-8124, 1] = X - C (8124 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((38609 : ℕ) : ℤ[X]) = poly [38609] := by simp [poly]
  refine ⟨X - C (8124 : ℤ),
    poly [13996, -10563, -18726, -13409, 8011, 12576, 18731, 10030, 16440, -9213, 5084, 14719, -14113,
      15900, -18737, -13889, 8125, 1],
    poly [2945, -2223, -3940, -2821, 1686, 2646, 3941, 2110, 3459, -1939, 1070, 3097, -2970, 3346, -3943,
      -2922, 1710],
    poly [1, 1, 0, 0, 0, 0, -1, 0, -1, 0, -1],
    poly [-2578, -20305, -14647, -16956, -15925, -6035, -13210, -13919, -13268, -12940, -9157, -23086,
      -9643, -16214, -15136, -6705, -17877, -21015],
    poly [41187, -18304, 12069, -3349, 1278, -10921, -5293, -9843, 3138, -21015],
    poly [543, 4273, 3082, 3568, 3351, 1270, 2780, 2929, 2792, 2723, 1927, 4858, 2029, 3412, 3185, 1411,
      3762, 4422],
    poly [-8667, 3852, -2540, 705, -269, 2298, 1114, 2071, -660, 4422],
    poly [13996, -10563, 5887, -2846, -11872, -12624, -3276, -16596, -8124, -1],
    poly [2945, -2223, 1239, -599, -2498, -2656, -689, -3492, -1709],
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
theorem certificado_38723 :
    haveI : Fact (Nat.Prime 38723) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 38723 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((38723 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((38723 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((38723 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 38723) := ⟨by norm_num⟩
  have hP : poly [-2291, 1] = X - C (2291 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((38723 : ℕ) : ℤ[X]) = poly [38723] := by simp [poly]
  refine ⟨X - C (2291 : ℤ),
    poly [-17460, -2881, -18543, -15237, 10253, -16509, -10588, 18385, 9693, 2810, -16901, -937, 2349,
      -11577, -17820, -15355, 2292, 1],
    poly [-1033, -170, -1097, -901, 607, -977, -626, 1088, 573, 166, -1000, -55, 139, -685, -1054, -908,
      136],
    poly [-1, 0, 1, -1, 0, 0, 0, 0, -1, 0, 0, -1, -1],
    poly [-495, -7966, 6161, -1929, 8175, 2027, -1897, -13950, 175, -4112, -3573, -2322, 366, 570, -106,
      7449, -11512, 11078],
    poly [38228, -46194, 14622, -1114, -11494, 16069, -22118, 4199, 11406, -3629, -11512, 11078],
    poly [29, 471, -365, 114, -484, -120, 112, 825, -11, 243, 211, 137, -22, -34, 6, -441, 681, -656],
    poly [-2262, 2734, -866, 66, 680, -951, 1309, -249, -675, 215, 681, -656],
    poly [17460, -14579, -1798, -9990, -17008, 7007, 16263, -3779, -18611, 15356, -2292, -1],
    poly [1033, -863, -106, -591, -1006, 415, 962, -224, -1101, 909, -136],
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
theorem certificado_39103 :
    haveI : Fact (Nat.Prime 39103) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 39103 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((39103 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((39103 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((39103 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 39103) := ⟨by norm_num⟩
  have hP : poly [-5358, 1] = X - C (5358 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((39103 : ℕ) : ℤ[X]) = poly [39103] := by simp [poly]
  refine ⟨X - C (5358 : ℤ),
    poly [11655, 16452, -14396, 6062, 18166, -9433, -4366, -14721, 946, 13071, 14438, -3026, 8779,
      -14142, 17520, 11921, 5359, 1],
    poly [1597, 2254, -1973, 831, 2489, -1293, -598, -2017, 130, 1791, 1978, -415, 1203, -1938, 2401,
      1633, 734],
    poly [-1, -1, 1, 0, -1, -1, 0, 0, -1, -1, -1],
    poly [10468, 7288, 544, 4834, 17621, 6669, 20037, 2349, 4973, 799, 4637, 6579, 13206, 3946, 4966,
      4178, -887, 25261],
    poly [49571, -31815, -20392, 726, 34289, 4833, -20295, 4178, -887, 25261],
    poly [-1435, -999, -75, -663, -2415, -914, -2746, -322, -682, -110, -636, -902, -1810, -541, -681,
      -573, 121, -3462],
    poly [-6793, 4360, 2794, -100, -4699, -662, 2781, -573, 121, -3462],
    poly [-11655, -16452, -1397, 15187, 3141, 19501, -17519, -11921, -5359, -1],
    poly [-1597, -2254, -191, 2081, 430, 2672, -2401, -1633, -734],
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

end ATK.FermatDezenoveCertB

#print axioms ATK.FermatDezenoveCertB.certificado_17519
#print axioms ATK.FermatDezenoveCertB.certificado_17747
#print axioms ATK.FermatDezenoveCertB.certificado_18013
#print axioms ATK.FermatDezenoveCertB.certificado_18089
#print axioms ATK.FermatDezenoveCertB.certificado_18127
#print axioms ATK.FermatDezenoveCertB.certificado_18583
#print axioms ATK.FermatDezenoveCertB.certificado_18773
#print axioms ATK.FermatDezenoveCertB.certificado_19001
#print axioms ATK.FermatDezenoveCertB.certificado_19267
#print axioms ATK.FermatDezenoveCertB.certificado_19381
#print axioms ATK.FermatDezenoveCertB.certificado_19457
#print axioms ATK.FermatDezenoveCertB.certificado_19571
#print axioms ATK.FermatDezenoveCertB.certificado_19609
#print axioms ATK.FermatDezenoveCertB.certificado_19913
#print axioms ATK.FermatDezenoveCertB.certificado_20369
#print axioms ATK.FermatDezenoveCertB.certificado_20407
#print axioms ATK.FermatDezenoveCertB.certificado_20483
#print axioms ATK.FermatDezenoveCertB.certificado_20521
#print axioms ATK.FermatDezenoveCertB.certificado_20749
#print axioms ATK.FermatDezenoveCertB.certificado_20939
#print axioms ATK.FermatDezenoveCertB.certificado_21319
#print axioms ATK.FermatDezenoveCertB.certificado_21433
#print axioms ATK.FermatDezenoveCertB.certificado_21661
#print axioms ATK.FermatDezenoveCertB.certificado_21737
#print axioms ATK.FermatDezenoveCertB.certificado_21851
#print axioms ATK.FermatDezenoveCertB.certificado_22003
#print axioms ATK.FermatDezenoveCertB.certificado_22079
#print axioms ATK.FermatDezenoveCertB.certificado_22193
#print axioms ATK.FermatDezenoveCertB.certificado_22307
#print axioms ATK.FermatDezenoveCertB.certificado_22573
#print axioms ATK.FermatDezenoveCertB.certificado_22877
#print axioms ATK.FermatDezenoveCertB.certificado_23029
#print axioms ATK.FermatDezenoveCertB.certificado_23143
#print axioms ATK.FermatDezenoveCertB.certificado_23333
#print axioms ATK.FermatDezenoveCertB.certificado_23371
#print axioms ATK.FermatDezenoveCertB.certificado_23447
#print axioms ATK.FermatDezenoveCertB.certificado_23561
#print axioms ATK.FermatDezenoveCertB.certificado_23599
#print axioms ATK.FermatDezenoveCertB.certificado_23789
#print axioms ATK.FermatDezenoveCertB.certificado_23827
#print axioms ATK.FermatDezenoveCertB.certificado_24169
#print axioms ATK.FermatDezenoveCertB.certificado_24359
#print axioms ATK.FermatDezenoveCertB.certificado_24473
#print axioms ATK.FermatDezenoveCertB.certificado_24967
#print axioms ATK.FermatDezenoveCertB.certificado_25309
#print axioms ATK.FermatDezenoveCertB.certificado_25423
#print axioms ATK.FermatDezenoveCertB.certificado_25537
#print axioms ATK.FermatDezenoveCertB.certificado_25841
#print axioms ATK.FermatDezenoveCertB.certificado_26107
#print axioms ATK.FermatDezenoveCertB.certificado_26183
#print axioms ATK.FermatDezenoveCertB.certificado_26297
#print axioms ATK.FermatDezenoveCertB.certificado_26449
#print axioms ATK.FermatDezenoveCertB.certificado_26981
#print axioms ATK.FermatDezenoveCertB.certificado_27361
#print axioms ATK.FermatDezenoveCertB.certificado_27437
#print axioms ATK.FermatDezenoveCertB.certificado_27551
#print axioms ATK.FermatDezenoveCertB.certificado_27779
#print axioms ATK.FermatDezenoveCertB.certificado_27817
#print axioms ATK.FermatDezenoveCertB.certificado_27893
#print axioms ATK.FermatDezenoveCertB.certificado_28349
#print axioms ATK.FermatDezenoveCertB.certificado_28387
#print axioms ATK.FermatDezenoveCertB.certificado_28463
#print axioms ATK.FermatDezenoveCertB.certificado_28729
#print axioms ATK.FermatDezenoveCertB.certificado_28843
#print axioms ATK.FermatDezenoveCertB.certificado_29033
#print axioms ATK.FermatDezenoveCertB.certificado_29147
#print axioms ATK.FermatDezenoveCertB.certificado_29527
#print axioms ATK.FermatDezenoveCertB.certificado_29641
#print axioms ATK.FermatDezenoveCertB.certificado_29717
#print axioms ATK.FermatDezenoveCertB.certificado_29983
#print axioms ATK.FermatDezenoveCertB.certificado_30059
#print axioms ATK.FermatDezenoveCertB.certificado_30097
#print axioms ATK.FermatDezenoveCertB.certificado_30211
#print axioms ATK.FermatDezenoveCertB.certificado_30553
#print axioms ATK.FermatDezenoveCertB.certificado_30781
#print axioms ATK.FermatDezenoveCertB.certificado_30971
#print axioms ATK.FermatDezenoveCertB.certificado_31123
#print axioms ATK.FermatDezenoveCertB.certificado_31237
#print axioms ATK.FermatDezenoveCertB.certificado_31541
#print axioms ATK.FermatDezenoveCertB.certificado_31769
#print axioms ATK.FermatDezenoveCertB.certificado_31883
#print axioms ATK.FermatDezenoveCertB.certificado_32377
#print axioms ATK.FermatDezenoveCertB.certificado_32491
#print axioms ATK.FermatDezenoveCertB.certificado_32719
#print axioms ATK.FermatDezenoveCertB.certificado_32833
#print axioms ATK.FermatDezenoveCertB.certificado_32909
#print axioms ATK.FermatDezenoveCertB.certificado_33023
#print axioms ATK.FermatDezenoveCertB.certificado_33289
#print axioms ATK.FermatDezenoveCertB.certificado_33403
#print axioms ATK.FermatDezenoveCertB.certificado_33479
#print axioms ATK.FermatDezenoveCertB.certificado_34429
#print axioms ATK.FermatDezenoveCertB.certificado_34543
#print axioms ATK.FermatDezenoveCertB.certificado_34847
#print axioms ATK.FermatDezenoveCertB.certificado_34961
#print axioms ATK.FermatDezenoveCertB.certificado_35227
#print axioms ATK.FermatDezenoveCertB.certificado_35531
#print axioms ATK.FermatDezenoveCertB.certificado_35569
#print axioms ATK.FermatDezenoveCertB.certificado_35759
#print axioms ATK.FermatDezenoveCertB.certificado_35797
#print axioms ATK.FermatDezenoveCertB.certificado_35911
#print axioms ATK.FermatDezenoveCertB.certificado_36671
#print axioms ATK.FermatDezenoveCertB.certificado_36709
#print axioms ATK.FermatDezenoveCertB.certificado_36899
#print axioms ATK.FermatDezenoveCertB.certificado_37013
#print axioms ATK.FermatDezenoveCertB.certificado_37507
#print axioms ATK.FermatDezenoveCertB.certificado_37811
#print axioms ATK.FermatDezenoveCertB.certificado_37963
#print axioms ATK.FermatDezenoveCertB.certificado_38039
#print axioms ATK.FermatDezenoveCertB.certificado_38153
#print axioms ATK.FermatDezenoveCertB.certificado_38609
#print axioms ATK.FermatDezenoveCertB.certificado_38723
#print axioms ATK.FermatDezenoveCertB.certificado_39103
