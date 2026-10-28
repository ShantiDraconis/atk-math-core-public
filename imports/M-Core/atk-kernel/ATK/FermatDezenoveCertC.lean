import ATK.FermatDezenoveBase

/-!
# ATK — Certificados para `𝓞(ℚ(ζ₁₉))` principal (parte C)

Primos 39217 a 59509 da lista de `ATK.FermatDezenove`: para cada um, um gerador do ideal
primo e as identidades polinomiais do critério `pid6`, conferidas por reflexão (`ATK.PolyLista`).
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista
  ATK.FermatDezenoveBase

namespace ATK.FermatDezenoveCertC

set_option maxHeartbeats 4000000 in
theorem certificado_39217 :
    haveI : Fact (Nat.Prime 39217) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 39217 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((39217 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((39217 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((39217 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 39217) := ⟨by norm_num⟩
  have hP : poly [-1051, 1] = X - C (1051 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((39217 : ℕ) : ℤ[X]) = poly [39217] := by simp [poly]
  refine ⟨X - C (1051 : ℤ),
    poly [14142, -14539, 9949, -13237, -10162, -5159, -10117, -14077, -13633, -17961, 10095, 532, -18955,
      -11660, 2377, 7577, 1052, 1],
    poly [379, -390, 267, -355, -272, -138, -271, -377, -365, -481, 271, 14, -508, -312, 64, 203, 28],
    poly [-1, -1, 0, 0, -1, -1, 0, -1, -1, 0, -1],
    poly [-3403, 2564, 12234, 8773, 11419, 4705, 9736, 972, 15740, -2791, 14617, -4210, 3011, 4697, 5221,
      6826, 15559, 7806],
    poly [35814, -36653, 15637, 6209, -4218, -1504, 13954, -927, 7753, 7806],
    poly [91, -69, -328, -235, -306, -126, -261, -26, -422, 75, -392, 113, -81, -126, -140, -183, -417,
      -209],
    poly [-960, 983, -420, -166, 113, 40, -374, 25, -208, -209],
    poly [-14142, 14539, 4193, -1302, 5969, 6461, 4148, -6526, -1051, -1],
    poly [-379, 390, 112, -35, 160, 173, 111, -175, -28],
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
theorem certificado_39293 :
    haveI : Fact (Nat.Prime 39293) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 39293 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((39293 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((39293 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((39293 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 39293) := ⟨by norm_num⟩
  have hP : poly [-7593, 1] = X - C (7593 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((39293 : ℕ) : ℤ[X]) = poly [39293] := by simp [poly]
  refine ⟨X - C (7593 : ℤ),
    poly [13936, -12154, -43, -15504, 5473, 9921, -12346, 3745, 4720, 12498, -11616, 7352, -6685, 12393,
      -2177, 18412, 7594, 1],
    poly [2693, -2349, -8, -2996, 1058, 1917, -2386, 724, 912, 2415, -2245, 1421, -1292, 2395, -421,
      3558, 1467],
    poly [-1, 0, -1, 0, 0, 1, -1, 0, -1, -1, 0, 0, 0, 0, -1],
    poly [-12527, -15054, -5310, -1086, -5836, -18541, -15919, -13621, -14754, -21052, -32686, -24180,
      -16815, -22139, -12059, -14464, -15313, -10842],
    poly [26766, -41820, -2783, 1697, 4994, 4046, -12128, -22678, -5518, -10080, 2405, 849, -4471,
      -10842],
    poly [2421, 2909, 1026, 210, 1128, 3583, 3076, 2632, 2851, 4068, 6316, 4672, 3249, 4278, 2330, 2795,
      2959, 2095],
    poly [-5172, 8082, 537, -328, -965, -782, 2344, 4382, 1066, 1948, -465, -164, 864, 2095],
    poly [-13936, -13203, 13246, 2258, 6205, -14344, 557, 17662, 19077, -14570, -18704, -10818, -7593,
      -1],
    poly [-2693, -2551, 2560, 436, 1199, -2772, 108, 3413, 3686, -2816, -3614, -2090, -1467],
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
theorem certificado_39521 :
    haveI : Fact (Nat.Prime 39521) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 39521 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((39521 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((39521 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((39521 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 39521) := ⟨by norm_num⟩
  have hP : poly [-2513, 1] = X - C (2513 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((39521 : ℕ) : ℤ[X]) = poly [39521] := by simp [poly]
  refine ⟨X - C (2513 : ℤ),
    poly [2186, 5631, -16149, 11647, -6632, -4469, 9733, -11854, -10746, 17468, -5576, 18854, 7745,
      -13396, 781, -5677, 2514, 1],
    poly [139, 358, -1027, 741, -422, -284, 619, -754, -683, 1111, -355, 1199, 492, -852, 50, -361, 160],
    poly [-2, -1, -1, -1, -1, 0, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0, -1, -1],
    poly [-1996, 13950, 13516, 13736, 7068, 67, 9626, 20261, 10499, 8891, 6610, 13230, 6596, 4313, 15305,
      15561, 9239, -3219],
    poly [35529, -9625, 13082, 13956, 400, -4938, 3239, 31330, 2513, -1995, 11764, 10071, -2009, 2847,
      18780, 9239, -3219],
    poly [127, -887, -859, -873, -449, -4, -612, -1288, -667, -565, -420, -841, -419, -274, -973, -989,
      -587, 205],
    poly [-2259, 613, -832, -887, -25, 314, -206, -1992, -159, 127, -748, -640, 128, -181, -1194, -587,
      205],
    poly [-4372, -9076, -1592, 78, -14610, 4492, 19031, 11661, 99, 18526, 9003, -1286, 5205, 1732, 5678,
      -2514, -1],
    poly [-278, -577, -101, 5, -929, 286, 1210, 741, 6, 1178, 572, -82, 331, 110, 361, -160],
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
theorem certificado_39749 :
    haveI : Fact (Nat.Prime 39749) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 39749 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((39749 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((39749 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((39749 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 39749) := ⟨by norm_num⟩
  have hP : poly [-2563, 1] = X - C (2563 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((39749 : ℕ) : ℤ[X]) = poly [39749] := by simp [poly]
  refine ⟨X - C (2563 : ℤ),
    poly [884, 14408, -16108, 10214, -5269, 8047, 2407, 19542, 16571, 19501, 13066, 17499, -5871, -16271,
      -4690, 12948, 2564, 1],
    poly [57, 929, -1039, 659, -340, 519, 155, 1260, 1068, 1257, 842, 1128, -379, -1049, -302, 835, 165],
    poly [-1, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, -1],
    poly [976, 12670, 9914, 21529, 9111, 15899, 17406, -3065, 7504, 5523, 7771, 7989, 14022, 7216, 21621,
      7281, 3910, 2699],
    poly [40725, -27079, 9914, 21529, 8135, 3229, 8468, -11924, 8307, 10177, -13194, 17039, 3371, 1211,
      2699],
    poly [-63, -817, -639, -1388, -587, -1025, -1122, 198, -484, -356, -501, -515, -904, -465, -1394,
      -469, -252, -174],
    poly [-2626, 1747, -640, -1388, -524, -208, -546, 769, -536, -656, 851, -1099, -217, -78, -174],
    poly [-884, -14408, 16108, -10214, 6153, 6361, -19399, 16013, -5732, 18965, 9018, 17637, -10384,
      -2563, -1],
    poly [-57, -929, 1039, -659, 397, 410, -1251, 1033, -370, 1223, 581, 1137, -670, -165],
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
theorem certificado_39863 :
    haveI : Fact (Nat.Prime 39863) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 39863 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((39863 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((39863 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((39863 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 39863) := ⟨by norm_num⟩
  have hP : poly [-742, 1] = X - C (742 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((39863 : ℕ) : ℤ[X]) = poly [39863] := by simp [poly]
  refine ⟨X - C (742 : ℤ),
    poly [-17890, -9963, 11376, -1865, -17409, -15281, -14526, 18730, 13295, 7002, -1656, 14342, 2222,
      -9721, -4311, -6775, 743, 1],
    poly [-333, -185, 212, -35, -324, -284, -270, 349, 247, 130, -31, 267, 41, -181, -80, -126, 14],
    poly [1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1],
    poly [12837, 16024, 27364, 37157, 36042, 20192, 9211, 3985, -10420, -1575, 19228, 23930, 31780,
      30931, 30124, 23300, 2446, 2203],
    poly [27026, -43050, -24177, -12980, -23062, 2870, 756, 11283, 26501, -606, 1396, -6824, -20854,
      -243, -2203],
    poly [-239, -298, -509, -691, -670, -375, -171, -74, 194, 29, -358, -445, -591, -575, -560, -433,
      -45, -41],
    poly [-503, 802, 449, 241, 429, -54, -14, -210, -493, 12, -26, 127, 388, 4, 41],
    poly [-17890, 7927, 3449, -5314, -12095, -3186, 6550, -17720, 19639, 11201, -5411, 2464, -7518, 742,
      1],
    poly [-333, 148, 64, -99, -225, -59, 122, -330, 366, 208, -101, 46, -140, 14],
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
theorem certificado_39901 :
    haveI : Fact (Nat.Prime 39901) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 39901 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((39901 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((39901 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((39901 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 39901) := ⟨by norm_num⟩
  have hP : poly [-3811, 1] = X - C (3811 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((39901 : ℕ) : ℤ[X]) = poly [39901] := by simp [poly]
  refine ⟨X - C (3811 : ℤ),
    poly [11674, -8687, -4630, -3561, 5946, -14091, -1815, 12553, -15576, 17041, -18475, -15982, 8466,
      14367, -4781, 3569, 3812, 1],
    poly [1115, -830, -442, -340, 568, -1346, -173, 1199, -1488, 1628, -1765, -1526, 809, 1372, -457,
      341, 364],
    poly [-1, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [-7582, 4268, 4135, 638, 5893, -13140, 9334, -3067, 5379, 2146, -2158, 7379, -3769, 20822,
      -6718, 12885, -302, 6678],
    poly [32319, -35633, 11717, -3630, 1758, -13778, 11023, -1777, -11404, 20560, -12925, 13187, -6980,
      6678],
    poly [724, -408, -395, -61, -563, 1255, -892, 293, -514, -205, 206, -705, 360, -1989, 642, -1231, 29,
      -638],
    poly [-3087, 3404, -1120, 347, -168, 1316, -1053, 170, 1089, -1964, 1235, -1260, 667, -638],
    poly [-11674, 8687, 16304, -5126, -10576, 10530, 19435, -7104, 6144, 16942, 8349, 243, -3811, -1],
    poly [-1115, 830, 1557, -490, -1010, 1006, 1856, -679, 587, 1618, 797, 23, -364],
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
theorem certificado_40129 :
    haveI : Fact (Nat.Prime 40129) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 40129 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((40129 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((40129 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((40129 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 40129) := ⟨by norm_num⟩
  have hP : poly [-2007, 1] = X - C (2007 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((40129 : ℕ) : ℤ[X]) = poly [40129] := by simp [poly]
  refine ⟨X - C (2007 : ℤ),
    poly [-7298, -16919, -5227, 8735, 15880, -7610, -6542, 2696, 4900, -2037, 14535, 8185, 14880, -2132,
      3418, 17157, 2008, 1],
    poly [-365, -846, -261, 437, 794, -381, -327, 135, 245, -102, 727, 409, 744, -107, 171, 858, 100],
    poly [1, 0, 0, -1, 0, -1, 0, 0, 0, 0, -1, 0, -1],
    poly [10945, -9284, -5935, -3494, -6352, 3044, -5409, -17130, -1960, -7211, -5814, -3274, -5952,
      -7173, -9393, 1163, -8829, -16052],
    poly [29184, -19900, -3349, 8504, -17371, 4898, -9335, 12212, -3333, -6060, 7223, -16052],
    poly [-547, 465, 297, 175, 318, -152, 271, 857, 98, 361, 291, 164, 298, 359, 470, -58, 442, 803],
    poly [-1460, 996, 167, -425, 869, -245, 467, -611, 167, 303, -361, 803],
    poly [-7298, -9621, 11692, -18869, 16766, 12245, -3273, -9599, 11732, -15150, -2007, -1],
    poly [-365, -481, 585, -944, 839, 612, -164, -480, 587, -758, -100],
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
theorem certificado_40357 :
    haveI : Fact (Nat.Prime 40357) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 40357 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((40357 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((40357 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((40357 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 40357) := ⟨by norm_num⟩
  have hP : poly [-1149, 1] = X - C (1149 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((40357 : ℕ) : ℤ[X]) = poly [40357] := by simp [poly]
  refine ⟨X - C (1149 : ℤ),
    poly [-3126, -8608, 6385, 20026, 4443, 2884, 12647, -18464, -11080, -12900, -11883, 19413, -15016,
      -7951, 1960, -10430, 1150, 1],
    poly [-89, -245, 182, 570, 126, 82, 360, -526, -315, -367, -338, 553, -428, -226, 56, -297, 33],
    poly [1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1],
    poly [-2142, 1228, 2671, -6495, -5941, -9488, 765, 8185, -2170, -5586, 10603, 9739, 12794, -1885,
      -2530, -950, 14576, -619],
    poly [42499, -41585, -4813, 9865, 5242, 1550, 2460, -16085, 5254, 847, -15840, 2199, 15526, -15195,
      619],
    poly [61, -35, -76, 185, 169, 270, -22, -233, 62, 159, -302, -277, -364, 54, 72, 27, -415, 18],
    poly [-1210, 1185, 136, -281, -149, -44, -70, 458, -150, -24, 451, -63, -442, 433, -18],
    poly [-3126, -8608, 9511, -14849, -7424, -2149, -18512, 300, 6463, -18645, -8762, 12391, -11580,
      1149, 1],
    poly [-89, -245, 271, -423, -211, -61, -527, 9, 184, -531, -249, 353, -330, 33],
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
theorem certificado_40433 :
    haveI : Fact (Nat.Prime 40433) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 40433 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((40433 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((40433 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((40433 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 40433) := ⟨by norm_num⟩
  have hP : poly [-3472, 1] = X - C (3472 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((40433 : ℕ) : ℤ[X]) = poly [40433] := by simp [poly]
  refine ⟨X - C (3472 : ℤ),
    poly [19576, -16659, 3582, 9166, -12819, -3311, -18820, 14400, -16381, 19909, 14679, -19630, -19209,
      -12373, -679, 9223, 3473, 1],
    poly [1681, -1431, 308, 787, -1101, -284, -1616, 1237, -1407, 1710, 1260, -1686, -1649, -1062, -58,
      792, 298],
    poly [-1, 0, 1, 0, 0, 1, 0, 0, 1, -1],
    poly [-19217, -15857, -6726, -889, -2343, -3671, -5162, -9972, -17869, -1556, -5010, 6518, -9037,
      -5280, -4685, -7701, 1335, 6974],
    poly [21216, -37073, 28348, 2477, -10585, 12052, -3397, -12613, 6974],
    poly [1650, 1361, 577, 76, 201, 315, 443, 856, 1534, 133, 430, -560, 776, 453, 402, 661, -115, -599],
    poly [-1822, 3184, -2435, -212, 909, -1035, 292, 1083, -599],
    poly [-19576, -4198, -665, -1386, 1793, 15652, -2278, -3471, -1],
    poly [-1681, -360, -57, -119, 154, 1344, -196, -298],
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
theorem certificado_40471 :
    haveI : Fact (Nat.Prime 40471) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 40471 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((40471 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((40471 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((40471 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 40471) := ⟨by norm_num⟩
  have hP : poly [-2050, 1] = X - C (2050 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((40471 : ℕ) : ℤ[X]) = poly [40471] := by simp [poly]
  refine ⟨X - C (2050 : ℤ),
    poly [612, -9693, -16509, -13630, 5146, 7998, 2827, 10741, -16578, -11873, -17892, -17125, -877,
      11213, 18326, -4433, 2051, 1],
    poly [31, -491, -836, -690, 261, 405, 143, 544, -840, -601, -906, -867, -44, 568, 928, -225, 104],
    poly [1, 0, -1, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [8810, -267, 10330, 326, 11653, 70, 6441, -7395, 1798, 1151, -7595, 2785, 4172, 5219, 11991,
      -4431, 9025, -10434],
    poly [31661, -31394, -1787, 927, -730, 1579, 4956, 2253, 5988, -13456, 19459, -10434],
    poly [-446, 14, -523, -16, -590, -3, -326, 375, -91, -58, 385, -141, -211, -264, -607, 225, -457,
      529],
    poly [-1604, 1591, 90, -47, 37, -80, -251, -114, -303, 682, -986, 529],
    poly [612, -10305, -7428, 13184, -14879, -27, 16524, 5062, 17711, 6484, -2050, -1],
    poly [31, -522, -376, 668, -754, -1, 837, 256, 897, 328, -104],
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
theorem certificado_40699 :
    haveI : Fact (Nat.Prime 40699) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 40699 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((40699 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((40699 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((40699 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 40699) := ⟨by norm_num⟩
  have hP : poly [-835, 1] = X - C (835 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((40699 : ℕ) : ℤ[X]) = poly [40699] := by simp [poly]
  refine ⟨X - C (835 : ℤ),
    poly [12624, -16167, -653, -5801, -13752, -4062, 10572, 3717, 15163, 2309, 4292, 785, -7359, -3177,
      -10142, 6178, 836, 1],
    poly [259, -332, -13, -119, -282, -83, 217, 76, 311, 47, 88, 16, -151, -65, -208, 127, 17],
    poly [1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1],
    poly [3318, -3843, 4142, 12925, 409, 8875, 9665, 7960, 2109, -3552, -6532, 7112, 3424, 1080, 3563,
      -3599, 17010, -2998],
    poly [37381, -36856, -824, -20086, 10894, -3935, -18039, 10113, 2933, 9898, -6422, -1080, -3563,
      3599, -17010, 2998],
    poly [-68, 79, -85, -265, -8, -182, -198, -163, -43, 73, 134, -146, -70, -22, -73, 74, -349, 62],
    poly [-767, 757, 16, 412, -224, 81, 370, -208, -60, -203, 132, 22, 73, -74, 349, -62],
    poly [12624, -16167, -13277, -17709, -1191, 17253, 19176, 12452, -1886, -51, -7360, -3177, -10142,
      6178, 836, 1],
    poly [259, -332, -272, -363, -24, 354, 393, 255, -39, -1, -151, -65, -208, 127, 17],
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
theorem certificado_40813 :
    haveI : Fact (Nat.Prime 40813) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 40813 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((40813 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((40813 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((40813 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 40813) := ⟨by norm_num⟩
  have hP : poly [-2106, 1] = X - C (2106 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((40813 : ℕ) : ℤ[X]) = poly [40813] := by simp [poly]
  refine ⟨X - C (2106 : ℤ),
    poly [8275, 16864, -1678, 17305, -18596, -15648, -4174, 20327, -7277, -14538, -6499, -4034, 4591,
      14653, 10123, -11274, 2107, 1],
    poly [427, 870, -87, 893, -960, -807, -215, 1049, -376, -750, -335, -208, 237, 756, 522, -582, 109],
    poly [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 2],
    poly [-5281, -15729, -463, -10378, 2117, -14679, 3956, -9155, 3416, 10728, -11206, -2767, -4449,
      -3132, -4236, -10748, 2892, -20163],
    poly [46094, -30365, -15266, 15196, -2047, 1530, -8720, 616, 4225, -25947, 40326],
    poly [273, 812, 24, 536, -109, 758, -204, 473, -176, -553, 579, 143, 230, 162, 219, 555, -149, 1041],
    poly [-2379, 1568, 787, -785, 106, -79, 450, -32, -218, 1339, -2082],
    poly [8275, 8589, -18542, -13555, 13501, -15594, -10356, -11400, 16157, 4213, 2],
    poly [427, 443, -957, -699, 697, -805, -534, -588, 834, 217],
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
theorem certificado_40927 :
    haveI : Fact (Nat.Prime 40927) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 40927 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((40927 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((40927 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((40927 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 40927) := ⟨by norm_num⟩
  have hP : poly [-2865, 1] = X - C (2865 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((40927 : ℕ) : ℤ[X]) = poly [40927] := by simp [poly]
  refine ⟨X - C (2865 : ℤ),
    poly [-11171, -15989, -18862, 14550, 5762, 18887, -3179, 856, 15214, 15519, -15194, -19076, -2278,
      -2115, 17970, -15236, 2866, 1],
    poly [-782, -1119, -1320, 1019, 403, 1322, -223, 60, 1065, 1086, -1064, -1335, -159, -148, 1258,
      -1067, 201],
    poly [1, 0, 0, 0, 1, 1, 1, -1],
    poly [-3927, 1300, -10712, 2869, -169, -9184, 5598, -5125, 1571, -11969, -1117, 801, -18969, 13380,
      -1351, 6115, -425, -4070],
    poly [44854, -46154, 12012, -13581, 6965, 7715, -4070],
    poly [275, -91, 750, -201, 12, 643, -392, 359, -110, 838, 78, -56, 1328, -937, 95, -428, 30, 285],
    poly [-3140, 3232, -842, 951, -488, -540, 285],
    poly [-11171, -4818, -2873, -7515, -19959, -2864, -1],
    poly [-782, -337, -201, -526, -1397, -200],
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
theorem certificado_41117 :
    haveI : Fact (Nat.Prime 41117) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 41117 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((41117 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((41117 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((41117 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 41117) := ⟨by norm_num⟩
  have hP : poly [-3265, 1] = X - C (3265 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((41117 : ℕ) : ℤ[X]) = poly [41117] := by simp [poly]
  refine ⟨X - C (3265 : ℤ),
    poly [-15326, -181, 6624, -13775, 4819, -5464, -1261, -16422, 19376, -5724, 2328, 15163, -20472,
      -5371, -15038, 14188, 3266, 1],
    poly [-1217, -14, 526, -1094, 383, -434, -100, -1304, 1539, -455, 185, 1204, -1626, -426, -1194,
      1127, 259],
    poly [1, -1, 0, -1, 0, 0, 1, 0, 0, 0, -1, -1],
    poly [15830, -5007, 2870, 6260, -10488, 3095, 782, -5402, -6701, -14547, 4882, 4422, -14531, 3396,
      8804, -60, 844, -881],
    poly [25287, -4450, -28714, 20317, -699, -22454, 3456, 7960, 821, 844, -881],
    poly [-1257, 398, -228, -497, 833, -246, -62, 429, 532, 1155, -388, -351, 1154, -270, -699, 5, -67,
      70],
    poly [-2008, 354, 2280, -1614, 56, 1783, -275, -632, -65, -67, 70],
    poly [-15326, -10646, -8340, -11878, -17269, 5435, 19559, 18304, -14187, -3266, -1],
    poly [-1217, -845, -662, -943, -1371, 432, 1553, 1453, -1127, -259],
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
theorem certificado_41231 :
    haveI : Fact (Nat.Prime 41231) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 41231 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((41231 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((41231 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((41231 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 41231) := ⟨by norm_num⟩
  have hP : poly [-2813, 1] = X - C (2813 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((41231 : ℕ) : ℤ[X]) = poly [41231] := by simp [poly]
  refine ⟨X - C (2813 : ℤ),
    poly [2609, -1157, 11359, 12067, 20290, 6603, 9940, 3448, -4865, -3754, -16183, 3512, -6917, -10116,
      7413, -569, 2814, 1],
    poly [178, -79, 775, 823, 1384, 450, 678, 235, -332, -256, -1104, 240, -472, -690, 506, -39, 192],
    poly [-1, 0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [-3243, 5389, -3373, 14711, 1819, -7449, 11397, -10465, 5020, 11035, -14320, 2351, 6417, -5410,
      10445, -557, 6885, 10508],
    poly [37988, -32599, -8762, 21327, -21524, -506, 762, -8970, 21510, -7442, -3623, 10508],
    poly [221, -368, 230, -1004, -124, 508, -778, 714, -343, -753, 977, -161, -438, 369, -713, 38, -470,
      -717],
    poly [-2592, 2225, 597, -1455, 1469, 34, -52, 612, -1468, 508, 247, -717],
    poly [-2609, 3766, -12516, 1901, -11989, -15028, -2629, 14715, -7983, 3383, -2813, -1],
    poly [-178, 257, -854, 130, -818, -1025, -179, 1004, -545, 231, -192],
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
theorem certificado_41269 :
    haveI : Fact (Nat.Prime 41269) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 41269 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((41269 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((41269 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((41269 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 41269) := ⟨by norm_num⟩
  have hP : poly [-559, 1] = X - C (559 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((41269 : ℕ) : ℤ[X]) = poly [41269] := by simp [poly]
  refine ⟨X - C (559 : ℤ),
    poly [-16168, 18723, -10819, 1531, 16909, 2688, -12841, -5117, -3479, -14993, -8886, 13642, 6152,
      -8922, 9360, -17111, 560, 1],
    poly [-219, 254, -147, 21, 229, 36, -174, -69, -47, -203, -120, 185, 83, -121, 127, -232, 8],
    poly [1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    poly [7305, 2667, 1256, 9965, 7249, 5177, 15509, 6373, -2724, -304, 3244, 3398, 17130, 8886, 18764,
      15238, -641, 2136],
    poly [33964, -36631, 1411, -8709, -4589, -595, -4283, -5467, 7742, -3526, -15879, 2777, -2136],
    poly [-99, -36, -17, -135, -98, -70, -210, -86, 37, 4, -44, -46, -232, -120, -254, -206, 9, -29],
    poly [-460, 497, -20, 118, 62, 8, 58, 74, -105, 48, 215, -38, 29],
    poly [-16168, -6378, 11727, 12350, -790, 4502, -10180, 15633, -18281, -14798, -17671, 559, 1],
    poly [-219, -86, 159, 167, -11, 61, -138, 212, -248, -200, -239, 8],
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
theorem certificado_41611 :
    haveI : Fact (Nat.Prime 41611) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 41611 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((41611 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((41611 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((41611 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 41611) := ⟨by norm_num⟩
  have hP : poly [-4115, 1] = X - C (4115 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((41611 : ℕ) : ℤ[X]) = poly [41611] := by simp [poly]
  refine ⟨X - C (4115 : ℤ),
    poly [-11012, -20702, 5233, -16451, 4870, -19151, -17276, -8832, 17522, -8955, -5402, 5894, -19444,
      1866, -18454, 1664, 4116, 1],
    poly [-1089, -2047, 518, -1627, 482, -1894, -1708, -873, 1733, -886, -534, 583, -1923, 185, -1825,
      165, 407],
    poly [-1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1],
    poly [15348, 3642, 8048, 8494, 9748, 3944, 4792, 22104, 246, 19585, 15555, -5479, 16550, 7768, 4348,
      1263, 25430, 8478],
    poly [56959, -53317, 4406, -14902, 12960, -10210, 402, 710, -4348, -1263, -25430, -8478],
    poly [-1518, -360, -796, -840, -964, -390, -474, -2186, -24, -1937, -1538, 542, -1637, -768, -430,
      -125, -2515, -838],
    poly [-5633, 5274, -437, 1474, -1282, 1010, -40, -70, 430, 125, 2515, 838],
    poly [11012, 9690, 15676, 10672, 10600, 8345, 18052, 1865, -18454, 1664, 4116, 1],
    poly [1089, 958, 1550, 1055, 1048, 825, 1785, 184, -1825, 165, 407],
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
theorem certificado_41687 :
    haveI : Fact (Nat.Prime 41687) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 41687 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((41687 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((41687 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((41687 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 41687) := ⟨by norm_num⟩
  have hP : poly [-145, 1] = X - C (145 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((41687 : ℕ) : ℤ[X]) = poly [41687] := by simp [poly]
  refine ⟨X - C (145 : ℤ),
    poly [-575, 2296, -14359, -2974, -1458, -5185, 19514, 6172, 4930, -541, -19841, 13088, -20322,
      -13365, -15042, -20516, 146, 1],
    poly [-2, 8, -50, -10, -5, -18, 68, 21, 17, -2, -69, 46, -71, -46, -52, -71, 1],
    poly [-1, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1, -1],
    poly [-7173, -4635, -4330, 4297, 4069, -1970, -14374, -18197, -7011, 5141, -10875, -7248, -6073,
      2560, 5782, -17483, -13331, -2090],
    poly [34514, -39149, 305, 8627, -7401, -3501, -19272, 169, 13801, 7872, -17483, -13331, -2090],
    poly [25, 16, 15, -15, -14, 7, 50, 63, 24, -18, 38, 25, 21, -9, -20, 61, 46, 7],
    poly [-120, 137, -2, -30, 26, 12, 67, -1, -48, -27, 61, 46, 7],
    poly [575, -2871, 16655, -11385, -941, 856, -7469, -339, 13510, 15043, 20516, -146, -1],
    poly [2, -10, 58, -40, -3, 3, -26, -1, 47, 52, 71, -1],
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
theorem certificado_41801 :
    haveI : Fact (Nat.Prime 41801) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 41801 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((41801 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((41801 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((41801 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 41801) := ⟨by norm_num⟩
  have hP : poly [-2652, 1] = X - C (2652 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((41801 : ℕ) : ℤ[X]) = poly [41801] := by simp [poly]
  refine ⟨X - C (2652 : ℤ),
    poly [18615, -11121, -4323, -17466, 20027, -2672, 14705, -2012, 18299, 19079, 4326, -1149, 5138,
      15433, -10208, 13189, 2653, 1],
    poly [1181, -706, -274, -1108, 1271, -170, 933, -128, 1161, 1210, 274, -73, 326, 979, -648, 837, 168],
    poly [1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1],
    poly [4941, -9574, -14513, 4573, -14618, -5499, -1823, -2326, -2405, 5145, -3143, -9514, -2786,
      -8710, -4488, -11138, 5851, -19819],
    poly [36860, -27286, 9880, -33601, 14252, 5026, -8352, 14561, -15331, 11138, -5851, 19819],
    poly [-313, 608, 921, -290, 928, 349, 116, 148, 153, -326, 200, 604, 177, 553, 285, 707, -371, 1258],
    poly [-2339, 1732, -627, 2132, -905, -319, 530, -924, 973, -707, 371, -1258],
    poly [18615, 12065, -11817, 16593, -11106, 9059, -8051, 12780, -10209, 13189, 2653, 1],
    poly [1181, 765, -750, 1053, -705, 575, -511, 811, -648, 837, 168],
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
theorem certificado_41953 :
    haveI : Fact (Nat.Prime 41953) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 41953 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((41953 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((41953 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((41953 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 41953) := ⟨by norm_num⟩
  have hP : poly [-641, 1] = X - C (641 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((41953 : ℕ) : ℤ[X]) = poly [41953] := by simp [poly]
  refine ⟨X - C (641 : ℤ),
    poly [4516, -582, -10211, 11045, 7413, 5902, -8761, 7513, 15785, -2397, 5494, -12165, -16774, -11218,
      -14220, -8007, 642, 1],
    poly [69, -9, -156, 169, 113, 90, -134, 115, 241, -37, 84, -186, -256, -171, -217, -122, 10],
    poly [-1, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0, -1],
    poly [-16046, -5141, 701, 6666, 2552, -3803, -475, -10549, 6583, -197, -7407, -2575, -8327, -1202,
      249, -7799, 5671, 7001],
    poly [25907, -31048, 5842, 5965, -20160, 4550, -6876, -9250, 13719, -6469, -1330, 7001],
    poly [245, 78, -11, -102, -39, 58, 7, 161, -101, 3, 113, 39, 127, 18, -4, 119, -87, -107],
    poly [-396, 475, -90, -91, 308, -70, 105, 141, -210, 99, 20, -107],
    poly [-4516, 5098, 9629, 20697, -884, 6609, 19776, 5005, 5571, 8648, -641, -1],
    poly [-69, 78, 147, 316, -14, 101, 302, 76, 85, 132, -10],
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
theorem certificado_42181 :
    haveI : Fact (Nat.Prime 42181) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 42181 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((42181 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((42181 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((42181 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 42181) := ⟨by norm_num⟩
  have hP : poly [-2260, 1] = X - C (2260 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((42181 : ℕ) : ℤ[X]) = poly [42181] := by simp [poly]
  refine ⟨X - C (2260 : ℤ),
    poly [-7447, 2759, -3321, -20868, -16639, 9698, -313, -18403, -8519, -8216, 12632, -573, -14297,
      -12362, 13862, 5960, 2261, 1],
    poly [-399, 148, -178, -1118, -891, 520, -17, -986, -456, -440, 677, -31, -766, -662, 743, 319, 121],
    poly [0, -1, 0, 0, -1, 0, -1, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0, -1],
    poly [8916, 13474, 1195, 7890, 7613, 11663, 12598, 15678, 5974, -3661, -5625, 5274, 13883, 9986,
      9555, 5654, 17616, 12358],
    poly [42181, -33265, 4558, -12279, 15611, 4281, 687, 12188, -560, 14515, -7782, 13056, 827, 9159,
      396, 5258, 12358],
    poly [-478, -722, -64, -423, -408, -625, -675, -840, -320, 196, 301, -283, -744, -535, -512, -303,
      -944, -662],
    poly [-2260, 1783, -245, 658, -837, -229, -37, -653, 30, -778, 417, -700, -44, -491, -21, -282, -662],
    poly [0, 7447, -10206, 6080, -17187, -14435, -12810, 17352, -14793, 20748, 8800, -8227, -19657,
      -10162, -3700, -2260, -1],
    poly [0, 399, -547, 326, -921, -773, -686, 930, -793, 1112, 471, -441, -1053, -544, -198, -121],
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
theorem certificado_42257 :
    haveI : Fact (Nat.Prime 42257) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 42257 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((42257 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((42257 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((42257 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 42257) := ⟨by norm_num⟩
  have hP : poly [-9092, 1] = X - C (9092 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((42257 : ℕ) : ℤ[X]) = poly [42257] := by simp [poly]
  refine ⟨X - C (9092 : ℤ),
    poly [17573, -20857, 416, 17666, -7123, -17439, -16901, -5607, 6060, 12833, -13384, 12143, -15773,
      -9418, -582, 18865, 9093, 1],
    poly [3781, -4488, 90, 3801, -1533, -3752, -3636, -1206, 1304, 2761, -2880, 2613, -3394, -2026, -125,
      4059, 1956],
    poly [-1, -1, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [-6738, -3978, 5578, 7308, -11199, 2440, 5997, -3061, -8946, 5280, 4194, -11692, 3244, -8857,
      4792, 1647, -3424, -10754],
    poly [35519, -46235, 5578, 7308, -4461, 6418, -6319, -7609, 5071, 7330, -10754],
    poly [1450, 856, -1200, -1572, 2410, -525, -1290, 659, 1925, -1136, -902, 2516, -698, 1906, -1031,
      -354, 737, 2314],
    poly [-7642, 9949, -1201, -1572, 960, -1381, 1360, 1637, -1091, -1577, 2314],
    poly [-17573, 20857, -416, -17666, -17561, -3418, -256, 19446, -9772, -9092, -1],
    poly [-3781, 4488, -90, -3801, -3778, -735, -55, 4184, -2103, -1956],
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
theorem certificado_42409 :
    haveI : Fact (Nat.Prime 42409) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 42409 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((42409 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((42409 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((42409 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 42409) := ⟨by norm_num⟩
  have hP : poly [-3891, 1] = X - C (3891 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((42409 : ℕ) : ℤ[X]) = poly [42409] := by simp [poly]
  refine ⟨X - C (3891 : ℤ),
    poly [2921, -5111, 4184, -4751, 12849, 2957, 16960, -3527, -99, -4763, 5492, -8609, 1273, 16480,
      -944, 3760, 3892, 1],
    poly [268, -469, 384, -436, 1179, 271, 1556, -324, -9, -437, 504, -790, 117, 1512, -87, 345, 357],
    poly [-2, 0, -1, 0, 0, -1, 0, -1, 0, -1, -1],
    poly [1457, -13540, -15800, 12265, 10997, -17167, -23583, 15184, 8807, -23936, -13928, 14914, -8294,
      -29717, -6409, 19777, -6102, -28790],
    poly [45323, -72403, -3063, 41133, -4796, -26806, -29097, 48567, -6102, -28790],
    poly [-133, 1243, 1450, -1125, -1008, 1576, 2164, -1393, -807, 2197, 1278, -1368, 762, 2727, 588,
      -1814, 561, 2642],
    poly [-4157, 6644, 280, -3774, 441, 2460, 2669, -4456, 561, 2642],
    poly [-5842, 16064, 20898, -16507, -2086, -16611, 4835, -3759, -3892, -1],
    poly [-536, 1474, 1917, -1515, -191, -1524, 444, -345, -357],
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
theorem certificado_42751 :
    haveI : Fact (Nat.Prime 42751) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 42751 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((42751 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((42751 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((42751 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 42751) := ⟨by norm_num⟩
  have hP : poly [-4551, 1] = X - C (4551 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((42751 : ℕ) : ℤ[X]) = poly [42751] := by simp [poly]
  refine ⟨X - C (4551 : ℤ),
    poly [6322, 10823, -15084, -10111, 15319, -9381, 17367, -3284, -9216, 261, -19182, -9661, -8015,
      17217, 4494, -18082, 4552, 1],
    poly [673, 1152, -1606, -1076, 1631, -999, 1849, -350, -981, 28, -2042, -1028, -853, 1833, 478,
      -1925, 485],
    poly [-1, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0, -1, 0, -1],
    poly [-2880, -7446, 1881, -9784, -9129, -3192, -1528, -4590, -12829, 3411, -20718, -12748, 4341,
      -540, -9080, -13713, -8322, -17677],
    poly [39871, -47317, 6447, -19111, 2536, -3847, -4585, 1192, -14528, 13988, -23068, 9355, -17677],
    poly [307, 793, -200, 1042, 972, 340, 163, 489, 1366, -363, 2206, 1357, -462, 58, 967, 1460, 886,
      1882],
    poly [-4244, 5038, -687, 2035, -270, 410, 488, -127, 1547, -1489, 2456, -996, 1882],
    poly [-6322, -4501, 19585, -15796, -10346, -7940, 7006, -1896, 9910, 15624, -20118, -4551, -1],
    poly [-673, -479, 2085, -1682, -1101, -845, 746, -202, 1055, 1663, -2142, -484],
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
theorem certificado_42979 :
    haveI : Fact (Nat.Prime 42979) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 42979 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((42979 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((42979 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((42979 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 42979) := ⟨by norm_num⟩
  have hP : poly [-1553, 1] = X - C (1553 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((42979 : ℕ) : ℤ[X]) = poly [42979] := by simp [poly]
  refine ⟨X - C (1553 : ℤ),
    poly [-7915, 8242, -14607, -8810, 15852, 4964, -661, 3708, -13752, 10812, -2124, -14586, -14511,
      20387, 12024, 6539, 1554, 1],
    poly [-286, 298, -528, -318, 573, 179, -24, 134, -497, 391, -77, -527, -524, 737, 434, 236, 56],
    poly [-1, -1, 0, 0, 0, 0, -1, 0, 0, -1, -1, 0, -1],
    poly [-1638, 13250, 3352, 11399, 8526, 4622, 6363, -9881, 12027, -6418, 1070, 549, 2818, -3269,
      -2415, 9292, 7473, 8053],
    poly [41341, -29729, 4990, -1851, 5174, -6777, -3801, 385, -4234, 9872, -580, 8053],
    poly [59, -479, -121, -412, -308, -167, -230, 357, -435, 232, -39, -20, -102, 118, 87, -336, -270,
      -291],
    poly [-1494, 1075, -181, 67, -187, 245, 137, -14, 153, -357, 21, -291],
    poly [7915, -8242, 6692, 17052, 12520, -13774, -18551, -14901, -7039, -4986, -1553, -1],
    poly [286, -298, 242, 616, 452, -498, -670, -538, -254, -180, -56],
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
theorem certificado_43093 :
    haveI : Fact (Nat.Prime 43093) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43093 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43093 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43093 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43093 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43093) := ⟨by norm_num⟩
  have hP : poly [-1820, 1] = X - C (1820 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43093 : ℕ) : ℤ[X]) = poly [43093] := by simp [poly]
  refine ⟨X - C (1820 : ℤ),
    poly [14609, -11736, -1214, -4381, -19560, 16966, -13842, -3062, 16833, -10030, -16414, -5810, -311,
      -9850, -17361, -3940, 1821, 1],
    poly [617, -496, -51, -185, -826, 717, -585, -129, 711, -424, -693, -245, -13, -416, -733, -166, 77],
    poly [1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, -1],
    poly [-12639, -22993, -17837, -15277, -9593, -6938, -10133, -4097, -15743, -10493, -2203, -19483,
      -14757, -21905, -11112, -8762, 5209, -8682],
    poly [55732, -20100, 5198, 4923, 14749, 9498, 3178, -16241, -5289, 13891, -8682],
    poly [534, 971, 753, 645, 405, 293, 428, 173, 665, 443, 93, 823, 623, 925, 469, 370, -220, 367],
    poly [-2354, 850, -220, -208, -623, -401, -134, 686, 223, -587, 367],
    poly [14609, -11736, -15823, -21129, 13011, 20133, -13272, 15241, 5762, -1820, -1],
    poly [617, -496, -668, -892, 550, 850, -561, 644, 243, -77],
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
theorem certificado_43207 :
    haveI : Fact (Nat.Prime 43207) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43207 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43207 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43207 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43207 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43207) := ⟨by norm_num⟩
  have hP : poly [-551, 1] = X - C (551 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43207 : ℕ) : ℤ[X]) = poly [43207] := by simp [poly]
  refine ⟨X - C (551 : ℤ),
    poly [6038, 15302, -10872, 19741, 17993, -13298, 20756, -18390, 2868, 15061, 18455, 5601, 18281,
      19245, -11649, 1704, 552, 1],
    poly [77, 195, -139, 252, 229, -170, 265, -235, 37, 192, 235, 71, 233, 245, -149, 22, 7],
    poly [-1, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 1],
    poly [-6120, 4455, 12551, -3980, 2028, 19604, 12108, -7980, 1315, 3998, 6669, -4618, 8849, 10677,
      -9002, -6450, 9473, 1974],
    poly [37087, -32632, 1976, -5956, 14104, -5075, 9087, 5584, -14732, -11397, 23422, -5525, -1974],
    poly [78, -57, -160, 51, -26, -250, -154, 102, -17, -51, -85, 59, -113, -136, 115, 82, -121, -25],
    poly [-473, 417, -26, 76, -180, 65, -116, -71, 188, 145, -299, 71, 25],
    poly [-6038, -9264, 20136, 3330, -15285, -5360, 1637, 10197, 489, -14506, 601, 550, 1],
    poly [-77, -118, 257, 42, -195, -68, 21, 130, 6, -185, 8, 7],
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
theorem certificado_43283 :
    haveI : Fact (Nat.Prime 43283) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43283 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43283 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43283 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43283 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43283) := ⟨by norm_num⟩
  have hP : poly [-2439, 1] = X - C (2439 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43283 : ℕ) : ℤ[X]) = poly [43283] := by simp [poly]
  refine ⟨X - C (2439 : ℤ),
    poly [12866, -6898, -10899, 2480, 4757, 11466, -226, 20621, -15413, -6182, -3676, -37, 12795, -2355,
      14196, 21390, 2440, 1],
    poly [725, -389, -614, 140, 268, 646, -13, 1162, -869, -348, -207, -2, 721, -133, 800, 1205, 137],
    poly [-1, -1, -1, -1, -1, 0, -1, 0, 0, 0, -1, -1],
    poly [-3213, -20, -5591, -5753, 955, 2129, 3212, 6460, -14213, -9430, 918, 2058, 7755, -11728, 4697,
      -11747, -10547, 2284],
    poly [40070, -43303, -5591, -5753, 955, 5342, 19, 15244, -14031, -10547, 2284],
    poly [181, 1, 315, 324, -54, -120, -181, -364, 801, 531, -52, -116, -437, 661, -265, 662, 594, -129],
    poly [-2258, 2441, 314, 324, -54, -301, -1, -859, 791, 594, -129],
    poly [-12866, 6898, 10899, -2480, -4757, 1400, -19538, -11756, -21389, -2440, -1],
    poly [-725, 389, 614, -140, -268, 79, -1101, -662, -1205, -137],
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
theorem certificado_43321 :
    haveI : Fact (Nat.Prime 43321) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43321 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43321 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43321 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43321 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43321) := ⟨by norm_num⟩
  have hP : poly [-1840, 1] = X - C (1840 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43321 : ℕ) : ℤ[X]) = poly [43321] := by simp [poly]
  refine ⟨X - C (1840 : ℤ),
    poly [17917, 7638, 18910, 20988, 2201, 4710, 18155, -11150, -3985, -19167, -15832, 13953, -15814,
      -5306, -4076, 8403, 1841, 1],
    poly [761, 324, 803, 891, 93, 200, 771, -474, -169, -814, -672, 593, -672, -225, -173, 357, 78],
    poly [1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1],
    poly [10030, -1972, -7582, 2068, -2871, -15611, -11380, -6457, -10292, -5703, -3558, -9796, -11730,
      -17052, -12299, -2714, -12715, -454],
    poly [33291, -31319, -4420, 2352, 519, 15092, 6318, -1833, 4543, -6802, -569, 14338, -416, 2260,
      12715, 454],
    poly [-426, 84, 322, -88, 122, 663, 483, 274, 437, 242, 151, 416, 498, 724, 522, 115, 540, 19],
    poly [-1414, 1331, 187, -100, -22, -641, -268, 78, -193, 289, 24, -609, 18, -96, -540, -19],
    poly [17917, -10279, -14132, -8201, 10402, -5692, 5930, 18603, 1823, 19260, -11738, -13709, -5917,
      8402, 1841, 1],
    poly [761, -437, -600, -348, 442, -242, 252, 790, 77, 818, -499, -582, -251, 357, 78],
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
theorem certificado_43397 :
    haveI : Fact (Nat.Prime 43397) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43397 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43397 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43397 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43397 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43397) := ⟨by norm_num⟩
  have hP : poly [-1674, 1] = X - C (1674 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43397 : ℕ) : ℤ[X]) = poly [43397] := by simp [poly]
  refine ⟨X - C (1674 : ℤ),
    poly [-3759, 13582, 16107, 3639, 5187, 8921, -15601, -18571, 13625, 4156, -4275, -16594, -19116,
      4629, -5545, -16854, 1675, 1],
    poly [-145, 524, 621, 140, 200, 344, -602, -716, 526, 160, -165, -640, -737, 179, -214, -650, 65],
    poly [-1, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, 0, 0, -1],
    poly [1096, -1755, 395, 10403, 5276, 1151, -11995, 1374, 1719, -3336, 2805, -380, 4777, -8519, 5161,
      2836, -14042, -12030],
    poly [44493, -46248, 3246, 8253, -5828, 8033, -7169, 1266, -13680, 2325, 16878, -2012, -12030],
    poly [-42, 68, -15, -401, -203, -44, 463, -53, -66, 129, -108, 15, -184, 329, -199, -109, 542, 464],
    poly [-1716, 1785, -126, -318, 225, -310, 277, -49, 528, -90, -651, 78, 464],
    poly [3759, -17341, 1234, -1114, -21414, 6209, -4196, -19653, -10174, -11309, 18529, -1674, -1],
    poly [145, -669, 48, -43, -826, 240, -162, -758, -392, -436, 715, -65],
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
theorem certificado_43777 :
    haveI : Fact (Nat.Prime 43777) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43777 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43777 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43777 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43777 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43777) := ⟨by norm_num⟩
  have hP : poly [-1099, 1] = X - C (1099 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43777 : ℕ) : ℤ[X]) = poly [43777] := by simp [poly]
  refine ⟨X - C (1099 : ℤ),
    poly [239, -13105, -19610, 2890, 9961, -16482, -493, -13265, 18630, 12923, 19809, -6196, -7335, 2224,
      -5973, -16855, 1100, 1],
    poly [6, -329, -492, 73, 250, -414, -12, -333, 468, 324, 497, -156, -184, 56, -150, -423, 28],
    poly [-1, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, -1, -1],
    poly [-1319, 7483, 5101, 5298, 1992, 4140, 16092, 5069, 12946, 12754, 14865, -8117, 12456, -1467,
      -922, 154, 5652, 4940],
    poly [42458, -36294, 6420, -2185, -3109, -2477, 21583, 7349, -6650, 13378, -1621, -6574, -4786, 5652,
      4940],
    poly [33, -188, -128, -133, -50, -104, -404, -127, -325, -320, -373, 204, -313, 37, 23, -4, -142,
      -124],
    poly [-1066, 912, -162, 55, 78, 62, -542, -184, 167, -336, 41, 165, 120, -142, -124],
    poly [-239, 13105, 19849, -15995, 14206, 19133, -20218, 16632, 8420, 1362, -19079, 7073, 16856,
      -1100, -1],
    poly [-6, 329, 498, -402, 357, 480, -508, 418, 211, 34, -479, 178, 423, -28],
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
theorem certificado_43853 :
    haveI : Fact (Nat.Prime 43853) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43853 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43853 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43853 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43853 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43853) := ⟨by norm_num⟩
  have hP : poly [-1230, 1] = X - C (1230 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43853 : ℕ) : ℤ[X]) = poly [43853] := by simp [poly]
  refine ⟨X - C (1230 : ℤ),
    poly [-6881, 6198, 16441, -17100, -14382, 6798, -20994, -14813, -20762, 2871, 14620, -5443, -9702,
      21776, -11926, -20724, 1231, 1],
    poly [-193, 174, 461, -480, -403, 191, -589, -415, -582, 81, 410, -153, -272, 611, -335, -581, 35],
    poly [-2, 0, -1, 0, -1, 0, 0, 0, -1],
    poly [-29992, 11127, 11410, -14652, 11496, 7025, -16973, 3187, 17108, -11296, -6399, 10754, -11729,
      -3868, 16924, -5663, -11778, 9787],
    poly [-16131, 38385, -29426, -11005, 22587, 6115, -21565, 9787],
    poly [841, -313, -320, 411, -323, -197, 476, -90, -480, 317, 179, -302, 329, 108, -475, 159, 330,
      -275],
    poly [452, -1077, 826, 308, -634, -171, 605, -275],
    poly [13762, 17695, -13605, 10150, -8798, -21898, -1230, -1],
    poly [386, 496, -382, 285, -247, -614, -34],
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
theorem certificado_43891 :
    haveI : Fact (Nat.Prime 43891) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 43891 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((43891 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((43891 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((43891 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 43891) := ⟨by norm_num⟩
  have hP : poly [-314, 1] = X - C (314 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((43891 : ℕ) : ℤ[X]) = poly [43891] := by simp [poly]
  refine ⟨X - C (314 : ℤ),
    poly [12720, -3454, 12709, 4793, 10359, 7022, 11065, -19534, 18249, -18952, -11103, 1642, 18596, 199,
      -16773, 11129, 315, 1],
    poly [91, -25, 91, 34, 74, 50, 79, -140, 131, -136, -79, 12, 133, 1, -120, 80, 2],
    poly [1, 0, 0, 0, -1, -1, 1, 0, -1, -1, -1],
    poly [13650, 18446, 21816, 36923, 30681, 30102, 21294, 5331, 14925, -3775, 14896, 13977, 28651,
      43794, 18542, 29644, 9551, 15218],
    poly [30241, -48687, -3370, -15107, 19892, 19025, 3324, 29644, 9551, 15218],
    poly [-98, -132, -156, -264, -219, -215, -152, -38, -107, 27, -107, -100, -205, -313, -132, -212,
      -68, -109],
    poly [-216, 349, 23, 108, -143, -136, -23, -212, -68, -109],
    poly [12720, -16174, 16163, -7916, -7154, 117, 16774, -11129, -315, -1],
    poly [91, -116, 116, -57, -51, 1, 120, -80, -2],
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
theorem certificado_44119 :
    haveI : Fact (Nat.Prime 44119) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 44119 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((44119 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((44119 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((44119 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 44119) := ⟨by norm_num⟩
  have hP : poly [-4496, 1] = X - C (4496 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((44119 : ℕ) : ℤ[X]) = poly [44119] := by simp [poly]
  refine ⟨X - C (4496 : ℤ),
    poly [-15161, -11092, 655, -11481, 14972, -16924, -3821, -17095, 6669, 16919, -14068, 15256, 9257,
      -12323, -199, 12011, 4497, 1],
    poly [-1545, -1130, 67, -1170, 1526, -1725, -389, -1742, 680, 1724, -1434, 1555, 943, -1256, -20,
      1224, 458],
    poly [-1, 0, -1, 0, 0, 0, -1, 0, 0, 1, -1],
    poly [-10539, 6700, 6223, 9942, 9619, 9825, 542, 589, 7252, -7515, 13923, 10768, 2809, 1875, 3700,
      9912, -4021, -462],
    poly [33580, -26880, -11016, 20958, -800, 3925, -20145, 17492, -3097, -462],
    poly [1074, -683, -634, -1013, -980, -1001, -55, -60, -739, 766, -1419, -1097, -286, -191, -377,
      -1010, 410, 47],
    poly [-3422, 2740, 1122, -2136, 82, -400, 2053, -1783, 316, 47],
    poly [15161, -4069, 3414, 8067, 5919, -87, 19724, -3018, -4495, -1],
    poly [1545, -415, 348, 822, 603, -9, 2010, -308, -458],
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
theorem certificado_44537 :
    haveI : Fact (Nat.Prime 44537) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 44537 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((44537 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((44537 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((44537 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 44537) := ⟨by norm_num⟩
  have hP : poly [-1263, 1] = X - C (1263 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((44537 : ℕ) : ℤ[X]) = poly [44537] := by simp [poly]
  refine ⟨X - C (1263 : ℤ),
    poly [-19183, 2559, -9660, -8506, -6213, -22150, 4884, 9278, -9161, -11644, 11557, 18099, 8019,
      -21504, 15816, -6899, 1264, 1],
    poly [-544, 73, -274, -241, -176, -628, 139, 263, -260, -330, 328, 513, 227, -610, 449, -196, 36],
    poly [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 2, 0, 1, 1, 1, 1],
    poly [-13781, -3072, -21506, -17148, -13583, 9517, -6333, -2784, -19390, 873, -12934, -11076, 1338,
      -239, -11207, -17563, -2405, -8564],
    poly [58318, -41465, 7725, 27857, -4851, -5159, 9898, 25884, -10241, 13385, -8325, 11207, 17563,
      2405, 8564],
    poly [391, 87, 610, 486, 385, -270, 180, 79, 550, -25, 367, 314, -38, 7, 318, 498, 68, 243],
    poly [-1654, 1177, -220, -790, 138, 146, -281, -734, 291, -380, 236, -318, -498, -68, -243],
    poly [-19183, 2559, 9523, 14289, 6006, 21233, 2591, -19322, -17012, 6757, -21505, 15816, -6899, 1264,
      1],
    poly [-544, 73, 270, 405, 170, 602, 73, -548, -482, 192, -610, 449, -196, 36],
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
theorem certificado_44651 :
    haveI : Fact (Nat.Prime 44651) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 44651 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((44651 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((44651 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((44651 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 44651) := ⟨by norm_num⟩
  have hP : poly [-1410, 1] = X - C (1410 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((44651 : ℕ) : ℤ[X]) = poly [44651] := by simp [poly]
  refine ⟨X - C (1410 : ℤ),
    poly [-14852, -20816, -10560, 6991, 1905, 14125, -750, 8898, 15935, 1468, -1804, -17260, -18981,
      5750, 11436, -19784, 1411, 1],
    poly [-469, -657, -333, 221, 60, 446, -24, 281, 503, 46, -57, -545, -599, 182, 361, -625, 45],
    poly [0, 1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1, 1, 0, -1],
    poly [-13514, -17197, -19638, -16758, -18656, -32971, -11289, -13237, -11085, -19697, -6, -13324,
      -8330, -2753, -754, -4521, -4302, -11237],
    poly [44651, -31137, 3683, 2441, -2880, 1898, 27829, -17999, -9125, -8715, 8069, 11018, 6935, -11237],
    poly [427, 543, 620, 529, 589, 1041, 356, 418, 350, 622, 0, 421, 263, 87, 24, 143, 136, 355],
    poly [-1410, 984, -117, -77, 91, -60, -879, 569, 288, 275, -255, -348, -219, 355],
    poly [0, -14852, -5964, 10256, 17551, -5086, -2632, -20839, -9895, -14099, 14842, 21196, -1410, -1],
    poly [0, -469, -188, 324, 554, -161, -83, -658, -312, -445, 469, 669, -45],
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
theorem certificado_44879 :
    haveI : Fact (Nat.Prime 44879) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 44879 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((44879 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((44879 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((44879 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 44879) := ⟨by norm_num⟩
  have hP : poly [-493, 1] = X - C (493 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((44879 : ℕ) : ℤ[X]) = poly [44879] := by simp [poly]
  refine ⟨X - C (493 : ℤ),
    poly [-14019, -21239, 8605, -15276, -5675, -1377, -20212, -41, -5371, -3106, 20476, -7059, -15945,
      -4675, 15375, 19148, 494, 1],
    poly [-154, -233, 95, -168, -62, -15, -222, 0, -59, -34, 225, -78, -175, -51, 169, 210, 5],
    poly [0, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1],
    poly [18641, 16403, 12302, 10382, 21302, 26513, 16510, 31328, 19979, 14403, 23677, 21420, 20232,
      15769, 10298, 10560, 3460, 10182],
    poly [44879, -26238, 16403, 12302, -8259, 23540, 11973, 2027, 8106, 4386, 21745, -1251, 9920, 7100,
      -6722, 10182],
    poly [-205, -180, -135, -114, -234, -291, -181, -344, -219, -158, -260, -235, -222, -173, -113, -116,
      -38, -112],
    poly [-493, 289, -181, -135, 91, -259, -131, -22, -89, -48, -239, 14, -109, -78, 74, -112],
    poly [0, 14019, 21239, -8605, 1257, -1545, 17202, 19971, 18247, -5607, -7385, 19557, 3772, -18654,
      -493, -1],
    poly [0, 154, 233, -95, 14, -17, 189, 219, 200, -62, -81, 215, 41, -205, -5],
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
theorem certificado_44917 :
    haveI : Fact (Nat.Prime 44917) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 44917 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((44917 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((44917 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((44917 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 44917) := ⟨by norm_num⟩
  have hP : poly [-3960, 1] = X - C (3960 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((44917 : ℕ) : ℤ[X]) = poly [44917] := by simp [poly]
  refine ⟨X - C (3960 : ℤ),
    poly [-16186, -1921, 17989, 1774, -4185, -19760, 2411, 20304, 11586, -13665, 18349, -10476, -19047,
      -640, 601, 9528, 3961, 1],
    poly [-1427, -169, 1586, 156, -369, -1742, 213, 1790, 1021, -1205, 1618, -924, -1679, -56, 53, 840,
      349],
    poly [-1, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, -1],
    poly [-1886, 14878, 13385, 13033, 20020, 10596, 11864, 8643, 22174, 19648, 8282, 18238, 3858, 9072,
      3833, 8675, 1122, 12338],
    poly [43031, -30039, 15271, -3731, 21513, 10948, 6763, 3189, 7521, 7950, -8505, 8675, 1122, 12338],
    poly [166, -1312, -1180, -1149, -1765, -934, -1046, -762, -1955, -1732, -730, -1608, -340, -800,
      -338, -765, -99, -1088],
    poly [-3794, 2649, -1347, 329, -1897, -965, -596, -281, -663, -701, 750, -765, -99, -1088],
    poly [16186, 1921, 10742, 12491, -20822, 3545, 20361, 7117, -16343, 4601, -600, -9528, -3961, -1],
    poly [1427, 169, 947, 1101, -1836, 313, 1795, 627, -1441, 406, -53, -840, -349],
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
theorem certificado_45259 :
    haveI : Fact (Nat.Prime 45259) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 45259 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((45259 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((45259 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((45259 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 45259) := ⟨by norm_num⟩
  have hP : poly [-2650, 1] = X - C (2650 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((45259 : ℕ) : ℤ[X]) = poly [45259] := by simp [poly]
  refine ⟨X - C (2650 : ℤ),
    poly [16891, -21513, 8463, -3720, -13340, -1730, 1007, -20221, 129, 10384, -628, -11426, -16178,
      5647, -5873, 10006, 2651, 1],
    poly [989, -1260, 496, -218, -781, -101, 59, -1184, 8, 608, -37, -669, -947, 331, -344, 586, 155],
    poly [-1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, -1],
    poly [-8867, 1599, 2047, -6868, -296, 12379, -5976, 4179, 7684, 3501, 9255, -10486, 11692, 11837,
      6628, 8351, 6695, 8129],
    poly [36392, -34793, 448, -8915, 6572, 21542, -28821, 9707, 3553, -289, -6473, -1434, 8129],
    poly [519, -94, -120, 402, 17, -725, 350, -245, -450, -205, -542, 614, -685, -693, -388, -489, -392,
      -476],
    poly [-2131, 2038, -27, 522, -385, -1261, 1688, -569, -208, 17, 379, 84, -476],
    poly [-16891, -6855, 15283, 12183, 9620, 5281, 4118, 5945, -4165, 18529, -7354, -2650, -1],
    poly [-989, -401, 895, 713, 563, 309, 241, 348, -244, 1085, -431, -155],
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
theorem certificado_45677 :
    haveI : Fact (Nat.Prime 45677) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 45677 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((45677 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((45677 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((45677 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 45677) := ⟨by norm_num⟩
  have hP : poly [-2563, 1] = X - C (2563 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((45677 : ℕ) : ℤ[X]) = poly [45677] := by simp [poly]
  refine ⟨X - C (2563 : ℤ),
    poly [-11994, 14520, 20162, -3004, -2817, 1888, 22563, 18080, 10807, 21515, 9543, -19814, -3679,
      -13938, -6546, -5955, 2564, 1],
    poly [-673, 815, 1131, -169, -158, 106, 1266, 1014, 606, 1207, 535, -1112, -206, -782, -367, -334,
      144],
    poly [-1, 0, -1, 0, 0, 1, 0, 0, 0, -1, 0, -1, -1],
    poly [-5399, 8981, 6349, 948, -8660, -3941, 1942, -8321, -3228, 12065, -2525, -6398, -5651, 1175,
      19035, 6745, 164, -2494],
    poly [40278, -31297, -8031, 8979, -12240, 4717, -18105, -2912, 16377, 9239, 164, -2494],
    poly [303, -504, -356, -53, 486, 221, -109, 467, 181, -677, 142, 359, 317, -66, -1068, -378, -9, 140],
    poly [-2260, 1757, 450, -504, 687, -265, 1016, 163, -919, -518, -9, 140],
    poly [11994, 19163, 6352, -3348, -5829, 6467, 5652, 5420, 9109, 5956, -2564, -1],
    poly [673, 1075, 356, -188, -327, 363, 317, 304, 511, 334, -144],
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
theorem certificado_45943 :
    haveI : Fact (Nat.Prime 45943) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 45943 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((45943 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((45943 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((45943 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 45943) := ⟨by norm_num⟩
  have hP : poly [-22, 1] = X - C (22 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((45943 : ℕ) : ℤ[X]) = poly [45943] := by simp [poly]
  refine ⟨X - C (22 : ℤ),
    poly [-6265, -21168, 13656, 2709, 12653, 13105, -3581, -21046, -3045, -16845, -9119, 16292, -22231,
      15696, 11155, 507, 23, 1],
    poly [-3, -10, 7, 1, 6, 6, -2, -10, -1, -8, -4, 8, -11, 8, 5],
    poly [-1, 0, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0, -1],
    poly [-10157, -12707, -293, -8082, -14701, 3793, 457, 4482, -1600, -18583, -13090, -10752, -18999,
      -579, -8095, -4260, -6174, -6261],
    poly [35786, -48493, 12414, -17946, -9169, 20751, -13675, -337, 2073, -24681, 7516, -3835, 1914, 87,
      -6261],
    poly [5, 6, 0, 4, 7, -2, 0, -2, 1, 9, 6, 5, 9, 0, 4, 2, 3, 3],
    poly [-17, 24, -7, 9, 4, -10, 7, 0, -1, 12, -4, 2, -1, 0, 3],
    poly [6265, 14903, 11119, 17212, 4959, 16932, -3407, -21038, 7397, -8017, -4541, -10648, -484, -22,
      -1],
    poly [3, 7, 5, 8, 2, 8, -2, -10, 4, -4, -2, -5],
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
theorem certificado_46133 :
    haveI : Fact (Nat.Prime 46133) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 46133 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((46133 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((46133 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((46133 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 46133) := ⟨by norm_num⟩
  have hP : poly [-957, 1] = X - C (957 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((46133 : ℕ) : ℤ[X]) = poly [46133] := by simp [poly]
  refine ⟨X - C (957 : ℤ),
    poly [-1639, -12246, -4978, 4960, 8393, 6854, 21748, -17476, 3790, -17784, 6441, -9297, -15532, 6829,
      -19227, -5853, 958, 1],
    poly [-34, -254, -103, 103, 174, 142, 451, -363, 79, -369, 134, -193, -322, 142, -399, -121, 20],
    poly [-1, -1, 0, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1, -1],
    poly [7229, -621, 4336, 9451, -3270, -873, 6505, 12201, -17054, 12321, -4906, -6563, -539, 335, 2698,
      483, 14605, 1797],
    poly [53362, -46754, -2893, 10072, -7606, -10324, 17004, 12453, -19223, 9571, 1649, -11907, -1314,
      14605, 1797],
    poly [-150, 13, -90, -196, 68, 18, -135, -253, 354, -256, 102, 136, 11, -7, -56, -10, -303, -37],
    poly [-1107, 971, 59, -209, 158, 214, -353, -258, 399, -199, -34, 247, 27, -303, -37],
    poly [1639, 12246, 3339, -17206, -13371, -1894, -11716, -9557, 22936, -4652, -12683, 20185, 5854,
      -958, -1],
    poly [34, 254, 69, -357, -277, -39, -243, -198, 476, -97, -263, 419, 121, -20],
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
theorem certificado_46171 :
    haveI : Fact (Nat.Prime 46171) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 46171 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((46171 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((46171 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((46171 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 46171) := ⟨by norm_num⟩
  have hP : poly [-3397, 1] = X - C (3397 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((46171 : ℕ) : ℤ[X]) = poly [46171] := by simp [poly]
  refine ⟨X - C (3397 : ℤ),
    poly [-14081, 15803, 9913, -4061, 8847, -8832, 7201, -8316, -22021, -7346, 16104, 562, 4200, -18932,
      -4219, 257, 3398, 1],
    poly [-1036, 1163, 729, -299, 651, -650, 530, -612, -1620, -540, 1185, 41, 309, -1393, -310, 19, 250],
    poly [1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 0, -1],
    poly [-4374, -2554, -39, 519, 8647, 1106, 9585, 4178, 4190, -11522, -762, -22424, 6751, -9632, 17832,
      10120, 11640, -8584],
    poly [50545, -47991, -6889, 1262, -1239, 6279, -7240, -872, -1520, 20224, -8584],
    poly [322, 188, 3, -38, -636, -81, -705, -307, -308, 848, 56, 1650, -497, 709, -1312, -744, -856,
      632],
    poly [-3719, 3532, 506, -93, 91, -462, 533, 64, 112, -1488, 632],
    poly [-14081, -16287, 8191, 2313, 4717, -19992, 11316, 4475, 3141, -3397, -1],
    poly [-1036, -1198, 603, 170, 347, -1471, 833, 329, 231, -250],
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
theorem certificado_46399 :
    haveI : Fact (Nat.Prime 46399) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 46399 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((46399 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((46399 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((46399 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 46399) := ⟨by norm_num⟩
  have hP : poly [-43, 1] = X - C (43 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((46399 : ℕ) : ℤ[X]) = poly [46399] := by simp [poly]
  refine ⟨X - C (43 : ℤ),
    poly [-22660, -527, 6462, 17415, -22255, -10229, -2396, 17209, -3916, 2067, -1031, -24, -9712, 20276,
      -11398, 1893, 44, 1],
    poly [-21, 0, 6, 16, -21, -9, -2, 16, -4, 2, -1, 0, -9, 19, -11, 2],
    poly [1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, -1],
    poly [3419, -8371, -4329, -4235, -8549, -1096, -8476, -17280, -220, -17088, -11006, 2084, -7323,
      -12937, -119, -1979, -19287, -7820],
    poly [42980, -34609, -4042, 3325, -7476, -3411, 7474, 4490, -9607, 9488, -11467, -7820],
    poly [-3, 8, 4, 4, 8, 1, 8, 16, 0, 16, 10, -2, 7, 12, 0, 2, 18, 7],
    poly [-40, 33, 3, -3, 7, 3, -7, -4, 9, -9, 11, 7],
    poly [-22660, 22133, 6989, -12786, -15404, 5037, -3120, 12876, 13248, -1850, -43, -1],
    poly [-21, 21, 6, -12, -14, 5, -3, 12, 12, -2],
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
theorem certificado_46589 :
    haveI : Fact (Nat.Prime 46589) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 46589 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((46589 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((46589 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((46589 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 46589) := ⟨by norm_num⟩
  have hP : poly [-372, 1] = X - C (372 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((46589 : ℕ) : ℤ[X]) = poly [46589] := by simp [poly]
  refine ⟨X - C (372 : ℤ),
    poly [-20414, -13205, 23259, 313, -13525, 13239, -22257, 7705, -15008, 22127, -191, -6012, 12633,
      -467, -3007, -1010, 373, 1],
    poly [-163, -105, 186, 2, -108, 106, -178, 62, -120, 177, -2, -48, 101, -4, -24, -8, 3],
    poly [-1, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1],
    poly [-14158, 2586, -8891, -4288, -8659, -20318, -3943, -768, 8383, -4993, -4528, -16174, -13951,
      -11315, -10306, -4918, -10915, 2219],
    poly [32431, -29845, -11477, -9555, -1785, -6392, -4657, 5993, -15770, 1210, -5388, 5997, -13134,
      2219],
    poly [113, -21, 71, 34, 69, 162, 31, 6, -67, 40, 36, 129, 111, 90, 82, 39, 87, -18],
    poly [-259, 239, 91, 76, 14, 51, 37, -48, 126, -10, 43, -48, 105, -18],
    poly [20414, -7209, 10125, -3229, -19546, 22741, -4197, 20027, -13472, -2541, 1997, 1383, -372, -1],
    poly [163, -58, 81, -26, -156, 182, -34, 160, -108, -20, 16, 11, -3],
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
theorem certificado_46703 :
    haveI : Fact (Nat.Prime 46703) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 46703 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((46703 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((46703 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((46703 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 46703) := ⟨by norm_num⟩
  have hP : poly [-408, 1] = X - C (408 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((46703 : ℕ) : ℤ[X]) = poly [46703] := by simp [poly]
  refine ⟨X - C (408 : ℤ),
    poly [5380, 16840, 10000, 7236, -20701, -9895, -940, 18656, 847, -21289, -22259, 12308, 13194, 10220,
      -8789, -19939, 409, 1],
    poly [47, 147, 87, 63, -181, -86, -8, 163, 7, -186, -194, 108, 115, 89, -77, -174, 4],
    poly [1, 0, -1, 0, 0, 0, 0, 0, 0, -1, -1, -1],
    poly [14899, 627, 4255, 7469, -3741, 12486, -867, 9059, -11292, 5256, -7066, 13737, -6015, 10420,
      -1101, 6998, 8277, -7402],
    poly [31804, -32431, 11271, -17486, 14838, -13013, 2143, 6301, 6998, 8277, -7402],
    poly [-130, -5, -37, -65, 33, -109, 8, -79, 99, -46, 62, -120, 53, -91, 10, -61, -72, 65],
    poly [-278, 284, -99, 153, -130, 114, -19, -55, -61, -72, 65],
    poly [5380, 11460, -12220, -14224, -21097, 13570, -9811, 8790, 19939, -409, -1],
    poly [47, 100, -107, -124, -184, 119, -86, 77, 174, -4],
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
theorem certificado_46817 :
    haveI : Fact (Nat.Prime 46817) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 46817 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((46817 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((46817 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((46817 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 46817) := ⟨by norm_num⟩
  have hP : poly [-847, 1] = X - C (847 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((46817 : ℕ) : ℤ[X]) = poly [46817] := by simp [poly]
  refine ⟨X - C (847 : ℤ),
    poly [-12713, -20798, 4729, -5964, 10495, -18228, -1127, -14262, -3278, -18797, 21811, 20256, 8315,
      -16904, -23235, 16002, 848, 1],
    poly [-230, -376, 86, -108, 190, -330, -20, -258, -59, -340, 395, 366, 150, -306, -420, 290, 15],
    poly [1, 0, 0, 0, -1, 0, 0, 1, -1, 0, -1],
    poly [16475, 3892, 9902, 9688, 4492, 6531, -8280, -2549, 8402, -5293, 2595, 725, 10451, 13392, -4458,
      -9509, 10052, -2859],
    poly [30342, -34234, -6010, 214, 21671, -14622, 20821, -22420, 12911, -2859],
    poly [-298, -70, -179, -175, -81, -118, 150, 46, -152, 96, -47, -13, -189, -242, 81, 172, -182, 52],
    poly [-549, 620, 108, -4, -392, 265, -377, 406, -234, 52],
    poly [-12713, -8085, -21290, -10693, -17645, -20638, -8426, -15155, -847, -1],
    poly [-230, -146, -385, -193, -319, -373, -152, -274, -15],
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
theorem certificado_47387 :
    haveI : Fact (Nat.Prime 47387) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 47387 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((47387 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((47387 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((47387 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 47387) := ⟨by norm_num⟩
  have hP : poly [-1906, 1] = X - C (1906 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((47387 : ℕ) : ℤ[X]) = poly [47387] := by simp [poly]
  refine ⟨X - C (1906 : ℤ),
    poly [-16036, -83, -20188, -2820, 17029, 17114, 5951, -23218, -20225, 19879, -8741, -15966, -14851,
      390, -17080, -14056, 1907, 1],
    poly [-645, -3, -812, -113, 685, 688, 239, -934, -813, 800, -352, -642, -597, 16, -687, -565, 77],
    poly [1, 0, 0, 0, 1, 1, 2],
    poly [-14740, -19024, -6098, 4500, -23141, -16219, 4619, -10337, -19146, -19623, 7899, -11827,
      -29738, 9460, 33, -6809, -24216, -6051],
    poly [62127, -43103, -12926, -10598, 42381, 12102],
    poly [593, 765, 245, -181, 931, 652, -186, 416, 770, 789, -318, 476, 1196, -381, -1, 274, 974, 243],
    poly [-2499, 1735, 519, 426, -1705, -486],
    poly [-16036, 15953, -20105, 17368, 3813, 2],
    poly [-645, 642, -809, 699, 153],
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
theorem certificado_47501 :
    haveI : Fact (Nat.Prime 47501) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 47501 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((47501 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((47501 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((47501 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 47501) := ⟨by norm_num⟩
  have hP : poly [-2356, 1] = X - C (2356 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((47501 : ℕ) : ℤ[X]) = poly [47501] := by simp [poly]
  refine ⟨X - C (2356 : ℤ),
    poly [-6109, 9796, -13605, 7696, -17235, 14993, 4200, 1151, -4798, -8974, -12121, 761, -12258, 18846,
      -18319, -4524, 2357, 1],
    poly [-303, 486, -675, 382, -855, 744, 208, 57, -238, -445, -601, 38, -608, 935, -909, -224, 117],
    poly [1, 1, 1, 0, -1, 0, 1, 1, 0, 0, -1],
    poly [7433, 4674, 12798, 3769, -5731, 4991, 1810, -3010, 2230, -2284, 19771, -6571, 3539, 14229,
      5564, -12807, 3617, 15721],
    poly [40068, -52175, -12798, 3664, 17838, 5048, 2650, -16424, -12104, 15721],
    poly [-369, -232, -635, -187, 284, -248, -90, 149, -111, 113, -981, 326, -176, -706, -276, 635, -180,
      -780],
    poly [-1987, 2589, 634, -182, -885, -250, -131, 815, 600, -780],
    poly [-6109, 9796, -13605, 13805, -20922, 12693, 13796, 6881, -2356, -1],
    poly [-303, 486, -675, 685, -1038, 630, 684, 341, -117],
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
theorem certificado_47653 :
    haveI : Fact (Nat.Prime 47653) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 47653 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((47653 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((47653 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((47653 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 47653) := ⟨by norm_num⟩
  have hP : poly [-3093, 1] = X - C (3093 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((47653 : ℕ) : ℤ[X]) = poly [47653] := by simp [poly]
  refine ⟨X - C (3093 : ℤ),
    poly [14205, -5018, 6007, -16360, 4324, 16502, 8402, -13093, 10611, 11389, 15395, 7847, 7937, 16118,
      -16973, -8510, 3094, 1],
    poly [922, -326, 390, -1062, 281, 1071, 545, -850, 689, 739, 999, 509, 515, 1046, -1102, -552, 201],
    poly [-1, 0, 0, 0, 1, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1, -1],
    poly [-36216, -2071, -19562, -22649, -12574, -25990, -16057, -13789, -17301, -22032, -8907, -30996,
      -4103, -32720, -8325, -6684, -14772, -16115],
    poly [11437, -13508, -17491, -3087, 46291, -47561, -8792, 3284, 3067, -11893, -26036, 6447, 9431,
      -14772, -16115],
    poly [2351, 134, 1270, 1470, 816, 1687, 1042, 895, 1123, 1430, 578, 2012, 266, 2124, 540, 434, 959,
      1046],
    poly [-742, 877, 1135, 200, -3005, 3088, 570, -213, -199, 772, 1690, -419, -612, 959, 1046],
    poly [-14205, 19223, -11025, 22367, -6479, 16252, 4920, 4146, 5178, 22742, 23025, 20067, 8511, -3094,
      -1],
    poly [-922, 1248, -716, 1452, -421, 1055, 319, 269, 336, 1476, 1494, 1302, 552, -201],
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
theorem certificado_47843 :
    haveI : Fact (Nat.Prime 47843) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 47843 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((47843 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((47843 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((47843 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 47843) := ⟨by norm_num⟩
  have hP : poly [-1786, 1] = X - C (1786 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((47843 : ℕ) : ℤ[X]) = poly [47843] := by simp [poly]
  refine ⟨X - C (1786 : ℤ),
    poly [-19314, -18039, 16009, 17046, -553, 16876, 17234, -5589, 16391, -20671, -9173, 23836, 3844,
      19209, 8690, -13898, 1787, 1],
    poly [-721, -673, 598, 636, -21, 630, 643, -209, 612, -772, -342, 890, 143, 717, 324, -519, 67],
    poly [-1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, -1],
    poly [-4312, 8383, 4238, -10953, 11192, 3302, -4203, 8517, 8792, 9569, -6155, 7873, 9756, 17338,
      8663, 5899, 14791, -1491],
    poly [43531, -35148, -4145, -15191, 22145, -7890, -3193, 25, 4420, 11656, -25174, 17773, -1491],
    poly [161, -313, -158, 409, -418, -123, 157, -318, -328, -357, 230, -294, -364, -647, -323, -220,
      -552, 56],
    poly [-1625, 1313, 154, 567, -827, 295, 119, -1, -165, -435, 940, -664, 56],
    poly [19314, -1275, 13795, -1037, 17599, -17429, -19672, -23745, 12068, 9570, 17471, -1785, -1],
    poly [721, -48, 515, -39, 657, -651, -734, -886, 451, 357, 652, -67],
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
theorem certificado_47881 :
    haveI : Fact (Nat.Prime 47881) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 47881 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((47881 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((47881 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((47881 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 47881) := ⟨by norm_num⟩
  have hP : poly [-216, 1] = X - C (216 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((47881 : ℕ) : ℤ[X]) = poly [47881] := by simp [poly]
  refine ⟨X - C (216 : ℤ),
    poly [16182, 20247, -18970, 23631, -2994, 9518, -18798, 17425, 16041, 3621, -20377, 349, 18622,
      -9889, 21678, -1008, 217, 1],
    poly [73, 91, -86, 107, -14, 43, -85, 79, 72, 16, -92, 2, 84, -45, 98, -5, 1],
    poly [1, 0, 0, -1, -1, 0, -1, -1],
    poly [19681, -1730, 4156, -7787, 6123, 3084, 6395, 6632, 1978, -3807, 1708, 8162, -2005, 1273, 8825,
      -5327, -12486, 10313],
    poly [28200, -26470, -5886, 31624, -15640, -12486, 10313],
    poly [-89, 8, -19, 35, -28, -14, -29, -30, -9, 17, -8, -37, 9, -6, -40, 24, 56, -47],
    poly [-127, 120, 26, -143, 71, 56, -47],
    poly [16182, 4065, 8664, -21462, 1009, -217, -1],
    poly [73, 18, 39, -97, 5, -1],
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
theorem certificado_48109 :
    haveI : Fact (Nat.Prime 48109) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48109 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48109 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48109 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48109 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48109) := ⟨by norm_num⟩
  have hP : poly [-2871, 1] = X - C (2871 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48109 : ℕ) : ℤ[X]) = poly [48109] := by simp [poly]
  refine ⟨X - C (2871 : ℤ),
    poly [-3653, -21869, 17939, 3056, -1373, -15886, -15757, 22499, 15022, -20656, 23000, 17033, 12959,
      -3682, 16521, 18874, 2872, 1],
    poly [-218, -1305, 1071, 182, -82, -948, -940, 1343, 896, -1233, 1373, 1016, 773, -220, 986, 1126,
      171],
    poly [-2, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, -1],
    poly [-42001, -3944, -16733, -21111, 6352, -26683, 1943, -16245, -18480, -4405, -16951, 388, -19798,
      -8159, -19248, -19587, -7120, -24392],
    poly [-35893, -13996, 12479, -21545, 8547, -550, 11428, -12128, 4805, -7120, -24392],
    poly [2507, 235, 999, 1260, -379, 1593, -116, 970, 1103, 263, 1012, -23, 1182, 487, 1149, 1169, 425,
      1456],
    poly [2143, 835, -745, 1286, -510, 33, -682, 724, -287, 425, 1456],
    poly [7306, -8024, -13291, -10042, -20715, 3562, 22556, -13649, -18873, -2872, -1],
    poly [436, -479, -793, -599, -1236, 213, 1346, -815, -1126, -171],
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
theorem certificado_48299 :
    haveI : Fact (Nat.Prime 48299) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48299 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48299 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48299 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48299 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48299) := ⟨by norm_num⟩
  have hP : poly [-6707, 1] = X - C (6707 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48299 : ℕ) : ℤ[X]) = poly [48299] := by simp [poly]
  refine ⟨X - C (6707 : ℤ),
    poly [5617, -5825, -22080, -2855, 6884, -22611, -14766, 16856, -8495, 2620, 20272, -21464, 14601,
      3502, -7424, -24111, 6708, 1],
    poly [780, -809, -3066, -396, 956, -3140, -2050, 2341, -1180, 364, 2815, -2981, 2028, 486, -1031,
      -3348, 932],
    poly [1, 0, -1, 0, 1, -1, 0, 0, -1],
    poly [12393, -229, -5387, -12301, -8759, -4985, -282, 2520, 9160, -892, -339, -15404, -15147, -9746,
      -15391, 8430, -5897, 2728],
    poly [35906, -35677, 17551, -5708, -21093, 14327, -8625, 2728],
    poly [-1721, 32, 748, 1708, 1216, 692, 39, -350, -1272, 124, 47, 2139, 2103, 1353, 2137, -1171, 819,
      -379],
    poly [-4986, 4955, -2438, 793, 2929, -1990, 1198, -379],
    poly [5617, -11442, -21872, -17632, -16688, -17480, -6707, -1],
    poly [780, -1589, -3037, -2448, -2317, -2427, -931],
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
theorem certificado_48337 :
    haveI : Fact (Nat.Prime 48337) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48337 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48337 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48337 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48337 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48337) := ⟨by norm_num⟩
  have hP : poly [-3321, 1] = X - C (3321 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48337 : ℕ) : ℤ[X]) = poly [48337] := by simp [poly]
  refine ⟨X - C (3321 : ℤ),
    poly [-18805, -13338, -19202, 13312, -23968, 5480, -21889, -3558, 19750, 6774, -1730, -20654, 18857,
      -13152, -1736, 11527, 3322, 1],
    poly [-1292, -916, -1319, 915, -1647, 377, -1504, -244, 1357, 465, -119, -1419, 1296, -904, -119,
      792, 228],
    poly [-1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, -1],
    poly [-8258, 6833, 6561, 15323, 3900, 4013, 2150, 12760, -1326, -1796, 5525, 13154, 12283, 19371,
      -4235, 11943, 6155, 17739],
    poly [40079, -33246, 7986, -6329, -11151, -8649, 17818, -4594, -11951, -11584, 17739],
    poly [567, -470, -451, -1053, -268, -276, -148, -877, 91, 123, -380, -904, -844, -1331, 291, -821,
      -423, -1219],
    poly [-2754, 2285, -549, 435, 766, 594, -1224, 316, 821, 796, -1219],
    poly [18805, -5467, -12941, 21290, -16921, 3066, 19621, 16584, -8204, -3321, -1],
    poly [1292, -376, -889, 1463, -1163, 211, 1348, 1139, -564, -228],
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
theorem certificado_48413 :
    haveI : Fact (Nat.Prime 48413) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48413 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48413 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48413 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48413 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48413) := ⟨by norm_num⟩
  have hP : poly [-5697, 1] = X - C (5697 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48413 : ℕ) : ℤ[X]) = poly [48413] := by simp [poly]
  refine ⟨X - C (5697 : ℤ),
    poly [6314, -16383, -10005, -1081, 5515, -6449, 9967, 11576, 19080, -13262, -11908, 8037, -2480,
      -20778, -624, -23616, 5698, 1],
    poly [743, -1928, -1177, -127, 649, -759, 1173, 1362, 2245, -1561, -1401, 946, -292, -2445, -73,
      -2779, 671],
    poly [-1, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, -1, -1, -1],
    poly [-19518, 6049, -15047, 934, -10408, 153, -17300, -7046, -22621, -8874, -2923, -9049, -11472,
      -11158, -8821, 1326, -16433, -10615],
    poly [28895, -22846, -21096, -3537, 14225, -10535, -20990, 4961, -543, -8821, 1326, -16433, -10615],
    poly [2297, -712, 1771, -110, 1225, -18, 2036, 829, 2662, 1044, 344, 1065, 1350, 1313, 1038, -156,
      1934, 1249],
    poly [-3400, 2689, 2482, 416, -1674, 1240, 2470, -584, 64, 1038, -156, 1934, 1249],
    poly [-6314, 22697, -6378, -15238, 16101, 5586, 16759, 8178, 20779, 624, 23616, -5698, -1],
    poly [-743, 2671, -751, -1793, 1895, 657, 1972, 962, 2445, 73, 2779, -671],
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
theorem certificado_48527 :
    haveI : Fact (Nat.Prime 48527) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48527 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48527 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48527 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48527 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48527) := ⟨by norm_num⟩
  have hP : poly [-73, 1] = X - C (73 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48527 : ℕ) : ℤ[X]) = poly [48527] := by simp [poly]
  refine ⟨X - C (73 : ℤ),
    poly [2659, 17320, 902, -17936, -7558, 9203, -10510, -2803, -17322, 9734, -15156, -23474, 14303,
      16150, 6204, 5403, 74, 1],
    poly [4, 26, 1, -27, -11, 14, -16, -4, -26, 15, -23, -35, 22, 24, 9, 8],
    poly [1, 0, 0, -1, 0, 0, 0, -1, -1, 0, -1],
    poly [5938, -11929, -11509, -12168, -6859, -2133, -74, 8596, 5391, -13266, 1103, -15319, -23521,
      -3026, -3410, -1421, -729, 3269],
    poly [42589, -30660, -420, 6597, -23176, -4306, -2718, 2577, -3998, 3269],
    poly [-9, 18, 17, 18, 10, 3, 0, -13, -8, 20, -2, 23, 35, 4, 5, 2, 1, -5],
    poly [-64, 47, 0, -10, 35, 6, 4, -4, 6, -5],
    poly [2659, 14661, -16418, -21497, -4283, -15348, -875, -5330, -73, -1],
    poly [4, 22, -25, -32, -6, -23, -1, -8],
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
theorem certificado_48679 :
    haveI : Fact (Nat.Prime 48679) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48679 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48679 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48679 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48679 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48679) := ⟨by norm_num⟩
  have hP : poly [-2677, 1] = X - C (2677 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48679 : ℕ) : ℤ[X]) = poly [48679] := by simp [poly]
  refine ⟨X - C (2677 : ℤ),
    poly [-9874, -1713, 16256, 7207, -16654, -13808, -187, -6510, 15345, 17608, 18809, -193, -17075,
      15632, -20615, 13194, 2678, 1],
    poly [-543, -94, 894, 396, -916, -759, -10, -358, 844, 968, 1034, -11, -939, 860, -1134, 726, 147],
    poly [1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1],
    poly [2040, -8106, -8328, -9801, 818, -1742, -14781, -5912, -6927, -1163, 6822, -9268, 6328, -19124,
      -2495, -2016, 5767, -9032],
    poly [46639, -40573, 10368, -345, -1040, 2309, 17294, -7016, -5767, 9032],
    poly [-112, 446, 458, 539, -45, 96, 813, 325, 381, 64, -375, 510, -348, 1052, 137, 111, -317, 497],
    poly [-2565, 2232, -571, 19, 57, -127, -951, 386, 317, -497],
    poly [-9874, -1713, -22549, -954, 14056, 5115, -23292, 13193, 2678, 1],
    poly [-543, -94, -1240, -52, 773, 281, -1281, 726, 147],
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
theorem certificado_48869 :
    haveI : Fact (Nat.Prime 48869) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48869 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48869 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48869 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48869 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48869) := ⟨by norm_num⟩
  have hP : poly [-619, 1] = X - C (619 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48869 : ℕ) : ℤ[X]) = poly [48869] := by simp [poly]
  refine ⟨X - C (619 : ℤ),
    poly [4579, 2139, -16102, -7684, 3935, 18875, -23654, 22541, 668, -24315, 19382, 505, -10973, 12614,
      8231, -7171, 620, 1],
    poly [58, 27, -204, -97, 50, 239, -300, 286, 8, -308, 246, 6, -139, 160, 104, -91, 8],
    poly [-1, 0, 1, 0, 1, 1, 0, 0, 0, 0, -1],
    poly [-9811, 4147, 11117, 6944, 7332, -10036, 8173, -324, 7715, -4509, 14182, -2288, 8975, -7507,
      9835, 12942, 6868, 13253],
    poly [39058, -34911, 16781, -18131, 3229, -17342, -3107, 6074, -6385, 13253],
    poly [124, -53, -141, -88, -93, 127, -104, 4, -98, 57, -180, 29, -114, 95, -125, -164, -87, -168],
    poly [-495, 443, -213, 230, -41, 220, 39, -77, 81, -168],
    poly [-4579, 2440, 22820, -10858, 23588, -4383, -15402, 7791, -619, -1],
    poly [-58, 31, 289, -138, 299, -56, -195, 99, -8],
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
theorem certificado_48907 :
    haveI : Fact (Nat.Prime 48907) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 48907 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((48907 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((48907 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((48907 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 48907) := ⟨by norm_num⟩
  have hP : poly [-4270, 1] = X - C (4270 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((48907 : ℕ) : ℤ[X]) = poly [48907] := by simp [poly]
  refine ⟨X - C (4270 : ℤ),
    poly [-21613, 16282, -4612, 20604, -5596, -20950, 15950, 9201, -16262, 2390, -12335, 22996, -1999,
      7788, 11444, -5140, 4271, 1],
    poly [-1887, 1422, -403, 1799, -489, -1829, 1393, 803, -1420, 209, -1077, 2008, -175, 680, 999, -449,
      373],
    poly [-1, 1, -1, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1],
    poly [-28618, -22623, -7331, -14841, -6138, -4521, -24805, -20549, -29688, -15522, -3584, -20922,
      -21682, -14810, -20833, -5498, -12882, -19733],
    poly [20289, -14294, -19321, -16807, 31505, -14596, -13198, -2461, -27684, 14235, -12882, -19733],
    poly [2499, 1975, 640, 1296, 536, 395, 2166, 1794, 2592, 1355, 313, 1827, 1893, 1293, 1819, 480,
      1125, 1723],
    poly [-1771, 1248, 1687, 1467, -2751, 1275, 1152, 215, 2417, -1243, 1125, 1723],
    poly [21613, -10601, -17412, 13809, 23403, 12845, 22853, -17198, -7174, 5141, -4271, -1],
    poly [1887, -926, -1520, 1206, 2043, 1121, 1995, -1502, -626, 449, -373],
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
theorem certificado_49211 :
    haveI : Fact (Nat.Prime 49211) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 49211 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((49211 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((49211 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((49211 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 49211) := ⟨by norm_num⟩
  have hP : poly [-3091, 1] = X - C (3091 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((49211 : ℕ) : ℤ[X]) = poly [49211] := by simp [poly]
  refine ⟨X - C (3091 : ℤ),
    poly [17274, -7509, 7544, 12946, 2854, -22511, 6966, 7485, -1319, 16987, -20182, -18793, 2589,
      -21524, -15466, 10439, 3092, 1],
    poly [1085, -472, 474, 813, 179, -1414, 438, 470, -83, 1067, -1268, -1180, 163, -1352, -971, 656,
      194],
    poly [-1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -1, 0, -1],
    poly [-1867, 15486, 3965, 8435, 5714, 11763, -3710, 11951, -3296, -3890, 20978, 13965, -955, 9118,
      18212, 9968, 190, 13210],
    poly [47344, -31858, -11521, 4470, -854, -11304, -3952, 11191, -12526, -4776, 22988, -13020, 13210],
    poly [117, -973, -249, -530, -359, -739, 233, -751, 207, 244, -1318, -877, 60, -573, -1144, -626,
      -12, -830],
    poly [-2974, 2002, 723, -281, 54, 710, 248, -703, 787, 300, -1444, 818, -830],
    poly [-17274, -24428, -15053, -5402, -21845, 582, -14424, 4883, -1288, 22814, -7348, -3091, -1],
    poly [-1085, -1534, -945, -339, -1372, 37, -906, 307, -81, 1433, -462, -194],
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
theorem certificado_49363 :
    haveI : Fact (Nat.Prime 49363) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 49363 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((49363 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((49363 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((49363 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 49363) := ⟨by norm_num⟩
  have hP : poly [-3148, 1] = X - C (3148 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((49363 : ℕ) : ℤ[X]) = poly [49363] := by simp [poly]
  refine ⟨X - C (3148 : ℤ),
    poly [-3340, -2902, -20872, -15264, 6879, 18725, -4761, -10194, 9170, 19400, -20959, -9666, -4378,
      -14412, -10495, -8910, 3149, 1],
    poly [-213, -185, -1331, -973, 439, 1194, -304, -650, 585, 1237, -1337, -616, -279, -919, -669, -568,
      201],
    poly [1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, -1],
    poly [-1835, -9723, 4199, 3733, -22454, -15798, 1892, -1019, 752, -7668, 6442, -7823, -17628, 10704,
      10713, -8590, -12532, 1109],
    poly [51198, -41475, -12087, 8354, 12265, -6190, 10332, 4143, -33383, 13632, 18194, 3942, -13641,
      1109],
    poly [117, 620, -268, -238, 1432, 1007, -121, 65, -48, 489, -411, 499, 1124, -683, -683, 548, 799,
      -71],
    poly [-3265, 2646, 770, -533, -782, 395, -659, -264, 2129, -870, -1160, -251, 870, -71],
    poly [-3340, 438, -21310, 6046, 4173, 17454, -4683, 6851, -22092, 7065, 1586, 12059, -3148, -1],
    poly [-213, 28, -1359, 386, 266, 1113, -299, 437, -1409, 451, 101, 769, -201],
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
theorem certificado_49477 :
    haveI : Fact (Nat.Prime 49477) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 49477 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((49477 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((49477 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((49477 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 49477) := ⟨by norm_num⟩
  have hP : poly [-112, 1] = X - C (112 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((49477 : ℕ) : ℤ[X]) = poly [49477] := by simp [poly]
  refine ⟨X - C (112 : ℤ),
    poly [12811, 6299, 13309, 8954, -9197, -18636, -17395, 15748, -17088, -8546, 3016, 16372, 4122,
      -2172, -17248, 12657, 113, 1],
    poly [29, 14, 30, 20, -21, -42, -39, 36, -39, -19, 7, 37, 9, -5, -39, 29],
    poly [1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 0, -1, -1],
    poly [1122, 24987, 8855, 10478, -1435, 28940, -18057, 24374, -4845, 26259, -8804, 31083, -12295,
      27076, 13733, 7871, -133, 22767],
    poly [48355, -73342, 16132, -1623, 11913, -32619, -1855, -34032, 42105, -8901, -14896, -133, 22767],
    poly [-3, -57, -20, -24, 3, -66, 41, -56, 11, -60, 20, -71, 28, -62, -31, -18, 0, -52],
    poly [-109, 167, -38, 4, -27, 75, 4, 77, -96, 21, 34, 0, -52],
    poly [12811, -6512, 7010, -4355, -18151, 16183, 1028, -8826, 14941, 17362, -12656, -113, -1],
    poly [29, -15, 16, -10, -41, 37, 2, -20, 34, 39, -29],
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
theorem certificado_49667 :
    haveI : Fact (Nat.Prime 49667) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 49667 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((49667 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((49667 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((49667 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 49667) := ⟨by norm_num⟩
  have hP : poly [-3382, 1] = X - C (3382 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((49667 : ℕ) : ℤ[X]) = poly [49667] := by simp [poly]
  refine ⟨X - C (3382 : ℤ),
    poly [-16727, 14622, 5159, 6287, 883, 2115, -2026, 16932, 3603, 4583, 6933, -20881, 14797, 2031,
      -16418, 17897, 3383, 1],
    poly [-1139, 996, 351, 428, 60, 144, -138, 1153, 245, 312, 472, -1422, 1008, 138, -1118, 1219, 230],
    poly [1, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, -1],
    poly [9916, -12932, -3863, 10282, 109, -4520, -2950, -15403, -13336, -6859, 10193, 1416, 4189, -818,
      -14345, 2378, 3455, -10687],
    poly [39751, -26819, -9069, -14145, 257, 27477, -10639, -1692, 8106, -11764, 14142, -10687],
    poly [-675, 881, 263, -700, -7, 308, 201, 1049, 908, 467, -694, -96, -285, 56, 977, -162, -235, 728],
    poly [-2707, 1827, 617, 963, -18, -1871, 725, 115, -552, 801, -963, 728],
    poly [-16727, -18318, -9463, 1128, -22131, -17086, -13604, 20086, -18733, -14515, -3382, -1],
    poly [-1139, -1247, -644, 77, -1507, -1163, -926, 1368, -1276, -988, -230],
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
theorem certificado_50047 :
    haveI : Fact (Nat.Prime 50047) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 50047 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((50047 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((50047 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((50047 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 50047) := ⟨by norm_num⟩
  have hP : poly [-3974, 1] = X - C (3974 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((50047 : ℕ) : ℤ[X]) = poly [50047] := by simp [poly]
  refine ⟨X - C (3974 : ℤ),
    poly [2758, 3338, 5202, 19131, -11002, 17792, -21518, -6340, 22075, -22940, 11870, -3964, -24823,
      296, -12858, -18201, 3975, 1],
    poly [219, 265, 413, 1519, -874, 1413, -1709, -503, 1753, -1822, 943, -315, -1971, 24, -1021, -1445,
      316],
    poly [1, 0, -1, 0, 1, 1, 1, -1, -1],
    poly [-11469, -9671, -13902, -5755, -4078, -24920, 3360, -19654, -6638, -21067, -13250, -2279,
      -31909, 10927, -19841, 8638, -12701, -15011],
    poly [61516, -51845, -7238, -6349, 5561, 38660, -12701, -15011],
    poly [911, 768, 1104, 457, 324, 1979, -267, 1561, 527, 1673, 1052, 181, 2534, -868, 1576, -686, 1009,
      1192],
    poly [-4885, 4118, 574, 504, -442, -3070, 1009, 1192],
    poly [2758, 580, -894, 13349, 20808, 18203, -3975, -1],
    poly [219, 46, -71, 1060, 1652, 1445, -316],
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
theorem certificado_50123 :
    haveI : Fact (Nat.Prime 50123) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 50123 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((50123 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((50123 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((50123 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 50123) := ⟨by norm_num⟩
  have hP : poly [-437, 1] = X - C (437 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((50123 : ℕ) : ℤ[X]) = poly [50123] := by simp [poly]
  refine ⟨X - C (437 : ℤ),
    poly [11011, 16427, -22902, 16120, -766, 24773, 4874, -24993, -16459, -3708, -10446, -368, 3096,
      4595, -10427, -9085, 438, 1],
    poly [96, 143, -200, 141, -7, 216, 42, -218, -143, -32, -91, -3, 27, 40, -91, -79, 4],
    poly [-1, 0, 0, 0, -1, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1],
    poly [7897, 17435, 2202, 21207, 20677, -7884, 5585, 12383, -6756, 15681, 18141, -2499, 6859, 18809,
      10234, -2173, 26129, 7498],
    poly [58020, -40585, -15233, 19005, 7367, -19023, -1764, 25803, -11772, 11311, 10234, -2173, 26129,
      7498],
    poly [-69, -152, -19, -185, -180, 69, -49, -108, 59, -137, -158, 22, -60, -164, -89, 19, -228, -65],
    poly [-506, 355, 132, -166, -64, 166, 15, -225, 103, -99, -89, 19, -228, -65],
    poly [-11011, -5416, -10794, 11101, 5875, 19168, 9105, -9155, -2659, -4594, 10427, 9085, -438, -1],
    poly [-96, -47, -94, 97, 51, 167, 79, -80, -23, -40, 91, 79, -4],
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
theorem certificado_50503 :
    haveI : Fact (Nat.Prime 50503) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 50503 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((50503 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((50503 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((50503 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 50503) := ⟨by norm_num⟩
  have hP : poly [-6447, 1] = X - C (6447 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((50503 : ℕ) : ℤ[X]) = poly [50503] := by simp [poly]
  refine ⟨X - C (6447 : ℤ),
    poly [22451, -5010, -18723, -14448, 13730, -9970, -20878, -14417, 24791, -17230, 201, 4567, 9824,
      10428, -15172, 6288, 6448, 1],
    poly [2866, -640, -2390, -1844, 1753, -1273, -2665, -1840, 3165, -2200, 26, 583, 1254, 1331, -1937,
      803, 823],
    poly [0, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1],
    poly [7542, 18659, 16718, 10020, -11116, -12968, 2315, 1064, 7597, -4074, 11983, 6690, 6274, 2835,
      -7263, -5032, 5763, 11115],
    poly [50503, -42961, 11117, -1941, 844, -10019, -3793, 16127, -3728, 13857, 2515, -1911, -16147,
      5763, 11115],
    poly [-963, -2382, -2134, -1279, 1419, 1655, -296, -136, -970, 520, -1530, -854, -801, -362, 927,
      642, -736, -1419],
    poly [-6447, 5485, -1420, 248, -108, 1279, 484, -2059, 476, -1769, -321, 244, 2061, -736, -1419],
    poly [0, -22451, -23042, 13713, 23777, -717, -13090, -15818, 20874, -24837, -10587, 21619, -6287,
      -6448, -1],
    poly [0, -2866, -2941, 1751, 3035, -92, -1671, -2019, 2665, -3171, -1351, 2760, -803, -823],
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
theorem certificado_51263 :
    haveI : Fact (Nat.Prime 51263) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 51263 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((51263 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((51263 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((51263 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 51263) := ⟨by norm_num⟩
  have hP : poly [-7854, 1] = X - C (7854 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((51263 : ℕ) : ℤ[X]) = poly [51263] := by simp [poly]
  refine ⟨X - C (7854 : ℤ),
    poly [2539, 15156, 19968, 2894, -14718, 814, -13687, -2482, -1012, 8857, 19073, 19727, -363, 1462,
      -18543, 23782, 7855, 1],
    poly [389, 2322, 3059, 443, -2255, 125, -2097, -380, -155, 1357, 2922, 3022, -56, 224, -2841, 3644,
      1203],
    poly [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, -1],
    poly [23830, 9800, 4185, 9556, 8545, 12324, 3624, -1429, 12388, -5083, 11291, 11998, 11130, 10673,
      -8053, 16460, 11235, 393],
    poly [27433, -37233, 5615, -5371, 1011, 20051, -5330, -562, -8446, 16460, 11235, 393],
    poly [-3651, -1501, -641, -1464, -1309, -1888, -555, 219, -1898, 779, -1730, -1838, -1705, -1635,
      1234, -2522, -1721, -60],
    poly [-4203, 5705, -861, 823, -155, -3072, 817, 86, 1294, -2522, -1721, -60],
    poly [2539, 12617, 4812, -17074, -17612, 12993, 24145, 6393, 18544, -23782, -7855, -1],
    poly [389, 1933, 737, -2616, -2698, 1991, 3699, 979, 2841, -3644, -1203],
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
theorem certificado_51719 :
    haveI : Fact (Nat.Prime 51719) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 51719 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((51719 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((51719 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((51719 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 51719) := ⟨by norm_num⟩
  have hP : poly [-2765, 1] = X - C (2765 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((51719 : ℕ) : ℤ[X]) = poly [51719] := by simp [poly]
  refine ⟨X - C (2765 : ℤ),
    poly [-8810, 5309, 9504, -11631, -22581, 15573, -21187, -12409, 1866, -15992, -15774, -8797, 16401,
      -18886, -14447, -6421, 2766, 1],
    poly [-471, 284, 508, -622, -1207, 833, -1133, -663, 100, -855, -843, -470, 877, -1010, -772, -343,
      148],
    poly [-1, 0, 0, -1, -1, 0, -1, 0, 1, 0, -1],
    poly [-22592, 8319, -18025, 6207, -5905, -16328, 9986, -19951, 1979, -16905, -4922, 6829, -8299,
      -6116, -13354, -10607, -14029, -9672],
    poly [29127, -20808, -26344, 1640, -3793, -5856, 1610, 13094, -4357, -9672],
    poly [1208, -445, 964, -332, 316, 873, -534, 1067, -106, 904, 263, -365, 444, 327, 714, 567, 750,
      517],
    poly [-1557, 1113, 1408, -88, 203, 313, -86, -700, 233, 517],
    poly [8810, -14119, -4195, -21774, 5641, -4749, 10791, 9188, -2765, -1],
    poly [471, -755, -224, -1164, 302, -254, 577, 491, -148],
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
theorem certificado_51871 :
    haveI : Fact (Nat.Prime 51871) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 51871 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((51871 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((51871 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((51871 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 51871) := ⟨by norm_num⟩
  have hP : poly [-1393, 1] = X - C (1393 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((51871 : ℕ) : ℤ[X]) = poly [51871] := by simp [poly]
  refine ⟨X - C (1393 : ℤ),
    poly [17762, 8540, 1086, 24242, 12529, 4254, -17610, 24452, 17221, 21647, -8400, -14305, -12857,
      -4217, 18392, 22616, 1394, 1],
    poly [477, 229, 29, 651, 336, 114, -473, 657, 462, 581, -226, -384, -345, -113, 494, 607, 37],
    poly [1, 0, 1, 0, 0, 1, 1, 1, 0, 0, -1, -1],
    poly [5193, -6235, 6678, 19534, 7404, -11670, 11217, 5350, 6165, 2144, -3221, 2882, 11786, 13617,
      14512, -9952, -3751, 28091],
    poly [46678, -40443, -18106, -1428, -783, 1025, -4522, 18263, -38043, -3751, 28091],
    poly [-140, 167, -180, -525, -199, 313, -302, -144, -166, -58, 86, -78, -317, -366, -390, 267, 100,
      -755],
    poly [-1253, 1087, 486, 38, 21, -27, 122, -490, 1022, 100, -755],
    poly [17762, -9222, 10308, 13934, -19167, -19228, -25037, -16998, -22615, -1394, -1],
    poly [477, -248, 277, 374, -515, -516, -672, -456, -607, -37],
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
theorem certificado_52289 :
    haveI : Fact (Nat.Prime 52289) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 52289 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((52289 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((52289 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((52289 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 52289) := ⟨by norm_num⟩
  have hP : poly [-793, 1] = X - C (793 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((52289 : ℕ) : ℤ[X]) = poly [52289] := by simp [poly]
  refine ⟨X - C (793 : ℤ),
    poly [11737, -16206, -5823, 14565, -4927, 8302, -14430, 12576, 19072, 12882, -16798, -11956, -4367,
      23996, -761, 2175, 794, 1],
    poly [178, -246, -88, 221, -75, 126, -219, 191, 289, 195, -255, -181, -66, 364, -12, 33, 12],
    poly [0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 1, 0, 1],
    poly [1510, 4611, 1318, 9688, 22029, 16242, 14850, -13703, -7343, 14029, 1198, 6325, 15365, 7266,
      3827, 262, 11467, 5217],
    poly [52289, -52289, 1510, 3101, -1783, 11471, 10558, 5684, 9166, -22869, 14016, -4598, 5988, -6250,
      -5217],
    poly [-23, -70, -20, -147, -334, -246, -225, 208, 111, -213, -18, -96, -233, -110, -58, -4, -174,
      -79],
    poly [-793, 794, -24, -47, 27, -174, -160, -86, -139, 347, -213, 70, -91, 95, 79],
    poly [0, 0, -11737, -24346, -22120, 7555, -2628, -5674, 20104, 19609, 25345, -2144, 1382, 793, 1],
    poly [0, 0, -178, -369, -335, 115, -40, -86, 305, 297, 384, -33, 21, 12],
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
theorem certificado_52517 :
    haveI : Fact (Nat.Prime 52517) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 52517 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((52517 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((52517 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((52517 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 52517) := ⟨by norm_num⟩
  have hP : poly [-1094, 1] = X - C (1094 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((52517 : ℕ) : ℤ[X]) = poly [52517] := by simp [poly]
  refine ⟨X - C (1094 : ℤ),
    poly [10513, -16888, -5920, 14828, -5795, 13628, 5725, 8070, -14442, 12612, 25982, 2664, -4558,
      -19254, -25220, -9960, 1095, 1],
    poly [219, -352, -123, 309, -121, 284, 119, 168, -301, 263, 541, 55, -95, -401, -525, -207, 23],
    poly [0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [12560, -2982, 9677, 3688, -1838, 9198, -2217, 2333, 11170, 10362, -2888, 19278, 6049, 17510,
      2015, -6784, 14666, 18814],
    poly [52517, -52517, -12560, 15542, -99, -9553, 18185, -17025, -6671, 22028, -32911, 11347, 27613,
      -21450, -4148, 18814],
    poly [-262, 62, -202, -77, 38, -192, 46, -49, -233, -216, 60, -402, -126, -365, -42, 141, -306, -392],
    poly [-1094, 1095, 261, -324, 2, 199, -379, 355, 139, -459, 686, -237, -575, 447, 86, -392],
    poly [0, 0, 10513, 25116, 455, -4368, 20926, -1325, 23233, 8038, -3641, -7060, 15259, 11055, -1094,
      -1],
    poly [0, 0, 219, 523, 9, -91, 436, -28, 484, 167, -76, -147, 318, 230, -23],
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
theorem certificado_52631 :
    haveI : Fact (Nat.Prime 52631) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 52631 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((52631 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((52631 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((52631 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 52631) := ⟨by norm_num⟩
  have hP : poly [-1377, 1] = X - C (1377 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((52631 : ℕ) : ℤ[X]) = poly [52631] := by simp [poly]
  refine ⟨X - C (1377 : ℤ),
    poly [-11734, -15794, -24779, 17755, 11938, 17667, -20665, -23827, -21880, -17636, -7466, 12837,
      -12298, -2264, 1145, 2791, 1378, 1],
    poly [-307, -413, -648, 465, 312, 462, -541, -623, -572, -461, -195, 336, -322, -59, 30, 73, 36],
    poly [-1, -1, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0, -1],
    poly [-14598, 6375, 1001, -5577, 17848, -4915, -3632, -1376, -2865, -1299, 5926, -4465, 13568,
      -16461, -12202, 16085, -7974, -3596],
    poly [38033, -46256, 1001, -5577, 32446, -25888, 1742, 19800, -32665, 20463, -4378, -3596],
    poly [382, -167, -26, 146, -467, 129, 95, 36, 75, 34, -155, 117, -355, 431, 319, -421, 209, 94],
    poly [-995, 1211, -27, 146, -849, 678, -46, -518, 855, -536, 115, 94],
    poly [11734, 15794, 24779, -17755, -23672, -21727, 11680, 1996, 269, -1414, -1377, -1],
    poly [307, 413, 648, -465, -619, -568, 306, 52, 7, -37, -36],
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
theorem certificado_52783 :
    haveI : Fact (Nat.Prime 52783) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 52783 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((52783 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((52783 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((52783 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 52783) := ⟨by norm_num⟩
  have hP : poly [-3684, 1] = X - C (3684 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((52783 : ℕ) : ℤ[X]) = poly [52783] := by simp [poly]
  refine ⟨X - C (3684 : ℤ),
    poly [15918, -8406, 17721, 5392, 11220, -19153, 18764, -23220, -7471, 19197, -1141, 21004, 1768,
      6233, -21719, 10310, 3685, 1],
    poly [1111, -587, 1237, 376, 783, -1337, 1310, -1621, -521, 1340, -80, 1466, 123, 435, -1516, 720,
      257],
    poly [1, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 0, -1, -1],
    poly [9984, 14285, 10518, 12136, 14916, -4970, 727, -2925, 15528, 18069, 2209, 600, 12907, -12206,
      10869, 19916, 1794, 8695],
    poly [42799, -57084, 3767, 8366, 1521, 16119, 5905, 10733, -32122, 9075, 11221, 1794, 8695],
    poly [-697, -997, -734, -847, -1041, 347, -51, 204, -1084, -1261, -154, -42, -901, 852, -759, -1390,
      -125, -607],
    poly [-2987, 3985, -264, -584, -106, -1125, -412, -749, 2242, -634, -783, -125, -607],
    poly [15918, -24324, 26127, 24536, -22631, -3717, -18455, -23488, 4077, 25404, -10309, -3685, -1],
    poly [1111, -1698, 1824, 1712, -1580, -259, -1288, -1639, 285, 1773, -720, -257],
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
theorem certificado_52859 :
    haveI : Fact (Nat.Prime 52859) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 52859 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((52859 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((52859 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((52859 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 52859) := ⟨by norm_num⟩
  have hP : poly [-1251, 1] = X - C (1251 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((52859 : ℕ) : ℤ[X]) = poly [52859] := by simp [poly]
  refine ⟨X - C (1251 : ℤ),
    poly [9338, -24415, 15741, 20759, -4251, 8067, 3767, -15673, -2759, -22312, -11384, 13681, 16363,
      -25846, 5092, -19517, 1252, 1],
    poly [221, -578, 373, 491, -101, 191, 89, -371, -65, -528, -269, 324, 387, -612, 121, -462, 30],
    poly [-1, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [10806, 12209, 20027, 13822, 22648, 12641, 3295, 6034, 13008, 12084, 24379, 23417, 20543, 5583,
      -4274, 12873, 4098, 13598],
    poly [63665, -40650, 9221, 12419, 4024, 17443, -13349, 11440, 1319, -675, 23735, 357, -3549, 8775,
      -9500, 13598],
    poly [-256, -289, -474, -327, -536, -299, -78, -143, -308, -286, -577, -554, -486, -132, 101, -305,
      -97, -322],
    poly [-1507, 963, -219, -294, -95, -413, 316, -271, -31, 16, -562, -8, 84, -208, 225, -322],
    poly [-9338, 24415, -6403, -1653, 886, 16057, 11379, -10512, 1893, -21928, -21440, -23172, -24610,
      20769, -1251, -1],
    poly [-221, 578, -152, -39, 21, 380, 269, -249, 45, -519, -507, -548, -582, 492, -30],
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
theorem certificado_52973 :
    haveI : Fact (Nat.Prime 52973) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 52973 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((52973 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((52973 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((52973 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 52973) := ⟨by norm_num⟩
  have hP : poly [-360, 1] = X - C (360 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((52973 : ℕ) : ℤ[X]) = poly [52973] := by simp [poly]
  refine ⟨X - C (360 : ℤ),
    poly [-23985, -17430, -19619, 26432, 19644, -4507, -6487, 19994, 20509, -22898, -8451, 6451, 22090,
      21692, 10802, 24015, 361, 1],
    poly [-163, -118, -133, 180, 133, -31, -44, 136, 139, -156, -57, 44, 150, 147, 73, 163, 2],
    poly [1, -1, -1, 0, 0, 0, 0, 0, -1, -1],
    poly [35281, 6391, 19554, 15029, 24581, 21076, 21802, 6795, 15435, 15459, 8396, 9995, 9558, 16767,
      20760, 17681, 12228, 12360],
    poly [17692, 11198, -6772, -11202, -914, 8532, 5321, 12228, 12360],
    poly [-240, -43, -133, -102, -167, -143, -148, -46, -105, -105, -57, -68, -65, -114, -141, -120, -83,
      -84],
    poly [-120, -76, 46, 76, 6, -58, -36, -83, -84],
    poly [-23985, -22433, 15241, -11288, 2323, -10441, -24014, -361, -1],
    poly [-163, -152, 104, -77, 16, -71, -163, -2],
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
theorem certificado_53087 :
    haveI : Fact (Nat.Prime 53087) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 53087 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((53087 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((53087 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((53087 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 53087) := ⟨by norm_num⟩
  have hP : poly [-3362, 1] = X - C (3362 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((53087 : ℕ) : ℤ[X]) = poly [53087] := by simp [poly]
  refine ⟨X - C (3362 : ℤ),
    poly [13027, -23650, -15371, 6880, -1877, -8401, -12540, 22908, -7462, 18204, 9148, 22346, -12294,
      3486, -9710, -1124, 3363, 1],
    poly [825, -1498, -973, 436, -119, -532, -794, 1451, -473, 1153, 579, 1415, -779, 221, -615, -71,
      213],
    poly [-1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-10009, -4438, -7926, -12222, -1928, -4104, -5810, -25201, -6590, -3758, -757, -22752, -4426,
      -4989, 3206, 4898, -5681, -6900],
    poly [43078, -47516, -3488, -4296, 20303, -7747, 1782, -15095, -1692, 10579, 1219, -6900],
    poly [634, 281, 502, 774, 122, 260, 368, 1596, 417, 238, 48, 1441, 280, 316, -203, -310, 360, 437],
    poly [-2728, 3010, 220, 272, -1286, 491, -113, 956, 107, -670, -77, 437],
    poly [-13027, -16410, -8279, -22251, 21784, 22934, 12418, -13197, 8586, 4487, -3362, -1],
    poly [-825, -1039, -524, -1409, 1380, 1452, 786, -836, 544, 284, -213],
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
theorem certificado_53201 :
    haveI : Fact (Nat.Prime 53201) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 53201 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((53201 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((53201 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((53201 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 53201) := ⟨by norm_num⟩
  have hP : poly [-889, 1] = X - C (889 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((53201 : ℕ) : ℤ[X]) = poly [53201] := by simp [poly]
  refine ⟨X - C (889 : ℤ),
    poly [-18372, 11589, -15666, -16714, -11808, -1270, 4427, 23344, 4335, -17649, -5705, -24662, 4281,
      1082, 16159, -6804, 890, 1],
    poly [-307, 194, -262, -279, -197, -21, 74, 390, 72, -295, -95, -412, 72, 18, 270, -114, 15],
    poly [-1, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, -1, -1],
    poly [-767, 6174, 3429, 6837, 1036, -13333, -17239, -10122, -24656, -27485, -24496, -14020, -30166,
      -15702, -22089, -2647, -5737, -9750],
    poly [52434, -47027, 3429, 7604, -5138, -17529, -17135, -14670, -974, -18792, -26102, 7103, -5737,
      -9750],
    poly [13, -103, -57, -114, -17, 223, 288, 169, 412, 459, 409, 234, 504, 262, 369, 44, 96, 163],
    poly [-876, 787, -58, -127, 86, 293, 286, 245, 16, 314, 436, -119, 96, 163],
    poly [18372, -11589, 15666, -1658, 23397, 3976, 2099, 10475, 18683, -8776, -15270, 6805, -890, -1],
    poly [307, -194, 262, -28, 391, 66, 35, 175, 312, -147, -255, 114, -15],
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
theorem certificado_53239 :
    haveI : Fact (Nat.Prime 53239) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 53239 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((53239 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((53239 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((53239 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 53239) := ⟨by norm_num⟩
  have hP : poly [-1865, 1] = X - C (1865 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((53239 : ℕ) : ℤ[X]) = poly [53239] := by simp [poly]
  refine ⟨X - C (1865 : ℤ),
    poly [25235, 11689, -2620, 18097, -21657, -11944, -7143, 11586, -12126, 7073, -4792, -7653, -2402,
      484, 3226, 19556, 1866, 1],
    poly [884, 409, -92, 634, -759, -418, -250, 406, -425, 248, -168, -268, -84, 17, 113, 685, 65],
    poly [1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, -1],
    poly [12074, 11481, 15677, 21988, 1752, -11276, -521, 9476, 34802, 14148, 8028, -111, -8508, -1433,
      24548, 32298, 7895, 2087],
    poly [41165, -64720, -15677, -9914, -2345, 15472, 18906, -18231, -32153, 18595, 3721, 2087],
    poly [-423, -402, -549, -770, -61, 395, 18, -332, -1219, -495, -281, 4, 298, 50, -860, -1131, -276,
      -73],
    poly [-1442, 2268, 548, 347, 82, -542, -662, 639, 1126, -652, -130, -73],
    poly [25235, 11689, -2620, -7138, -8111, 2365, 144, -13588, -19219, -15825, -1864, -1],
    poly [884, 409, -92, -250, -284, 83, 5, -476, -673, -554, -65],
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
theorem certificado_53353 :
    haveI : Fact (Nat.Prime 53353) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 53353 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((53353 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((53353 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((53353 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 53353) := ⟨by norm_num⟩
  have hP : poly [-4270, 1] = X - C (4270 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((53353 : ℕ) : ℤ[X]) = poly [53353] := by simp [poly]
  refine ⟨X - C (4270 : ℤ),
    poly [1212, 26152, -3330, -17656, 5731, -8870, -25654, -10939, -25617, -2430, 11957, 21344, 8489,
      9673, 15196, -9555, 4271, 1],
    poly [97, 2093, -267, -1413, 459, -710, -2053, -875, -2050, -194, 957, 1708, 679, 774, 1216, -765,
      342],
    poly [-1, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1],
    poly [-18665, -18357, -18182, -16870, -6424, -22315, -22856, -7400, -13169, -10384, -24565, -16859,
      -19756, -29890, -18672, -9873, -3661, -9832],
    poly [34688, -34380, -133, 1137, 9134, -26337, -3315, 16305, -21050, -8799, -6212, 6171, -9832],
    poly [1494, 1469, 1455, 1350, 514, 1786, 1829, 592, 1054, 831, 1966, 1349, 1581, 2392, 1494, 790,
      293, 787],
    poly [-2776, 2752, 10, -91, -731, 2108, 265, -1305, 1685, 704, 497, -494, 787],
    poly [-1212, -23728, 1069, -15156, 15640, -15365, 971, -3086, 5522, -24751, 13826, -4270, -1],
    poly [-97, -1899, 86, -1213, 1252, -1230, 78, -247, 442, -1981, 1107, -342],
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
theorem certificado_53657 :
    haveI : Fact (Nat.Prime 53657) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 53657 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((53657 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((53657 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((53657 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 53657) := ⟨by norm_num⟩
  have hP : poly [-3745, 1] = X - C (3745 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((53657 : ℕ) : ℤ[X]) = poly [53657] := by simp [poly]
  refine ⟨X - C (3745 : ℤ),
    poly [-24314, -2084, 11175, 19245, 9576, -11173, -19245, -4547, 7005, -12062, -10620, 12147, -10284,
      25787, -21241, 24294, 3746, 1],
    poly [-1697, -145, 780, 1343, 668, -780, -1343, -317, 489, -842, -741, 848, -718, 1800, -1483, 1696,
      261],
    poly [1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [21849, 478, 372, -1376, -5904, 4468, 1376, -4055, -3512, -632, 1303, -8296, 9568, 1449, 186,
      -16592, -2713, 2420],
    poly [31808, -32286, 106, 1748, 26377, -31743, 2986, 3683, 16778, -13879, -5133, 2420],
    poly [-1525, -33, -26, 96, 412, -312, -96, 283, 245, 44, -91, 579, -668, -101, -13, 1158, 189, -169],
    poly [-2220, 2254, -8, -122, -1841, 2216, -209, -257, -1171, 969, 358, -169],
    poly [-24314, 22230, 13259, 8070, 14645, 10678, -21331, 6628, -8122, -20548, -3745, -1],
    poly [-1697, 1552, 925, 563, 1022, 745, -1489, 463, -567, -1434, -261],
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
theorem certificado_53923 :
    haveI : Fact (Nat.Prime 53923) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 53923 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((53923 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((53923 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((53923 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 53923) := ⟨by norm_num⟩
  have hP : poly [-729, 1] = X - C (729 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((53923 : ℕ) : ℤ[X]) = poly [53923] := by simp [poly]
  refine ⟨X - C (729 : ℤ),
    poly [-23448, 20679, -17872, 3452, -19375, 26750, -21784, -2101, -2074, -16054, -21177, -4837, 12568,
      -18179, -23325, -7059, 730, 1],
    poly [-317, 280, -242, 47, -262, 362, -295, -28, -28, -217, -286, -65, 170, -246, -315, -95, 10],
    poly [-1, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1],
    poly [-15810, -8065, -15969, -15610, -9766, 2003, -16399, -14649, -16052, -20566, -13989, -16273,
      -25966, -21985, -16210, -4663, 2010, -14032],
    poly [38113, -46178, -23714, 8104, -2060, -3682, -20623, -2450, -19605, -20275, 15081, -7746, -31354,
      -18220, 9369, 2010, -14032],
    poly [214, 109, 216, 211, 132, -27, 222, 198, 217, 278, 189, 220, 351, 297, 219, 63, -27, 190],
    poly [-515, 625, 320, -110, 28, 50, 279, 33, 265, 274, -204, 105, 424, 246, -127, -27, 190],
    poly [23448, 9796, 8076, -11528, 7455, 9922, -3241, 5987, 21607, 3876, -6282, 17300, 11119, 24055,
      7060, -730, -1],
    poly [317, 132, 109, -156, 101, 134, -44, 81, 292, 52, -85, 234, 150, 325, 95, -10],
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
theorem certificado_54037 :
    haveI : Fact (Nat.Prime 54037) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 54037 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((54037 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((54037 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((54037 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 54037) := ⟨by norm_num⟩
  have hP : poly [-853, 1] = X - C (853 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((54037 : ℕ) : ℤ[X]) = poly [54037] := by simp [poly]
  refine ⟨X - C (853 : ℤ),
    poly [-19765, 12520, 2612, 1080, -18180, -1415, 3926, -19507, -21625, -5220, 17605, -1183, -3739,
      1516, 7477, 25982, 854, 1],
    poly [-312, 198, 41, 17, -287, -22, 62, -308, -341, -82, 278, -19, -59, 24, 118, 410, 13],
    poly [1, 0, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1],
    poly [17978, 5836, -2477, 17595, 1021, -11795, 5421, 8672, 14694, -3987, 869, 9997, -4626, 15692,
      -2022, -13509, 9410, 11274],
    poly [36059, -41895, 8313, -2094, 4432, 22481, -9286, -10160, -10908, 28988, 11487, -22919, -1864,
      11274],
    poly [-284, -92, 39, -278, -16, 186, -86, -137, -232, 63, -14, -158, 73, -248, 32, 213, -149, -178],
    poly [-569, 662, -132, 33, -70, -355, 147, 160, 172, -458, -181, 362, 29, -178],
    poly [-19765, -21752, -9908, 18233, 2492, -7599, -25412, 25500, 4401, 5960, 18505, -25128, -853, -1],
    poly [-312, -343, -156, 288, 39, -120, -401, 403, 69, 94, 292, -397, -13],
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
theorem certificado_54151 :
    haveI : Fact (Nat.Prime 54151) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 54151 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((54151 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((54151 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((54151 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 54151) := ⟨by norm_num⟩
  have hP : poly [-2157, 1] = X - C (2157 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((54151 : ℕ) : ℤ[X]) = poly [54151] := by simp [poly]
  refine ⟨X - C (2157 : ℤ),
    poly [18929, -25096, -5610, 20508, -22635, -20019, 9882, 105, -19180, -5306, 6098, -14332, 12847,
      -23944, 11035, -2179, 2158, 1],
    poly [754, -1000, -223, 817, -902, -797, 394, 4, -764, -211, 243, -571, 512, -954, 440, -87, 86],
    poly [0, 1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 1, -1],
    poly [-29043, -15048, -19711, -19914, -22048, -24208, -21573, -26417, -11984, -22446, -17455, 1401,
      -14582, -14012, -27493, -5156, -11221, -6956],
    poly [54151, -25108, -13995, 4663, 29246, -40904, 20818, -7095, 35818, -28402, 10330, 2691, -6956],
    poly [1157, 599, 785, 793, 878, 964, 859, 1052, 477, 894, 695, -56, 581, 558, 1095, 205, 447, 277],
    poly [-2157, 1001, 557, -186, -1165, 1630, -830, 283, -1427, 1132, -412, -107, 277],
    poly [0, 18929, 10126, 19486, -9104, 2205, 11976, -17618, -5958, -17551, 6494, -2156, -1],
    poly [0, 754, 403, 776, -363, 88, 477, -702, -237, -699, 259, -86],
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
theorem certificado_54493 :
    haveI : Fact (Nat.Prime 54493) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 54493 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((54493 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((54493 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((54493 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 54493) := ⟨by norm_num⟩
  have hP : poly [-229, 1] = X - C (229 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((54493 : ℕ) : ℤ[X]) = poly [54493] := by simp [poly]
  refine ⟨X - C (229 : ℤ),
    poly [-12136, -53, -1428, -13570, -19810, -3180, -23572, 6322, -14488, 10407, 26935, 22010, -23462,
      -21043, 18707, -1822, 230, 1],
    poly [-51, 0, -6, -57, -83, -13, -99, 27, -61, 44, 113, 92, -99, -88, 79, -8, 1],
    poly [1, 1, -1, 1, 0, 1, 0, 0, 0, 0, 0, 0, -1],
    poly [18225, 9738, 3276, -4129, -12252, -15143, -6827, -4887, -2023, -11053, -13710, 794, 8948, 6604,
      5166, -8642, -16555, -32057],
    poly [36268, -64231, 33174, -12845, 17553, -8154, 2344, 1438, 13808, 7913, 15502, -32057],
    poly [-76, -40, -13, 18, 52, 64, 29, 21, 9, 47, 58, -3, -37, -27, -21, 37, 70, 135],
    poly [-153, 270, -140, 54, -74, 34, -10, -6, -58, -33, -65, 135],
    poly [-12136, -53, 22844, 16757, -4924, 9021, 2419, -14743, -20529, 2052, -229, -1],
    poly [-51, 0, 96, 70, -21, 38, 10, -62, -86, 9, -1],
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
theorem certificado_54721 :
    haveI : Fact (Nat.Prime 54721) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 54721 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((54721 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((54721 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((54721 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 54721) := ⟨by norm_num⟩
  have hP : poly [-322, 1] = X - C (322 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((54721 : ℕ) : ℤ[X]) = poly [54721] := by simp [poly]
  refine ⟨X - C (322 : ℤ),
    poly [-2889, 23103, -17942, -16540, -15516, -12114, 21205, 25557, 12655, 3778, 22274, -5199, 25475,
      -5359, 1003, -5435, 323, 1],
    poly [-17, 136, -106, -97, -91, -71, 125, 150, 74, 22, 131, -31, 150, -32, 6, -32, 2],
    poly [-1, -1, 0, 1, 0, 1, -1, 0, 0, 0, -1],
    poly [16472, -3190, -6310, 8975, 7493, -5767, -9207, 11855, 10221, -4399, 3033, 23449, 16035, -7100,
      24947, 20798, 18236, 3953],
    poly [71193, -57911, -22782, -4307, 33465, -28094, 4149, 2562, 14283, 3953],
    poly [-97, 19, 37, -53, -44, 34, 54, -70, -60, 26, -18, -138, -94, 42, -147, -122, -107, -23],
    poly [-419, 342, 133, 25, -197, 166, -25, -15, -84, -23],
    poly [2889, -23103, 15053, -17967, 23566, 6361, -6438, 5758, -322, -1],
    poly [17, -136, 89, -106, 139, 37, -38, 34, -2],
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
theorem certificado_54949 :
    haveI : Fact (Nat.Prime 54949) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 54949 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((54949 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((54949 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((54949 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 54949) := ⟨by norm_num⟩
  have hP : poly [-2108, 1] = X - C (2108 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((54949 : ℕ) : ℤ[X]) = poly [54949] := by simp [poly]
  refine ⟨X - C (2108 : ℤ),
    poly [-7794, 19364, 25268, -6218, -5868, -25418, -24541, -2879, 27421, 14819, -11306, 11438, 12700,
      12857, -27312, -5096, 2109, 1],
    poly [-299, 743, 969, -239, -225, -975, -941, -110, 1052, 568, -434, 439, 487, 493, -1048, -195, 81],
    poly [-1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, -1],
    poly [-26218, -13979, -14677, -14938, -16059, -16242, -13870, 10634, -7914, -207, 8894, 2929, -1427,
      6391, 1442, 3134, 2822, -11150],
    poly [28731, -42710, -698, 25957, -13360, 515, 2633, -593, -6126, 4637, -15664, 11462, 13972, -11150],
    poly [1006, 536, 563, 573, 616, 623, 532, -408, 304, 8, -341, -112, 55, -245, -55, -120, -108, 428],
    poly [-1102, 1639, 26, -996, 513, -20, -101, 23, 235, -178, 601, -440, -536, 428],
    poly [7794, -27158, -5904, 23692, 26808, 25454, 22586, -13518, -22059, 7575, 24324, 7206, -2108, -1],
    poly [299, -1042, -226, 909, 1028, 976, 866, -519, -846, 291, 933, 276, -81],
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
theorem certificado_55291 :
    haveI : Fact (Nat.Prime 55291) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 55291 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((55291 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((55291 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((55291 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 55291) := ⟨by norm_num⟩
  have hP : poly [-5627, 1] = X - C (5627 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((55291 : ℕ) : ℤ[X]) = poly [55291] := by simp [poly]
  refine ⟨X - C (5627 : ℤ),
    poly [-12312, 10266, -12546, 4390, 18061, -25682, 133, 21745, -6894, -19555, 18833, 24421, -13418,
      -5220, 22481, -12986, 5628, 1],
    poly [-1253, 1045, -1277, 447, 1838, -2614, 14, 2213, -702, -1990, 1917, 2485, -1366, -531, 2288,
      -1322, 573],
    poly [1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, -1],
    poly [-226, -18188, -2332, -15781, -3324, -9974, 1197, -25459, -6755, -10122, 3624, -1375, -10180,
      8311, -18835, -6292, -4639, 9],
    poly [55517, -37103, 2106, -2407, 992, -5807, -4295, 33447, -7904, -1662, -4648, 9],
    poly [23, 1851, 237, 1606, 338, 1015, -122, 2591, 687, 1030, -369, 140, 1036, -846, 1917, 640, 472,
      -1],
    poly [-5650, 3777, -215, 245, -101, 591, 437, -3404, 805, 169, 473, -1],
    poly [-12312, 10266, -234, -5876, -24684, 25219, 25051, 14714, 25452, 18615, -5627, -1],
    poly [-1253, 1045, -24, -598, -2512, 2567, 2549, 1497, 2590, 1894, -573],
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
theorem certificado_55633 :
    haveI : Fact (Nat.Prime 55633) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 55633 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((55633 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((55633 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((55633 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 55633) := ⟨by norm_num⟩
  have hP : poly [-141, 1] = X - C (141 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((55633 : ℕ) : ℤ[X]) = poly [55633] := by simp [poly]
  refine ⟨X - C (141 : ℤ),
    poly [9864, 13485, 12327, -25559, -4916, -10688, 11761, -5835, -13851, 1480, -13010, -4827, 1544,
      23290, -14039, 20023, 142, 1],
    poly [25, 34, 31, -65, -12, -27, 30, -15, -35, 4, -33, -12, 4, 59, -36, 51],
    poly [1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1],
    poly [21953, 1197, 8941, 6234, 4242, 14881, -4377, 25473, -5091, 2978, 21185, 10661, 8219, 7018,
      3853, 13300, 13367, 20075],
    poly [33680, -56830, -8941, -6234, -4242, 7072, 5574, -16532, -10628, 67, 6708, -20075],
    poly [-56, -3, -23, -16, -11, -38, 11, -65, 13, -8, -54, -27, -21, -18, -10, -34, -34, -51],
    poly [-85, 145, 22, 16, 11, -18, -14, 42, 27, 0, -17, 51],
    poly [9864, 13485, 12327, -25559, -4916, -20552, -1724, -18162, 21572, 19881, 141, 1],
    poly [25, 34, 31, -65, -12, -52, -4, -46, 55, 50],
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
theorem certificado_55823 :
    haveI : Fact (Nat.Prime 55823) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 55823 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((55823 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((55823 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((55823 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 55823) := ⟨by norm_num⟩
  have hP : poly [-5421, 1] = X - C (5421 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((55823 : ℕ) : ℤ[X]) = poly [55823] := by simp [poly]
  refine ⟨X - C (5421 : ℤ),
    poly [3357, 10154, 24232, -9356, -16900, 20489, -4280, 24806, 17531, -10768, -21771, 16297, 868,
      -7723, 27596, -26058, 5422, 1],
    poly [326, 986, 2353, -909, -1641, 1990, -416, 2409, 1702, -1046, -2114, 1583, 84, -750, 2680, -2531,
      527],
    poly [1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1],
    poly [-4816, -26174, -4100, -29397, -14151, -5282, -24856, -18609, -340, -35719, -3937, -18358,
      -5602, -11253, -20666, -17043, -10040, -17628],
    poly [60639, -29649, 4100, 24581, -12023, 1182, -4541, 9274, 16416, -11211, 10625, 7588, -17628],
    poly [468, 2542, 398, 2855, 1374, 513, 2414, 1807, 33, 3469, 382, 1783, 544, 1093, 2007, 1655, 975,
      1712],
    poly [-5889, 2880, -399, -2387, 1168, -115, 441, -901, -1594, 1089, -1032, -737, 1712],
    poly [3357, 10154, 24232, -12713, -27054, -3743, 5076, -10760, 3839, 7590, -24342, -5421, -1],
    poly [326, 986, 2353, -1235, -2627, -363, 493, -1045, 373, 737, -2364, -526],
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
theorem certificado_56393 :
    haveI : Fact (Nat.Prime 56393) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 56393 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((56393 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((56393 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((56393 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 56393) := ⟨by norm_num⟩
  have hP : poly [-4018, 1] = X - C (4018 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((56393 : ℕ) : ℤ[X]) = poly [56393] := by simp [poly]
  refine ⟨X - C (4018 : ℤ),
    poly [800, -18877, -10924, -915, -309, 22428, -8626, 21654, -9749, 17766, -964, -17502, 16936,
      -13680, 4558, 19945, 4019, 1],
    poly [57, -1345, -778, -65, -22, 1598, -615, 1543, -695, 1266, -69, -1247, 1207, -975, 325, 1421,
      286],
    poly [-1, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, -1],
    poly [-7139, 8368, 9228, -2056, 2264, -13763, 6626, -6997, 7554, -16288, -3522, -9189, 12971, -7627,
      4017, -6338, -12109, -19535],
    poly [49254, -40886, -6279, -2916, 20687, -33590, 21793, -8963, 8489, -31179, 10355, 5771, 7426,
      -19535],
    poly [509, -596, -657, 147, -161, 981, -472, 499, -538, 1161, 251, 655, -924, 544, -286, 452, 863,
      1392],
    poly [-3509, 2914, 447, 208, -1474, 2394, -1553, 639, -605, 2222, -738, -411, -529, 1392],
    poly [-800, 19677, -8753, 8868, 11118, 14894, -17077, 14494, 21758, 18237, 15387, -15926, -4018, -1],
    poly [-57, 1402, -624, 632, 792, 1061, -1217, 1033, 1550, 1299, 1096, -1135, -286],
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
theorem certificado_56431 :
    haveI : Fact (Nat.Prime 56431) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 56431 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((56431 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((56431 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((56431 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 56431) := ⟨by norm_num⟩
  have hP : poly [-6079, 1] = X - C (6079 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((56431 : ℕ) : ℤ[X]) = poly [56431] := by simp [poly]
  refine ⟨X - C (6079 : ℤ),
    poly [15781, 5823, -7314, -19811, 25432, 10661, -4649, 21350, -15499, -22885, 5566, -14629, 16809,
      -21348, 15499, -1984, 6080, 1],
    poly [1700, 627, -788, -2134, 2740, 1148, -501, 2300, -1670, -2465, 600, -1576, 1811, -2300, 1670,
      -214, 655],
    poly [-1, 1, 0, 0, 0, 1, 0, 0, 0, -1, -1],
    poly [-42634, -5862, -24821, -30004, -5600, -39980, -16834, -5997, -38764, -19990, -29734, -34145,
      -3577, -24997, -17667, -8847, -38421, -15497],
    poly [13797, 22975, -55731, 13776, 29587, -16150, 20754, 6650, -38421, -15497],
    poly [4593, 631, 2674, 3232, 603, 4307, 1813, 646, 4176, 2153, 3203, 3678, 385, 2693, 1903, 953,
      4139, 1669],
    poly [-1486, -2475, 6004, -1485, -3187, 1740, -2236, -716, 4139, 1669],
    poly [-15781, 25739, 3179, -640, -1309, 19364, -9419, 1985, -6080, -1],
    poly [-1700, 2773, 342, -69, -141, 2086, -1015, 214, -655],
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
theorem certificado_56659 :
    haveI : Fact (Nat.Prime 56659) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 56659 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((56659 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((56659 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((56659 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 56659) := ⟨by norm_num⟩
  have hP : poly [-4364, 1] = X - C (4364 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((56659 : ℕ) : ℤ[X]) = poly [56659] := by simp [poly]
  refine ⟨X - C (4364 : ℤ),
    poly [-24837, 1786, 26707, -9991, -4884, -21826, -3887, -19320, 26053, 7744, 12245, 15375, 19037,
      -22223, -5510, 11437, 4365, 1],
    poly [-1913, 138, 2057, -770, -376, -1681, -299, -1488, 2007, 596, 943, 1184, 1466, -1712, -424, 881,
      336],
    poly [0, -1, 0, -2, -1, -1, -1, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1],
    poly [34, -5393, -4031, -1460, -226, -3887, 5551, 18874, 33665, 20776, 20033, 36976, 43874, 32684,
      19049, 17397, 7789, 21601],
    poly [56659, -56625, -5427, 1430, -8249, -1435, -2550, 10412, 11168, 33845, 15375, 43874, 32684,
      19049, 17397, 7789, 21601],
    poly [-3, 415, 310, 112, 17, 299, -428, -1454, -2593, -1600, -1543, -2848, -3379, -2517, -1467,
      -1340, -600, -1664],
    poly [-4364, 4362, 417, -111, 635, 110, 196, -802, -860, -2607, -1184, -3379, -2517, -1467, -1340,
      -600, -1664],
    poly [0, 24837, -26623, 24753, 8289, -76, 6972, 13660, -672, -7881, -15374, -19037, 22223, 5510,
      -11437, -4365, -1],
    poly [0, 1913, -2051, 1907, 638, -6, 537, 1052, -52, -607, -1184, -1466, 1712, 424, -881, -336],
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
theorem certificado_56773 :
    haveI : Fact (Nat.Prime 56773) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 56773 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((56773 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((56773 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((56773 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 56773) := ⟨by norm_num⟩
  have hP : poly [-2620, 1] = X - C (2620 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((56773 : ℕ) : ℤ[X]) = poly [56773] := by simp [poly]
  refine ⟨X - C (2620 : ℤ),
    poly [-23901, 24997, 7117, -12392, -20352, -25989, 23176, 28287, 10802, 7870, -11980, 5131, -17550,
      9246, 4229, -2512, 2621, 1],
    poly [-1103, 1154, 328, -572, -939, -1199, 1070, 1305, 498, 363, -553, 237, -810, 427, 195, -116,
      121],
    poly [-1, 0, 0, 0, 1, -1, 0, 0, 1, 0, 0, -1],
    poly [-18238, -21582, -10142, -1470, -10221, -16140, -7843, -9335, -16183, -13672, -7322, 9799, -964,
      -8964, -5500, 12530, -16283, -19306],
    poly [38535, -60117, 11440, 8672, 9487, -20813, -6487, 1276, 28813, 3023, -19306],
    poly [842, 996, 468, 68, 472, 745, 362, 431, 747, 631, 338, -452, 45, 414, 254, -578, 752, 891],
    poly [-1778, 2775, -529, -400, -438, 961, 299, -59, -1330, -139, 891],
    poly [23901, 7875, 17880, 19509, -15941, 21663, -2397, -6740, 5133, -2620, -1],
    poly [1103, 363, 825, 900, -736, 1000, -111, -311, 237, -121],
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
theorem certificado_56963 :
    haveI : Fact (Nat.Prime 56963) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 56963 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((56963 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((56963 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((56963 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 56963) := ⟨by norm_num⟩
  have hP : poly [-3936, 1] = X - C (3936 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((56963 : ℕ) : ℤ[X]) = poly [56963] := by simp [poly]
  refine ⟨X - C (3936 : ℤ),
    poly [23778, -11731, 15685, 2609, 19683, 9412, -24094, -2944, 18683, -23122, 11818, 13853, -12790,
      18941, -5842, 2097, 3937, 1],
    poly [1643, -811, 1084, 180, 1360, 650, -1665, -203, 1291, -1598, 817, 957, -884, 1309, -404, 145,
      272],
    poly [0, 0, -1, 0, -1, 1, 0, 0, -1, 0, -1, 0, 0, -1, 0, -1, 0, -1],
    poly [9322, -6161, -3256, 17773, 11425, 2219, -6322, 8481, -2876, -17713, 4614, 8368, 6777, 14143,
      26620, 11818, -603, -7220],
    poly [56963, -56963, 9322, -15483, 12227, -3776, 12040, 8918, -26596, -3538, 1535, 14053, -7276,
      21419, 5201, 6617, -7220],
    poly [-644, 426, 225, -1228, -789, -153, 437, -586, 199, 1224, -319, -578, -468, -977, -1839, -816,
      42, 499],
    poly [-3936, 3937, -645, 1070, -845, 261, -832, -616, 1838, 244, -106, -971, 503, -1480, -359, -457,
      499],
    poly [0, 0, -23778, -21454, 5769, 15400, -23036, -6200, -20422, -15259, 7377, -21229, -22944, 4003,
      1839, -3936, -1],
    poly [0, 0, -1643, -1482, 399, 1064, -1592, -428, -1411, -1054, 510, -1467, -1585, 277, 127, -272],
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
theorem certificado_57077 :
    haveI : Fact (Nat.Prime 57077) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 57077 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((57077 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((57077 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((57077 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 57077) := ⟨by norm_num⟩
  have hP : poly [-5388, 1] = X - C (5388 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((57077 : ℕ) : ℤ[X]) = poly [57077] := by simp [poly]
  refine ⟨X - C (5388 : ℤ),
    poly [15943, 575, -18962, -9760, 27721, 7251, -5825, 19639, -21289, -10449, -3413, -22056, 3354,
      24270, 4316, -16260, 5389, 1],
    poly [1505, 54, -1790, -921, 2617, 684, -550, 1854, -2010, -986, -322, -2082, 317, 2291, 407, -1535,
      509],
    poly [1, 0, 0, 0, -1, 0, 0, 0, 1, -1, -1],
    poly [19351, 7543, 22541, 4980, 17318, -74, 516, 11851, 3728, 1004, -5861, 26225, 3201, 12646, 137,
      4086, 1110, 16491],
    poly [37726, -45269, -14998, 17561, 7013, 5584, 14408, -28896, 1110, 16491],
    poly [-1827, -712, -2128, -470, -1635, 7, -49, -1119, -352, -95, 553, -2476, -302, -1194, -13, -386,
      -105, -1557],
    poly [-3561, 4274, 1415, -1658, -662, -527, -1360, 2728, -105, -1557],
    poly [15943, -15368, -19537, 9202, 21538, -5102, 6461, 16262, -5389, -1],
    poly [1505, -1451, -1844, 869, 2033, -482, 610, 1535, -509],
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
theorem certificado_57191 :
    haveI : Fact (Nat.Prime 57191) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 57191 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((57191 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((57191 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((57191 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 57191) := ⟨by norm_num⟩
  have hP : poly [-1978, 1] = X - C (1978 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((57191 : ℕ) : ℤ[X]) = poly [57191] := by simp [poly]
  refine ⟨X - C (1978 : ℤ),
    poly [22408, -16267, -2090, 15699, 21057, 2902, 20559, 9841, -23415, -21697, 28093, 15801, 23081,
      1573, 4280, 25475, 1979, 1],
    poly [775, -563, -72, 543, 728, 100, 711, 340, -810, -750, 972, 546, 798, 54, 148, 881, 68],
    poly [-1, 0, 0, 0, -1, -1, -2, -1, -1, 0, -1],
    poly [-25822, -7793, -4401, -5498, -16052, -6805, -10588, 1814, -11133, -24700, 14471, -19020,
      -12994, -15651, -13426, -674, -21254, 4353],
    poly [31369, -39162, 3392, -1097, -36376, 1454, -34006, 24933, -25607, 4353],
    poly [893, 269, 152, 190, 555, 235, 366, -63, 385, 854, -501, 658, 449, 541, 464, 23, 735, -151],
    poly [-1085, 1355, -118, 38, 1258, -51, 1176, -863, 886, -151],
    poly [-22408, -18516, -14177, -17789, -27766, -22769, 19216, -23497, -1978, -1],
    poly [-775, -640, -490, -615, -960, -787, 665, -813, -68],
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
theorem certificado_57457 :
    haveI : Fact (Nat.Prime 57457) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 57457 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((57457 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((57457 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((57457 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 57457) := ⟨by norm_num⟩
  have hP : poly [-701, 1] = X - C (701 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((57457 : ℕ) : ℤ[X]) = poly [57457] := by simp [poly]
  refine ⟨X - C (701 : ℤ),
    poly [2295, 21314, -17428, 9483, 15013, 21660, -7100, -20993, -25193, 18488, -24399, -22575, -14294,
      -922, -7624, -25010, 702, 1],
    poly [28, 260, -213, 116, 183, 264, -87, -256, -307, 226, -298, -275, -174, -11, -93, -305, 9],
    poly [0, 0, -1, -1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, -1],
    poly [-20054, -19181, -11721, -10235, -30642, -24032, -25334, -25008, -26237, -21075, -31723, -13788,
      -35401, -18957, -8688, -18673, -28441, -19111],
    poly [57457, -57457, -20054, -19181, -11721, 9819, -11461, -32365, -14226, -6960, 154, -8688, -18673,
      -28441, -19111],
    poly [245, 234, 143, 125, 374, 293, 309, 305, 320, 257, 387, 168, 432, 231, 106, 228, 347, 233],
    poly [-701, 702, 244, 234, 143, -120, 140, 395, 173, 85, -2, 106, 228, 347, 233],
    poly [0, 0, -2295, -21314, 17428, -7188, 6301, 16074, -2436, 14996, 923, 7624, 25010, -702, -1],
    poly [0, 0, -28, -260, 213, -88, 77, 196, -30, 183, 11, 93, 305, -9],
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
theorem certificado_57571 :
    haveI : Fact (Nat.Prime 57571) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 57571 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((57571 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((57571 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((57571 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 57571) := ⟨by norm_num⟩
  have hP : poly [-1405, 1] = X - C (1405 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((57571 : ℕ) : ℤ[X]) = poly [57571] := by simp [poly]
  refine ⟨X - C (1405 : ℤ),
    poly [-5081, 27737, -7192, 9952, 13693, 23284, -7482, -24263, -25873, 26370, 13172, 24349, -7891,
      27735, -17354, 18017, 1406, 1],
    poly [-124, 677, -176, 243, 334, 568, -183, -592, -631, 644, 321, 594, -193, 677, -424, 440, 34],
    poly [1, 0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1],
    poly [34342, 28343, 2483, -15155, 4214, 29264, 18833, -15758, -8366, 14094, 27632, 16865, 2188,
      -17204, 13596, 30418, 10065, -6012],
    poly [23229, -51572, -8482, 23637, 6491, -7412, 25404, -30800, -16822, 20353, 16077, -6012],
    poly [-838, -691, -60, 370, -103, -714, -459, 385, 204, -344, -674, -411, -53, 420, -332, -742, -245,
      147],
    poly [-567, 1259, 206, -577, -158, 181, -620, 752, 410, -497, -392, 147],
    poly [-5081, -24753, 17561, -7609, 26383, 26735, -21944, 12482, -22200, -16611, -1405, -1],
    poly [-124, -604, 429, -186, 644, 652, -536, 305, -542, -405, -34],
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
theorem certificado_58027 :
    haveI : Fact (Nat.Prime 58027) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 58027 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((58027 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((58027 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((58027 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 58027) := ⟨by norm_num⟩
  have hP : poly [-364, 1] = X - C (364 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((58027 : ℕ) : ℤ[X]) = poly [58027] := by simp [poly]
  refine ⟨X - C (364 : ℤ),
    poly [21521, -18433, -12485, -11831, 13996, -26265, -28448, 8052, 3051, -10513, 24521, 2618, 23760,
      16485, 24914, 16807, 365, 1],
    poly [135, -116, -78, -74, 88, -165, -178, 51, 19, -66, 154, 16, 149, 103, 156, 105, 2],
    poly [1, 1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, -1],
    poly [-908, -14939, -26296, -22023, -8461, -453, -431, -9677, -1094, -15896, -30284, -18208, -2871,
      -12872, -3494, -9526, -1253, -17650],
    poly [58935, -43088, 25388, 7992, -3804, -9305, 1728, 7019, -11618, -8273, 16397, -17650],
    poly [6, 94, 165, 138, 53, 3, 3, 61, 7, 100, 190, 114, 18, 81, 22, 60, 8, 111],
    poly [-370, 271, -160, -50, 24, 58, -11, -44, 73, 52, -103, 111],
    poly [21521, -18433, 24021, 28123, -13473, 13035, -23717, 8065, -8108, -16442, -364, -1],
    poly [135, -116, 151, 176, -85, 82, -149, 51, -51, -103, -2],
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
theorem certificado_58217 :
    haveI : Fact (Nat.Prime 58217) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 58217 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((58217 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((58217 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((58217 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 58217) := ⟨by norm_num⟩
  have hP : poly [-1270, 1] = X - C (1270 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((58217 : ℕ) : ℤ[X]) = poly [58217] := by simp [poly]
  refine ⟨X - C (1270 : ℤ),
    poly [23516, 24543, -24551, 26843, -27758, -6577, 5679, 25950, 13910, -20938, 2138, -12421, -17154,
      -26830, 1950, -15905, 1271, 1],
    poly [513, 535, -536, 586, -606, -143, 124, 566, 303, -457, 47, -271, -374, -585, 43, -347, 28],
    poly [-1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [12412, 31858, 34257, 31646, 12987, 16502, 25902, 25451, 35673, 33114, 14180, 22508, 23248,
      28291, 25132, 27284, 11425, 13567],
    poly [70629, -26359, 21845, 12200, -1824, -333, 29750, -7311, 10675, 10816, 1017, 11415, 15859,
      -2142, 13567],
    poly [-271, -695, -747, -690, -283, -360, -565, -555, -778, -722, -309, -491, -507, -617, -548, -595,
      -249, -296],
    poly [-1541, 576, -477, -266, 40, 7, -649, 160, -233, -236, -22, -249, -346, 47, -296],
    poly [-23516, -24543, -10150, -25816, 2180, 781, -27641, 12951, -22589, 7500, 27510, -17856, 17176,
      -1270, -1],
    poly [-513, -535, -221, -563, 48, 17, -603, 283, -493, 164, 600, -390, 375, -28],
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
theorem certificado_58369 :
    haveI : Fact (Nat.Prime 58369) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 58369 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((58369 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((58369 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((58369 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 58369) := ⟨by norm_num⟩
  have hP : poly [-5523, 1] = X - C (5523 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((58369 : ℕ) : ℤ[X]) = poly [58369] := by simp [poly]
  refine ⟨X - C (5523 : ℤ),
    poly [-14225, 473, 1765, -5770, -25661, -2224, -14627, 2185, 15092, -11707, -19543, -1853, 9638,
      -22456, 2712, -17934, 5524, 1],
    poly [-1346, 45, 167, -546, -2428, -210, -1384, 207, 1428, -1108, -1849, -175, 912, -2125, 257,
      -1697, 523],
    poly [1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1],
    poly [-5190, 3845, -1818, -8773, -8193, 12278, 9312, 18749, 11374, -8908, -2391, 11962, 8625, -6203,
      11063, 3161, 15905, 5191],
    poly [63559, -67404, 5663, 12145, -9615, -9618, 886, 836, -9986, 19296, -23807, 7553, -10714, -5191],
    poly [491, -364, 172, 830, 775, -1162, -881, -1774, -1076, 843, 226, -1132, -816, 587, -1047, -299,
      -1505, -491],
    poly [-6014, 6379, -537, -1149, 910, 910, -84, -79, 945, -1826, 2253, -715, 1014, 491],
    poly [-14225, 14698, 1292, -21760, -5193, 10504, -5240, -16012, -29087, 15266, 26170, -23457, 5523,
      1],
    poly [-1346, 1391, 122, -2059, -491, 994, -496, -1515, -2752, 1445, 2476, -2220, 523],
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
theorem certificado_58711 :
    haveI : Fact (Nat.Prime 58711) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 58711 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((58711 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((58711 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((58711 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 58711) := ⟨by norm_num⟩
  have hP : poly [-2472, 1] = X - C (2472 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((58711 : ℕ) : ℤ[X]) = poly [58711] := by simp [poly]
  refine ⟨X - C (2472 : ℤ),
    poly [-14654, 10468, -28425, -59, 1425, 24891, 25328, -29084, -28441, 321, -7600, -10287, 9496,
      -5340, -5251, 7313, 2473, 1],
    poly [-617, 441, -1197, -2, 60, 1048, 1066, -1225, -1197, 14, -320, -433, 400, -225, -221, 308, 104],
    poly [-1, 0, 0, -1, -1, 0, 0, -2, -1, 0, -1],
    poly [-30624, -7836, -20652, -9827, -17399, -13697, -13553, -16973, 5541, -30123, -5057, -42620,
      -16486, -20703, 6062, -27819, -1066, -34662],
    poly [28087, -35923, -12816, -19799, -15408, 13674, -1847, -61415, 33596, -34662],
    poly [1290, 330, 870, 414, 733, 577, 571, 715, -233, 1269, 213, 1795, 694, 872, -255, 1172, 45, 1460],
    poly [-1182, 1513, 539, 834, 649, -576, 78, 2587, -1415, 1460],
    poly [14654, -25122, -19818, -13712, -11952, -9695, 10090, -4841, -2472, -1],
    poly [617, -1058, -834, -577, -503, -408, 425, -204, -104],
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
theorem certificado_58787 :
    haveI : Fact (Nat.Prime 58787) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 58787 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((58787 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((58787 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((58787 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 58787) := ⟨by norm_num⟩
  have hP : poly [-11544, 1] = X - C (11544 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((58787 : ℕ) : ℤ[X]) = poly [58787] := by simp [poly]
  refine ⟨X - C (11544 : ℤ),
    poly [21322, -6491, -20961, -5797, -4105, 14289, -14502, 13346, -13010, 4689, -19636, 19100, -11329,
      22477, -1648, 5352, 11545, 1],
    poly [4187, -1275, -4116, -1138, -806, 2806, -2848, 2621, -2555, 921, -3856, 3751, -2225, 4414, -324,
      1051, 2267],
    poly [1, 0, 0, 0, -1, 0, 1, 1, 0, 0, -1],
    poly [23210, 8556, 8239, 6808, 8137, 6533, -7013, 268, 11253, -3509, 6257, -841, 24977, 15049, 7878,
      2953, 20221, 14906],
    poly [35577, -44133, 317, 1431, 21881, -13050, -9981, -17268, 5315, 14906],
    poly [-4558, -1680, -1618, -1337, -1598, -1283, 1377, -53, -2210, 689, -1229, 165, -4905, -2955,
      -1547, -580, -3971, -2927],
    poly [-6986, 8667, -63, -281, -4297, 2563, 1960, 3391, -1044, -2927],
    poly [21322, -27813, -14470, 15164, -19630, -12580, 7001, 6193, -11544, -1],
    poly [4187, -5462, -2841, 2978, -3855, -2470, 1375, 1216, -2267],
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
theorem certificado_58901 :
    haveI : Fact (Nat.Prime 58901) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 58901 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((58901 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((58901 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((58901 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 58901) := ⟨by norm_num⟩
  have hP : poly [-1336, 1] = X - C (1336 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((58901 : ℕ) : ℤ[X]) = poly [58901] := by simp [poly]
  refine ⟨X - C (1336 : ℤ),
    poly [-21647, 2100, 24382, 22547, -424, -11419, -1243, -11111, 10220, -21463, -20120, 13608, -13172,
      -16190, -25627, 19203, 1337, 1],
    poly [-491, 48, 553, 511, -10, -259, -28, -252, 232, -487, -456, 309, -299, -367, -581, 436, 30],
    poly [-1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, -1],
    poly [9336, 16397, 17769, 31349, 22718, 21433, 6310, 10487, 16971, 15036, 6702, 14367, 14505, -2160,
      19210, 7146, 24772, 14116],
    poly [68237, -42504, 8433, 14952, 14285, -2855, -5700, 9695, 3402, 26180, -17626, 10656, 14116],
    poly [-212, -372, -403, -711, -515, -486, -143, -238, -385, -341, -152, -326, -329, 49, -436, -162,
      -562, -320],
    poly [-1548, 965, -192, -339, -324, 65, 129, -220, -77, -594, 400, -242, -320],
    poly [21647, -2100, 12872, -20447, -12448, 10219, 184, -22220, -10774, -14072, -17866, -1336, -1],
    poly [491, -48, 292, -464, -282, 232, 4, -504, -244, -319, -405, -30],
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
theorem certificado_59053 :
    haveI : Fact (Nat.Prime 59053) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59053 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59053 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59053 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59053 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59053) := ⟨by norm_num⟩
  have hP : poly [-2250, 1] = X - C (2250 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59053 : ℕ) : ℤ[X]) = poly [59053] := by simp [poly]
  refine ⟨X - C (2250 : ℤ),
    poly [-13989, -4468, 20286, 17200, 14889, -11699, 23616, 7753, 21420, -4531, 24774, 26493, -20040,
      -28958, -3871, -13807, 2251, 1],
    poly [-533, -170, 773, 655, 567, -446, 900, 295, 816, -173, 944, 1009, -764, -1103, -147, -526, 86],
    poly [-1, 0, 0, -1, -1, 0, -1, 1, 0, -1],
    poly [8157, 26034, 17932, 1761, 17685, 30605, 7252, 3331, 12699, 23044, 346, 6005, 38736, 15733,
      6563, -9451, 17785, 12233],
    poly [67210, -41176, -8102, -8014, 41958, 22695, -39469, 5552, 12233],
    poly [-311, -992, -683, -67, -674, -1166, -276, -127, -484, -878, -13, -229, -1476, -599, -250, 360,
      -678, -466],
    poly [-2561, 1570, 308, 305, -1599, -864, 1504, -212, -466],
    poly [13989, -9521, -24754, 17075, 6779, -7687, 16059, -2250, -1],
    poly [533, -363, -943, 651, 258, -293, 612, -86],
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
theorem certificado_59167 :
    haveI : Fact (Nat.Prime 59167) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59167 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59167 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59167 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59167 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59167) := ⟨by norm_num⟩
  have hP : poly [-1879, 1] = X - C (1879 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59167 : ℕ) : ℤ[X]) = poly [59167] := by simp [poly]
  refine ⟨X - C (1879 : ℤ),
    poly [-27521, 22972, -14504, 7644, 4318, 821, 24593, -14881, -13548, -11595, 13282, -27325, -26276,
      28924, 16232, -17499, 1880, 1],
    poly [-874, 730, -461, 243, 137, 26, 781, -473, -430, -368, 422, -868, -834, 919, 515, -556, 60],
    poly [-1, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, -1],
    poly [-3328, -2700, 3724, 7632, -5906, -10605, 7278, 14215, -4517, -5818, -14604, 1419, -1249, -1030,
      -8965, -2703, -19672, -18390],
    poly [55839, -58539, 3096, 1208, -6486, 2305, 8881, -4876, -1640, 6653, -24652, 16969, -1282, -18390],
    poly [106, 86, -118, -242, 188, 337, -231, -451, 144, 185, 464, -45, 40, 33, 285, 86, 625, 584],
    poly [-1773, 1860, -99, -38, 206, -73, -282, 155, 52, -211, 783, -539, 41, 584],
    poly [27521, 8674, 5830, 14047, -9691, -12821, 25247, 24606, 15411, -14571, 25435, 19379, -1879, -1],
    poly [874, 275, 185, 446, -308, -407, 802, 781, 489, -463, 808, 615, -60],
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
theorem certificado_59243 :
    haveI : Fact (Nat.Prime 59243) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59243 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59243 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59243 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59243 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59243) := ⟨by norm_num⟩
  have hP : poly [-1796, 1] = X - C (1796 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59243 : ℕ) : ℤ[X]) = poly [59243] := by simp [poly]
  refine ⟨X - C (1796 : ℤ),
    poly [14217, 28244, 18323, 7597, 7657, -15961, -28179, -25349, 25781, 22181, 17429, -19650, -11721,
      1115, -19857, 28291, 1797, 1],
    poly [431, 856, 555, 230, 232, -484, -854, -768, 782, 672, 528, -596, -355, 34, -602, 858, 54],
    poly [1, 0, -1, 0, 0, 0, -1, -1, 0, -1],
    poly [7560, -6158, -5308, -4186, -19293, 1051, -5271, 2972, -5105, 12670, -23110, 752, -19884, -9208,
      -9334, 4718, -5170, -11113],
    poly [51683, -45525, 6710, -14840, 15957, -19222, -1225, 5943, -11113],
    poly [-229, 187, 161, 127, 585, -32, 160, -90, 155, -384, 701, -23, 603, 279, 283, -143, 157, 337],
    poly [-1567, 1381, -204, 450, -484, 583, 37, -180, 337],
    poly [14217, 14027, -24138, -24753, 9981, -12892, -26495, -1796, -1],
    poly [431, 425, -732, -750, 303, -391, -803, -54],
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
theorem certificado_59281 :
    haveI : Fact (Nat.Prime 59281) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59281 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59281 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59281 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59281 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59281) := ⟨by norm_num⟩
  have hP : poly [-6672, 1] = X - C (6672 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59281 : ℕ) : ℤ[X]) = poly [59281] := by simp [poly]
  refine ⟨X - C (6672 : ℤ),
    poly [-26433, 15225, 16564, 19594, 22953, 8462, -17600, -9945, 8617, -10874, -5306, -21085, -6276,
      7578, -27658, 2226, 6673, 1],
    poly [-2975, 1714, 1864, 2205, 2583, 952, -1981, -1119, 970, -1224, -597, -2373, -706, 853, -3113,
      251, 751],
    poly [-1, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1, -1],
    poly [-13025, 1198, -2345, 9516, -5880, -4283, 1146, -13398, -17665, 4467, -24566, -2029, 3723,
      -9426, -12440, -7838, -7784, -3146],
    poly [46256, -45058, -3543, 11861, -28421, 2795, 16109, -6226, -7802, -4692, -7784, -3146],
    poly [1466, -135, 264, -1071, 662, 482, -129, 1508, 1988, -503, 2765, 228, -419, 1061, 1400, 882,
      876, 354],
    poly [-5206, 5072, 398, -1335, 3199, -315, -1813, 701, 878, 528, 876, 354],
    poly [26433, 17623, -1339, -3030, 23074, -734, -16935, -12024, -24951, -2225, -6673, -1],
    poly [2975, 1983, -151, -341, 2597, -83, -1906, -1353, -2808, -250, -751],
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
theorem certificado_59357 :
    haveI : Fact (Nat.Prime 59357) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59357 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59357 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59357 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59357 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59357) := ⟨by norm_num⟩
  have hP : poly [-11222, 1] = X - C (11222 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59357 : ℕ) : ℤ[X]) = poly [59357] := by simp [poly]
  refine ⟨X - C (11222 : ℤ),
    poly [-11663, 9012, -25954, 7535, 20682, -24345, 16490, -5473, 24870, 28845, -27904, -1584, -25828,
      -6852, 27340, -11047, 11223, 1],
    poly [-2205, 1704, -4907, 1425, 3910, -4603, 3118, -1035, 4702, 5453, -5276, -299, -4883, -1295,
      5169, -2089, 2122],
    poly [-1, 0, -1, -1, -1, 0, 0, -1, -1, -1, -1, -1],
    poly [-28402, -9511, -16962, -19327, -1317, -15110, -25399, -6152, -16565, -18962, -18026, -23146,
      -24564, -2095, -7303, -25996, -24194, -19846],
    poly [30955, -40466, -35853, -11876, 1048, -4718, -2095, -7303, -25996, -24194, -19846],
    poly [5370, 1798, 3207, 3654, 249, 2857, 4802, 1163, 3132, 3585, 3408, 4376, 4644, 396, 1381, 4915,
      4574, 3752],
    poly [-5852, 7651, 6778, 2245, -198, 892, 396, 1381, 4915, 4574, 3752],
    poly [11663, -20675, -12728, 16856, 12807, 25829, 6852, -27340, 11047, -11223, -1],
    poly [2205, -3909, -2406, 3187, 2421, 4883, 1295, -5169, 2089, -2122],
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
theorem certificado_59471 :
    haveI : Fact (Nat.Prime 59471) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59471 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59471 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59471 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59471 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59471) := ⟨by norm_num⟩
  have hP : poly [-3626, 1] = X - C (3626 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59471 : ℕ) : ℤ[X]) = poly [59471] := by simp [poly]
  refine ⟨X - C (3626 : ℤ),
    poly [-20682, 9097, 16699, -61, 26078, -17985, 4653, -11414, 14840, -29633, 17738, 19506, 10617,
      -6820, -6710, 8412, 3627, 1],
    poly [-1261, 555, 1018, -4, 1590, -1097, 284, -696, 905, -1807, 1082, 1189, 647, -416, -409, 513,
      221],
    poly [-1, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1, 0, -1, 0, -1],
    poly [-969, -100, 12316, 4250, -607, -6562, -3431, -12008, 471, -12991, 9147, 34, -11433, -1579,
      -8268, -20620, 2732, 4805],
    poly [58502, -58602, 12416, -8066, -5826, -6055, 16416, -5196, 425, -11858, 10279, -18547, -2073,
      4805],
    poly [59, 6, -751, -259, 37, 400, 209, 732, -29, 792, -558, -2, 697, 96, 504, 1257, -167, -293],
    poly [-3567, 3574, -758, 492, 355, 369, -1001, 317, -26, 723, -627, 1131, 126, -293],
    poly [20682, 29692, -7602, 16760, -5457, -24505, -548, -13564, -5941, -4676, 11496, -4786, -3626, -1],
    poly [1261, 1810, -464, 1022, -333, -1494, -33, -827, -362, -285, 701, -292, -221],
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
theorem certificado_59509 :
    haveI : Fact (Nat.Prime 59509) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59509 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59509 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59509 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59509 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59509) := ⟨by norm_num⟩
  have hP : poly [-3380, 1] = X - C (3380 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59509 : ℕ) : ℤ[X]) = poly [59509] := by simp [poly]
  refine ⟨X - C (3380 : ℤ),
    poly [-20969, -7929, -16024, 19098, 8932, -684, -22096, -14919, -18667, 910, 17941, 27471, -28690,
      14411, -23412, 2053, 3381, 1],
    poly [-1191, -450, -910, 1085, 507, -39, -1255, -847, -1060, 52, 1019, 1560, -1630, 819, -1330, 117,
      192],
    poly [-1, 1, 0, 1, -1, 0, 1, 0, 0, 0, 1],
    poly [-12445, -24685, -22928, -16466, -16781, -16517, -15038, -6076, -11320, -124, 5795, -14468,
      -15055, -5495, -27676, -18721, 7779, -8763],
    poly [47064, -59304, 13997, 17150, -6982, -13418, 8955, 26500, -16542, 8763],
    poly [707, 1402, 1302, 935, 953, 938, 854, 345, 643, 7, -329, 822, 855, 312, 1572, 1063, -442, 498],
    poly [-2673, 3369, -796, -974, 397, 762, -509, -1505, 940, -498],
    poly [20969, 25500, 21135, -4677, 19788, -21685, -25465, -1328, 3380, 1],
    poly [1191, 1448, 1200, -266, 1124, -1232, -1446, -75, 192],
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

end ATK.FermatDezenoveCertC

#print axioms ATK.FermatDezenoveCertC.certificado_39217
#print axioms ATK.FermatDezenoveCertC.certificado_39293
#print axioms ATK.FermatDezenoveCertC.certificado_39521
#print axioms ATK.FermatDezenoveCertC.certificado_39749
#print axioms ATK.FermatDezenoveCertC.certificado_39863
#print axioms ATK.FermatDezenoveCertC.certificado_39901
#print axioms ATK.FermatDezenoveCertC.certificado_40129
#print axioms ATK.FermatDezenoveCertC.certificado_40357
#print axioms ATK.FermatDezenoveCertC.certificado_40433
#print axioms ATK.FermatDezenoveCertC.certificado_40471
#print axioms ATK.FermatDezenoveCertC.certificado_40699
#print axioms ATK.FermatDezenoveCertC.certificado_40813
#print axioms ATK.FermatDezenoveCertC.certificado_40927
#print axioms ATK.FermatDezenoveCertC.certificado_41117
#print axioms ATK.FermatDezenoveCertC.certificado_41231
#print axioms ATK.FermatDezenoveCertC.certificado_41269
#print axioms ATK.FermatDezenoveCertC.certificado_41611
#print axioms ATK.FermatDezenoveCertC.certificado_41687
#print axioms ATK.FermatDezenoveCertC.certificado_41801
#print axioms ATK.FermatDezenoveCertC.certificado_41953
#print axioms ATK.FermatDezenoveCertC.certificado_42181
#print axioms ATK.FermatDezenoveCertC.certificado_42257
#print axioms ATK.FermatDezenoveCertC.certificado_42409
#print axioms ATK.FermatDezenoveCertC.certificado_42751
#print axioms ATK.FermatDezenoveCertC.certificado_42979
#print axioms ATK.FermatDezenoveCertC.certificado_43093
#print axioms ATK.FermatDezenoveCertC.certificado_43207
#print axioms ATK.FermatDezenoveCertC.certificado_43283
#print axioms ATK.FermatDezenoveCertC.certificado_43321
#print axioms ATK.FermatDezenoveCertC.certificado_43397
#print axioms ATK.FermatDezenoveCertC.certificado_43777
#print axioms ATK.FermatDezenoveCertC.certificado_43853
#print axioms ATK.FermatDezenoveCertC.certificado_43891
#print axioms ATK.FermatDezenoveCertC.certificado_44119
#print axioms ATK.FermatDezenoveCertC.certificado_44537
#print axioms ATK.FermatDezenoveCertC.certificado_44651
#print axioms ATK.FermatDezenoveCertC.certificado_44879
#print axioms ATK.FermatDezenoveCertC.certificado_44917
#print axioms ATK.FermatDezenoveCertC.certificado_45259
#print axioms ATK.FermatDezenoveCertC.certificado_45677
#print axioms ATK.FermatDezenoveCertC.certificado_45943
#print axioms ATK.FermatDezenoveCertC.certificado_46133
#print axioms ATK.FermatDezenoveCertC.certificado_46171
#print axioms ATK.FermatDezenoveCertC.certificado_46399
#print axioms ATK.FermatDezenoveCertC.certificado_46589
#print axioms ATK.FermatDezenoveCertC.certificado_46703
#print axioms ATK.FermatDezenoveCertC.certificado_46817
#print axioms ATK.FermatDezenoveCertC.certificado_47387
#print axioms ATK.FermatDezenoveCertC.certificado_47501
#print axioms ATK.FermatDezenoveCertC.certificado_47653
#print axioms ATK.FermatDezenoveCertC.certificado_47843
#print axioms ATK.FermatDezenoveCertC.certificado_47881
#print axioms ATK.FermatDezenoveCertC.certificado_48109
#print axioms ATK.FermatDezenoveCertC.certificado_48299
#print axioms ATK.FermatDezenoveCertC.certificado_48337
#print axioms ATK.FermatDezenoveCertC.certificado_48413
#print axioms ATK.FermatDezenoveCertC.certificado_48527
#print axioms ATK.FermatDezenoveCertC.certificado_48679
#print axioms ATK.FermatDezenoveCertC.certificado_48869
#print axioms ATK.FermatDezenoveCertC.certificado_48907
#print axioms ATK.FermatDezenoveCertC.certificado_49211
#print axioms ATK.FermatDezenoveCertC.certificado_49363
#print axioms ATK.FermatDezenoveCertC.certificado_49477
#print axioms ATK.FermatDezenoveCertC.certificado_49667
#print axioms ATK.FermatDezenoveCertC.certificado_50047
#print axioms ATK.FermatDezenoveCertC.certificado_50123
#print axioms ATK.FermatDezenoveCertC.certificado_50503
#print axioms ATK.FermatDezenoveCertC.certificado_51263
#print axioms ATK.FermatDezenoveCertC.certificado_51719
#print axioms ATK.FermatDezenoveCertC.certificado_51871
#print axioms ATK.FermatDezenoveCertC.certificado_52289
#print axioms ATK.FermatDezenoveCertC.certificado_52517
#print axioms ATK.FermatDezenoveCertC.certificado_52631
#print axioms ATK.FermatDezenoveCertC.certificado_52783
#print axioms ATK.FermatDezenoveCertC.certificado_52859
#print axioms ATK.FermatDezenoveCertC.certificado_52973
#print axioms ATK.FermatDezenoveCertC.certificado_53087
#print axioms ATK.FermatDezenoveCertC.certificado_53201
#print axioms ATK.FermatDezenoveCertC.certificado_53239
#print axioms ATK.FermatDezenoveCertC.certificado_53353
#print axioms ATK.FermatDezenoveCertC.certificado_53657
#print axioms ATK.FermatDezenoveCertC.certificado_53923
#print axioms ATK.FermatDezenoveCertC.certificado_54037
#print axioms ATK.FermatDezenoveCertC.certificado_54151
#print axioms ATK.FermatDezenoveCertC.certificado_54493
#print axioms ATK.FermatDezenoveCertC.certificado_54721
#print axioms ATK.FermatDezenoveCertC.certificado_54949
#print axioms ATK.FermatDezenoveCertC.certificado_55291
#print axioms ATK.FermatDezenoveCertC.certificado_55633
#print axioms ATK.FermatDezenoveCertC.certificado_55823
#print axioms ATK.FermatDezenoveCertC.certificado_56393
#print axioms ATK.FermatDezenoveCertC.certificado_56431
#print axioms ATK.FermatDezenoveCertC.certificado_56659
#print axioms ATK.FermatDezenoveCertC.certificado_56773
#print axioms ATK.FermatDezenoveCertC.certificado_56963
#print axioms ATK.FermatDezenoveCertC.certificado_57077
#print axioms ATK.FermatDezenoveCertC.certificado_57191
#print axioms ATK.FermatDezenoveCertC.certificado_57457
#print axioms ATK.FermatDezenoveCertC.certificado_57571
#print axioms ATK.FermatDezenoveCertC.certificado_58027
#print axioms ATK.FermatDezenoveCertC.certificado_58217
#print axioms ATK.FermatDezenoveCertC.certificado_58369
#print axioms ATK.FermatDezenoveCertC.certificado_58711
#print axioms ATK.FermatDezenoveCertC.certificado_58787
#print axioms ATK.FermatDezenoveCertC.certificado_58901
#print axioms ATK.FermatDezenoveCertC.certificado_59053
#print axioms ATK.FermatDezenoveCertC.certificado_59167
#print axioms ATK.FermatDezenoveCertC.certificado_59243
#print axioms ATK.FermatDezenoveCertC.certificado_59281
#print axioms ATK.FermatDezenoveCertC.certificado_59357
#print axioms ATK.FermatDezenoveCertC.certificado_59471
#print axioms ATK.FermatDezenoveCertC.certificado_59509
