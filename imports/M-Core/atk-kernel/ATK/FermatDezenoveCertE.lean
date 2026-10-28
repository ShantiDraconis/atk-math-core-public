import ATK.FermatDezenoveBase

/-!
# ATK — Certificados para `𝓞(ℚ(ζ₁₉))` principal (parte E)

Primos 82613 a 105907 da lista de `ATK.FermatDezenove`: para cada um, um gerador do ideal
primo e as identidades polinomiais do critério `pid6`, conferidas por reflexão (`ATK.PolyLista`).
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista
  ATK.FermatDezenoveBase

namespace ATK.FermatDezenoveCertE

set_option maxHeartbeats 4000000 in
theorem certificado_82613 :
    haveI : Fact (Nat.Prime 82613) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 82613 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((82613 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((82613 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((82613 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 82613) := ⟨by norm_num⟩
  have hP : poly [-1469, 1] = X - C (1469 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((82613 : ℕ) : ℤ[X]) = poly [82613] := by simp [poly]
  refine ⟨X - C (1469 : ℤ),
    poly [-36217, 21908, -9433, 16190, 12552, 22841, -7689, -20307, 8703, -8261, -568, -36836, -8292,
      33287, 30166, 11493, 1470, 1],
    poly [-644, 390, -168, 288, 223, 406, -137, -361, 155, -147, -10, -655, -147, 592, 536, 204, 26],
    poly [-1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1],
    poly [-9722, -14790, 3540, -16918, 11693, 1421, -13264, 2585, 10694, 5132, -23328, 3253, -1959, 5742,
      11371, -12020, 32448, -10431],
    poly [72891, -87681, 18330, -10736, 33679, -18880, 10841, -31092, 38839, -19488, -34037, 42879,
      -10431],
    poly [173, 263, -63, 301, -208, -25, 236, -46, -190, -91, 415, -58, 35, -102, -202, 214, -577, 186],
    poly [-1296, 1560, -327, 191, -599, 336, -193, 553, -691, 347, 605, -763, 186],
    poly [36217, 24488, 31341, 20773, -20850, 4766, 31665, -22361, 6902, -17204, -10022, -1469, -1],
    poly [644, 435, 557, 369, -371, 85, 563, -398, 123, -306, -178, -26],
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
theorem certificado_82651 :
    haveI : Fact (Nat.Prime 82651) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 82651 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((82651 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((82651 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((82651 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 82651) := ⟨by norm_num⟩
  have hP : poly [-17673, 1] = X - C (17673 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((82651 : ℕ) : ℤ[X]) = poly [82651] := by simp [poly]
  refine ⟨X - C (17673 : ℤ),
    poly [7160, -14820, -5524, -30829, -18021, 19309, 29843, -15885, 15984, 33355, -35901, 13710, 32948,
      -14566, -5842, 14474, 17674, 1],
    poly [1531, -3169, -1181, -6592, -3853, 4129, 6381, -3397, 3418, 7132, -7677, 2932, 7045, -3115,
      -1249, 3095, 3779],
    poly [-1, -1, -1, 0, 0, 1, 0, -1],
    poly [-12804, 3877, -1388, 7156, -6144, 7904, 10491, 1395, -233, 2456, 6899, 15654, -20688, 2684,
      27439, -14617, 8750, -13346],
    poly [69847, -78774, -1388, 19960, -10021, 22096, -13346],
    poly [2738, -829, 297, -1530, 1314, -1690, -2243, -298, 50, -525, -1475, -3347, 4424, -574, -5867,
      3126, -1871, 2854],
    poly [-14935, 16845, 296, -4268, 2143, -4725, 2854],
    poly [-7160, 14820, 5524, 37989, 3201, -17673, -1],
    poly [-1531, 3169, 1181, 8123, 684, -3779],
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
theorem certificado_82727 :
    haveI : Fact (Nat.Prime 82727) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 82727 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((82727 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((82727 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((82727 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 82727) := ⟨by norm_num⟩
  have hP : poly [-3690, 1] = X - C (3690 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((82727 : ℕ) : ℤ[X]) = poly [82727] := by simp [poly]
  refine ⟨X - C (3690 : ℤ),
    poly [25401, 2473, -1479, 35422, 10031, 27130, 12181, 14800, 2089, -9281, 132, -18451, -31930, 23823,
      -37344, -30164, 3691, 1],
    poly [1133, 110, -66, 1580, 447, 1210, 543, 660, 93, -414, 6, -823, -1424, 1063, -1666, -1345, 165],
    poly [-1, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0, -1, -1],
    poly [7959, 26188, 14378, 32086, 17877, 2785, -2241, 15424, 18007, 9735, 227, 32822, 19043, 1485,
      10986, -9256, 9481, -625],
    poly [90686, -56539, 14378, 24127, -352, 6636, -38178, 41443, 7432, 10741, 1505, -8631, 9481, -625],
    poly [-355, -1168, -641, -1431, -797, -124, 100, -688, -803, -434, -10, -1464, -849, -66, -490, 413,
      -423, 28],
    poly [-4045, 2523, -642, -1076, 16, -296, 1703, -1849, -331, -479, -67, 385, -423, 28],
    poly [-25401, -2473, 1479, -10021, -32959, -5681, 1792, 38584, -5415, 28740, 41035, 30165, -3691, -1],
    poly [-1133, -110, 66, -447, -1470, -253, 80, 1721, -242, 1282, 1830, 1345, -165],
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
theorem certificado_83221 :
    haveI : Fact (Nat.Prime 83221) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 83221 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((83221 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((83221 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((83221 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 83221) := ⟨by norm_num⟩
  have hP : poly [-280, 1] = X - C (280 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((83221 : ℕ) : ℤ[X]) = poly [83221] := by simp [poly]
  refine ⟨X - C (280 : ℤ),
    poly [30019, 6646, 4482, -30003, -10807, -33327, -9630, 3235, 37461, -29588, 14458, 12832, -27001,
      498, -22884, -4540, 281, 1],
    poly [101, 22, 15, -101, -36, -112, -32, 11, 126, -100, 49, 43, -91, 2, -77, -15, 1],
    poly [-1, 1, 0, 0, 1, 0, -1, 0, 0, -1],
    poly [-34452, -7231, -7431, 4457, -9767, -26462, -16119, -5085, -15151, -19348, -26199, -5121,
      -16340, -28566, -20882, 1734, 8948, -7076],
    poly [48769, -21548, -27421, 12088, 8340, -29692, -7214, 16024, -7076],
    poly [116, 24, 25, -15, 33, 89, 54, 17, 51, 65, 88, 17, 55, 96, 70, -6, -30, 24],
    poly [-164, 73, 92, -41, -28, 100, 24, -54, 24],
    poly [-30019, -29829, -21209, 32321, -23662, 18343, 4821, -280, -1],
    poly [-101, -100, -71, 109, -80, 62, 16, -1],
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
theorem certificado_83449 :
    haveI : Fact (Nat.Prime 83449) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 83449 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((83449 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((83449 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((83449 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 83449) := ⟨by norm_num⟩
  have hP : poly [-1099, 1] = X - C (1099 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((83449 : ℕ) : ℤ[X]) = poly [83449] := by simp [poly]
  refine ⟨X - C (1099 : ℤ),
    poly [-28930, 19640, 35478, 10359, -8419, -2969, 30370, 24098, -6736, 35454, -16369, -11025, -40102,
      11657, -9329, 40615, 1100, 1],
    poly [-381, 259, 467, 136, -111, -39, 400, 317, -89, 467, -216, -145, -528, 154, -123, 535, 14],
    poly [-1, -1, 0, -1, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0, -1],
    poly [-6850, 14025, 7362, 13962, 20650, -13741, 17056, -10707, 2328, -1153, 16460, 20956, -6755,
      8558, -17093, 11434, -13066, 17740],
    poly [76599, -69424, 14212, -6913, 27313, -20341, 10368, 23684, -21619, 12585, -10787, 24500, -30806,
      17740],
    poly [90, -185, -97, -184, -272, 181, -225, 141, -31, 15, -217, -276, 89, -113, 225, -151, 172, -234],
    poly [-1009, 915, -188, 91, -360, 268, -137, -312, 285, -166, 142, -323, 406, -234],
    poly [28930, -19640, 19041, 38211, 24257, -22150, 34301, -18648, 11145, -22086, -33506, -39515,
      -1099, -1],
    poly [381, -259, 251, 503, 319, -292, 452, -246, 147, -291, -441, -520, -14],
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
theorem certificado_83563 :
    haveI : Fact (Nat.Prime 83563) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 83563 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((83563 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((83563 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((83563 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 83563) := ⟨by norm_num⟩
  have hP : poly [-1528, 1] = X - C (1528 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((83563 : ℕ) : ℤ[X]) = poly [83563] := by simp [poly]
  refine ⟨X - C (1528 : ℤ),
    poly [-10336, 33845, 16866, 4222, 8370, 14279, 5150, -9567, -39819, -31745, 25245, 38298, -139,
      -26469, -8658, -3451, 1529, 1],
    poly [-189, 619, 308, 77, 153, 261, 94, -175, -728, -580, 462, 700, -3, -484, -158, -63, 28],
    poly [-1, 0, -1, 0, 0, 0, 0, 1, 0, -1],
    poly [-18471, 6728, -2279, -9449, 1812, -7751, 4110, 12485, 5217, 6306, -18795, 384, 23092, 4513,
      -257, -807, -3323, -20606],
    poly [65092, -58364, -27478, 18029, 2254, -16733, 23122, 17283, -20606],
    poly [338, -123, 42, 173, -33, 142, -75, -228, -95, -115, 344, -7, -422, -82, 5, 15, 61, 377],
    poly [-1190, 1068, 502, -330, -41, 306, -423, -316, 377],
    poly [10336, 39382, 27315, -31537, 12831, 6735, 4981, -1528, -1],
    poly [189, 720, 499, -577, 235, 123, 91, -28],
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
theorem certificado_83639 :
    haveI : Fact (Nat.Prime 83639) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 83639 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((83639 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((83639 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((83639 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 83639) := ⟨by norm_num⟩
  have hP : poly [-15630, 1] = X - C (15630 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((83639 : ℕ) : ℤ[X]) = poly [83639] := by simp [poly]
  refine ⟨X - C (15630 : ℤ),
    poly [-23283, 26626, -22393, 6024, -29094, -26624, 22393, 31049, -1293, -18162, -10345, -5598, 31684,
      -20691, -11196, 3012, 15631, 1],
    poly [-4351, 4976, -4185, 1126, -5437, -4975, 4185, 5802, -242, -3394, -1933, -1046, 5921, -3867,
      -2092, 563, 2921],
    poly [1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [40979, 1324, 4880, -3382, 2172, 10060, -4880, 1701, 476, -300, -1884, 2643, 19644, -9460, 5286,
      -1691, -20244, 5692],
    poly [42660, -43984, -3556, 49241, -45209, -4332, 47657, -40682, 12669, 18553, -25936, 5692],
    poly [-7658, -247, -912, 632, -406, -1880, 912, -318, -89, 56, 352, -494, -3671, 1768, -988, 316,
      3783, -1064],
    poly [-7972, 8220, 664, -9202, 8449, 809, -8906, 7603, -2368, -3467, 4847, -1064],
    poly [-23283, -33730, 34620, -31939, -1388, -32150, -39756, -6135, 14207, 12619, -15630, -1],
    poly [-4351, -6303, 6470, -5969, -259, -6008, -7429, -1146, 2655, 2358, -2921],
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
theorem certificado_83791 :
    haveI : Fact (Nat.Prime 83791) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 83791 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((83791 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((83791 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((83791 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 83791) := ⟨by norm_num⟩
  have hP : poly [-121, 1] = X - C (121 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((83791 : ℕ) : ℤ[X]) = poly [83791] := by simp [poly]
  refine ⟨X - C (121 : ℤ),
    poly [-28392, 19155, 16778, -19251, -34091, 13568, 7037, 8368, 8379, -14473, -34744, -8597, -31233,
      -35575, 26713, 14763, 122, 1],
    poly [-41, 28, 24, -28, -49, 20, 10, 12, 12, -21, -50, -12, -45, -51, 39, 21],
    poly [-1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    poly [-36594, -5042, 9761, 881, 7040, 1551, 9123, -14359, 9684, -6737, -18645, -13896, -7, 16035,
      -7377, -6878, 51, -13049],
    poly [47197, -52239, -21791, 22672, 20962, -14369, 13731, -28971, -4979, -8351, 26938, 16042, -23412,
      499, 6929, -13100, 13049],
    poly [53, 7, -14, -1, -10, -2, -13, 21, -14, 10, 27, 20, 0, -23, 11, 10, 0, 19],
    poly [-68, 76, 31, -33, -30, 21, -20, 42, 7, 12, -39, -23, 34, -1, -10, 19, -19],
    poly [28392, 36244, 30769, -11518, 17217, -11630, 21371, 34801, 34912, -26026, 22637, 4342, 21503,
      11950, 14641, 121, 1],
    poly [41, 52, 44, -17, 25, -17, 31, 50, 50, -38, 33, 6, 31, 17, 21],
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
theorem certificado_84247 :
    haveI : Fact (Nat.Prime 84247) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 84247 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((84247 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((84247 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((84247 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 84247) := ⟨by norm_num⟩
  have hP : poly [-8468, 1] = X - C (8468 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((84247 : ℕ) : ℤ[X]) = poly [84247] := by simp [poly]
  refine ⟨X - C (8468 : ℤ),
    poly [-20624, -6897, 28831, -25406, 22372, -41315, -27026, -26696, 39464, -25355, -21015, 16831,
      4280, -40760, -38298, 21296, 8469, 1],
    poly [-2073, -693, 2898, -2554, 2249, -4153, -2716, -2683, 3967, -2549, -2112, 1692, 430, -4097,
      -3849, 2141, 851],
    poly [-1, 0, 0, 0, 0, 0, 0, -1, 0, 1, -1, 1],
    poly [-13761, 7518, 22991, 10507, -677, 8793, 33527, 31958, 23750, -5819, 27158, 18775, 2627, -5334,
      4405, 16693, 29429, 14547],
    poly [70486, -62968, 15473, -12484, -11184, 9470, 24734, -15330, 13071, -335, -14547],
    poly [1383, -756, -2311, -1056, 68, -884, -3370, -3212, -2387, 585, -2730, -1887, -264, 536, -443,
      -1678, -2958, -1462],
    poly [-7085, 6330, -1556, 1255, 1124, -952, -2486, 1541, -1314, 34, 1462],
    poly [20624, -13727, -35728, -30010, 36469, -20560, -14289, 20294, 4360, 8467, 1],
    poly [2073, -1380, -3591, -3016, 3666, -2067, -1436, 2040, 438, 851],
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
theorem certificado_84437 :
    haveI : Fact (Nat.Prime 84437) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 84437 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((84437 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((84437 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((84437 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 84437) := ⟨by norm_num⟩
  have hP : poly [-620, 1] = X - C (620 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((84437 : ℕ) : ℤ[X]) = poly [84437] := by simp [poly]
  refine ⟨X - C (620 : ℤ),
    poly [7218, 5323, 4639, -40032, 14780, -30891, -19661, -18281, -15555, -18002, -2889, 4081, 19073,
      -29386, 9622, -37164, 621, 1],
    poly [53, 39, 34, -294, 109, -227, -144, -134, -114, -132, -21, 30, 140, -216, 71, -273, 5],
    poly [-1, 1, 0, 0, 0, 0, 1, -1, 0, -1, 0, 1, -1],
    poly [-14438, 3788, 1366, 4903, -25189, 6903, -22462, -2762, -5454, 4892, -30228, -13942, -29986,
      12479, 6419, 9133, 8865, 1238],
    poly [69999, -51773, -20648, 5959, -33629, 62184, -47019, 16401, -1744, -7359, 6389, 1238],
    poly [106, -28, -10, -36, 185, -51, 165, 20, 40, -36, 222, 102, 220, -92, -47, -67, -65, -9],
    poly [-514, 381, 151, -44, 247, -457, 346, -121, 13, 54, -47, -9],
    poly [-7218, 9113, -1211, -40450, -15046, 16046, 34754, 737, -135, 38405, -619, -1],
    poly [-53, 67, -9, -297, -110, 118, 255, 5, -1, 282, -5],
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
theorem certificado_84551 :
    haveI : Fact (Nat.Prime 84551) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 84551 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((84551 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((84551 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((84551 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 84551) := ⟨by norm_num⟩
  have hP : poly [-2173, 1] = X - C (2173 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((84551 : ℕ) : ℤ[X]) = poly [84551] := by simp [poly]
  refine ⟨X - C (2173 : ℤ),
    poly [-9922, -38642, 22939, -20456, 32597, 9937, -1474, -7627, -11871, -14441, 20421, 23044, 6742,
      4361, -30192, -10753, 2174, 1],
    poly [-255, -993, 590, -526, 838, 255, -38, -196, -305, -371, 525, 592, 173, 112, -776, -276, 56],
    poly [1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1],
    poly [43686, 3201, 12832, 28984, -19568, 19086, 20738, 8988, 21317, 4358, -6350, 29481, 7708, 3807,
      22443, 15798, 33888, 21095],
    poly [40865, -44066, -9631, -16152, 4866, 1831, -11283, -4402, 36223, 21991, -31429, -14450, -18090,
      12793, 21095],
    poly [-1123, -82, -330, -745, 503, -491, -533, -231, -548, -112, 163, -758, -198, -98, -577, -406,
      -871, -542],
    poly [-1050, 1133, 247, 415, -125, -47, 290, 113, -931, -565, 808, 371, 465, -329, -542],
    poly [-9922, -28720, -22970, 41156, -41420, 33171, -34381, 35003, -35742, -15308, -32380, 19440,
      12927, -2173, -1],
    poly [-255, -738, -590, 1058, -1065, 853, -884, 900, -919, -393, -832, 500, 332, -56],
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
theorem certificado_84589 :
    haveI : Fact (Nat.Prime 84589) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 84589 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((84589 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((84589 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((84589 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 84589) := ⟨by norm_num⟩
  have hP : poly [-1815, 1] = X - C (1815 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((84589 : ℕ) : ℤ[X]) = poly [84589] := by simp [poly]
  refine ⟨X - C (1815 : ℤ),
    poly [5080, -1675, -29409, 18626, 40091, 33112, -40948, 16569, 615, 10673, 7789, 24612, -1338, 35000,
      11158, -2930, 1816, 1],
    poly [109, -36, -631, 400, 860, 710, -879, 356, 13, 229, 167, 528, -29, 751, 239, -63, 39],
    poly [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, -1, 1],
    poly [-15366, -31733, -38360, -39622, -57426, -38747, -19209, -49352, -29002, -39244, -32119, -23027,
      -24793, -19947, -22228, -23441, -36398, -25080],
    poly [99955, -52856, 22994, 7889, 19066, 14491, -21850, 17232, 11055, 23062, 805, -13762, 25080],
    poly [330, 681, 823, 850, 1232, 831, 412, 1059, 622, 842, 689, 494, 532, 428, 477, 503, 781, 538],
    poly [-2145, 1135, -494, -169, -409, -311, 469, -370, -237, -495, -17, 295, -538],
    poly [5080, -1675, -34489, 20301, -15089, 19566, -3205, 40312, 5009, 20649, -6560, 1814, 1],
    poly [109, -36, -740, 436, -324, 420, -69, 865, 107, 443, -141, 39],
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
theorem certificado_85121 :
    haveI : Fact (Nat.Prime 85121) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 85121 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((85121 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((85121 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((85121 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 85121) := ⟨by norm_num⟩
  have hP : poly [-3363, 1] = X - C (3363 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((85121 : ℕ) : ℤ[X]) = poly [85121] := by simp [poly]
  refine ⟨X - C (3363 : ℤ),
    poly [-35562, 36412, -12670, 24472, -39402, 12416, -20397, 7486, 8203, -30143, 32946, -15354, -3295,
      -735, -41485, -7960, 3364, 1],
    poly [-1405, 1439, -501, 967, -1557, 491, -806, 296, 324, -1191, 1302, -607, -130, -29, -1639, -314,
      133],
    poly [0, 0, 1, 0, 2, 0, 2, 0, 0, 1, -1],
    poly [47509, 80959, 63884, 10827, -10121, 16095, 64295, 71118, 30673, 15120, 35592, 20943, 13725,
      52145, 67014, 66740, 26546, -650],
    poly [85121, -85121, -47509, -33450, -77943, -13843, -39920, 12998, 27846, -650],
    poly [-1877, -3198, -2523, -427, 400, -636, -2540, -2809, -1211, -597, -1406, -827, -542, -2060,
      -2647, -2636, -1048, 26],
    poly [-3363, 3364, 1876, 1321, 3079, 546, 1577, -514, -1100, 26],
    poly [0, 0, -35562, -13147, -35085, 10848, 22201, 14687, -3362, -1],
    poly [0, 0, -1405, -519, -1386, 429, 877, 580, -133],
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
theorem certificado_85159 :
    haveI : Fact (Nat.Prime 85159) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 85159 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((85159 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((85159 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((85159 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 85159) := ⟨by norm_num⟩
  have hP : poly [-4015, 1] = X - C (4015 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((85159 : ℕ) : ℤ[X]) = poly [85159] := by simp [poly]
  refine ⟨X - C (4015 : ℤ),
    poly [-39048, -13457, 8205, -18366, 14482, -1672, -10351, 24877, 34494, 7920, 8783, -15757, 40550,
      -3935, 19067, 29190, 4016, 1],
    poly [-1841, -634, 387, -866, 683, -79, -488, 1173, 1626, 373, 414, -743, 1912, -186, 899, 1376, 189],
    poly [-1, 0, -1, 0, 0, 1, -1, 0, -1, 0, 0, 0, 1],
    poly [-3454, 16610, 12882, -21331, 3837, 29041, 12270, 10972, -3727, 1381, 16187, 16424, -11531,
      -30309, 30496, 26057, -9450, -13107],
    poly [81705, -65095, -7182, -14149, 21440, -5555, -15121, 47698, -4439, -35507, -3657, 13107],
    poly [163, -783, -607, 1006, -181, -1369, -578, -517, 176, -65, -763, -774, 544, 1429, -1438, -1228,
      446, 618],
    poly [-3852, 3070, 338, 667, -1011, 262, 713, -2249, 210, 1674, 172, -618],
    poly [39048, -25591, 17386, 980, 30649, 3677, 40470, -23003, -10123, 25174, 4015, 1],
    poly [1841, -1207, 820, 46, 1445, 173, 1908, -1085, -477, 1187, 189],
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
theorem certificado_85577 :
    haveI : Fact (Nat.Prime 85577) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 85577 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((85577 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((85577 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((85577 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 85577) := ⟨by norm_num⟩
  have hP : poly [-68, 1] = X - C (68 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((85577 : ℕ) : ℤ[X]) = poly [85577] := by simp [poly]
  refine ⟨X - C (68 : ℤ),
    poly [41530, 19488, 6579, -22556, -19209, 42506, -35871, 39744, -3191, 4987, 27760, -23503, 29858,
      -36057, -23183, 4693, 69, 1],
    poly [33, 15, 5, -18, -15, 34, -29, 32, -3, 4, 22, -19, 24, -29, -18, 4],
    poly [1, 0, 0, 1, 0, 0, 1, 1, -1, 0, 0, 0, -1],
    poly [31390, -869, 7466, 13881, 132, 26358, -943, -86, 8736, -13787, 9793, -9996, 31243, 28074,
      19218, -1048, -3863, 4905],
    poly [54187, -53318, -8335, -37805, 46008, -34561, -10504, 13761, 20266, 2815, -8768, 4905],
    poly [-25, 1, -6, -11, 0, -21, 1, 0, -7, 11, -8, 8, -25, -22, -15, 1, 3, -4],
    poly [-43, 43, 6, 30, -37, 28, 8, -11, -16, -2, 7, -4],
    poly [41530, -22042, -12909, 12395, -18695, -36771, 19595, 12873, 27876, -4624, -68, -1],
    poly [33, -18, -10, 10, -15, -29, 16, 10, 22, -4],
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
theorem certificado_85691 :
    haveI : Fact (Nat.Prime 85691) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 85691 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((85691 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((85691 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((85691 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 85691) := ⟨by norm_num⟩
  have hP : poly [-2562, 1] = X - C (2562 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((85691 : ℕ) : ℤ[X]) = poly [85691] := by simp [poly]
  refine ⟨X - C (2562 : ℤ),
    poly [33079, 1217, -34985, -40752, -22325, 36716, 3058, -7123, 4546, -42041, 28079, 12587, 40275,
      14331, 20542, -31800, 2563, 1],
    poly [989, 36, -1046, -1218, -667, 1098, 91, -213, 136, -1257, 840, 376, 1204, 428, 614, -951, 77],
    poly [1, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1],
    poly [7130, -24508, -15289, 3679, -9291, -29498, 8055, -30896, -20643, -14652, 12342, -21964, -19703,
      -3079, -29228, -11411, 2744, -14877],
    poly [78561, -61183, 22419, -28187, -5998, 33177, -17346, 8528, -2940, -14155, 17621, -14877],
    poly [-213, 733, 457, -110, 278, 882, -241, 924, 617, 438, -369, 657, 589, 92, 874, 341, -82, 445],
    poly [-2349, 1830, -671, 843, 179, -992, 519, -255, 88, 423, -527, 445],
    poly [33079, 1217, 17627, -41969, 12660, -8223, 25383, 8773, 33350, 34363, -2562, -1],
    poly [989, 36, 527, -1255, 379, -246, 759, 262, 997, 1027, -77],
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
theorem certificado_85843 :
    haveI : Fact (Nat.Prime 85843) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 85843 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((85843 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((85843 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((85843 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 85843) := ⟨by norm_num⟩
  have hP : poly [-5890, 1] = X - C (5890 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((85843 : ℕ) : ℤ[X]) = poly [85843] := by simp [poly]
  refine ⟨X - C (5890 : ℤ),
    poly [17737, 31163, 22683, 35507, -25674, 360, -15201, 5011, -14865, -31454, 23678, -14993, 6964,
      25346, 15526, 17419, 5891, 1],
    poly [1217, 2138, 1556, 2436, -1762, 25, -1043, 344, -1020, -2158, 1625, -1029, 478, 1739, 1065,
      1195, 404],
    poly [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    poly [-4484, -48237, -21996, -17867, -29861, -11237, -21261, -6426, -26026, -44976, -4171, -20123,
      -18027, -24760, -9152, -4573, -14818, -28884],
    poly [90327, -37606, 17512, -25886, 56102, 15366, 4783, -18703, 37759, 20187, -5666, -24311, 14818,
      28884],
    poly [308, 3310, 1509, 1226, 2049, 771, 1459, 441, 1786, 3086, 286, 1381, 1237, 1699, 628, 314, 1017,
      1982],
    poly [-6198, 2581, -1202, 1776, -3850, -1054, -328, 1283, -2591, -1385, 389, 1668, -1017, -1982],
    poly [17737, 31163, 4946, 22081, -17194, -12464, 28243, -34449, -8561, 7927, 9635, 17418, 5891, 1],
    poly [1217, 2138, 339, 1515, -1180, -855, 1938, -2364, -587, 544, 661, 1195, 404],
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
theorem certificado_86413 :
    haveI : Fact (Nat.Prime 86413) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 86413 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((86413 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((86413 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((86413 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 86413) := ⟨by norm_num⟩
  have hP : poly [-1919, 1] = X - C (1919 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((86413 : ℕ) : ℤ[X]) = poly [86413] := by simp [poly]
  refine ⟨X - C (1919 : ℤ),
    poly [34268, 4701, 14232, -39349, -29065, 37450, 17131, -7331, -36028, -27172, -22124, -8162, 10803,
      30356, 34554, -31278, 1920, 1],
    poly [761, 104, 316, -874, -645, 832, 380, -163, -800, -603, -491, -181, 240, 674, 767, -695, 43],
    poly [-1, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1],
    poly [-27215, 7309, 19260, -6401, 6059, -6588, 19613, -5185, -12763, -924, 9259, -6091, 11778, -596,
      3045, 13629, -3522, 32133],
    poly [59198, -51889, 39166, -60185, 27724, -21510, 1790, 13510, -46239, 49284, -35655, 32133],
    poly [604, -163, -428, 142, -135, 146, -436, 115, 283, 20, -206, 135, -262, 13, -68, -303, 78, -714],
    poly [-1315, 1153, -870, 1337, -616, 478, -40, -300, 1027, -1095, 792, -714],
    poly [-34268, 29567, 24737, 24014, 33515, 23163, 40134, 37396, 18662, 33197, -1919, -1],
    poly [-761, 657, 549, 533, 744, 514, 891, 830, 414, 737, -43],
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
theorem certificado_86869 :
    haveI : Fact (Nat.Prime 86869) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 86869 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((86869 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((86869 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((86869 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 86869) := ⟨by norm_num⟩
  have hP : poly [-21558, 1] = X - C (21558 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((86869 : ℕ) : ℤ[X]) = poly [86869] := by simp [poly]
  refine ⟨X - C (21558 : ℤ),
    poly [23456, -19103, 33122, -16709, -3168, -27800, -25327, -3523, -40344, -18566, 33255, -9073,
      10694, -24205, 152, 19773, 21559, 1],
    poly [5821, -4741, 8220, -4147, -786, -6899, -6285, -874, -10012, -4607, 8253, -2252, 2654, -6007,
      38, 4907, 5350],
    poly [-1, 0, 1, -1, 1, 0, -1, 0, -1, 0, 0, -1],
    poly [17499, 16980, 28984, 5589, 7236, 31909, 23299, 9034, -10514, 12792, 13873, 23685, -10606, -981,
      7550, 50590, 8999, 28625],
    poly [104368, -87388, -5495, -5377, -28375, 60591, -28157, -14415, 41591, -19626, 28625],
    poly [-4343, -4214, -7193, -1387, -1796, -7919, -5782, -2242, 2609, -3175, -3443, -5878, 2632, 243,
      -1874, -12555, -2233, -7104],
    poly [-25901, 21688, 1363, 1334, 7042, -15037, 6988, 3577, -10322, 4871, -7104],
    poly [-23456, 42559, -28769, -16184, 17830, -33114, 2799, 19620, 1786, -21558, -1],
    poly [-5821, 10562, -7140, -4016, 4425, -8218, 695, 4869, 443, -5350],
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
theorem certificado_87211 :
    haveI : Fact (Nat.Prime 87211) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 87211 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((87211 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((87211 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((87211 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 87211) := ⟨by norm_num⟩
  have hP : poly [-4174, 1] = X - C (4174 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((87211 : ℕ) : ℤ[X]) = poly [87211] := by simp [poly]
  refine ⟨X - C (4174 : ℤ),
    poly [39176, 19378, -28808, 23833, 38534, -33609, -6318, -38885, -3812, -14355, -13083, 39737, 18814,
      2073, 20769, -15749, 4175, 1],
    poly [1875, 927, -1379, 1141, 1844, -1609, -302, -1861, -182, -687, -626, 1902, 900, 99, 994, -754,
      200],
    poly [1, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [132, -25651, -28645, -34496, -6228, -28118, -11241, -38002, -12497, -19950, -23650, -17132,
      -12492, -41408, -11871, -37835, -14064, -27702],
    poly [87079, -61560, 28777, 8845, -22417, -6378, 5145, -15899, -1738, -23771, 13638, -27702],
    poly [-6, 1228, 1371, 1651, 298, 1346, 538, 1819, 598, 955, 1132, 820, 598, 1982, 568, 1811, 673,
      1326],
    poly [-4168, 2947, -1378, -423, 1073, 305, -246, 761, 83, 1138, -653, 1326],
    poly [39176, 19378, 19227, 4455, -19869, 29769, 3183, 14522, -36519, 19924, -4174, -1],
    poly [1875, 927, 920, 213, -951, 1425, 152, 695, -1748, 954, -200],
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
theorem certificado_87553 :
    haveI : Fact (Nat.Prime 87553) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 87553 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((87553 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((87553 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((87553 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 87553) := ⟨by norm_num⟩
  have hP : poly [-2559, 1] = X - C (2559 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((87553 : ℕ) : ℤ[X]) = poly [87553] := by simp [poly]
  refine ⟨X - C (2559 : ℤ),
    poly [18407, 30868, -37452, 5049, -24803, -21667, 38961, 9903, 19232, -8238, 13477, -15083, 20625,
      3840, -9202, -15434, 2560, 1],
    poly [538, 902, -1095, 148, -725, -633, 1139, 289, 562, -241, 394, -441, 603, 112, -269, -451, 75],
    poly [-1, 0, 0, 0, 0, 0, -1, 0, 0, -2, 0, 0, 0, 0, 0, 0, -1],
    poly [-6223, 21214, -5941, -3933, -17823, 647, -8344, 13823, -17166, -10438, -52792, -14626, -10916,
      -9546, -11872, -10607, -6364, -9989],
    poly [81330, -60116, -27155, 2008, -13890, 18470, -15214, 49604, -58144, -3710, -1370, 2326, -1265,
      -4243, 3625, -9989],
    poly [182, -620, 174, 115, 521, -19, 244, -404, 502, 305, 1543, 427, 319, 279, 347, 310, 186, 292],
    poly [-2377, 1758, 793, -59, 406, -540, 445, -1450, 1700, 108, 40, -68, 37, 124, -106, 292],
    poly [-18407, -12461, -19233, -42501, 29852, -3136, 8518, 16597, -28562, 35708, -16785, -13042,
      -6232, 17994, -2559, -1],
    poly [-538, -364, -562, -1242, 873, -92, 249, 485, -835, 1044, -491, -381, -182, 526, -75],
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
theorem certificado_87629 :
    haveI : Fact (Nat.Prime 87629) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 87629 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((87629 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((87629 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((87629 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 87629) := ⟨by norm_num⟩
  have hP : poly [-1714, 1] = X - C (1714 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((87629 : ℕ) : ℤ[X]) = poly [87629] := by simp [poly]
  refine ⟨X - C (1714 : ℤ),
    poly [14673, 22197, 35085, 32843, -18795, 25245, 2571, -29140, -43627, 23799, 13511, -15432, 15073,
      24140, 4871, -39875, 1715, 1],
    poly [287, 434, 686, 642, -368, 494, 50, -570, -853, 466, 264, -302, 295, 472, 95, -780, 34],
    poly [1, 0, 0, 0, -1, 0, -1, 1, 1, 0, 1, 0, 1],
    poly [4158, -16392, -17631, 23013, -31054, -11300, 14990, 4678, -22629, 13194, -18943, -4391, 25986,
      -14641, -34757, -7161, 10340, -28863],
    poly [83471, -67079, 1239, -40644, 58225, -40304, -23371, 26248, -11607, 46364, -39203, 28863],
    poly [-81, 321, 345, -450, 608, 221, -293, -91, 443, -258, 371, 86, -508, 287, 680, 140, -202, 565],
    poly [-1633, 1313, -25, 795, -1139, 789, 457, -514, 227, -907, 767, -565],
    poly [14673, 7524, 12888, -2242, 21318, 36516, 37394, -22320, -41169, -41589, 1714, 1],
    poly [287, 147, 252, -44, 417, 714, 731, -437, -805, -813, 34],
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
theorem certificado_87743 :
    haveI : Fact (Nat.Prime 87743) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 87743 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((87743 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((87743 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((87743 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 87743) := ⟨by norm_num⟩
  have hP : poly [-1033, 1] = X - C (1033 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((87743 : ℕ) : ℤ[X]) = poly [87743] := by simp [poly]
  refine ⟨X - C (1033 : ℤ),
    poly [-4247, 33802, 5299, 38398, -42178, 36993, -42689, -27392, 9147, -27087, -11663, 37787, -4805,
      33037, 2835, 15207, 1034, 1],
    poly [-50, 398, 62, 452, -497, 436, -503, -322, 108, -319, -137, 445, -57, 389, 33, 179, 12],
    poly [1, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0, -1],
    poly [7545, 24965, 40356, 37398, 22021, -3306, 5843, -8503, 45420, 47171, 25513, -1349, -18363,
      23411, 21243, 26762, 38574, 15142],
    poly [80198, -105163, -15391, 2958, 22922, 50292, 23662, 34324, -47293, -9644, 17913, 3330, 23432,
      15142],
    poly [-89, -294, -475, -440, -259, 39, -69, 100, -535, -555, -300, 16, 216, -276, -250, -315, -454,
      -178],
    poly [-944, 1239, 180, -35, -270, -592, -278, -404, 557, 113, -211, -39, -276, -178],
    poly [-4247, 38049, -28503, 33099, 11414, -42374, -1485, 14948, -37529, 43368, 11339, -14174, -1033,
      -1],
    poly [-50, 448, -336, 390, 134, -499, -17, 176, -442, 511, 133, -167, -12],
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
theorem certificado_88237 :
    haveI : Fact (Nat.Prime 88237) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 88237 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((88237 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((88237 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((88237 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 88237) := ⟨by norm_num⟩
  have hP : poly [-411, 1] = X - C (411 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((88237 : ℕ) : ℤ[X]) = poly [88237] := by simp [poly]
  refine ⟨X - C (411 : ℤ),
    poly [13096, 40608, 15127, 1969, -7724, -41239, -19637, -31607, 18601, 36757, -23741, -21956, -15511,
      23578, -23129, -7141, 412, 1],
    poly [61, 189, 70, 9, -36, -192, -91, -147, 87, 171, -111, -102, -72, 110, -108, -33, 2],
    poly [-1, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, -1],
    poly [9984, 26754, 28727, 43760, 28339, 7262, 26318, 3178, 38760, 36485, 5779, 35546, 37980, 15873,
      23548, 13691, 10232, 43715],
    poly [98221, -61483, 18743, 26990, 16382, -24541, 29782, -17532, 6398, 36942, -77198, 43715],
    poly [-47, -125, -134, -204, -132, -34, -123, -15, -181, -170, -27, -166, -177, -74, -110, -64, -48,
      -204],
    poly [-458, 287, -88, -126, -76, 114, -139, 82, -30, -172, 360, -204],
    poly [-13096, -40608, -2031, 25543, -4661, -32644, -2441, 25542, 8435, 7964, -410, -1],
    poly [-61, -189, -9, 119, -22, -152, -11, 119, 39, 37, -2],
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
theorem certificado_88427 :
    haveI : Fact (Nat.Prime 88427) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 88427 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((88427 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((88427 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((88427 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 88427) := ⟨by norm_num⟩
  have hP : poly [-7856, 1] = X - C (7856 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((88427 : ℕ) : ℤ[X]) = poly [88427] := by simp [poly]
  refine ⟨X - C (7856 : ℤ),
    poly [15522, -41814, -1750, 31933, -15169, -12361, -3626, -29705, 38154, -15247, -39623, 33943, 342,
      12618, 24731, 2547, 7857, 1],
    poly [1379, -3715, -155, 2837, -1348, -1098, -322, -2639, 3390, -1355, -3520, 3016, 30, 1121, 2197,
      226, 698],
    poly [-1, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1],
    poly [250, 10538, 19364, -4385, -24570, -9861, -4445, 22480, -1368, 11866, 9639, 2176, 3492, 3177,
      29122, 7390, -17511, -18606],
    poly [88677, -78139, 9076, -13211, -1071, -214, -38268, 31737, 5103, 21826, -19335, -3118, 28027,
      25996, -17511, -18606],
    poly [-22, -936, -1720, 390, 2183, 876, 395, -1997, 122, -1054, -856, -193, -310, -282, -2587, -656,
      1556, 1653],
    poly [-7878, 6943, -807, 1174, 95, 19, 3400, -2820, -453, -1939, 1718, 277, -2490, -2309, 1556, 1653],
    poly [-15522, -31091, 32841, 8131, -24053, 11872, -10838, 39282, -31039, 37062, 29698, -17927,
      -16875, -2546, -7857, -1],
    poly [-1379, -2762, 2918, 722, -2137, 1055, -963, 3490, -2758, 3293, 2638, -1593, -1499, -226, -698],
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
theorem certificado_88807 :
    haveI : Fact (Nat.Prime 88807) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 88807 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((88807 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((88807 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((88807 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 88807) := ⟨by norm_num⟩
  have hP : poly [-8777, 1] = X - C (8777 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((88807 : ℕ) : ℤ[X]) = poly [88807] := by simp [poly]
  refine ⟨X - C (8777 : ℤ),
    poly [34341, -1787, 36071, 166, 17383, -43415, -31867, 10327, 1185, 13862, 4919, 21876, 9038, 40848,
      -20262, -39969, 8778, 1],
    poly [3394, -177, 3565, 16, 1718, -4291, -3149, 1021, 117, 1370, 486, 2162, 893, 4037, -2003, -3950,
      868],
    poly [1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, -1],
    poly [50972, 7490, 21954, 11281, 26285, 32135, 18719, 6859, 22217, 37912, 25600, 21865, 48192, 7945,
      26831, 20226, 29453, 28422],
    poly [37835, -45325, -14464, 10673, -15004, -5850, 13416, -39112, -22848, -37649, 1031, 28422],
    poly [-5038, -740, -2170, -1115, -2598, -3176, -1850, -678, -2196, -3747, -2530, -2161, -4763, -785,
      -2652, -1999, -2911, -2809],
    poly [-3739, 4480, 1429, -1055, 1483, 578, -1326, 3866, 2258, 3721, -102, -2809],
    poly [34341, -36128, 37858, -35905, 17217, 28009, 11548, -12272, -10929, -40059, -8777, -1],
    poly [3394, -3571, 3742, -3549, 1702, 2768, 1141, -1213, -1080, -3959, -867],
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
theorem certificado_88883 :
    haveI : Fact (Nat.Prime 88883) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 88883 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((88883 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((88883 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((88883 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 88883) := ⟨by norm_num⟩
  have hP : poly [-6832, 1] = X - C (6832 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((88883 : ℕ) : ℤ[X]) = poly [88883] := by simp [poly]
  refine ⟨X - C (6832 : ℤ),
    poly [-43778, 27067, -3925, 27294, -21215, 33302, -7788, -31654, -17737, 36607, -23022, 32326, 17607,
      -37908, 43174, 19482, 6833, 1],
    poly [-3365, 2081, -302, 2098, -1631, 2560, -599, -2433, -1363, 2814, -1770, 2485, 1353, -2914, 3319,
      1497, 525],
    poly [-1, 0, 0, 1, -1, -1, -1, 0, 0, -1],
    poly [-13674, -7041, -8328, 1208, -15235, 6528, 10265, -24952, 9740, 12295, -38612, 7084, -3109,
      -39603, -2010, -13284, 843, 4735],
    poly [75209, -82250, -1287, 23210, -36750, 16009, -14127, -3892, 4735],
    poly [1051, 541, 640, -93, 1171, -502, -789, 1918, -749, -945, 2968, -545, 239, 3044, 154, 1021, -65,
      -364],
    poly [-5781, 6323, 98, -1784, 2825, -1231, 1086, 299, -364],
    poly [43778, 18038, 30992, 13886, -14634, -23693, -12649, -6832, -1],
    poly [3365, 1386, 2382, 1067, -1125, -1821, -972, -525],
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
theorem certificado_88997 :
    haveI : Fact (Nat.Prime 88997) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 88997 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((88997 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((88997 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((88997 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 88997) := ⟨by norm_num⟩
  have hP : poly [-1842, 1] = X - C (1842 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((88997 : ℕ) : ℤ[X]) = poly [88997] := by simp [poly]
  refine ⟨X - C (1842 : ℤ),
    poly [34159, 36545, -34574, -31762, 29890, -4767, 5602, 18991, 19723, 23492, -32117, -36254, 41290,
      33505, 38284, 12921, 1843, 1],
    poly [707, 756, -716, -657, 619, -99, 116, 393, 408, 486, -665, -750, 855, 693, 792, 267, 38],
    poly [-1, -1, 0, 0, -1, 1, -1, 0, 0, 0, -1],
    poly [-498, 12257, 43524, 47068, 23492, 22223, 28455, 30391, 23338, 31886, 39911, 24696, 11401, 3615,
      42553, 19576, 26376, 27346],
    poly [88499, -76740, 44022, 34811, -20530, -11592, 22977, -6800, -970, 27346],
    poly [10, -254, -901, -974, -486, -460, -589, -629, -483, -660, -826, -511, -236, -75, -881, -405,
      -546, -566],
    poly [-1832, 1589, -912, -720, 425, 240, -476, 141, 20, -566],
    poly [-34159, -36545, -20264, -20690, -9626, 4778, -25363, -11078, -1842, -1],
    poly [-707, -756, -419, -428, -199, 99, -525, -229, -38],
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
theorem certificado_89491 :
    haveI : Fact (Nat.Prime 89491) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 89491 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((89491 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((89491 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((89491 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 89491) := ⟨by norm_num⟩
  have hP : poly [-13281, 1] = X - C (13281 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((89491 : ℕ) : ℤ[X]) = poly [89491] := by simp [poly]
  refine ⟨X - C (13281 : ℤ),
    poly [15370, 34710, -21479, 15301, 21348, -29384, -13627, -36071, 29895, -23986, -22730, 2606,
      -36373, 18103, -221, 11482, 13282, 1],
    poly [2281, 5151, -3188, 2271, 3168, -4361, -2022, -5353, 4437, -3560, -3373, 387, -5398, 2687, -33,
      1704, 1971],
    poly [-1, -1, 0, -1, -1, 0, 0, -1, -1, -2, -1, 0, -1, -1, 0, -1, -1],
    poly [8622, 24653, -3094, 43681, -6866, 29153, 8449, -1067, 31559, -11988, 2213, 1392, 1931, 40164,
      -3140, 34773, -12136, 39698],
    poly [98113, -64838, -11716, 27650, 20881, -26244, 34343, -25370, 33235, 9922, 146, -6745, 48694,
      -4925, -12136, 39698],
    poly [-1280, -3659, 459, -6483, 1019, -4327, -1254, 158, -4684, 1779, -329, -207, -287, -5961, 466,
      -5161, 1801, -5892],
    poly [-14561, 9623, 1738, -4104, -3099, 3895, -5097, 3765, -4933, -1473, -22, 1001, -7227, 731, 1801,
      -5892],
    poly [-15370, -34710, 36849, 4039, 11954, -7957, -35107, 37981, -33547, 28999, 24671, -19903, 13502,
      -11481, -13282, -1],
    poly [-2281, -5151, 5469, 599, 1774, -1181, -5210, 5637, -4979, 4304, 3661, -2954, 2004, -1704,
      -1971],
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
theorem certificado_89567 :
    haveI : Fact (Nat.Prime 89567) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 89567 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((89567 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((89567 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((89567 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 89567) := ⟨by norm_num⟩
  have hP : poly [-436, 1] = X - C (436 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((89567 : ℕ) : ℤ[X]) = poly [89567] := by simp [poly]
  refine ⟨X - C (436 : ℤ),
    poly [1438, -6365, 18474, 37225, 32954, -5471, -13160, 26881, 39504, -19836, 43300, -14897, 16811,
      10310, 43780, 11399, 437, 1],
    poly [7, -31, 90, 181, 160, -27, -64, 131, 192, -97, 211, -73, 82, 50, 213, 55, 2],
    poly [-1, -1, -1, 0, 0, -1, -1, 0, -1, 0, -1],
    poly [15014, 10529, 11135, 35377, 16944, 11766, 23669, 14452, 12582, 14632, 22443, -13900, 29773,
      14466, -7550, 34307, 32965, -7713],
    poly [104581, -79038, 11135, 20363, 6415, 15645, -1179, -6371, 40678, -7713],
    poly [-73, -51, -54, -172, -82, -57, -115, -70, -61, -71, -109, 68, -145, -70, 37, -167, -160, 38],
    poly [-509, 386, -55, -99, -31, -76, 6, 31, -198, 38],
    poly [-1438, 6365, -18474, -35787, -39319, 22507, -32817, -10963, -436, -1],
    poly [-7, 31, -90, -174, -191, 110, -160, -53, -2],
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
theorem certificado_89681 :
    haveI : Fact (Nat.Prime 89681) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 89681 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((89681 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((89681 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((89681 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 89681) := ⟨by norm_num⟩
  have hP : poly [-19444, 1] = X - C (19444 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((89681 : ℕ) : ℤ[X]) = poly [89681] := by simp [poly]
  refine ⟨X - C (19444 : ℤ),
    poly [14358, 38813, 15038, -39079, -23377, -14659, 6973, -19980, -2321, -22056, 30795, -12922, -1555,
      10479, 41594, -6515, 19445, 1],
    poly [3113, 8415, 3260, -8473, -5068, -3178, 1512, -4332, -503, -4782, 6677, -2802, -337, 2272, 9018,
      -1413, 4216],
    poly [-1, 0, 0, 0, 1, 0, -1, -1, -1, -1, 0, 0, -1, -1],
    poly [-27267, 14754, -38677, -7653, -4718, 4622, -26003, -18196, -9852, 812, -27433, -23205, -14792,
      -8339, -20040, 10405, -13711, -14524],
    poly [62414, -47660, -53431, 31024, 30202, -32681, -4461, -8463, -33268, -6329, 24929, -13711,
      -14524],
    poly [5912, -3199, 8386, 1659, 1023, -1002, 5638, 3945, 2136, -176, 5948, 5031, 3207, 1808, 4345,
      -2256, 2973, 3149],
    poly [-13532, 10334, 11584, -6727, -6548, 7086, 967, 1835, 7213, 1372, -5405, 2973, 3149],
    poly [-14358, -24455, 23775, -35564, -1344, 15737, 29916, 23704, -16995, -22149, 6516, -19445, -1],
    poly [-3113, -5302, 5155, -7711, -291, 3412, 6486, 5139, -3685, -4802, 1413, -4216],
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
theorem certificado_89833 :
    haveI : Fact (Nat.Prime 89833) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 89833 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((89833 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((89833 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((89833 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 89833) := ⟨by norm_num⟩
  have hP : poly [-1694, 1] = X - C (1694 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((89833 : ℕ) : ℤ[X]) = poly [89833] := by simp [poly]
  refine ⟨X - C (1694 : ℤ),
    poly [-24659, -11363, -35749, -28021, 938, 18402, 3776, 20737, -412, -33038, -13224, -21485, 11760,
      -15743, 26930, -3325, 1695, 1],
    poly [-465, -214, -674, -528, 18, 347, 71, 391, -8, -623, -249, -405, 222, -297, 508, -63, 32],
    poly [-1, 0, 0, 0, 0, 0, -1, 0, -2, 0, 0, -1],
    poly [29872, 12920, -13499, -10704, 9290, 37832, 13455, -26385, -27257, 30015, 35670, -28334, -26993,
      -17818, 29013, 31427, -1026, -27189],
    poly [119705, -106785, -26419, 2795, 19994, 28542, 5495, -56792, 32453, 26163, -27189],
    poly [-563, -243, 255, 202, -175, -713, -253, 498, 514, -566, -672, 535, 509, 336, -547, -592, 20,
      513],
    poly [-2257, 2015, 497, -53, -377, -538, -103, 1071, -612, -493, 513],
    poly [24659, -13296, 24386, -7728, -28959, -17464, 39285, -30257, 5020, -1694, -1],
    poly [465, -251, 460, -146, -546, -329, 741, -571, 95, -32],
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
theorem certificado_89909 :
    haveI : Fact (Nat.Prime 89909) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 89909 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((89909 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((89909 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((89909 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 89909) := ⟨by norm_num⟩
  have hP : poly [-7593, 1] = X - C (7593 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((89909 : ℕ) : ℤ[X]) = poly [89909] := by simp [poly]
  refine ⟨X - C (7593 : ℤ),
    poly [25103, 36675, 40738, 4055, 9426, 44713, 18620, 44134, -12001, 1147, 2842, -19786, -34164, 2044,
      -37299, 29574, 7594, 1],
    poly [2120, 3097, 3440, 342, 796, 3776, 1572, 3727, -1014, 97, 240, -1671, -2885, 173, -3150, 2498,
      641],
    poly [-1, 0, -1, -1, -1, -1, 1, 0, 0, 0, -1],
    poly [-45503, 12370, -23927, 1858, -24106, -155, -20625, 7850, -23525, -19740, -782, -15119, -19135,
      6524, -3277, -49707, -7784, -16008],
    poly [44406, -32036, -81800, 38155, -49891, 25809, 46430, -41923, 8224, -16008],
    poly [3843, -1045, 2021, -157, 2036, 13, 1742, -663, 1987, 1667, 66, 1277, 1616, -551, 277, 4198,
      657, 1352],
    poly [-3750, 2706, 6908, -3223, 4214, -2180, -3921, 3541, -695, 1352],
    poly [-25103, -11572, -29166, 8, 43800, -39342, -23036, -21980, -7593, -1],
    poly [-2120, -977, -2463, 1, 3699, -3323, -1945, -1856, -641],
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
theorem certificado_90023 :
    haveI : Fact (Nat.Prime 90023) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 90023 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((90023 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((90023 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((90023 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 90023) := ⟨by norm_num⟩
  have hP : poly [-12877, 1] = X - C (12877 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((90023 : ℕ) : ℤ[X]) = poly [90023] := by simp [poly]
  refine ⟨X - C (12877 : ℤ),
    poly [776, 28761, 7944, -42204, -17292, 5941, -18267, 42357, -9861, 957, -21672, -16053, 34730,
      -32827, -1981, 7641, 12878, 1],
    poly [111, 4114, 1136, -6037, -2473, 850, -2613, 6059, -1411, 137, -3100, -2296, 4968, -4696, -283,
      1093, 1842],
    poly [-1, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1],
    poly [7997, 13912, 15045, 36067, 17158, 16793, 29964, -18133, 35617, 6266, 6823, 24706, 11040, -6858,
      18448, 6006, 28537, 8943],
    poly [98020, -76111, 15045, 28070, 3246, 9745, 7809, -28243, 40979, -13588, 19594, 8943],
    poly [-1144, -1990, -2152, -5159, -2454, -2402, -4286, 2594, -5095, -896, -976, -3534, -1579, 981,
      -2639, -859, -4082, -1279],
    poly [-14021, 10888, -2153, -4015, -464, -1394, -1117, 4040, -5862, 1944, -2803, -1279],
    poly [-776, -28761, -7944, 42980, -43970, 1227, 37325, 23206, -3256, 5236, -12877, -1],
    poly [-111, -4114, -1136, 6148, -6290, 176, 5339, 3319, -466, 749, -1842],
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
theorem certificado_90289 :
    haveI : Fact (Nat.Prime 90289) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 90289 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((90289 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((90289 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((90289 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 90289) := ⟨by norm_num⟩
  have hP : poly [-989, 1] = X - C (989 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((90289 : ℕ) : ℤ[X]) = poly [90289] := by simp [poly]
  refine ⟨X - C (989 : ℤ),
    poly [-12142, 1631, 18169, 19829, 41102, 21039, 15815, -31115, -41296, 36932, 41028, 25421, 41838,
      18940, -8745, -14068, 990, 1],
    poly [-133, 18, 199, 217, 450, 230, 173, -341, -452, 405, 449, 278, 458, 207, -96, -154, 11],
    poly [-1, 1, 0, 0, -1, -1, -1, 0, 0, 0, -1, -1],
    poly [-52005, -15449, -13221, -47545, -35529, -44281, -40912, -35431, -28122, -36331, -30953, -10224,
      -44438, -51137, -40006, -50037, -46578, -31785],
    poly [38284, -1728, -34328, -36552, -5665, -36217, -1100, 6572, -18252, -46578, -31785],
    poly [570, 169, 145, 521, 389, 485, 448, 388, 308, 398, 339, 112, 487, 560, 438, 548, 510, 348],
    poly [-419, 19, 376, 400, 62, 397, 12, -72, 200, 510, 348],
    poly [12142, -25915, -2765, 14878, -7471, 39705, -33008, 9735, 14069, -990, -1],
    poly [133, -284, -30, 163, -82, 435, -362, 107, 154, -11],
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
theorem certificado_90403 :
    haveI : Fact (Nat.Prime 90403) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 90403 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((90403 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((90403 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((90403 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 90403) := ⟨by norm_num⟩
  have hP : poly [-783, 1] = X - C (783 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((90403 : ℕ) : ℤ[X]) = poly [90403] := by simp [poly]
  refine ⟨X - C (783 : ℤ),
    poly [-43181, 10336, -43976, 34581, 12629, -21228, -3029, -25289, 20750, -21564, 43038, -33774,
      33324, -24088, -10191, -18948, 784, 1],
    poly [-374, 90, -381, 300, 109, -184, -26, -219, 180, -187, 373, -293, 289, -209, -88, -164, 7],
    poly [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [-5946, -15652, -22130, -41766, -54145, -38805, -25046, -26183, -34151, -26541, -34036, -32891,
      -41087, -24818, -34842, -31622, -28616, -45238],
    poly [90403, -84457, 3760, -3228, 13158, -7257, -27719, -4365, 5190, 353, -35214, -3220, -3006,
      16622, -45238],
    poly [52, 136, 192, 362, 469, 336, 217, 227, 296, 230, 295, 285, 356, 215, 302, 274, 248, 392],
    poly [-783, 732, -33, 28, -114, 63, 240, 38, -45, -3, 305, 28, 26, -144, 392],
    poly [0, -43181, 6295, -17426, 42466, -10106, -11905, 4834, -3573, 32208, 13896, -8757, 19732, -783,
      -1],
    poly [0, -374, 55, -151, 368, -88, -103, 42, -31, 279, 120, -76, 171, -7],
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
theorem certificado_90631 :
    haveI : Fact (Nat.Prime 90631) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 90631 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((90631 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((90631 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((90631 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 90631) := ⟨by norm_num⟩
  have hP : poly [-5780, 1] = X - C (5780 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((90631 : ℕ) : ℤ[X]) = poly [90631] := by simp [poly]
  refine ⟨X - C (5780 : ℤ),
    poly [-12058, -35298, -32166, 30994, 41981, 20705, -39573, -11077, 11570, 17893, 39956, -17006,
      27547, -12947, 30229, -28658, 5781, 1],
    poly [-769, -2251, -2051, 1977, 2677, 1320, -2524, -706, 738, 1141, 2548, -1085, 1757, -826, 1928,
      -1828, 369],
    poly [-1, -1, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, -1],
    poly [14091, -9756, 15281, 19566, 28426, 8357, 1125, -15309, 33516, 26390, 19270, -6133, 17273,
      21887, 10065, 22952, -17767, 31289],
    poly [104722, -100387, 1190, 43413, -10702, 13828, -23016, -28897, 36169, 9430, -49056, 31289],
    poly [-899, 622, -975, -1248, -1813, -533, -72, 976, -2138, -1683, -1229, 391, -1102, -1396, -642,
      -1464, 1133, -1996],
    poly [-6679, 6403, -77, -2769, 683, -882, 1468, 1843, -2307, -601, 3129, -1996],
    poly [12058, 35298, 20108, 36397, 39724, 7157, 18394, 8737, 37524, 34440, -5780, -1],
    poly [769, 2251, 1282, 2321, 2533, 456, 1173, 557, 2393, 2196, -369],
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
theorem certificado_90821 :
    haveI : Fact (Nat.Prime 90821) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 90821 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((90821 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((90821 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((90821 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 90821) := ⟨by norm_num⟩
  have hP : poly [-6162, 1] = X - C (6162 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((90821 : ℕ) : ℤ[X]) = poly [90821] := by simp [poly]
  refine ⟨X - C (6162 : ℤ),
    poly [-15579, 43713, 13390, -28606, -9806, -22331, 25023, 14006, 31853, -23636, 38332, 10574, -32527,
      27468, -40159, 13229, 6163, 1],
    poly [-1057, 2966, 908, -1941, -665, -1515, 1698, 950, 2161, -1604, 2601, 717, -2207, 1864, -2725,
      898, 418],
    poly [1, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, -1],
    poly [7251, -10744, 9578, 4010, -5807, -2286, -4511, 25836, -12377, -1049, 12660, -25821, -11899,
      -1609, 7236, 28034, -9252, 3270],
    poly [83570, -72826, -20322, 5568, 2566, 14474, -18097, -17528, 37286, -12522, 3270],
    poly [-492, 729, -650, -272, 394, 155, 306, -1753, 840, 71, -859, 1752, 807, 109, -491, -1902, 628,
      -222],
    poly [-5670, 4942, 1378, -378, -174, -982, 1228, 1189, -2530, 850, -222],
    poly [-15579, -31529, -30323, -41996, 3221, -44054, 17031, -37434, -7066, -6162, -1],
    poly [-1057, -2139, -2057, -2849, 219, -2989, 1156, -2540, -479, -418],
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
theorem certificado_91163 :
    haveI : Fact (Nat.Prime 91163) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 91163 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((91163 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((91163 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((91163 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 91163) := ⟨by norm_num⟩
  have hP : poly [-3310, 1] = X - C (3310 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((91163 : ℕ) : ℤ[X]) = poly [91163] := by simp [poly]
  refine ⟨X - C (3310 : ℤ),
    poly [-45251, 5054, 16499, 17191, -29189, -15983, -4742, -27791, -22207, -44459, 16787, 13170,
      -22112, -30275, -21712, 19851, 3311, 1],
    poly [-1643, 184, 599, 624, -1060, -580, -172, -1009, -806, -1614, 610, 478, -803, -1099, -788, 721,
      120],
    poly [-1, -1, -1, 0, 1, 0, 1, 0, -1, 0, 0, 1],
    poly [-160, -38443, -11987, -4047, 15510, -21087, -4876, -29576, 20267, 2077, -2886, -49130, 10291,
      17277, -12521, -9886, -14705, -17378],
    poly [91003, -129606, -11987, -3887, 54113, 29183, -27125, -14743, -4819, -2673, 17378],
    poly [6, 1396, 435, 147, -563, 766, 177, 1074, -736, -75, 105, 1784, -374, -627, 455, 359, 534, 631],
    poly [-3304, 4707, 434, 141, -1965, -1059, 985, 535, 175, 97, -631],
    poly [45251, -5054, -16499, 28721, -11008, -8376, -11873, -41564, 16540, 3310, 1],
    poly [1643, -184, -599, 1043, -400, -304, -431, -1509, 601, 120],
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
theorem certificado_91733 :
    haveI : Fact (Nat.Prime 91733) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 91733 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((91733 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((91733 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((91733 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 91733) := ⟨by norm_num⟩
  have hP : poly [-11796, 1] = X - C (11796 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((91733 : ℕ) : ℤ[X]) = poly [91733] := by simp [poly]
  refine ⟨X - C (11796 : ℤ),
    poly [-38782, -28038, -5516, -38938, -23652, 19354, -11360, -8703, 18912, 1067, -29971, -25261,
      -2444, 29932, -5340, -1548, 11797, 1],
    poly [-4987, -3605, -709, -5007, -3041, 2489, -1461, -1119, 2432, 137, -3854, -3248, -314, 3849,
      -687, -199, 1517],
    poly [1, 1, 0, 0, 0, -1, 0, -1, -1, -1],
    poly [7694, -11047, -23950, -24581, -3312, -12090, -19323, -10015, 3486, -12696, -37567, -12194,
      -16399, 6565, -39284, -2730, -7284, -34487],
    poly [84039, -80686, 31644, 13534, -20638, -4797, -2730, -7284, -34487],
    poly [-989, 1421, 3080, 3161, 426, 1555, 2485, 1288, -448, 1633, 4831, 1568, 2109, -844, 5052, 351,
      937, 4435],
    poly [-10807, 10376, -4070, -1740, 2654, 617, 351, 937, 4435],
    poly [-38782, -28038, 33266, -10900, -18136, 5341, 1548, -11797, -1],
    poly [-4987, -3605, 4278, -1402, -2332, 687, 199, -1517],
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
theorem certificado_91771 :
    haveI : Fact (Nat.Prime 91771) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 91771 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((91771 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((91771 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((91771 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 91771) := ⟨by norm_num⟩
  have hP : poly [-430, 1] = X - C (430 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((91771 : ℕ) : ℤ[X]) = poly [91771] := by simp [poly]
  refine ⟨X - C (430 : ℤ),
    poly [-4055, -20071, 8917, -3394, -1075, 41828, 15677, -31123, -22695, 14033, 1740, -14722, 41156,
      43847, 35103, 1789, 431, 1],
    poly [-19, -94, 42, -16, -5, 196, 73, -146, -106, 66, 8, -69, 193, 205, 164, 8, 2],
    poly [-2, -1, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1],
    poly [-18325, 8310, -1232, 33320, 7363, 13065, 8383, 19470, 9465, 1972, -5942, 22638, 7765, -8703,
      22845, 21211, 2853, -12556],
    poly [55121, -56826, -10774, 67872, -269, -7868, 13243, -3995, 43742, -37858, 368, 23904, 2219, 4487,
      5802, 15409, -12556],
    poly [86, -39, 6, -156, -34, -61, -39, -91, -44, -9, 28, -106, -36, 41, -107, -99, -13, 59],
    poly [-258, 267, 50, -318, 2, 37, -62, 19, -205, 178, -2, -112, -10, -21, -27, -72, 59],
    poly [8110, 36087, -37905, 15705, -5299, -8976, 39462, -26159, 12531, -23874, 13390, -31982, -10532,
      -33745, -1359, -430, -1],
    poly [38, 169, -178, 74, -25, -42, 185, -123, 59, -112, 63, -150, -49, -158, -6, -2],
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
theorem certificado_91961 :
    haveI : Fact (Nat.Prime 91961) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 91961 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((91961 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((91961 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((91961 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 91961) := ⟨by norm_num⟩
  have hP : poly [-8271, 1] = X - C (8271 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((91961 : ℕ) : ℤ[X]) = poly [91961] := by simp [poly]
  refine ⟨X - C (8271 : ℤ),
    poly [-17923, -32079, -29668, -38985, -26400, -45778, -20975, -16280, -12110, -37493, -45935, 15905,
      -31708, -1427, -28886, -1271, 8272, 1],
    poly [-1612, -2885, -2668, -3506, -2374, -4117, -1886, -1464, -1089, -3372, -4131, 1431, -2852, -128,
      -2598, -114, 744],
    poly [1, -1, 0, 0, -1, 1, 0, -1, 0, 0, -1],
    poly [26818, 5685, 26285, 16670, 21939, 14279, 21872, 8931, -6970, -13454, 12518, 2092, 1646, 8595,
      40328, 12102, -5035, -1746],
    poly [65143, -44010, -41733, 30215, 11934, -35022, 26480, 17137, -3289, -1746],
    poly [-2412, -511, -2364, -1499, -1973, -1284, -1967, -803, 627, 1210, -1126, -188, -148, -773,
      -3627, -1088, 453, 157],
    poly [-5859, 3959, 3753, -2718, -1073, 3150, -2382, -1541, 296, 157],
    poly [-17923, 3767, 16567, -11728, 39825, -35730, 27614, 9543, -8271, -1],
    poly [-1612, 339, 1490, -1055, 3582, -3214, 2484, 858, -744],
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
theorem certificado_92189 :
    haveI : Fact (Nat.Prime 92189) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 92189 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((92189 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((92189 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((92189 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 92189) := ⟨by norm_num⟩
  have hP : poly [-413, 1] = X - C (413 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((92189 : ℕ) : ℤ[X]) = poly [92189] := by simp [poly]
  refine ⟨X - C (413 : ℤ),
    poly [-17411, -42900, -34033, 24918, -11547, 1981, -4906, 23426, 8539, -45739, 41631, 30012, -5731,
      40835, -794, -13395, 414, 1],
    poly [-78, -192, -152, 112, -52, 9, -22, 105, 38, -205, 187, 134, -26, 183, -4, -60, 2],
    poly [1, -1, -1, -1, 0, -1, -1, -1],
    poly [63356, 21098, 27469, 49583, 2984, 23184, 24349, 26584, 36411, 31524, 34414, 17010, 21209,
      24121, 21003, 32826, 25042, 15648],
    poly [28833, 13425, 14727, 5355, 32826, 25042, 15648],
    poly [-284, -94, -123, -222, -13, -104, -109, -119, -163, -141, -154, -76, -95, -108, -94, -147,
      -112, -70],
    poly [-129, -60, -66, -24, -147, -112, -70],
    poly [-17411, -8078, -40422, 795, 13395, -414, -1],
    poly [-78, -36, -181, 4, 60, -2],
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
theorem certificado_92227 :
    haveI : Fact (Nat.Prime 92227) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 92227 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((92227 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((92227 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((92227 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 92227) := ⟨by norm_num⟩
  have hP : poly [-4670, 1] = X - C (4670 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((92227 : ℕ) : ℤ[X]) = poly [92227] := by simp [poly]
  refine ⟨X - C (4670 : ℤ),
    poly [-12580, -7448, -5788, 33710, -526, 10684, 17401, 37329, -33644, -24397, 4616, 45917, 5579,
      -13507, 43721, -44228, 4671, 1],
    poly [-637, -377, -293, 1707, -27, 541, 881, 1890, -1704, -1235, 234, 2325, 282, -684, 2214, -2240,
      237],
    poly [-1, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, -1, -1],
    poly [10622, -1541, -7488, -24651, -31784, -28053, -35616, 108, -14143, -2435, -2314, -47993, -23376,
      -39782, -23236, -30895, -3900, 13386],
    poly [102849, -104390, -5947, -17163, 3489, -8432, -13510, 18561, -140, -8887, -19336, -44281, -3900,
      13386],
    poly [-538, 78, 379, 1248, 1609, 1420, 1803, -6, 716, 123, 117, 2430, 1183, 2014, 1176, 1564, 197,
      -678],
    poly [-5208, 5287, 300, 869, -177, 427, 684, -940, 7, 450, 979, 2242, 197, -678],
    poly [12580, -5132, -1660, -39498, -45411, -16342, -8377, 32801, 38142, -30721, -39050, 44229, -4671,
      -1],
    poly [637, -260, -84, -2000, -2299, -827, -424, 1661, 1931, -1556, -1977, 2240, -237],
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
theorem certificado_92569 :
    haveI : Fact (Nat.Prime 92569) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 92569 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((92569 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((92569 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((92569 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 92569) := ⟨by norm_num⟩
  have hP : poly [-769, 1] = X - C (769 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((92569 : ℕ) : ℤ[X]) = poly [92569] := by simp [poly]
  refine ⟨X - C (769 : ℤ),
    poly [-36835, 22342, -7675, -39734, -30266, 16091, -44157, -30031, -29170, 27167, -11280, 6606,
      23843, 17967, 1829, 36717, 770, 1],
    poly [-306, 186, -64, -330, -251, 134, -367, -249, -242, 226, -94, 55, 198, 149, 15, 305, 6],
    poly [-1, 0, 0, 1, 1, 0, 0, 0, -1, -1, -1],
    poly [-36313, -3618, -5983, -13329, -24052, -13834, -19358, -29236, 3373, -19456, -28875, -29128,
      1086, -23311, -26954, 8191, -3199, -31141],
    poly [56256, -59874, -2365, 28967, -7105, -20112, 4187, 8191, -3199, -31141],
    poly [302, 30, 50, 111, 200, 115, 161, 243, -28, 162, 240, 242, -9, 194, 224, -68, 27, 259],
    poly [-467, 498, 19, -241, 59, 167, -35, -68, 27, 259],
    poly [36835, 33392, 30017, -4776, 12874, -17197, -1828, -36717, -770, -1],
    poly [306, 277, 249, -40, 107, -143, -15, -305, -6],
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
theorem certificado_92683 :
    haveI : Fact (Nat.Prime 92683) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 92683 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((92683 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((92683 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((92683 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 92683) := ⟨by norm_num⟩
  have hP : poly [-5629, 1] = X - C (5629 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((92683 : ℕ) : ℤ[X]) = poly [92683] := by simp [poly]
  refine ⟨X - C (5629 : ℤ),
    poly [-40060, -37515, -36115, -25330, 26307, 12650, 20979, 21919, -43662, -26204, -44642, 12588,
      39700, -5657, 43138, -6315, 5630, 1],
    poly [-2433, -2278, -2193, -1538, 1598, 768, 1274, 1331, -2652, -1591, -2711, 765, 2411, -344, 2620,
      -384, 342],
    poly [-1, 1, -1, 0, -1, -1, -1, 0, 0, -1, -1],
    poly [-25265, -42805, -65382, -99288, -104283, -101386, -86682, -44907, -22655, -32629, -34656,
      -45968, -77501, -112874, -124867, -95775, -66297, -51720],
    poly [67418, -84958, -30302, -28869, -18931, -68819, -58570, -44055, -66297, -51720],
    poly [1535, 2600, 3971, 6030, 6333, 6157, 5264, 2727, 1376, 1982, 2105, 2792, 4707, 6855, 7583, 5816,
      4026, 3141],
    poly [-4094, 5160, 1840, 1753, 1150, 4180, 3557, 2675, 4026, 3141],
    poly [40060, -42605, 41205, -11930, -2192, -659, -37508, 6316, -5630, -1],
    poly [2433, -2588, 2503, -725, -133, -40, -2278, 384, -342],
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
theorem certificado_92987 :
    haveI : Fact (Nat.Prime 92987) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 92987 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((92987 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((92987 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((92987 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 92987) := ⟨by norm_num⟩
  have hP : poly [-6733, 1] = X - C (6733 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((92987 : ℕ) : ℤ[X]) = poly [92987] := by simp [poly]
  refine ⟨X - C (6733 : ℤ),
    poly [-14805, -32471, -5170, -28354, 40530, -13266, -29391, 30600, -14469, 13698, -20562, 4223,
      19446, -4527, 6587, -37633, 6734, 1],
    poly [-1072, -2351, -374, -2053, 2935, -961, -2128, 2216, -1048, 992, -1489, 306, 1408, -328, 477,
      -2725, 488],
    poly [-1, -1, -1, -1, 0, -1, 0, 0, -1, 1],
    poly [23560, 35123, 36271, 15790, 25192, 20263, 41213, 1331, 15771, 22858, 56557, 2010, 25770, 22749,
      23591, 29143, 25995, 6342],
    poly [116547, -57864, 36271, 15790, 1632, 8700, 16505, -13311, -6342],
    poly [-1706, -2543, -2626, -1143, -1824, -1467, -2984, -96, -1142, -1655, -4095, -145, -1866, -1647,
      -1708, -2110, -1882, -459],
    poly [-8439, 4191, -2627, -1143, -118, -630, -1195, 964, 459],
    poly [14805, 32471, 5170, 28354, 37652, -4400, 41887, 6732, 1],
    poly [1072, 2351, 374, 2053, 2726, -319, 3033, 487],
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
theorem certificado_93139 :
    haveI : Fact (Nat.Prime 93139) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 93139 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((93139 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((93139 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((93139 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 93139) := ⟨by norm_num⟩
  have hP : poly [-5073, 1] = X - C (5073 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((93139 : ℕ) : ℤ[X]) = poly [93139] := by simp [poly]
  refine ⟨X - C (5073 : ℤ),
    poly [26181, -8679, -8080, -43147, -25143, -11388, 37470, -35941, 14185, -6111, 5470, -29246, 19988,
      -24745, 142, 34039, 5074, 1],
    poly [1426, -473, -440, -2350, -1369, -620, 2041, -1958, 773, -333, 298, -1593, 1089, -1348, 8, 1854,
      276],
    poly [-1, 0, 0, 0, -1, -1, 0, 0, -1, -2, 0, 0, -1],
    poly [-32712, -12945, -52488, -17190, -28970, -19, -968, -23312, -41107, -31490, -59450, -18091,
      -4056, -21036, -20103, -44558, -25689, -25722],
    poly [60427, -73372, -39543, 35298, -44492, 16006, -20725, -26589, -26989, -18869, 33, -25722],
    poly [1782, 705, 2859, 936, 1578, 1, 53, 1270, 2239, 1715, 3238, 985, 221, 1146, 1095, 2427, 1399,
      1401],
    poly [-3291, 3997, 2153, -1923, 2424, -872, 1129, 1448, 1470, 1028, -2, 1401],
    poly [-26181, 34860, -599, 35067, -44185, -5076, -14597, 14740, 33895, -28965, -5073, -1],
    poly [-1426, 1899, -33, 1910, -2407, -276, -795, 803, 1846, -1578, -276],
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
theorem certificado_93253 :
    haveI : Fact (Nat.Prime 93253) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 93253 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((93253 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((93253 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((93253 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 93253) := ⟨by norm_num⟩
  have hP : poly [-5965, 1] = X - C (5965 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((93253 : ℕ) : ℤ[X]) = poly [93253] := by simp [poly]
  refine ⟨X - C (5965 : ℤ),
    poly [37395, -19895, 38486, 26974, -30887, 25102, 32803, 19172, 29519, 10151, -19540, 5187, 35770,
      39277, 8730, -35455, 5966, 1],
    poly [2392, -1273, 2462, 1725, -1976, 1606, 2098, 1226, 1888, 649, -1250, 332, 2288, 2512, 558,
      -2268, 382],
    poly [-1, 0, -1, 0, -1, -1, 0, 1, 0, 0, -1],
    poly [-8653, -17628, -15050, 4242, -14890, -10766, 12716, -26426, -10424, -713, -16376, -20584,
      19765, 2450, -51957, -2893, 1602, -47017],
    poly [84600, -102228, -6075, 10317, -25207, 5788, -2047, -4495, 48619, -47017],
    poly [554, 1128, 963, -271, 953, 689, -813, 1691, 667, 46, 1048, 1317, -1264, -156, 3324, 185, -102,
      3008],
    poly [-5411, 6540, 388, -660, 1613, -370, 131, 287, -3110, 3008],
    poly [-37395, -35963, -2523, -24451, -37915, -24582, -44184, 41421, -5965, -1],
    poly [-2392, -2300, -161, -1564, -2425, -1572, -2826, 2650, -382],
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
theorem certificado_93329 :
    haveI : Fact (Nat.Prime 93329) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 93329 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((93329 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((93329 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((93329 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 93329) := ⟨by norm_num⟩
  have hP : poly [-15341, 1] = X - C (15341 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((93329 : ℕ) : ℤ[X]) = poly [93329] := by simp [poly]
  refine ⟨X - C (15341 : ℤ),
    poly [5092, 22090, -15743, -1163, -45968, 5016, 35766, -30501, 16728, 35493, -40320, -9268, -26726,
      20202, -14934, -14115, 15342, 1],
    poly [837, 3631, -2588, -191, -7556, 825, 5879, -5014, 2750, 5834, -6628, -1523, -4393, 3321, -2455,
      -2320, 2522],
    poly [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, -1],
    poly [14742, -15006, -11157, -11175, -12848, 13129, -14562, -32109, 1362, -14216, -20690, -219, 9942,
      -25604, 9697, 8659, -25598, -20855],
    poly [78587, -63581, -3849, 18, 1673, -40719, 57439, -1044, -3705, 13402, -4743, -20855],
    poly [-2423, 2467, 1834, 1837, 2112, -2158, 2394, 5278, -224, 2337, 3401, 36, -1634, 4209, -1594,
      -1423, 4208, 3428],
    poly [-12918, 10452, 632, -3, -275, 6693, -9442, 172, 609, -2203, 780, 3428],
    poly [5092, 16998, -37833, 14580, -44805, -37253, -45581, -5679, -14522, 29456, -15341, -1],
    poly [837, 2794, -6219, 2397, -7365, -6123, -7492, -933, -2387, 4842, -2522],
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
theorem certificado_93481 :
    haveI : Fact (Nat.Prime 93481) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 93481 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((93481 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((93481 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((93481 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 93481) := ⟨by norm_num⟩
  have hP : poly [-155, 1] = X - C (155 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((93481 : ℕ) : ℤ[X]) = poly [93481] := by simp [poly]
  refine ⟨X - C (155 : ℤ),
    poly [-17490, 45723, 41306, 3282, -12644, 14996, -45136, 915, 609, -22914, -30303, 20310, -23390,
      -35734, 8816, 24181, 156, 1],
    poly [-29, 76, 68, 5, -21, 25, -75, 2, 1, -38, -50, 34, -39, -59, 15, 40],
    poly [0, -1, 0, -1, -1, 0, -2, 0, 0, 0, 0, 0, 0, -1],
    poly [25352, 51449, 20256, 9802, 18178, 29691, 33987, 12303, 11560, 10349, 50146, 40150, 19580,
      -34832, 29349, 35191, 37038, -3358],
    poly [93481, -68129, 26097, -5841, 40995, 3280, 20570, 54412, -64181, -5842, -1847, 40396, -3358],
    poly [-42, -85, -33, -16, -30, -49, -56, -20, -19, -17, -83, -66, -32, 58, -49, -58, -61, 6],
    poly [-155, 114, -44, 10, -68, -5, -34, -90, 107, 9, 3, -67, 6],
    poly [0, 17490, 30268, 21907, -7699, -42870, -43700, -12344, 44550, 15365, -24025, -155, -1],
    poly [0, 29, 50, 36, -13, -71, -72, -20, 74, 25, -40],
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
theorem certificado_93557 :
    haveI : Fact (Nat.Prime 93557) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 93557 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((93557 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((93557 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((93557 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 93557) := ⟨by norm_num⟩
  have hP : poly [-3455, 1] = X - C (3455 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((93557 : ℕ) : ℤ[X]) = poly [93557] := by simp [poly]
  refine ⟨X - C (3455 : ℤ),
    poly [-16166, 42536, -23140, 37037, -40824, -25872, 30429, -23658, -10378, -39213, 8708, -45923,
      -32589, -30473, 28478, -34815, 3456, 1],
    poly [-597, 1571, -855, 1368, -1508, -955, 1124, -874, -383, -1448, 322, -1696, -1203, -1125, 1052,
      -1286, 128],
    poly [-1, -1, -1, 0, -1, 0, 0, -1, 0, 0, 0, -1, 0, -1],
    poly [6853, 20963, 31257, 6158, 12433, 38295, 17154, 15469, 846, 23967, 37838, 20295, -8576, 18711,
      19098, 7021, 23698, -7194],
    poly [100410, -72594, 31257, -695, -1677, 21148, 21290, -15210, -17064, 42969, -23871, 30892, -7194],
    poly [-253, -774, -1154, -227, -459, -1414, -633, -571, -31, -885, -1397, -749, 317, -691, -705,
      -259, -875, 266],
    poly [-3708, 2682, -1155, 26, 62, -781, -786, 562, 630, -1587, 882, -1141, 266],
    poly [16166, -42536, 23140, 40354, 5969, 37587, -21273, 32380, 3665, 26809, 38270, -3455, -1],
    poly [597, -1571, 855, 1490, 220, 1388, -786, 1196, 135, 990, 1413, -128],
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
theorem certificado_93937 :
    haveI : Fact (Nat.Prime 93937) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 93937 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((93937 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((93937 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((93937 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 93937) := ⟨by norm_num⟩
  have hP : poly [-2570, 1] = X - C (2570 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((93937 : ℕ) : ℤ[X]) = poly [93937] := by simp [poly]
  refine ⟨X - C (2570 : ℤ),
    poly [-17435, -16528, 15601, 38385, 17852, 18904, 42809, 28015, 45627, 30794, 26000, 46540, -20341,
      43342, 21107, 31881, 2571, 1],
    poly [-477, -452, 427, 1050, 488, 517, 1171, 766, 1248, 842, 711, 1273, -557, 1186, 577, 872, 70],
    poly [1, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, -1],
    poly [-173, -10444, -41407, -25373, -29095, -11698, -17576, -15239, -38302, 2590, -27220, -11149,
      -27335, -43497, -16967, -12205, -27043, -25075],
    poly [94110, -83493, 41234, 14929, -12312, -13675, -11692, -6730, -10237, -1968, -25075],
    poly [5, 286, 1133, 694, 796, 320, 481, 417, 1048, -71, 745, 305, 748, 1190, 464, 334, 740, 686],
    poly [-2575, 2285, -1129, -408, 337, 374, 320, 184, 280, 54, 686],
    poly [-17435, -16528, 33036, -39024, 2251, -19481, 42392, 8204, -29311, -2570, -1],
    poly [-477, -452, 904, -1068, 62, -533, 1160, 224, -802, -70],
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
theorem certificado_94583 :
    haveI : Fact (Nat.Prime 94583) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 94583 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((94583 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((94583 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((94583 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 94583) := ⟨by norm_num⟩
  have hP : poly [-6023, 1] = X - C (6023 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((94583 : ℕ) : ℤ[X]) = poly [94583] := by simp [poly]
  refine ⟨X - C (6023 : ℤ),
    poly [-8637, 19581, -1944, 36809, 17233, -40858, -10010, -16145, -37660, -7120, -25127, 37449,
      -35484, -35025, -43128, -37319, 6024, 1],
    poly [-550, 1247, -124, 2344, 1097, -2602, -637, -1028, -2398, -453, -1600, 2385, -2260, -2230,
      -2746, -2376, 384],
    poly [-1, -1, 0, 1, 0, -1, 0, -1, -1, -1, 0, 0, -1],
    poly [37416, 9297, 34638, 39793, 14935, 19799, 35315, 22896, 17115, 26442, -975, 34228, -1806, 45189,
      -9232, 34101, 36291, 34721],
    poly [131999, -85286, -2778, -6920, 8416, -7919, -12894, 90712, -8612, -2190, 1570, 34721],
    poly [-2383, -592, -2206, -2534, -951, -1261, -2249, -1458, -1090, -1684, 62, -2180, 115, -2878, 588,
      -2172, -2311, -2211],
    poly [-8406, 5432, 176, 441, -536, 504, 821, -5777, 549, 139, -100, -2211],
    poly [8637, -19581, -6693, -25865, 9041, -29804, 37778, -14127, 5808, 43343, -6023, -1],
    poly [550, -1247, -426, -1647, 576, -1898, 2406, -900, 370, 2760, -384],
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
theorem certificado_94621 :
    haveI : Fact (Nat.Prime 94621) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 94621 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((94621 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((94621 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((94621 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 94621) := ⟨by norm_num⟩
  have hP : poly [-3080, 1] = X - C (3080 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((94621 : ℕ) : ℤ[X]) = poly [94621] := by simp [poly]
  refine ⟨X - C (3080 : ℤ),
    poly [41197, -29356, -25293, -24155, 25675, -18240, -5505, 24145, -4416, 10966, -4451, 33546, -13660,
      -13491, 26170, 27381, 3081, 1],
    poly [1341, -956, -823, -786, 836, -594, -179, 786, -144, 357, -145, 1092, -445, -439, 852, 891, 100],
    poly [0, -1, 0, 0, -1, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, 0, -1],
    poly [60289, 40985, 18368, 37930, 29273, 45153, 46387, 20766, 31848, 33019, 48042, 61472, 34749,
      26845, 57072, 7713, 45146, 50903],
    poly [94621, -34332, -19304, -22617, 79851, -27961, -6737, -39493, -14974, -10710, 2147, 20676,
      49359, -37433, -5757, 50903],
    poly [-1963, -1334, -598, -1235, -953, -1470, -1510, -676, -1037, -1075, -1564, -2001, -1131, -874,
      -1858, -251, -1470, -1657],
    poly [-3080, 1118, 628, 736, -2600, 911, 219, 1286, 487, 349, -70, -673, -1607, 1219, 187, -1657],
    poly [0, -41197, -24068, -4063, -42335, 20723, 39852, 27324, 39209, 23115, -2911, 39660, 1211,
      -24300, -3080, -1],
    poly [0, -1341, -783, -132, -1378, 675, 1297, 889, 1276, 752, -95, 1291, 39, -791, -100],
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
theorem certificado_94811 :
    haveI : Fact (Nat.Prime 94811) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 94811 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((94811 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((94811 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((94811 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 94811) := ⟨by norm_num⟩
  have hP : poly [-4562, 1] = X - C (4562 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((94811 : ℕ) : ℤ[X]) = poly [94811] := by simp [poly]
  refine ⟨X - C (4562 : ℤ),
    poly [-5549, 16625, -4527, -957, -6526, -521, 42563, 2337, -26643, -37207, 31166, -679, 19120, -2178,
      44537, -42013, 4563, 1],
    poly [-267, 800, -218, -46, -314, -25, 2048, 112, -1282, -1790, 1500, -33, 920, -105, 2143, -2022,
      220],
    poly [-1, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [23291, 37657, 18540, 31816, 32193, 38324, 22094, 32274, 13738, 27409, 38988, 9001, 4443, 26638,
      27204, 39175, 3743, 29589],
    poly [118102, -57154, -4751, 17450, 28019, -12609, 3177, 17618, 35432, -25846, 29589],
    poly [-1121, -1812, -892, -1531, -1549, -1844, -1063, -1553, -661, -1319, -1876, -433, -214, -1282,
      -1309, -1885, -180, -1424],
    poly [-5683, 2751, 228, -840, -1348, 607, -153, -848, -1705, 1244, -1424],
    poly [5549, -16625, -1022, 23131, -20175, 20716, 42152, 8260, 46576, -4562, -1],
    poly [267, -800, -49, 1113, -971, 997, 2028, 397, 2241, -220],
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
theorem certificado_94849 :
    haveI : Fact (Nat.Prime 94849) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 94849 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((94849 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((94849 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((94849 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 94849) := ⟨by norm_num⟩
  have hP : poly [-4041, 1] = X - C (4041 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((94849 : ℕ) : ℤ[X]) = poly [94849] := by simp [poly]
  refine ⟨X - C (4041 : ℤ),
    poly [26922, -25953, -18995, -15496, -30517, 23558, -41140, 46229, -36487, -21157, -47418, 41627,
      -14237, 30627, 9185, 19695, 4042, 1],
    poly [1147, -1106, -809, -660, -1300, 1004, -1753, 1970, -1555, -901, -2020, 1774, -607, 1305, 391,
      839, 172],
    poly [-1, 0, 0, 1, 1, 0, 0, 0, -1, -1],
    poly [-46866, -1812, -16588, -13822, -23609, -28517, -19998, -23634, -19410, -13987, -39382, -26784,
      -10116, -15393, -31801, -7418, 3385, -27947],
    poly [47983, -49795, -14776, 49632, -7975, -35186, 20529, 3385, -27947],
    poly [1997, 77, 707, 589, 1006, 1215, 852, 1007, 827, 596, 1678, 1141, 431, 656, 1355, 316, -144,
      1191],
    poly [-2044, 2122, 629, -2115, 340, 1499, -875, -144, 1191],
    poly [-26922, -41974, -6958, 23423, -10932, -5143, -19694, -4042, -1],
    poly [-1147, -1788, -296, 998, -466, -219, -839, -172],
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
theorem certificado_95153 :
    haveI : Fact (Nat.Prime 95153) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 95153 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((95153 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((95153 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((95153 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 95153) := ⟨by norm_num⟩
  have hP : poly [-1437, 1] = X - C (1437 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((95153 : ℕ) : ℤ[X]) = poly [95153] := by simp [poly]
  refine ⟨X - C (1437 : ℤ),
    poly [8873, -29725, -5318, -401, 46285, 2416, -18870, -26897, 22230, 14252, 9214, -10522, 25486,
      -44877, -12811, -26959, 1438, 1],
    poly [134, -449, -80, -6, 699, 36, -285, -406, 336, 215, 139, -159, 385, -678, -193, -407, 22],
    poly [-1, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, -1],
    poly [-11185, -11259, -20728, -22390, -24179, -40933, -11677, -22781, 19656, -3424, 16160, -3294,
      4506, -28663, -28355, -1802, -7743, -8012],
    poly [83968, -95227, -9469, -1662, 9396, -27865, 27466, -7800, 33169, -308, -26553, 5941, 269, -8012],
    poly [169, 170, 313, 338, 365, 618, 176, 344, -297, 52, -244, 50, -68, 433, 428, 27, 117, 121],
    poly [-1268, 1439, 142, 25, -142, 421, -415, 118, -501, 5, 401, -90, -4, 121],
    poly [-8873, 38598, -24407, -4917, -37813, -3602, -19735, 36008, 24790, 32066, -14148, 28397, -1437,
      -1],
    poly [-134, 583, -369, -74, -571, -54, -298, 544, 374, 484, -214, 429, -22],
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
theorem certificado_95191 :
    haveI : Fact (Nat.Prime 95191) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 95191 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((95191 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((95191 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((95191 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 95191) := ⟨by norm_num⟩
  have hP : poly [-6322, 1] = X - C (6322 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((95191 : ℕ) : ℤ[X]) = poly [95191] := by simp [poly]
  refine ⟨X - C (6322 : ℤ),
    poly [21095, 39995, 4403, 46226, 20229, 31593, -1049, -29753, -28824, -16733, 35502, -25998, -41637,
      26253, 35298, -6213, 6323, 1],
    poly [1401, 2656, 292, 3070, 1343, 2098, -70, -1976, -1914, -1111, 2358, -1727, -2765, 1744, 2344,
      -413, 420],
    poly [-1, 0, 0, 0, 0, -2, -1, -1, -1, -1, -1, -1],
    poly [-2185, 17946, 1552, 4079, 3974, 29556, 15045, -9666, 2963, 33817, -10446, -10980, 21212, 23566,
      -39553, 19235, 34723, 10875],
    poly [93006, -75060, -16394, 2527, -105, 21212, 23566, -39553, 19235, 34723, 10875],
    poly [145, -1192, -103, -271, -264, -1963, -999, 642, -197, -2246, 694, 729, -1409, -1565, 2627,
      -1278, -2306, -722],
    poly [-6177, 4986, 1088, -168, 7, -1409, -1565, 2627, -1278, -2306, -722],
    poly [-21095, -18900, 35592, -41823, 25997, 41637, -26253, -35298, 6213, -6323, -1],
    poly [-1401, -1255, 2364, -2778, 1727, 2765, -1744, -2344, 413, -420],
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
theorem certificado_95267 :
    haveI : Fact (Nat.Prime 95267) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 95267 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((95267 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((95267 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((95267 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 95267) := ⟨by norm_num⟩
  have hP : poly [-4362, 1] = X - C (4362 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((95267 : ℕ) : ℤ[X]) = poly [95267] := by simp [poly]
  refine ⟨X - C (4362 : ℤ),
    poly [24876, -31335, 39742, -11457, -9656, -35842, 26615, -39481, 46729, 42206, 46027, -23970, 26443,
      47443, 404, -21993, 4363, 1],
    poly [1139, -1435, 1820, -525, -442, -1641, 1219, -1808, 2140, 1932, 2107, -1098, 1211, 2172, 18,
      -1007, 200],
    poly [-1, 0, 0, 0, 0, -1, -1, -1, -2, 0, -1],
    poly [8267, 39828, 23739, 37036, 27888, 673, 33711, 48832, 12952, 7309, 54286, -544, 12897, 41751,
      11225, 2744, 54962, 45539],
    poly [103534, -63706, -16089, 13297, -9148, -18948, 72866, 38860, 9423, 45539],
    poly [-379, -1824, -1087, -1696, -1277, -31, -1544, -2236, -593, -335, -2486, 25, -591, -1912, -514,
      -126, -2517, -2085],
    poly [-4741, 2918, 736, -609, 419, 867, -3337, -1779, -432, -2085],
    poly [-24876, -39056, 24190, -44068, -1801, 1310, -31122, 26354, -4362, -1],
    poly [-1139, -1788, 1108, -2018, -82, 60, -1425, 1207, -200],
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
theorem certificado_95419 :
    haveI : Fact (Nat.Prime 95419) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 95419 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((95419 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((95419 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((95419 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 95419) := ⟨by norm_num⟩
  have hP : poly [-4823, 1] = X - C (4823 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((95419 : ℕ) : ℤ[X]) = poly [95419] := by simp [poly]
  refine ⟨X - C (4823 : ℤ),
    poly [-42714, -21811, -6652, -18460, -538, -26867, -35439, 38275, 21909, 4179, 25562, 28356, 2103,
      -4451, 7339, -16083, 4824, 1],
    poly [-2159, -1102, -336, -933, -27, -1358, -1791, 1935, 1107, 211, 1292, 1433, 106, -225, 371, -813,
      244],
    poly [1, 0, 0, 1, 0, 1, 0, 0, -1, 1, 0, 0, 0, 1],
    poly [28685, 4396, 14837, 3305, -21665, 3337, 9317, 2374, 1324, -1446, 334, -17689, -11619, 8938,
      34998, 3784, 18675, 9795],
    poly [66734, -71130, -10441, -17153, 49259, -64128, 29841, 21472, 16265, -31214, 14891, -8880, -9795],
    poly [-1450, -222, -750, -167, 1095, -169, -471, -120, -67, 73, -17, 894, 587, -452, -1769, -191,
      -944, -495],
    poly [-3373, 3596, 527, 867, -2490, 3242, -1509, -1085, -822, 1578, -753, 449, 495],
    poly [-42714, 20903, 15159, 40897, 38825, 41535, 523, 11376, -11789, 23422, -20907, 4823, 1],
    poly [-2159, 1057, 766, 2067, 1962, 2099, 26, 575, -596, 1184, -1057, 244],
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
theorem certificado_95723 :
    haveI : Fact (Nat.Prime 95723) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 95723 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((95723 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((95723 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((95723 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 95723) := ⟨by norm_num⟩
  have hP : poly [-4250, 1] = X - C (4250 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((95723 : ℕ) : ℤ[X]) = poly [95723] := by simp [poly]
  refine ⟨X - C (4250 : ℤ),
    poly [-38582, -20933, 35086, 30527, -21660, 32811, 34468, 21878, -27000, 827, -7027, 28963, 37305,
      -28100, -34084, -24896, 4251, 1],
    poly [-1713, -929, 1558, 1355, -962, 1457, 1530, 971, -1199, 37, -312, 1286, 1656, -1248, -1513,
      -1105, 189],
    poly [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 1, -1],
    poly [35672, 27482, 22525, 26105, 21376, 15136, 6801, 55111, 33275, 14846, 17612, 4279, 5875, 32858,
      7616, 6574, 7790, 19232],
    poly [60051, -87533, 4957, -3580, 4729, 41912, 145, -53267, 25416, 13700, -9006, -30674, 19232],
    poly [-1584, -1220, -1000, -1159, -949, -672, -302, -2447, -1477, -659, -782, -190, -261, -1459,
      -338, -292, -346, -854],
    poly [-2666, 3887, -221, 159, -210, -1861, -6, 2365, -1129, -608, 400, 1362, -854],
    poly [-38582, 17649, -39704, -4559, 43536, -2670, -15992, 27114, -44319, -15709, 33398, -4249, -1],
    poly [-1713, 784, -1763, -202, 1933, -119, -710, 1204, -1968, -697, 1483, -189],
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
theorem certificado_95989 :
    haveI : Fact (Nat.Prime 95989) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 95989 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((95989 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((95989 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((95989 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 95989) := ⟨by norm_num⟩
  have hP : poly [-2174, 1] = X - C (2174 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((95989 : ℕ) : ℤ[X]) = poly [95989] := by simp [poly]
  refine ⟨X - C (2174 : ℤ),
    poly [20178, -42157, 9606, -7899, -31529, -2752, -27597, 40255, 13706, 4819, 19253, 627, 39120,
      -25635, -1513, 24990, 2175, 1],
    poly [457, -955, 218, -179, -714, -62, -625, 912, 310, 109, 436, 14, 886, -581, -34, 566, 49],
    poly [0, -1, -1, -1, -1, -1, -2, 0, -1, -1, -1, -1, 0, -1, 0, -1],
    poly [-4497, 26364, -6251, -1365, -10370, -14657, 2340, 5571, -13016, 6447, -26968, -5834, 31441,
      -29694, -2303, 6761, -27586, -14400],
    poly [95989, -100486, 26364, -6251, -1365, -10370, -19154, 37698, -57905, 24485, -7444, -22250,
      19947, -13186, -14400],
    poly [102, -597, 142, 31, 235, 332, -53, -126, 295, -146, 611, 132, -712, 673, 52, -153, 625, 326],
    poly [-2174, 2277, -598, 142, 31, 235, 434, -854, 1312, -555, 169, 504, -452, 299, 326],
    poly [0, -20178, 42157, -9606, 7899, 31529, -17426, 14121, 37625, -40427, 1306, 24329, -22816, -2174,
      -1],
    poly [0, -457, 955, -218, 179, 714, -395, 320, 852, -916, 30, 551, -517, -49],
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
theorem certificado_96179 :
    haveI : Fact (Nat.Prime 96179) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 96179 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((96179 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((96179 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((96179 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 96179) := ⟨by norm_num⟩
  have hP : poly [-2227, 1] = X - C (2227 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((96179 : ℕ) : ℤ[X]) = poly [96179] := by simp [poly]
  refine ⟨X - C (2227 : ℤ),
    poly [-27381, -31237, -7831, 31178, -27367, -32619, 46153, -7969, 3581, 17579, 23502, 43371, -8143,
      -47942, 19888, -39551, 2228, 1],
    poly [-634, -723, -181, 722, -634, -755, 1069, -185, 83, 407, 544, 1004, -189, -1110, 461, -916, 52],
    poly [1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, -1],
    poly [-7546, -32080, 12781, -46366, 7808, -22615, -28459, -1167, -29745, -11619, 12747, -15530,
      -27117, 3757, -48659, 28062, -15955, -26383],
    poly [103725, -64099, -20327, 21832, 37053, -44078, 50553, -16475, -14919, 78799, -76721, 44017,
      10428, -26383],
    poly [175, 743, -296, 1074, -181, 524, 659, 27, 689, 269, -295, 360, 628, -87, 1127, -650, 370, 611],
    poly [-2402, 1485, 470, -506, -858, 1021, -1171, 382, 345, -1825, 1777, -1020, -241, 611],
    poly [-27381, -31237, 19550, 35034, 45406, -44247, 39756, 5114, -37571, -28348, 36740, 41779, -2227,
      -1],
    poly [-634, -723, 453, 811, 1051, -1025, 921, 118, -870, -656, 851, 967, -52],
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
theorem certificado_96293 :
    haveI : Fact (Nat.Prime 96293) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 96293 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((96293 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((96293 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((96293 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 96293) := ⟨by norm_num⟩
  have hP : poly [-3055, 1] = X - C (3055 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((96293 : ℕ) : ℤ[X]) = poly [96293] := by simp [poly]
  refine ⟨X - C (3055 : ℤ),
    poly [6367, 7031, 16235, -39489, 11807, 36031, -33084, -36889, 20003, 42905, 13473, 20839, 16208,
      36127, 29735, -4340, 3056, 1],
    poly [202, 223, 515, -1253, 375, 1143, -1050, -1170, 635, 1361, 427, 661, 514, 1146, 943, -138, 97],
    poly [-1, 1, 0, -1, 0, 0, 0, -1, -1, 0, -1, -1],
    poly [-42290, -17088, -54084, -33230, -22601, -3465, -31732, -27360, -35207, -49425, -38839, -34801,
      -34516, -19544, -16198, -39427, -46432, -29256],
    poly [54003, -28801, -62198, 15560, 14977, -28489, -26549, 978, -10171, -46432, -29256],
    poly [1342, 542, 1716, 1054, 717, 110, 1007, 868, 1117, 1568, 1232, 1104, 1095, 620, 514, 1251, 1473,
      928],
    poly [-1713, 914, 1973, -494, -475, 904, 842, -31, 323, 1473, 928],
    poly [-6367, 5703, -8540, -37732, -11391, 17868, -43523, -26680, 4341, -3056, -1],
    poly [-202, 181, -271, -1197, -361, 567, -1381, -846, 138, -97],
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
theorem certificado_96331 :
    haveI : Fact (Nat.Prime 96331) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 96331 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((96331 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((96331 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((96331 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 96331) := ⟨by norm_num⟩
  have hP : poly [-346, 1] = X - C (346 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((96331 : ℕ) : ℤ[X]) = poly [96331] := by simp [poly]
  refine ⟨X - C (346 : ℤ),
    poly [-20881, -42936, -14880, 33645, -21619, -40154, -11531, 27808, -45301, 19358, -11359, -41238,
      -8750, 10276, 23138, 23732, 347, 1],
    poly [-75, -154, -53, 121, -78, -144, -41, 100, -163, 70, -41, -148, -31, 37, 83, 85, 1],
    poly [1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    poly [2245, -33107, -33766, -19012, -7276, -13924, -17841, -23699, -4227, -22546, -11184, -24515,
      7464, -5529, -44266, -20156, -5052, -6122],
    poly [94086, -63224, 33766, 19012, 7276, 16169, -17511, 23040, 21226, -1070, 6122],
    poly [-8, 119, 121, 68, 26, 50, 64, 85, 15, 81, 40, 88, -27, 20, 159, 72, 18, 22],
    poly [-338, 228, -122, -68, -26, -58, 63, -83, -76, 4, -22],
    poly [-20881, -42936, -14880, 33645, -21619, -19273, 10524, -248, 23386, 346, 1],
    poly [-75, -154, -53, 121, -78, -69, 38, -1, 84, 1],
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
theorem certificado_96749 :
    haveI : Fact (Nat.Prime 96749) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 96749 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((96749 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((96749 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((96749 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 96749) := ⟨by norm_num⟩
  have hP : poly [-4663, 1] = X - C (4663 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((96749 : ℕ) : ℤ[X]) = poly [96749] := by simp [poly]
  refine ⟨X - C (4663 : ℤ),
    poly [20520, 1768, 22035, -29603, -12891, 32074, 45487, -35117, 34808, -38522, -44119, -34742,
      -17021, 27550, -1073, -20292, 4664, 1],
    poly [989, 85, 1062, -1427, -621, 1546, 2192, -1693, 1678, -1857, -2126, -1674, -820, 1328, -52,
      -978, 225],
    poly [1, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1],
    poly [34433, 27220, 12010, 8936, 7068, 25824, 20226, 50123, 49092, 17181, 33669, 31162, 4334, 13084,
      29228, 22924, 27591, 42261],
    poly [62316, -55103, 7997, -12136, -35639, -13411, 39564, -32421, -1637, 19337, -27591, -42261],
    poly [-1660, -1312, -579, -431, -341, -1245, -975, -2416, -2366, -828, -1623, -1502, -209, -631,
      -1409, -1105, -1330, -2037],
    poly [-3003, 2656, -386, 585, 1718, 646, -1907, 1563, 79, -932, 1330, 2037],
    poly [20520, -39272, 39019, 24844, -7879, 9501, -11285, 47843, -5737, -20293, 4664, 1],
    poly [989, -1893, 1881, 1197, -380, 458, -544, 2306, -277, -978, 225],
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
theorem certificado_96787 :
    haveI : Fact (Nat.Prime 96787) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 96787 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((96787 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((96787 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((96787 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 96787) := ⟨by norm_num⟩
  have hP : poly [-11603, 1] = X - C (11603 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((96787 : ℕ) : ℤ[X]) = poly [96787] := by simp [poly]
  refine ⟨X - C (11603 : ℤ),
    poly [2369, 3854, -29779, -8903, -5990, -35010, -5400, 19085, -10467, 21220, -35358, 44716, -44857,
      -3524, 27043, 10496, 11604, 1],
    poly [284, 462, -3570, -1067, -718, -4197, -647, 2288, -1255, 2544, -4239, 5361, -5378, -422, 3242,
      1258, 1391],
    poly [-1, -1, 1, -1, -1, 0, -1, 0, 1, -1],
    poly [9231, 14854, 50573, 24100, 20661, 37544, 14748, 11326, -12064, 36682, 24299, 33165, 32390,
      29412, 18843, -11029, 4442, 35916],
    poly [106018, -81933, 32111, 12854, -50777, 81259, 16003, -67390, 35916],
    poly [-1107, -1781, -6063, -2889, -2477, -4501, -1768, -1358, 1446, -4398, -2913, -3976, -3883,
      -3526, -2259, 1322, -533, -4306],
    poly [-12710, 9823, -3850, -1541, 6087, -9742, -1918, 8079, -4306],
    poly [-2369, -3854, 34517, 11873, 35511, -17656, 12711, -11602, -1],
    poly [-284, -462, 4138, 1423, 4257, -2117, 1524, -1391],
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
theorem certificado_97547 :
    haveI : Fact (Nat.Prime 97547) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 97547 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((97547 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((97547 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((97547 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 97547) := ⟨by norm_num⟩
  have hP : poly [-2398, 1] = X - C (2398 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((97547 : ℕ) : ℤ[X]) = poly [97547] := by simp [poly]
  refine ⟨X - C (2398 : ℤ),
    poly [16068, 42353, -24064, 112, -27702, 24843, 1068, 23716, -34038, -7377, 30099, 23362, -3692,
      30548, 27308, -2470, 2399, 1],
    poly [395, 1041, -592, 3, -681, 611, 26, 583, -837, -181, 740, 574, -91, 751, 671, -61, 59],
    poly [-1, 0, 0, 1, 1, 0, 1, 0, -1],
    poly [-45431, -4324, -20863, 9761, -29603, -23599, -21888, -5982, -10450, -13218, -18426, -31608,
      2231, 4157, -20412, -18429, 16596, -16461],
    poly [52116, -56440, -16539, 76055, -35040, -18564, 33057, -16461],
    poly [1117, 106, 513, -240, 728, 580, 538, 147, 257, 325, 453, 777, -55, -102, 502, 453, -408, 405],
    poly [-1281, 1388, 406, -1870, 862, 456, -813, 405],
    poly [-16068, -26285, -31130, -8108, -27380, 4870, -2398, -1],
    poly [-395, -646, -765, -199, -673, 120, -59],
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
theorem certificado_97813 :
    haveI : Fact (Nat.Prime 97813) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 97813 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((97813 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((97813 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((97813 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 97813) := ⟨by norm_num⟩
  have hP : poly [-7568, 1] = X - C (7568 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((97813 : ℕ) : ℤ[X]) = poly [97813] := by simp [poly]
  refine ⟨X - C (7568 : ℤ),
    poly [-10792, 17227, -39521, 41069, 15153, -22952, -46260, -11160, -41709, 1106, -8026, 34934, 25634,
      16172, 19040, -36225, 7569, 1],
    poly [-835, 1333, -3058, 3178, 1172, -1776, -3579, -863, -3227, 86, -621, 2703, 1983, 1251, 1473,
      -2803, 586],
    poly [1, 0, 0, -1, 1, 0, 0, 0, -1, 0, -1],
    poly [2408, -28714, -7496, -3073, -2801, -1767, 6479, -12519, -22887, -16271, -19889, -37958, 516,
      -4261, -10194, 28385, -16988, -30526],
    poly [95405, -66691, -21218, -2015, -33802, 51306, -25041, 14847, 13538, -30526],
    poly [-186, 2222, 580, 238, 217, 137, -501, 969, 1771, 1259, 1539, 2937, -40, 330, 789, -2196, 1315,
      2362],
    poly [-7382, 5161, 1641, 156, 2615, -3970, 1938, -1149, -1047, 2362],
    poly [-10792, 28019, 41065, -6431, 33086, 46662, 34980, 43793, -7568, -1],
    poly [-835, 2168, 3177, -498, 2560, 3610, 2706, 3388, -586],
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
theorem certificado_97927 :
    haveI : Fact (Nat.Prime 97927) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 97927 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((97927 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((97927 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((97927 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 97927) := ⟨by norm_num⟩
  have hP : poly [-17156, 1] = X - C (17156 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((97927 : ℕ) : ℤ[X]) = poly [97927] := by simp [poly]
  refine ⟨X - C (17156 : ℤ),
    poly [-41857, -38349, 3434, 36172, -39800, -16333, 34076, -29480, -8090, -33421, 40468, -16100,
      -5943, 34499, -48756, -23069, 17157, 1],
    poly [-7333, -6718, 602, 6337, -6973, -2861, 5970, -5165, -1417, -5855, 7090, -2821, -1041, 6044,
      -8542, -4041, 3006],
    poly [-1, 0, 1, -1, 0, -1, 0, 0, -1, -1, 0, 0, 0, -1],
    poly [-22195, -4861, 3234, 8229, 9799, 16272, -7376, 4404, 17419, 18373, -4265, -21379, -26072,
      -19411, -8103, 29662, 21633, 37244],
    poly [75732, -80593, 30290, -34534, 10809, -12622, -2889, 14972, 25936, -37765, 8029, -15611, 37244],
    poly [3888, 851, -567, -1442, -1717, -2851, 1292, -772, -3052, -3219, 747, 3745, 4567, 3400, 1419,
      -5197, -3790, -6525],
    poly [-13268, 14120, -5307, 6050, -1894, 2211, 506, -2623, -4544, 6616, -1407, 2735, -6525],
    poly [41857, -3508, 14287, 12627, 16320, 9345, 33227, 23285, 14671, 25687, 40226, -17156, -1],
    poly [7333, -615, 2503, 2212, 2859, 1637, 5821, 4079, 2570, 4500, 7047, -3006],
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
theorem certificado_98041 :
    haveI : Fact (Nat.Prime 98041) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 98041 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((98041 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((98041 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((98041 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 98041) := ⟨by norm_num⟩
  have hP : poly [-4566, 1] = X - C (4566 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((98041 : ℕ) : ℤ[X]) = poly [98041] := by simp [poly]
  refine ⟨X - C (4566 : ℤ),
    poly [25659, -13307, -6831, 4980, -8738, 14234, -1822, 10800, -27675, 27521, -44398, -2479, 5711,
      -39636, -31551, -29810, 4567, 1],
    poly [1195, -620, -318, 232, -407, 663, -85, 503, -1289, 1282, -2068, -115, 266, -1846, -1469, -1388,
      213],
    poly [-1, -1, 0, -1, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0, -1, 0, -1],
    poly [-27553, -18777, -1984, -3376, 27028, 3029, -2151, -32127, -9588, 6070, 9466, 29951, 3137,
      -28175, -39562, -22709, 5015, 20395],
    poly [70488, -116818, 25569, -12152, 10235, 4421, -32555, 19425, 14369, 10477, -921, 4058, -32233,
      -7329, -15380, 20395],
    poly [1283, 874, 92, 157, -1259, -141, 100, 1496, 446, -283, -441, -1395, -146, 1312, 1842, 1057,
      -234, -950],
    poly [-3283, 5441, -1192, 566, -477, -206, 1516, -905, -669, -488, 43, -189, 1501, 341, 716, -950],
    poly [-25659, 13307, 32490, -43946, 15214, -2423, -11896, 37831, -1688, -47389, -48172, 42461, -2825,
      34376, -4566, -1],
    poly [-1195, 620, 1513, -2047, 709, -113, -554, 1762, -79, -2207, -2243, 1978, -132, 1601, -213],
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
theorem certificado_98269 :
    haveI : Fact (Nat.Prime 98269) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 98269 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((98269 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((98269 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((98269 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 98269) := ⟨by norm_num⟩
  have hP : poly [-3371, 1] = X - C (3371 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((98269 : ℕ) : ℤ[X]) = poly [98269] := by simp [poly]
  refine ⟨X - C (3371 : ℤ),
    poly [-7900, -17085, 42206, -7217, -26180, 26345, -16142, 23462, 6566, -22532, -45541, -18991, 19963,
      -21945, -26884, -32191, 3372, 1],
    poly [-271, -586, 1448, -248, -898, 904, -554, 805, 225, -773, -1562, -651, 685, -753, -922, -1104,
      116],
    poly [1, 0, 1, -1, 1, 0, 0, 0, 1, 0, 0, 1, 0, -1],
    poly [34419, 34196, 41338, 56732, 12310, -2891, -6073, 12991, 70483, 57965, 24379, 21279, 260, 24770,
      63840, 53911, 33473, 29240],
    poly [63850, -98046, -41561, 19248, 2638, 7172, 55856, -63679, -59508, 5696, -8802, 4233, 29240],
    poly [-1181, -1173, -1418, -1946, -422, 99, 208, -446, -2418, -1988, -836, -730, -9, -850, -2190,
      -1849, -1148, -1003],
    poly [-2190, 3364, 1425, -661, -90, -246, -1916, 2185, 2041, -196, 302, -145, -1003],
    poly [-7900, -9185, -46878, 47561, 41613, 32895, 47264, -36600, -40502, -1936, 35564, -3371, -1],
    poly [-271, -315, -1608, 1632, 1427, 1128, 1621, -1256, -1389, -66, 1220, -116],
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
theorem certificado_98459 :
    haveI : Fact (Nat.Prime 98459) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 98459 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((98459 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((98459 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((98459 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 98459) := ⟨by norm_num⟩
  have hP : poly [-13112, 1] = X - C (13112 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((98459 : ℕ) : ℤ[X]) = poly [98459] := by simp [poly]
  refine ⟨X - C (13112 : ℤ),
    poly [-26890, -16094, 31214, -45405, 22719, 47384, -29049, 19206, 4995, -9416, 13418, 29354, -43633,
      17643, 17918, 28243, 13113, 1],
    poly [-3581, -2143, 4157, -6047, 3026, 6310, -3869, 2558, 665, -1254, 1787, 3909, -5811, 2350, 2386,
      3761, 1746],
    poly [-1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, -1],
    poly [3977, 19033, 11465, 22698, 5856, 35876, 8335, 39443, 25899, 27580, 36989, 5369, 35493, 47660,
      39033, 28407, 23285, 36846],
    poly [102436, -83403, -7568, 11233, -16842, 30020, -31518, 16052, -1999, 5504, 18683, -50407, 36846],
    poly [-530, -2535, -1527, -3023, -780, -4778, -1110, -5253, -3449, -3673, -4926, -715, -4727, -6347,
      -5198, -3783, -3101, -4907],
    poly [-13642, 11108, 1007, -1496, 2243, -3998, 4198, -2138, 266, -733, -2488, 6713, -4907],
    poly [26890, -10796, -47308, -21840, 30335, -24665, -48916, -37459, -10050, 25455, -2018, -13111, -1],
    poly [3581, -1438, -6300, -2908, 4040, -3285, -6514, -4988, -1338, 3390, -269, -1746],
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
theorem certificado_98573 :
    haveI : Fact (Nat.Prime 98573) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 98573 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((98573 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((98573 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((98573 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 98573) := ⟨by norm_num⟩
  have hP : poly [-1811, 1] = X - C (1811 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((98573 : ℕ) : ℤ[X]) = poly [98573] := by simp [poly]
  refine ⟨X - C (1811 : ℤ),
    poly [14805, -45441, 8085, -15998, -5724, -14155, 13382, 26025, 36537, -45429, 27571, 16943, 41975,
      -20878, -11333, 28624, 1812, 1],
    poly [272, -835, 149, -294, -105, -260, 246, 478, 671, -835, 507, 311, 771, -384, -208, 526, 33],
    poly [-1, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, 1, 0, -1, -1, -1],
    poly [-10707, 1044, 8834, 8294, 18581, 14831, 36982, 43798, 71670, 53288, 38745, 64428, 23674, 21311,
      12111, -9775, 3004, -28504],
    poly [87866, -86822, -2917, 11211, 7370, 7461, 29521, 14277, 68100, -26563, 46811, 40615, -9775,
      3004, -28504],
    poly [197, -19, -162, -152, -341, -272, -679, -804, -1316, -978, -711, -1183, -434, -391, -222, 180,
      -55, 524],
    poly [-1614, 1596, 53, -206, -135, -137, -542, -262, -1251, 489, -860, -746, 180, -55, 524],
    poly [-14805, -38327, 30242, -14244, 19968, -5813, -7569, -18456, -3276, -11541, 22691, 11334,
      -28624, -1812, -1],
    poly [-272, -704, 556, -262, 367, -107, -139, -339, -60, -212, 417, 208, -526, -33],
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
theorem certificado_98801 :
    haveI : Fact (Nat.Prime 98801) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 98801 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((98801 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((98801 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((98801 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 98801) := ⟨by norm_num⟩
  have hP : poly [-1032, 1] = X - C (1032 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((98801 : ℕ) : ℤ[X]) = poly [98801] := by simp [poly]
  refine ⟨X - C (1032 : ℤ),
    poly [36093, 22629, -23338, -2799, -13023, -19926, -46069, -16320, 22291, 23573, -8785, -38112, 6186,
      -43746, 21690, -20754, 1033, 1],
    poly [377, 236, -244, -29, -136, -208, -481, -170, 233, 246, -92, -398, 65, -457, 227, -217, 11],
    poly [-1, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, -1],
    poly [-4309, 7654, -12535, 11667, -11478, -1448, -7374, -24421, 19123, 13038, 4320, -18091, -21655,
      -25105, 6485, -7845, -18390, 843],
    poly [94492, -86838, -20189, 19893, -15491, 1804, -6222, -8336, 17894, 13995, -50823, 15173, 10545,
      -19233, 843],
    poly [45, -80, 131, -122, 120, 15, 77, 255, -200, -136, -45, 189, 226, 262, -68, 82, 192, -9],
    poly [-987, 908, 210, -208, 162, -19, 65, 87, -187, -146, 531, -159, -110, 201, -9],
    poly [-36093, 13464, 45967, 42169, -12405, -32467, 15478, 36108, 1854, -28145, -34397, -42445, 21787,
      -1032, -1],
    poly [-377, 141, 480, 440, -130, -339, 162, 377, 19, -294, -359, -443, 228, -11],
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
theorem certificado_98953 :
    haveI : Fact (Nat.Prime 98953) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 98953 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((98953 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((98953 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((98953 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 98953) := ⟨by norm_num⟩
  have hP : poly [-348, 1] = X - C (348 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((98953 : ℕ) : ℤ[X]) = poly [98953] := by simp [poly]
  refine ⟨X - C (348 : ℤ),
    poly [-6540, -30444, -16864, 35495, -12978, 19014, -38901, -10917, 40346, 47602, 4402, -12783, 7925,
      -28412, 12714, 22500, 349, 1],
    poly [-23, -107, -59, 125, -46, 67, -137, -38, 142, 167, 15, -45, 28, -100, 45, 79, 1],
    poly [-1, 0, -1, 0, 0, -1, 0, -1, 0, 0, 1, -1],
    poly [5481, 30235, 34287, 14963, -1016, -9308, -12744, -21853, -25007, 29010, 37980, 22651, 10380,
      8923, -20369, -17041, -21581, -27281],
    poly [104434, -74199, 9533, 5430, -11927, -22135, 5339, -7868, -1160, 32981, -27281],
    poly [-19, -106, -120, -52, 4, 33, 45, 77, 88, -102, -133, -79, -36, -31, 72, 60, 76, 96],
    poly [-367, 262, -34, -19, 42, 78, -19, 28, 4, -116, 96],
    poly [6540, 23904, -7040, -28455, 34893, 21142, 31339, 31937, -21803, -347, -1],
    poly [23, 84, -25, -100, 123, 74, 110, 112, -77, -1],
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
theorem certificado_99181 :
    haveI : Fact (Nat.Prime 99181) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 99181 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((99181 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((99181 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((99181 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 99181) := ⟨by norm_num⟩
  have hP : poly [-2387, 1] = X - C (2387 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((99181 : ℕ) : ℤ[X]) = poly [99181] := by simp [poly]
  refine ⟨X - C (2387 : ℤ),
    poly [17285, -20768, -43055, -31264, -21744, -33665, 21883, 45964, -30645, -9611, 15245, 31377,
      -12452, 27335, 30094, 46840, 2388, 1],
    poly [416, -500, -1036, -752, -523, -810, 527, 1106, -738, -231, 367, 755, -300, 658, 724, 1127, 57],
    poly [1, 1, 0, 0, 1, -1, 0, -1, 0, 0, 0, 0, 1],
    poly [13938, 6257, -31017, -29703, -29744, -15326, 11397, -9741, -22215, -28619, -21475, -25170,
      -29659, 3164, -27071, 215, -32640, -44371],
    poly [85243, -105438, 44955, 35960, -15211, 7242, -11548, -30235, 27286, -32855, -11731, 44371],
    poly [-335, -150, 747, 715, 716, 369, -274, 235, 535, 689, 517, 606, 714, -76, 652, -5, 786, 1068],
    poly [-2052, 2538, -1083, -865, 366, -174, 278, 728, -657, 791, 282, -1068],
    poly [17285, -20768, 38841, -10496, 38596, 41442, -39788, -2759, -16746, 44452, 2387, 1],
    poly [416, -500, 935, -253, 929, 997, -958, -66, -403, 1070, 57],
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
theorem certificado_99257 :
    haveI : Fact (Nat.Prime 99257) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 99257 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((99257 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((99257 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((99257 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 99257) := ⟨by norm_num⟩
  have hP : poly [-2693, 1] = X - C (2693 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((99257 : ℕ) : ℤ[X]) = poly [99257] := by simp [poly]
  refine ⟨X - C (2693 : ℤ),
    poly [19903, 25181, -8947, 24986, 1115, -37631, -3626, 28342, 6608, 16404, -12636, -3027, 17285,
      21310, 12134, 9182, 2694, 1],
    poly [540, 683, -243, 678, 30, -1021, -98, 769, 179, 445, -343, -82, 469, 578, 329, 249, 73],
    poly [-1, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, -1, -1, 0, -1],
    poly [-38292, -7862, 10062, -1652, -12603, -23222, 8582, -24541, -42466, -10849, 5380, -18129,
      -16000, -6748, -27569, -25181, -9442, -7667],
    poly [60965, -68827, -20368, 18716, -31319, -30195, 30915, -7102, -29154, -4360, -11830, -23406,
      -1775, -7667],
    poly [1039, 213, -273, 45, 342, 630, -233, 666, 1152, 294, -146, 492, 434, 183, 748, 683, 256, 208],
    poly [-1654, 1868, 552, -508, 850, 819, -839, 193, 791, 118, 321, 635, 48, 208],
    poly [-19903, -5278, 14225, -39211, 38096, -20368, -1187, 1695, -8108, -18358, -5646, -6489, -2693,
      -1],
    poly [-540, -143, 386, -1064, 1034, -553, -32, 46, -220, -498, -153, -176, -73],
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
theorem certificado_99371 :
    haveI : Fact (Nat.Prime 99371) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 99371 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((99371 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((99371 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((99371 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 99371) := ⟨by norm_num⟩
  have hP : poly [-4977, 1] = X - C (4977 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((99371 : ℕ) : ℤ[X]) = poly [99371] := by simp [poly]
  refine ⟨X - C (4977 : ℤ),
    poly [-11760, 15072, -42904, 43138, 2165, 9664, -43544, -30437, -16538, -29593, -28198, -19213,
      13014, 1540, 13118, 32128, 4978, 1],
    poly [-589, 755, -2149, 2161, 108, 484, -2181, -1524, -828, -1482, -1412, -962, 652, 77, 657, 1609,
      249],
    poly [1, 0, 1, 1, 0, 0, 0, 1, 0, -1, -1],
    poly [65203, 6476, 5406, 42323, 34344, 7528, 54922, 36423, 11302, 18325, 31504, -2216, 40245, 42330,
      17293, 18446, 63270, 30355],
    poly [34168, -40644, -64133, -43393, 67776, -9031, -76332, -11909, 63270, 30355],
    poly [-3266, -324, -271, -2120, -1720, -377, -2751, -1824, -566, -918, -1578, 111, -2016, -2120,
      -866, -924, -3169, -1520],
    poly [-1711, 2036, 3212, 2173, -3395, 453, 3823, 596, -3169, -1520],
    poly [-11760, 26832, 29635, 1743, 27254, 35565, -8139, -32127, -4978, -1],
    poly [-589, 1344, 1484, 87, 1365, 1781, -408, -1609, -249],
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
theorem certificado_99409 :
    haveI : Fact (Nat.Prime 99409) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 99409 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((99409 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((99409 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((99409 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 99409) := ⟨by norm_num⟩
  have hP : poly [-338, 1] = X - C (338 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((99409 : ℕ) : ℤ[X]) = poly [99409] := by simp [poly]
  refine ⟨X - C (338 : ℤ),
    poly [-40293, -18354, 24945, 43602, -40164, 10175, -21734, 24935, 38308, -19592, 45529, -33982,
      -17453, 44653, -40455, 15174, 339, 1],
    poly [-137, -62, 85, 148, -137, 35, -74, 85, 130, -67, 155, -116, -59, 152, -138, 52, 1],
    poly [-1, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, -1],
    poly [-35556, -10956, -10295, -18234, -6199, 2954, -2607, -4094, 23842, 40983, 9564, 17412, 16847,
      15963, -14627, -5306, -1455, -10561],
    poly [63853, -39253, -23939, -8600, 19974, -38438, 9886, 4735, 21484, 1240, -3851, 9106, -10561],
    poly [121, 37, 35, 62, 21, -10, 9, 14, -81, -139, -32, -59, -57, -54, 50, 18, 5, 36],
    poly [-217, 134, 81, 29, -68, 131, -34, -16, -73, -4, 13, -31, 36],
    poly [40293, 37177, -21360, 24642, 3014, 5597, -39100, -22468, 14639, -43779, -14835, -338, -1],
    poly [137, 126, -73, 84, 10, 19, -133, -76, 50, -149, -50, -1],
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
theorem certificado_99523 :
    haveI : Fact (Nat.Prime 99523) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 99523 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((99523 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((99523 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((99523 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 99523) := ⟨by norm_num⟩
  have hP : poly [-8213, 1] = X - C (8213 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((99523 : ℕ) : ℤ[X]) = poly [99523] := by simp [poly]
  refine ⟨X - C (8213 : ℤ),
    poly [-22951, 3887, 14978, -15315, -2280, -2133, -12118, 23616, -14393, -39857, 34458, 12849, -12201,
      9620, 23655, -15011, 8214, 1],
    poly [-1894, 321, 1236, -1264, -188, -176, -1000, 1949, -1188, -3289, 2844, 1060, -1007, 794, 1952,
      -1239, 678],
    poly [1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, -1],
    poly [12859, -45450, -9528, -12238, -7573, -27906, -27242, -14797, -20612, -20334, -9428, -6167,
      -4252, -42253, 16368, -24498, -35312, -17064],
    poly [86664, -54073, 9528, 25097, -37877, 5519, 73313, -41557, 40866, 10814, -18248, -17064],
    poly [-1061, 3751, 786, 1010, 625, 2303, 2248, 1221, 1701, 1678, 778, 509, 351, 3487, -1351, 2022,
      2914, 1408],
    poly [-7152, 4463, -787, -2071, 3126, -456, -6050, 3430, -3373, -892, 1506, 1408],
    poly [-22951, 3887, 14978, 7636, -6167, -40062, 30035, 14036, -38666, 23225, -8213, -1],
    poly [-1894, 321, 1236, 630, -509, -3306, 2479, 1158, -3191, 1917, -678],
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
theorem certificado_99713 :
    haveI : Fact (Nat.Prime 99713) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 99713 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((99713 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((99713 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((99713 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 99713) := ⟨by norm_num⟩
  have hP : poly [-1146, 1] = X - C (1146 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((99713 : ℕ) : ℤ[X]) = poly [99713] := by simp [poly]
  refine ⟨X - C (1146 : ℤ),
    poly [45332, 40325, -28852, 28775, -37215, 31465, -31296, 39040, -9624, -23588, 14336, -4599, 27317,
      46835, 10308, 18194, 1147, 1],
    poly [521, 463, -332, 331, -428, 362, -360, 449, -111, -271, 165, -53, 314, 538, 118, 209, 13],
    poly [0, 0, 0, -1, 0, 0, 1, -1, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    poly [19572, 27942, 7067, 36197, 14296, -11913, 14080, 7925, 29411, 22643, 12718, 27762, -9639,
      32354, 26561, -9205, 1727, 5913],
    poly [99713, -99713, 0, 19572, 8370, -20875, 9558, -10699, -16536, -32382, 46179, -11706, -35766,
      10932, 4186, -5913],
    poly [-225, -321, -81, -416, -164, 137, -162, -91, -338, -260, -146, -319, 111, -372, -305, 106, -20,
      -68],
    poly [-1146, 1147, -1, -225, -96, 240, -110, 123, 190, 372, -531, 135, 411, -126, -48, 68],
    poly [0, 0, 0, -45332, 5007, -30536, -12295, 15651, 12195, -14868, -18372, 36528, -7886, 17047, 1146,
      1],
    poly [0, 0, 0, -521, 58, -351, -141, 180, 140, -171, -211, 420, -91, 196, 13],
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
theorem certificado_100169 :
    haveI : Fact (Nat.Prime 100169) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 100169 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((100169 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((100169 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((100169 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 100169) := ⟨by norm_num⟩
  have hP : poly [-10615, 1] = X - C (10615 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((100169 : ℕ) : ℤ[X]) = poly [100169] := by simp [poly]
  refine ⟨X - C (10615 : ℤ),
    poly [-37331, 10405, 36511, -44773, -38260, -11620, 8388, -33197, -23670, 28817, 15205, 22970, 9099,
      -35641, -6675, -1284, 10616, 1],
    poly [-3956, 1103, 3869, -4745, -4054, -1231, 889, -3518, -2508, 3054, 1611, 2434, 964, -3777, -707,
      -136, 1125],
    poly [-1, -1, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0, -1],
    poly [-11430, 15180, 17117, 5246, -3399, 14624, -3936, 1677, -12968, -3061, 11208, -11495, -7279,
      14718, -737, 22098, 37293, 24791],
    poly [88739, -84989, 28547, -9934, -20516, -2052, 26073, -22440, -5723, 15164, 20835, -32330, 25051,
      -10333, 9596, 12502, 24791],
    poly [1211, -1609, -1814, -556, 360, -1550, 417, -178, 1374, 324, -1188, 1218, 771, -1560, 78, -2342,
      -3952, -2627],
    poly [-9404, 9007, -3026, 1053, 2174, 217, -2763, 2378, 606, -1607, -2208, 3426, -2655, 1095, -1017,
      -1325, -2627],
    poly [37331, -10405, 26327, -44991, -25398, 4178, 5785, 32802, 2768, -42200, 26994, -49964, 40865,
      -5224, 11899, -10615, -1],
    poly [3956, -1103, 2790, -4768, -2691, 443, 613, 3476, 293, -4472, 2861, -5295, 4331, -554, 1261,
      -1125],
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
theorem certificado_100207 :
    haveI : Fact (Nat.Prime 100207) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 100207 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((100207 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((100207 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((100207 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 100207) := ⟨by norm_num⟩
  have hP : poly [-9173, 1] = X - C (9173 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((100207 : ℕ) : ℤ[X]) = poly [100207] := by simp [poly]
  refine ⟨X - C (9173 : ℤ),
    poly [35274, -49690, -20510, 10474, 38607, 25086, -20480, -45676, -17855, -48658, -48137, 12197,
      -13053, 15631, 6294, -20777, 9174, 1],
    poly [3229, -4549, -1877, 959, 3534, 2296, -1875, -4181, -1634, -4454, -4406, 1117, -1195, 1431, 576,
      -1902, 840],
    poly [-1, 1, -1, -1, 0, 0, 0, -1, 0, 0, -1],
    poly [-19997, -2892, -18315, -11216, -4049, 9454, -11497, -12548, -16164, -28891, -24053, -27144,
      -20426, -1603, 7477, -18871, -39444, -46536],
    poly [80210, -63105, -52525, 19630, 1750, -1988, -20188, 20573, 7092, -46536],
    poly [1831, 265, 1677, 1027, 371, -865, 1053, 1149, 1480, 2645, 2202, 2485, 1870, 147, -684, 1728,
      3611, 4260],
    poly [-7342, 5777, 4808, -1797, -160, 182, 1848, -1883, -649, 4260],
    poly [-35274, 20031, -49211, 47886, -41572, -18510, -27072, 29951, -9173, -1],
    poly [-3229, 1834, -4505, 4384, -3806, -1694, -2478, 2742, -840],
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
theorem certificado_100511 :
    haveI : Fact (Nat.Prime 100511) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 100511 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((100511 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((100511 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((100511 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 100511) := ⟨by norm_num⟩
  have hP : poly [-3457, 1] = X - C (3457 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((100511 : ℕ) : ℤ[X]) = poly [100511] := by simp [poly]
  refine ⟨X - C (3457 : ℤ),
    poly [1948, 26662, 28559, -48401, 7778, 27565, -21798, 48810, 3474, -31167, 6620, -28404, -48621,
      34294, 37051, -6502, 3458, 1],
    poly [67, 917, 982, -1665, 268, 948, -750, 1679, 119, -1072, 228, -977, -1672, 1180, 1274, -224, 119],
    poly [-1, -1, 0, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0, -1, -1],
    poly [12726, 48695, 37250, 18668, 32444, 33233, 3926, 3714, 14646, 27442, 27562, -5176, 44474, 17856,
      6044, -1199, 36625, 30036],
    poly [113237, -51816, 24524, -30027, 7920, 63260, 8732, -23577, 7195, 55680, -545, -31235, 36625,
      30036],
    poly [-438, -1675, -1281, -642, -1116, -1143, -135, -128, -504, -944, -948, 178, -1530, -614, -208,
      41, -1260, -1033],
    poly [-3895, 1783, -844, 1033, -273, -2176, -300, 811, -248, -1915, 19, 1074, -1260, -1033],
    poly [-1948, -26662, -26611, -25448, 18833, -2117, 1017, 29104, -8336, -44254, -33594, 6503, -3458,
      -1],
    poly [-67, -917, -915, -875, 648, -73, 35, 1001, -287, -1522, -1155, 224, -119],
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
theorem certificado_100549 :
    haveI : Fact (Nat.Prime 100549) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 100549 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((100549 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((100549 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((100549 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 100549) := ⟨by norm_num⟩
  have hP : poly [-1344, 1] = X - C (1344 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((100549 : ℕ) : ℤ[X]) = poly [100549] := by simp [poly]
  refine ⟨X - C (1344 : ℤ),
    poly [44065, 21579, -43226, -2501, 48926, -9016, -35543, -5413, -34867, -30849, -17230, 38516, 3096,
      -36731, -42222, -2201, 1345, 1],
    poly [589, 288, -578, -33, 654, -121, -475, -72, -466, -412, -230, 515, 41, -491, -564, -29, 18],
    poly [-1, 0, 1, -1, 0, 0, -1, -1, -1, 0, 0, -1],
    poly [9488, 3510, -14300, -1595, 9412, 34333, -13903, 126, -12507, 21374, 6661, -4946, -35254, -5052,
      10382, 24608, -21616, 17851],
    poly [110037, -106527, -27298, 28171, 22839, -5594, -37050, 3625, 46224, -39467, 17851],
    poly [-127, -47, 191, 21, -126, -459, 186, -2, 167, -286, -89, 66, 471, 67, -139, -329, 289, -239],
    poly [-1471, 1425, 364, -377, -305, 75, 495, -49, -618, 528, -239],
    poly [-44065, 22486, 8321, -6727, 6803, -37626, -6836, 40020, 3546, -1344, -1],
    poly [-589, 301, 111, -90, 91, -503, -91, 535, 47, -18],
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
theorem certificado_100853 :
    haveI : Fact (Nat.Prime 100853) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 100853 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((100853 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((100853 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((100853 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 100853) := ⟨by norm_num⟩
  have hP : poly [-701, 1] = X - C (701 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((100853 : ℕ) : ℤ[X]) = poly [100853] := by simp [poly]
  refine ⟨X - C (701 : ℤ),
    poly [-29925, 39090, 45231, -40363, 23681, 30822, 17740, 50236, -32443, 25131, -45571, -7834, 20850,
      29667, 46944, -12162, 702, 1],
    poly [-208, 272, 314, -281, 165, 214, 123, 349, -226, 175, -317, -54, 145, 206, 326, -85, 5],
    poly [-1, -1, 0, 0, -1, 0, 0, -1, 0, -1, 1, 0, 0, -1],
    poly [18817, 55243, 84069, 106410, 106298, 82847, 46846, 28667, 23174, 35539, 28507, 76118, 84962,
      103390, 97086, 44996, 35714, 21026],
    poly [119670, -45610, 65252, 51167, 41046, 12863, -30626, -13022, 12642, 31064, 9282, 14688, 21026],
    poly [-131, -384, -584, -739, -738, -575, -325, -199, -161, -247, -198, -529, -590, -718, -674, -312,
      -248, -146],
    poly [-832, 318, -454, -355, -285, -89, 213, 90, -88, -216, -64, -102, -146],
    poly [29925, -39090, 25697, -21400, -49378, -39347, -200, -4748, 17977, 41748, 12864, -701, -1],
    poly [208, -272, 179, -149, -343, -273, -1, -33, 125, 290, 89, -5],
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
theorem certificado_101081 :
    haveI : Fact (Nat.Prime 101081) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 101081 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((101081 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((101081 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((101081 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 101081) := ⟨by norm_num⟩
  have hP : poly [-2374, 1] = X - C (2374 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((101081 : ℕ) : ℤ[X]) = poly [101081] := by simp [poly]
  refine ⟨X - C (2374 : ℤ),
    poly [14945, -50151, 6025, 34491, -41031, -35187, -39783, 13438, 31982, -45077, -14155, -1113,
      -29635, -26922, -39226, -22285, 2375, 1],
    poly [351, -1178, 142, 810, -964, -826, -934, 316, 751, -1059, -332, -26, -696, -632, -921, -523, 56],
    poly [0, -1, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1, 1, 0, -1],
    poly [48474, 52071, 69998, 15633, 11480, 14331, 62318, 66298, 20826, 32303, 42995, 60116, 22782,
      12292, 8711, 54907, 38917, 53983],
    poly [101081, -52607, 3597, 66401, -2294, 17371, 14887, 41540, 72676, -27475, 22853, -37993, -15066,
      53983],
    poly [-1139, -1223, -1644, -367, -270, -337, -1464, -1557, -489, -759, -1010, -1412, -535, -289,
      -205, -1290, -914, -1268],
    poly [-2374, 1236, -85, -1560, 54, -408, -350, -976, -1707, 646, -537, 892, 354, -1268],
    poly [0, -14945, -35985, 29960, 21685, -16639, -4350, 722, 10432, -39338, 19314, 24661, -2374, -1],
    poly [0, -351, -845, 704, 509, -391, -102, 17, 245, -924, 454, 579, -56],
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
theorem certificado_101119 :
    haveI : Fact (Nat.Prime 101119) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 101119 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((101119 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((101119 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((101119 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 101119) := ⟨by norm_num⟩
  have hP : poly [-16521, 1] = X - C (16521 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((101119 : ℕ) : ℤ[X]) = poly [101119] := by simp [poly]
  refine ⟨X - C (16521 : ℤ),
    poly [-34349, -31658, -21265, 17822, -40897, 40865, 4697, 18099, -31410, 3291, -42832, 10733, -46406,
      5873, -35077, 39782, 16522, 1],
    poly [-5612, -5172, -3474, 2912, -6682, 6677, 767, 2957, -5132, 538, -6998, 1754, -7582, 960, -5731,
      6500, 2699],
    poly [0, -1, -1, 0, 0, -1, 0, 1, -1, -1, 0, -1, 0, 0, 0, -1],
    poly [7443, 38218, 30667, 31603, 26425, 35624, 15200, 34846, -12906, 4945, -16672, -22188, 5734,
      -15203, -21888, -3704, -13551, -5099],
    poly [101119, -93676, 38218, 23224, -6615, 3201, 34796, -26219, -23174, 12485, 1586, -18184, 9847,
      -8452, -5099],
    poly [-1216, -6244, -5010, -5163, -4317, -5820, -2483, -5693, 2109, -808, 2724, 3625, -937, 2484,
      3576, 605, 2214, 833],
    poly [-16521, 15306, -6245, -3794, 1081, -523, -5685, 4284, 3786, -2040, -259, 2971, -1609, 1381,
      833],
    poly [0, 34349, 31658, -13084, -49480, -47138, -25734, 10783, 20719, 35758, -40951, -26260, -23260,
      -16521, -1],
    poly [0, 5612, 5172, -2138, -8084, -7701, -4204, 1762, 3385, 5842, -6691, -4290, -3800, -2699],
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
theorem certificado_101347 :
    haveI : Fact (Nat.Prime 101347) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 101347 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((101347 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((101347 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((101347 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 101347) := ⟨by norm_num⟩
  have hP : poly [-2186, 1] = X - C (2186 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((101347 : ℕ) : ℤ[X]) = poly [101347] := by simp [poly]
  refine ⟨X - C (2186 : ℤ),
    poly [-47150, -21858, 47140, -37207, -40630, 10691, 34869, -24834, -7012, 32311, -31604, 30538,
      -17279, -23467, -9654, 17474, 2187, 1],
    poly [-1017, -471, 1017, -803, -876, 231, 752, -536, -151, 697, -682, 659, -373, -506, -208, 377, 47],
    poly [1, 0, -1, 1, 0, 0, 0, 0, 1, 1, -1],
    poly [-13660, -22475, -25678, -40098, -6075, -43288, -15627, -34020, -37691, -24665, -11585, 13920,
      -8832, -7637, -12319, -34853, 8995, -36605],
    poly [115007, -92532, -10457, 19265, -28411, 25996, 20782, -52843, 82205, -36605],
    poly [295, 485, 554, 865, 131, 934, 337, 734, 813, 532, 250, -300, 191, 165, 266, 752, -194, 790],
    poly [-2481, 1997, 225, -416, 613, -561, -448, 1140, -1774, 790],
    poly [-47150, 25292, 14801, 45905, -47129, 1972, 44601, -13100, -2185, -1],
    poly [-1017, 546, 319, 990, -1017, 43, 962, -283, -47],
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
theorem certificado_101537 :
    haveI : Fact (Nat.Prime 101537) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 101537 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((101537 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((101537 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((101537 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 101537) := ⟨by norm_num⟩
  have hP : poly [-739, 1] = X - C (739 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((101537 : ℕ) : ℤ[X]) = poly [101537] := by simp [poly]
  refine ⟨X - C (739 : ℤ),
    poly [-12778, -18566, 42843, 49109, 3364, 22263, -42838, -10775, -11556, -40548, 8189, 43154, -38413,
      -24234, 13020, 39176, 740, 1],
    poly [-93, -135, 312, 357, 24, 162, -312, -78, -84, -295, 60, 314, -280, -176, 95, 285, 5],
    poly [-1, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1, -1],
    poly [-36136, 8332, 19384, 3873, 4539, -14421, -18019, 2998, -7141, -2071, 1783, 2750, -28438,
      -15977, 665, 33663, -1054, 273],
    poly [65401, -57069, 11052, -15511, 36802, -63428, -14650, 392, 33663, -1054, 273],
    poly [263, -61, -141, -28, -33, 105, 131, -22, 52, 15, -13, -20, 207, 116, -5, -245, 8, -2],
    poly [-476, 416, -81, 113, -268, 462, 106, -3, -245, 8, -2],
    poly [12778, 5788, 40128, -6266, 32967, -24687, 24973, -13019, -39176, -740, -1],
    poly [93, 42, 292, -46, 240, -180, 182, -95, -285, -5],
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
theorem certificado_101879 :
    haveI : Fact (Nat.Prime 101879) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 101879 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((101879 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((101879 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((101879 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 101879) := ⟨by norm_num⟩
  have hP : poly [-1800, 1] = X - C (1800 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((101879 : ℕ) : ℤ[X]) = poly [101879] := by simp [poly]
  refine ⟨X - C (1800 : ℤ),
    poly [40695, 815, -15055, 3614, -19638, -31650, -18752, -22254, -37085, -20736, 28458, 978, -26205,
      -16202, 20197, -18327, 1801, 1],
    poly [719, 14, -266, 64, -347, -559, -331, -393, -655, -366, 503, 17, -463, -286, 357, -324, 32],
    poly [1, 1, 1, 0, 0, 0, 1, 1, -1, -1],
    poly [21145, -4596, 5521, -12755, 12365, 7851, 17244, 19117, 2874, 20807, -3351, -25891, 22772, 5989,
      -6642, 32348, -2156, 41746],
    poly [80734, -97283, -5521, 33900, -16961, -2330, -51144, -2156, 41746],
    poly [-374, 81, -98, 225, -219, -139, -305, -338, -51, -368, 59, 457, -403, -106, 117, -572, 38,
      -738],
    poly [-1426, 1720, 97, -599, 300, 41, 904, 38, -738],
    poly [40695, 815, -15055, -37081, -20453, -16595, 18329, -1801, -1],
    poly [719, 14, -266, -655, -361, -293, 324, -32],
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
theorem certificado_101917 :
    haveI : Fact (Nat.Prime 101917) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 101917 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((101917 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((101917 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((101917 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 101917) := ⟨by norm_num⟩
  have hP : poly [-9, 1] = X - C (9 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((101917 : ℕ) : ℤ[X]) = poly [101917] := by simp [poly]
  refine ⟨X - C (9 : ℤ),
    poly [11324, -10066, -46415, 28815, 48498, 50685, 50928, 50955, 50958, 16986, -20761, -13631, -35487,
      7381, 820, 91, 10, 1],
    poly [1, -1, -4, 3, 4, 4, 4, 4, 4, 1, -2, -1, -3, 1],
    poly [1, 0, 1, 1, 0, 1, 0, 0, -1, 0, 0, 0, 1, 1, 1],
    poly [33733, 26157, 2667, 57, -233, 22383, 36220, -7539, -1077, -359, 22369, -9078, -1248, -378,
      33691, -7820, 21540, 2154],
    poly [68184, -94341, -10243, -23547, 31356, -30249, -3361, 44923, -6572, 21918, -31537, 7820, -21540,
      -2154],
    poly [-3, -2, 0, 0, 0, -2, -3, 1, 0, 0, -2, 1, 0, 0, -3, 1, -2],
    poly [-6, 9, 0, 2, -3, 3, 0, -4, 1, -2, 3, -1, 2],
    poly [11324, -21390, -25025, -36753, -38056, -49525, -28151, -14452, -35578, 7371, 819, 91, 10, 1],
    poly [1, -2, -2, -3, -3, -4, -2, -1, -3, 1],
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
    exact igual_de_listas 29 0 (by decide +kernel)
  · rw [← hP, hc, ← poly_produto, ← poly_produto, ← poly_soma]
    exact igual_de_listas 0 0 (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem certificado_102031 :
    haveI : Fact (Nat.Prime 102031) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 102031 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((102031 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((102031 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((102031 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 102031) := ⟨by norm_num⟩
  have hP : poly [-4648, 1] = X - C (4648 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((102031 : ℕ) : ℤ[X]) = poly [102031] := by simp [poly]
  refine ⟨X - C (4648 : ℤ),
    poly [-17232, -48846, 24246, -27105, 7326, 12053, 46979, 10942, -17976, -13548, -29440, -29180,
      -38224, 18936, -7218, -22019, 4649, 1],
    poly [-785, -2225, 1105, -1235, 334, 549, 2140, 498, -819, -617, -1341, -1329, -1741, 863, -329,
      -1003, 212],
    poly [0, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, -1, 1],
    poly [5983, 53729, 34817, 30247, 47939, 47855, 28801, 26031, 43899, 15717, 51053, 39997, 14882,
      48704, 68336, 32164, 23639, 45479],
    poly [102031, -96048, 47746, -18912, -4570, 11709, -47830, -142, 1800, -5807, -75844, 67319, -45479],
    poly [-273, -2448, -1586, -1378, -2184, -2180, -1312, -1186, -2000, -716, -2326, -1822, -678, -2219,
      -3113, -1465, -1077, -2072],
    poly [-4648, 4376, -2176, 862, 208, -533, 2179, 6, -82, 265, 3455, -3067, 2072],
    poly [0, 17232, 31614, 28939, -50680, 50368, -36341, 38166, -15314, 46117, -31315, 4647, 1],
    poly [0, 785, 1440, 1318, -2309, 2295, -1656, 1739, -698, 2101, -1427, 212],
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
theorem certificado_102107 :
    haveI : Fact (Nat.Prime 102107) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 102107 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((102107 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((102107 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((102107 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 102107) := ⟨by norm_num⟩
  have hP : poly [-13803, 1] = X - C (13803 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((102107 : ℕ) : ℤ[X]) = poly [102107] := by simp [poly]
  refine ⟨X - C (13803 : ℤ),
    poly [27267, -20955, 16480, 40014, -21176, 18174, 2080, -18708, 11731, -42786, -1453, 28702, -42119,
      -13496, 29071, 4951, 13804, 1],
    poly [3686, -2833, 2228, 5409, -2863, 2457, 281, -2529, 1586, -5784, -196, 3880, -5694, -1824, 3930,
      669, 1866],
    poly [1, -1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1],
    poly [39908, 22771, 55718, 27255, 12569, -7923, 17937, 44259, 32388, 39755, 8235, 29456, 36818,
      39526, 23851, 14174, 32445, 17141],
    poly [62199, -45062, -50084, 21502, 3360, -27141, -57797, -8547, 2967, -32445, -17141],
    poly [-5395, -3078, -7532, -3684, -1699, 1071, -2425, -5983, -4378, -5374, -1113, -3982, -4977,
      -5343, -3224, -1916, -4386, -2317],
    poly [-8408, 6092, 6770, -2907, -454, 3669, 7813, 1155, -401, 4386, 2317],
    poly [27267, 26618, -16450, 13366, -30839, 35868, -4643, 15268, 4950, 13804, 1],
    poly [3686, 3598, -2224, 1807, -4169, 4849, -628, 2064, 669, 1866],
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
theorem certificado_102259 :
    haveI : Fact (Nat.Prime 102259) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 102259 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((102259 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((102259 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((102259 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 102259) := ⟨by norm_num⟩
  have hP : poly [-505, 1] = X - C (505 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((102259 : ℕ) : ℤ[X]) = poly [102259] := by simp [poly]
  refine ⟨X - C (505 : ℤ),
    poly [29159, -36796, -39964, -4129, -34432, -49274, -31484, -10187, 9497, 23508, 1464, -17614,
      -11172, -3667, -7702, 51013, 506, 1],
    poly [144, -182, -197, -20, -170, -243, -155, -50, 47, 116, 7, -87, -55, -18, -38, 252, 2],
    poly [-1, 0, 0, -1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1],
    poly [-33404, -23143, -13808, 385, -11129, 9300, -21236, 8875, -2000, -3034, -19033, -9750, -13174,
      22458, -19590, -27368, -39128, -3715],
    poly [68855, -91998, 9335, -19211, -1253, 29764, 17061, 8336, 219, -45763, -7778, -11760, 35413,
      3715],
    poly [165, 114, 68, -2, 55, -46, 105, -44, 10, 15, 94, 48, 65, -111, 97, 135, 193, 18],
    poly [-340, 455, -47, 95, 6, -147, -84, -41, -1, 226, 38, 58, -175, -18],
    poly [-29159, -36304, 3168, 37265, -6001, 18010, -24466, 45310, -8010, 4034, 43544, 50507, 505, 1],
    poly [-144, -179, 16, 184, -30, 89, -121, 224, -40, 20, 215, 249, 2],
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
theorem certificado_102563 :
    haveI : Fact (Nat.Prime 102563) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 102563 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((102563 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((102563 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((102563 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 102563) := ⟨by norm_num⟩
  have hP : poly [-6666, 1] = X - C (6666 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((102563 : ℕ) : ℤ[X]) = poly [102563] := by simp [poly]
  refine ⟨X - C (6666 : ℤ),
    poly [45681, 38718, -34905, -5975, -33050, -27192, -39623, 32120, 38239, 375, 43327, -16795, -15727,
      16953, -33662, 32444, 6667, 1],
    poly [2969, 2516, -2269, -388, -2148, -1767, -2575, 2088, 2485, 24, 2816, -1092, -1022, 1102, -2188,
      2109, 433],
    poly [-1, -1, 0, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0, 0, -1],
    poly [19414, 30741, 32389, 31343, 19311, 17986, 33141, 37836, 24774, -1538, 21137, -11801, 29767,
      13341, 18539, 2046, -9019, 20782],
    poly [121977, -71822, 12975, 20016, 17663, -382, 14432, 6772, -2310, -14217, 37275, 11065, -29801,
      20782],
    poly [-1262, -1998, -2105, -2037, -1255, -1169, -2154, -2459, -1610, 100, -1374, 767, -1935, -867,
      -1205, -133, 586, -1351],
    poly [-7928, 4669, -844, -1301, -1148, 25, -938, -440, 150, 924, -2423, -719, 1937, -1351],
    poly [-45681, -38718, -21977, -988, -40573, -760, 51266, 41396, 237, 45281, -36458, -25777, -6666,
      -1],
    poly [-2969, -2516, -1428, -64, -2637, -49, 3332, 2690, 15, 2943, -2370, -1675, -433],
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
theorem certificado_102677 :
    haveI : Fact (Nat.Prime 102677) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 102677 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((102677 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((102677 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((102677 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 102677) := ⟨by norm_num⟩
  have hP : poly [-1708, 1] = X - C (1708 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((102677 : ℕ) : ℤ[X]) = poly [102677] := by simp [poly]
  refine ⟨X - C (1708 : ℤ),
    poly [50557, -21131, 16339, 36199, -50115, -45717, 2979, -34264, -30739, 3108, 15211, -23917, -4703,
      20196, 21473, 44017, 1709, 1],
    poly [841, -352, 272, 602, -834, -760, 50, -570, -511, 52, 253, -398, -78, 336, 357, 732, 28],
    poly [1, 0, 0, 0, -1, -1, 0, 1, 0, -1, -1],
    poly [58784, -816, 37142, 27666, 14916, 10460, 19114, 5533, 19051, 7637, 20495, 6676, 39551, 10775,
      8594, -1687, 23856, 15034],
    poly [43893, -43077, -37958, 9476, 71534, 3640, -30296, -16721, 23856, 15034],
    poly [-978, 14, -618, -460, -248, -174, -318, -92, -317, -127, -341, -111, -658, -179, -143, 28,
      -397, -250],
    poly [-730, 717, 631, -158, -1190, -60, 504, 278, -397, -250],
    poly [50557, 30989, 37470, 19860, -34194, 25529, -19763, -44016, -1709, -1],
    poly [841, 515, 623, 330, -569, 425, -329, -732, -28],
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
theorem certificado_102829 :
    haveI : Fact (Nat.Prime 102829) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 102829 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((102829 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((102829 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((102829 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 102829) := ⟨by norm_num⟩
  have hP : poly [-3462, 1] = X - C (3462 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((102829 : ℕ) : ℤ[X]) = poly [102829] := by simp [poly]
  refine ⟨X - C (3462 : ℤ),
    poly [9475, 3567, 42891, -2542, 32939, -1535, -48118, -16261, 44608, -24135, -3096, 37810, 15961,
      40459, 6962, -42086, 3463, 1],
    poly [319, 120, 1444, -86, 1109, -52, -1620, -547, 1502, -813, -104, 1273, 537, 1362, 234, -1417,
      117],
    poly [-1, 0, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1],
    poly [-9940, -19804, -29965, -2434, 18514, -3816, -49148, -45181, 2908, -5068, -11783, -38309,
      -18535, -22747, -11699, -11577, -36408, -35435],
    poly [92889, -112693, -20101, 7727, 923, -14900, -16657, -17440, -12143, -10726, 23858, -36408,
      -35435],
    poly [335, 667, 1009, 82, -623, 129, 1655, 1521, -98, 171, 397, 1290, 624, 766, 394, 390, 1226, 1193],
    poly [-3127, 3795, 676, -260, -31, 502, 561, 587, 409, 361, -803, 1226, 1193],
    poly [-9475, 5908, -48799, 41866, 33932, 31108, -49861, 36549, 16822, -3500, 42087, -3463, -1],
    poly [-319, 199, -1643, 1410, 1142, 1047, -1679, 1231, 566, -118, 1417, -117],
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
theorem certificado_103171 :
    haveI : Fact (Nat.Prime 103171) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 103171 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((103171 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((103171 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((103171 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 103171) := ⟨by norm_num⟩
  have hP : poly [-568, 1] = X - C (568 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((103171 : ℕ) : ℤ[X]) = poly [103171] := by simp [poly]
  refine ⟨X - C (568 : ℤ),
    poly [-24158, 5225, 23259, -2502, -9268, -39432, -44571, 25351, -17756, 11412, -5974, -7821, 45396,
      47851, 32416, 13680, 569, 1],
    poly [-133, 29, 128, -14, -51, -217, -245, 140, -98, 63, -33, -43, 250, 263, 178, 75, 3],
    poly [0, 1, 0, 0, 0, 1, 0, 1, 1, 0, -1, 0, 0, 0, 0, 1],
    poly [-55727, -30214, -30714, -38707, 2511, -59537, -43662, -22019, -41053, -31278, -45247, -36008,
      881, -25755, -20716, -30334, -40886, -20561],
    poly [103171, -47444, -25513, 500, 7993, 14509, 36535, 40352, 16564, -47197, 5039, -9618, -10552,
      20325, 20561],
    poly [307, 166, 169, 213, -14, 328, 240, 121, 226, 172, 249, 198, -5, 142, 114, 167, 225, 113],
    poly [-568, 262, 140, -3, -44, -80, -201, -222, -91, 260, -28, 53, 58, -112, -113],
    poly [0, -24158, 29383, 18034, -25761, -30924, -781, -11263, 49386, -2456, 15435, 18736, 13111, 568,
      1],
    poly [0, -133, 162, 99, -142, -170, -4, -62, 272, -14, 85, 103, 72, 3],
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
theorem certificado_103399 :
    haveI : Fact (Nat.Prime 103399) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 103399 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((103399 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((103399 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((103399 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 103399) := ⟨by norm_num⟩
  have hP : poly [-1760, 1] = X - C (1760 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((103399 : ℕ) : ℤ[X]) = poly [103399] := by simp [poly]
  refine ⟨X - C (1760 : ℤ),
    poly [25791, 15877, 2124, 47177, -20183, -48421, -1320, 51640, -42329, 46388, -40687, -12243, 4458,
      29201, -42283, -2609, 1761, 1],
    poly [439, 270, 36, 803, -344, -824, -22, 879, -721, 790, -693, -208, 76, 497, -720, -44, 30],
    poly [-1, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1],
    poly [2577, 24727, 33552, 9176, 24672, 4471, -19099, -7950, 810, -1535, -10055, 6390, 16093, -8400,
      26072, -16678, 5035, 14036],
    poly [105976, -78672, 30975, -15551, -6303, 17445, -32369, -14647, 46807, -13435, 12036, -16678,
      5035, 14036],
    poly [-44, -421, -571, -156, -420, -76, 325, 135, -14, 26, 171, -109, -274, 143, -444, 284, -86,
      -239],
    poly [-1804, 1340, -528, 265, 107, -297, 551, 249, -797, 229, -205, 284, -86, -239],
    poly [-25791, -15877, 23667, -31300, -3484, 2113, -30901, -31801, -7068, -27440, 42284, 2609, -1761,
      -1],
    poly [-439, -270, 403, -533, -59, 36, -526, -541, -120, -467, 720, 44, -30],
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
theorem certificado_103703 :
    haveI : Fact (Nat.Prime 103703) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 103703 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((103703 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((103703 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((103703 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 103703) := ⟨by norm_num⟩
  have hP : poly [-6331, 1] = X - C (6331 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((103703 : ℕ) : ℤ[X]) = poly [103703] := by simp [poly]
  refine ⟨X - C (6331 : ℤ),
    poly [-49288, -9754, -37332, 37128, -27562, -15844, 18933, 822, 21278, -47663, 24530, 15778, 51682,
      -3661, -49436, -45168, 6332, 1],
    poly [-3009, -595, -2279, 2267, -1683, -967, 1156, 50, 1299, -2910, 1498, 963, 3155, -224, -3018,
      -2757, 387],
    poly [-1, 0, 0, 1, 0, -1, -1, 0, -1, -1, -1],
    poly [-60109, -21494, -26533, -20080, -21717, -25239, -18753, -53134, -13139, -29906, -32595, -35593,
      -24242, -33839, -61392, 832, -15178, -39931],
    poly [43594, -65088, -5039, 66562, -40252, -58592, -21461, 832, -15178, -39931],
    poly [3670, 1312, 1620, 1226, 1326, 1541, 1145, 3244, 802, 1826, 1990, 2173, 1480, 2066, 3748, -51,
      927, 2438],
    poly [-2661, 3974, 307, -4064, 2458, 3577, 1310, -51, 927, 2438],
    poly [49288, -39534, 27578, -20045, 521, 9992, 49437, 45168, -6332, -1],
    poly [3009, -2414, 1684, -1224, 32, 610, 3018, 2757, -387],
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
theorem certificado_103969 :
    haveI : Fact (Nat.Prime 103969) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 103969 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((103969 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((103969 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((103969 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 103969) := ⟨by norm_num⟩
  have hP : poly [-8845, 1] = X - C (8845 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((103969 : ℕ) : ℤ[X]) = poly [103969] := by simp [poly]
  refine ⟨X - C (8845 : ℤ),
    poly [-41329, -20869, -9406, -41812, -20728, -4281, -15540, 26493, -9671, 26717, -5216, 18313, 26297,
      -573, -17914, -45786, 8846, 1],
    poly [-3516, -1775, -800, -3557, -1763, -364, -1322, 2254, -823, 2273, -444, 1558, 2237, -49, -1524,
      -3895, 753],
    poly [-1, 0, -1, -1, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1],
    poly [-22801, 9686, 9243, -960, 17517, 1145, -6991, -23989, -15798, -13023, -2855, -12281, -7592,
      -14127, 12320, 14286, -36658, -25015],
    poly [81168, -71482, -23244, -517, 50521, -27018, -22663, -5207, -7074, -518, -13609, 25929, -11643,
      -25015],
    poly [1940, -824, -786, 82, -1490, -97, 595, 2041, 1344, 1108, 243, 1045, 646, 1202, -1048, -1215,
      3119, 2128],
    poly [-6905, 6082, 1977, 44, -4298, 2299, 1928, 443, 602, 44, 1158, -2206, 991, 2128],
    poly [41329, -20460, 29866, -50694, 50962, 4496, -40059, 45274, 40382, 37290, -36717, -49338, -8845,
      -1],
    poly [3516, -1741, 2541, -4313, 4336, 382, -3408, 3852, 3435, 3172, -3124, -4197, -752],
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
theorem certificado_104311 :
    haveI : Fact (Nat.Prime 104311) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 104311 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((104311 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((104311 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((104311 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 104311) := ⟨by norm_num⟩
  have hP : poly [-2305, 1] = X - C (2305 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((104311 : ℕ) : ℤ[X]) = poly [104311] := by simp [poly]
  refine ⟨X - C (2305 : ℤ),
    poly [-2670, -38422, -51697, -30207, -22957, 37008, 26173, -9130, 29004, 39248, -43065, -35498,
      36369, -10981, -10549, -4530, 2306, 1],
    poly [-59, -849, -1142, -667, -507, 818, 578, -202, 641, 867, -952, -784, 804, -243, -233, -100, 51],
    poly [-1, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0, 1, 0, -1],
    poly [-49640, -9159, 8915, -29498, -54495, -37445, 6459, -15425, -31545, 8498, 4533, -46606, -44637,
      -2957, -17194, -60780, -24324, -8967],
    poly [54671, -63830, -31566, 2068, -56563, -30522, 77462, -25173, -85266, 50693, 58943, -27489,
      -15357, -8967],
    poly [1097, 202, -197, 652, 1204, 827, -143, 341, 697, -188, -100, 1030, 986, 65, 380, 1343, 537,
      198],
    poly [-1208, 1411, 697, -46, 1250, 674, -1712, 557, 1884, -1121, -1302, 608, 339, 198],
    poly [2670, 35752, 15945, 14262, 8695, -43033, -51699, -32877, 50942, -6404, 8324, 6837, -2305, -1],
    poly [59, 790, 352, 315, 192, -951, -1142, -726, 1126, -142, 184, 151, -51],
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
theorem certificado_104729 :
    haveI : Fact (Nat.Prime 104729) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 104729 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((104729 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((104729 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((104729 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 104729) := ⟨by norm_num⟩
  have hP : poly [-785, 1] = X - C (785 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((104729 : ℕ) : ℤ[X]) = poly [104729] := by simp [poly]
  refine ⟨X - C (785 : ℤ),
    poly [-48162, 16215, 39244, -22897, -17106, -4291, 23742, -17180, -7493, -29894, 11302, 2149, -20276,
      17051, -17989, -11363, 786, 1],
    poly [-361, 122, 294, -172, -128, -32, 178, -129, -56, -224, 85, 16, -152, 128, -135, -85, 6],
    poly [1, -1, 0, 0, -1, 1, -1, -1],
    poly [16154, -6639, 6273, -6785, -8536, -33353, 2370, 5484, 10024, -8648, 18411, -13707, -33493,
      -37654, 11570, -12515, -15881, -8681],
    poly [88575, -65782, -35705, 25970, 4847, -15881, -8681],
    poly [-121, 50, -47, 51, 64, 250, -18, -41, -75, 65, -138, 103, 251, 282, -87, 94, 119, 65],
    poly [-664, 494, 267, -195, -36, 119, 65],
    poly [-48162, 7810, -41348, 19559, 11365, -786, -1],
    poly [-361, 59, -310, 147, 85, -6],
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
theorem certificado_105071 :
    haveI : Fact (Nat.Prime 105071) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 105071 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((105071 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((105071 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((105071 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 105071) := ⟨by norm_num⟩
  have hP : poly [-232, 1] = X - C (232 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((105071 : ℕ) : ℤ[X]) = poly [105071] := by simp [poly]
  refine ⟨X - C (232 : ℤ),
    poly [-29438, 326, 5889, -36206, -21442, 27534, -1240, 32150, 27765, -30677, -13719, 3564, 26736,
      43140, 37776, -51014, 233, 1],
    poly [-65, 1, 13, -80, -47, 61, -3, 71, 61, -68, -30, 8, 59, 95, 83, -113, 1],
    poly [-1, -1, -1, 0, 0, 0, 0, 0, 0, 1, -1],
    poly [-14887, -7252, 5009, 25442, 621, -16243, 1800, 17729, 3758, -26646, 40251, 8384, -18474, -5003,
      16341, 16433, -7117, -13559],
    poly [90184, -112323, 5009, 40329, 7873, -21252, -23642, 17108, 20001, -13559],
    poly [33, 16, -11, -56, -1, 36, -4, -39, -8, 59, -89, -18, 41, 11, -36, -36, 16, 30],
    poly [-199, 249, -12, -89, -17, 47, 52, -38, -44, 30],
    poly [29438, -326, -5889, 6768, 21768, -21645, -34966, 51479, -231, -1],
    poly [65, -1, -13, 15, 48, -48, -77, 114, -1],
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
theorem certificado_105337 :
    haveI : Fact (Nat.Prime 105337) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 105337 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((105337 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((105337 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((105337 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 105337) := ⟨by norm_num⟩
  have hP : poly [-6237, 1] = X - C (6237 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((105337 : ℕ) : ℤ[X]) = poly [105337] := by simp [poly]
  refine ⟨X - C (6237 : ℤ),
    poly [11721, -10672, -42123, 20885, 21824, -29147, 35817, -31391, 3491, -35534, 3237, -7836, 3613,
      9222, -3579, 37054, 6238, 1],
    poly [694, -632, -2494, 1237, 1292, -1726, 2121, -1859, 207, -2104, 192, -464, 214, 546, -212, 2194,
      369],
    poly [-1, -1, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0, -1, -2, 0, -1, -1],
    poly [16247, 34456, 19529, 14139, -11871, 6061, -27596, -20964, -15930, -30724, -14952, -12129,
      -24694, -11455, -24373, 18236, 864, 1655],
    poly [121584, -70881, 19529, 14139, -28118, -12148, -12669, -15574, -6167, -66865, 33632, -29618,
      -21927, 16581, 864, 1655],
    poly [-962, -2040, -1156, -837, 703, -359, 1634, 1241, 943, 1819, 885, 718, 1462, 678, 1443, -1080,
      -51, -98],
    poly [-7199, 4198, -1157, -837, 1665, 719, 750, 922, 365, 3959, -1992, 1754, 1298, -982, -51, -98],
    poly [-11721, 10672, 42123, -20885, -10103, 6754, 38069, -10938, 9169, -37830, 30276, 15357, 9815,
      -37053, -6238, -1],
    poly [-694, 632, 2494, -1237, -598, 400, 2254, -648, 543, -2240, 1793, 909, 581, -2194, -369],
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
theorem certificado_105527 :
    haveI : Fact (Nat.Prime 105527) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 105527 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((105527 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((105527 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((105527 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 105527) := ⟨by norm_num⟩
  have hP : poly [-2355, 1] = X - C (2355 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((105527 : ℕ) : ℤ[X]) = poly [105527] := by simp [poly]
  refine ⟨X - C (2355 : ℤ),
    poly [44048, 37166, -3569, 16130, -42428, 29422, 40879, 13057, 31462, -13564, 17246, -24414, 6263,
      19002, -21411, -44550, 2356, 1],
    poly [983, 829, -80, 360, -947, 657, 912, 291, 702, -303, 385, -545, 140, 424, -478, -994, 53],
    poly [-1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, -1],
    poly [-33766, -6536, -13694, -32786, -13033, -23062, -1692, -6612, -42910, -28183, -48610, -3316,
      -19966, -33416, -16394, -32115, -21681, -48428],
    poly [71761, -78297, -40924, -25628, 39825, -36279, -11735, 32034, -32115, -21681, -48428],
    poly [754, 146, 306, 732, 291, 515, 38, 148, 958, 629, 1085, 74, 446, 746, 366, 717, 484, 1081],
    poly [-1601, 1748, 913, 572, -889, 810, 262, -715, 717, 484, 1081],
    poly [-44048, 6882, -3313, 48662, 648, -50814, -16646, 21412, 44550, -2356, -1],
    poly [-983, 154, -74, 1086, 14, -1134, -371, 478, 994, -53],
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
theorem certificado_105907 :
    haveI : Fact (Nat.Prime 105907) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 105907 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((105907 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((105907 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((105907 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 105907) := ⟨by norm_num⟩
  have hP : poly [-3127, 1] = X - C (3127 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((105907 : ℕ) : ℤ[X]) = poly [105907] := by simp [poly]
  refine ⟨X - C (3127 : ℤ),
    poly [24995, 20363, 40852, -21358, -8982, 7245, 37190, 6684, -26246, -50100, 30127, -600, -16799,
      -5255, 49040, 37813, 3128, 1],
    poly [738, 601, 1206, -631, -265, 214, 1098, 197, -775, -1479, 890, -18, -496, -155, 1448, 1116, 92],
    poly [1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 1, 0, -1, 1],
    poly [7387, -34777, -26154, -37294, -22497, -46268, -28393, 7615, -14659, -29128, -48878, -30155,
      -8507, -21404, -41797, -49153, -40485, -11423],
    poly [98520, -63743, -8623, 11140, -14797, 31158, -60039, -27385, 18521, -12898, 4602, -4601, -20394,
      17639, 11423],
    poly [-218, 1027, 772, 1101, 664, 1366, 838, -225, 433, 860, 1443, 890, 251, 632, 1234, 1451, 1195,
      337],
    poly [-2909, 1883, 254, -329, 437, -920, 1773, 808, -547, 381, -136, 136, 602, -521, -337],
    poly [24995, -4632, 20489, 43697, 12376, -8768, 34577, -50995, 4285, -31598, 43511, -23457, 31558,
      3126, 1],
    poly [738, -137, 605, 1290, 365, -259, 1021, -1506, 127, -933, 1285, -693, 932, 92],
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

end ATK.FermatDezenoveCertE

#print axioms ATK.FermatDezenoveCertE.certificado_82613
#print axioms ATK.FermatDezenoveCertE.certificado_82651
#print axioms ATK.FermatDezenoveCertE.certificado_82727
#print axioms ATK.FermatDezenoveCertE.certificado_83221
#print axioms ATK.FermatDezenoveCertE.certificado_83449
#print axioms ATK.FermatDezenoveCertE.certificado_83563
#print axioms ATK.FermatDezenoveCertE.certificado_83639
#print axioms ATK.FermatDezenoveCertE.certificado_83791
#print axioms ATK.FermatDezenoveCertE.certificado_84247
#print axioms ATK.FermatDezenoveCertE.certificado_84437
#print axioms ATK.FermatDezenoveCertE.certificado_84551
#print axioms ATK.FermatDezenoveCertE.certificado_84589
#print axioms ATK.FermatDezenoveCertE.certificado_85121
#print axioms ATK.FermatDezenoveCertE.certificado_85159
#print axioms ATK.FermatDezenoveCertE.certificado_85577
#print axioms ATK.FermatDezenoveCertE.certificado_85691
#print axioms ATK.FermatDezenoveCertE.certificado_85843
#print axioms ATK.FermatDezenoveCertE.certificado_86413
#print axioms ATK.FermatDezenoveCertE.certificado_86869
#print axioms ATK.FermatDezenoveCertE.certificado_87211
#print axioms ATK.FermatDezenoveCertE.certificado_87553
#print axioms ATK.FermatDezenoveCertE.certificado_87629
#print axioms ATK.FermatDezenoveCertE.certificado_87743
#print axioms ATK.FermatDezenoveCertE.certificado_88237
#print axioms ATK.FermatDezenoveCertE.certificado_88427
#print axioms ATK.FermatDezenoveCertE.certificado_88807
#print axioms ATK.FermatDezenoveCertE.certificado_88883
#print axioms ATK.FermatDezenoveCertE.certificado_88997
#print axioms ATK.FermatDezenoveCertE.certificado_89491
#print axioms ATK.FermatDezenoveCertE.certificado_89567
#print axioms ATK.FermatDezenoveCertE.certificado_89681
#print axioms ATK.FermatDezenoveCertE.certificado_89833
#print axioms ATK.FermatDezenoveCertE.certificado_89909
#print axioms ATK.FermatDezenoveCertE.certificado_90023
#print axioms ATK.FermatDezenoveCertE.certificado_90289
#print axioms ATK.FermatDezenoveCertE.certificado_90403
#print axioms ATK.FermatDezenoveCertE.certificado_90631
#print axioms ATK.FermatDezenoveCertE.certificado_90821
#print axioms ATK.FermatDezenoveCertE.certificado_91163
#print axioms ATK.FermatDezenoveCertE.certificado_91733
#print axioms ATK.FermatDezenoveCertE.certificado_91771
#print axioms ATK.FermatDezenoveCertE.certificado_91961
#print axioms ATK.FermatDezenoveCertE.certificado_92189
#print axioms ATK.FermatDezenoveCertE.certificado_92227
#print axioms ATK.FermatDezenoveCertE.certificado_92569
#print axioms ATK.FermatDezenoveCertE.certificado_92683
#print axioms ATK.FermatDezenoveCertE.certificado_92987
#print axioms ATK.FermatDezenoveCertE.certificado_93139
#print axioms ATK.FermatDezenoveCertE.certificado_93253
#print axioms ATK.FermatDezenoveCertE.certificado_93329
#print axioms ATK.FermatDezenoveCertE.certificado_93481
#print axioms ATK.FermatDezenoveCertE.certificado_93557
#print axioms ATK.FermatDezenoveCertE.certificado_93937
#print axioms ATK.FermatDezenoveCertE.certificado_94583
#print axioms ATK.FermatDezenoveCertE.certificado_94621
#print axioms ATK.FermatDezenoveCertE.certificado_94811
#print axioms ATK.FermatDezenoveCertE.certificado_94849
#print axioms ATK.FermatDezenoveCertE.certificado_95153
#print axioms ATK.FermatDezenoveCertE.certificado_95191
#print axioms ATK.FermatDezenoveCertE.certificado_95267
#print axioms ATK.FermatDezenoveCertE.certificado_95419
#print axioms ATK.FermatDezenoveCertE.certificado_95723
#print axioms ATK.FermatDezenoveCertE.certificado_95989
#print axioms ATK.FermatDezenoveCertE.certificado_96179
#print axioms ATK.FermatDezenoveCertE.certificado_96293
#print axioms ATK.FermatDezenoveCertE.certificado_96331
#print axioms ATK.FermatDezenoveCertE.certificado_96749
#print axioms ATK.FermatDezenoveCertE.certificado_96787
#print axioms ATK.FermatDezenoveCertE.certificado_97547
#print axioms ATK.FermatDezenoveCertE.certificado_97813
#print axioms ATK.FermatDezenoveCertE.certificado_97927
#print axioms ATK.FermatDezenoveCertE.certificado_98041
#print axioms ATK.FermatDezenoveCertE.certificado_98269
#print axioms ATK.FermatDezenoveCertE.certificado_98459
#print axioms ATK.FermatDezenoveCertE.certificado_98573
#print axioms ATK.FermatDezenoveCertE.certificado_98801
#print axioms ATK.FermatDezenoveCertE.certificado_98953
#print axioms ATK.FermatDezenoveCertE.certificado_99181
#print axioms ATK.FermatDezenoveCertE.certificado_99257
#print axioms ATK.FermatDezenoveCertE.certificado_99371
#print axioms ATK.FermatDezenoveCertE.certificado_99409
#print axioms ATK.FermatDezenoveCertE.certificado_99523
#print axioms ATK.FermatDezenoveCertE.certificado_99713
#print axioms ATK.FermatDezenoveCertE.certificado_100169
#print axioms ATK.FermatDezenoveCertE.certificado_100207
#print axioms ATK.FermatDezenoveCertE.certificado_100511
#print axioms ATK.FermatDezenoveCertE.certificado_100549
#print axioms ATK.FermatDezenoveCertE.certificado_100853
#print axioms ATK.FermatDezenoveCertE.certificado_101081
#print axioms ATK.FermatDezenoveCertE.certificado_101119
#print axioms ATK.FermatDezenoveCertE.certificado_101347
#print axioms ATK.FermatDezenoveCertE.certificado_101537
#print axioms ATK.FermatDezenoveCertE.certificado_101879
#print axioms ATK.FermatDezenoveCertE.certificado_101917
#print axioms ATK.FermatDezenoveCertE.certificado_102031
#print axioms ATK.FermatDezenoveCertE.certificado_102107
#print axioms ATK.FermatDezenoveCertE.certificado_102259
#print axioms ATK.FermatDezenoveCertE.certificado_102563
#print axioms ATK.FermatDezenoveCertE.certificado_102677
#print axioms ATK.FermatDezenoveCertE.certificado_102829
#print axioms ATK.FermatDezenoveCertE.certificado_103171
#print axioms ATK.FermatDezenoveCertE.certificado_103399
#print axioms ATK.FermatDezenoveCertE.certificado_103703
#print axioms ATK.FermatDezenoveCertE.certificado_103969
#print axioms ATK.FermatDezenoveCertE.certificado_104311
#print axioms ATK.FermatDezenoveCertE.certificado_104729
#print axioms ATK.FermatDezenoveCertE.certificado_105071
#print axioms ATK.FermatDezenoveCertE.certificado_105337
#print axioms ATK.FermatDezenoveCertE.certificado_105527
#print axioms ATK.FermatDezenoveCertE.certificado_105907
