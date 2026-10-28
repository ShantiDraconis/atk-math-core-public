import ATK.FermatDezenoveBase

/-!
# ATK — Certificados para `𝓞(ℚ(ζ₁₉))` principal (parte D)

Primos 59699 a 82499 da lista de `ATK.FermatDezenove`: para cada um, um gerador do ideal
primo e as identidades polinomiais do critério `pid6`, conferidas por reflexão (`ATK.PolyLista`).
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista
  ATK.FermatDezenoveBase

namespace ATK.FermatDezenoveCertD

set_option maxHeartbeats 4000000 in
theorem certificado_59699 :
    haveI : Fact (Nat.Prime 59699) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 59699 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((59699 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((59699 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((59699 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 59699) := ⟨by norm_num⟩
  have hP : poly [-409, 1] = X - C (409 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((59699 : ℕ) : ℤ[X]) = poly [59699] := by simp [poly]
  refine ⟨X - C (409 : ℤ),
    poly [15910, 11570, -10773, 18511, 1067, -5544, -14172, 9307, -4940, -12273, 3911, -1742, -28905,
      -26636, -8531, -11406, 410, 1],
    poly [109, 79, -74, 127, 7, -38, -97, 64, -34, -84, 27, -12, -198, -182, -58, -78, 3],
    poly [-1, -1, -1, 1, 0, 0, 0, -1, 0, 0, 0, 0, -1],
    poly [8607, 20743, 3549, 19271, 21061, 18584, 26314, 21954, 19316, 21499, 34787, 16866, 17552, 28209,
      20499, 5154, 34893, 1978],
    poly [68306, -38956, 3549, 2057, -11818, 32229, -8679, 7710, 15345, -29739, 32915, 1978],
    poly [-59, -142, -24, -132, -144, -127, -180, -150, -132, -147, -238, -115, -120, -193, -140, -35,
      -239, -13],
    poly [-468, 268, -25, -14, 81, -221, 60, -53, -105, 204, -226, -13],
    poly [-15910, -11570, 10773, 13309, 6163, -27572, 2268, 18105, -2875, 11816, -409, -1],
    poly [-109, -79, 74, 91, 42, -189, 16, 124, -20, 81, -3],
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
theorem certificado_60041 :
    haveI : Fact (Nat.Prime 60041) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 60041 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((60041 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((60041 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((60041 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 60041) := ⟨by norm_num⟩
  have hP : poly [-1289, 1] = X - C (1289 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((60041 : ℕ) : ℤ[X]) = poly [60041] := by simp [poly]
  refine ⟨X - C (1289 : ℤ),
    poly [-21380, 26394, 17022, 479, 12670, 18269, 3135, -836, -2842, -21848, -12640, -20039, -2624,
      15835, 19762, -18337, 1290, 1],
    poly [-459, 567, 365, 10, 272, 392, 67, -18, -61, -469, -271, -430, -56, 340, 424, -394, 28],
    poly [-1, -1, 0, -1, 1, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [21276, 31540, 26005, 28516, 37042, 38446, 35466, 26567, 35876, 26381, 21902, 26277, 19899,
      11370, 5867, 32087, 12870, 13973],
    poly [81317, -28501, 4729, 18252, 25, -5869, 27746, 4400, -12247, 19217, -1103, 13973],
    poly [-457, -677, -558, -612, -795, -825, -761, -570, -770, -566, -470, -564, -427, -244, -126, -689,
      -276, -300],
    poly [-1746, 613, -102, -392, 0, 126, -596, -94, 263, -413, 24, -300],
    poly [21380, -26394, 21639, -12746, -4761, -20685, -21955, 2638, 21941, 19627, -1289, -1],
    poly [459, -567, 465, -274, -102, -444, -471, 57, 471, 421, -28],
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
theorem certificado_60383 :
    haveI : Fact (Nat.Prime 60383) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 60383 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((60383 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((60383 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((60383 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 60383) := ⟨by norm_num⟩
  have hP : poly [-3746, 1] = X - C (3746 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((60383 : ℕ) : ℤ[X]) = poly [60383] := by simp [poly]
  refine ⟨X - C (3746 : ℤ),
    poly [-9591, 26820, -10551, -2324, -17748, -10982, -30001, -24187, 4378, 13622, -29801, 22140, 28521,
      330, 15523, 27407, 3747, 1],
    poly [-595, 1664, -655, -144, -1101, -681, -1861, -1500, 272, 845, -1849, 1374, 1769, 20, 963, 1700,
      232],
    poly [1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1],
    poly [27479, 6773, 15214, -758, 3461, 11280, 7623, 15859, 26371, 7353, 22758, 14912, 1144, 9877,
      16859, 16474, 7302, 16681],
    poly [32904, -39677, -8441, 15972, -31698, -14592, 15922, -705, -26238, 207, -7302, -16681],
    poly [-1705, -420, -944, 47, -215, -700, -473, -984, -1636, -456, -1412, -925, -71, -613, -1046,
      -1022, -453, -1035],
    poly [-2041, 2462, 523, -991, 1967, 905, -988, 44, 1628, -13, 453, 1035],
    poly [-9591, -23972, 23012, 8227, -25015, -26797, -19979, -23330, 11777, 27406, 3747, 1],
    poly [-595, -1487, 1428, 510, -1552, -1662, -1239, -1447, 731, 1700, 232],
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
theorem certificado_60497 :
    haveI : Fact (Nat.Prime 60497) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 60497 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((60497 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((60497 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((60497 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 60497) := ⟨by norm_num⟩
  have hP : poly [-3532, 1] = X - C (3532 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((60497 : ℕ) : ℤ[X]) = poly [60497] := by simp [poly]
  refine ⟨X - C (3532 : ℤ),
    poly [-8547, 20620, 2832, -2243, -1919, -15553, -28129, -12032, -1151, 14867, 16002, -23170, 24641,
      8023, 20933, 16175, 3533, 1],
    poly [-499, 1204, 165, -131, -112, -908, -1642, -702, -67, 868, 934, -1353, 1439, 468, 1222, 944,
      206],
    poly [-1, -1, 1, 0, -1, 0, 0, -1, -1, -1],
    poly [35274, 5104, 40825, 19853, 24780, 29937, 4503, 46323, 5090, 42161, 4712, 17736, 19384, 9039,
      36938, 10517, 25531, 36052],
    poly [95771, -55393, -29723, 44919, -16492, 886, 10517, 25531, 36052],
    poly [-2060, -298, -2384, -1159, -1447, -1748, -263, -2705, -297, -2462, -275, -1036, -1132, -528,
      -2157, -614, -1491, -2105],
    poly [-5592, 3235, 1735, -2623, 963, -52, -614, -1491, -2105],
    poly [8547, -20620, -19926, -8467, -4490, -20932, -16175, -3533, -1],
    poly [499, -1204, -1163, -494, -262, -1222, -944, -206],
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
theorem certificado_60611 :
    haveI : Fact (Nat.Prime 60611) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 60611 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((60611 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((60611 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((60611 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 60611) := ⟨by norm_num⟩
  have hP : poly [-2712, 1] = X - C (2712 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((60611 : ℕ) : ℤ[X]) = poly [60611] := by simp [poly]
  refine ⟨X - C (2712 : ℤ),
    poly [-20673, -25441, 19792, 15093, -28512, -7274, -20184, 22230, -12485, 19171, 26692, -19501,
      19526, -28935, -23969, 23726, 2713, 1],
    poly [-925, -1138, 886, 675, -1276, -325, -903, 995, -559, 858, 1194, -873, 874, -1295, -1072, 1062,
      121],
    poly [-1, 0, -1, 0, 0, 1, 0, -1, 0, -1, 0, 0, -1],
    poly [-16424, -6954, -7174, -9409, -27982, -16926, -20319, -36881, -31568, -23051, -26065, -26379,
      -32324, -14201, 5987, -14835, -8719, -7197],
    poly [44187, -51141, -16644, 7235, -18793, 25245, -31436, -21710, 13625, -6116, -1522, -7197],
    poly [735, 311, 321, 421, 1252, 757, 909, 1650, 1412, 1031, 1166, 1180, 1446, 635, -268, 664, 390,
      322],
    poly [-1977, 2289, 744, -324, 841, -1130, 1407, 971, -610, 274, 68, 322],
    poly [20673, 4768, -24560, 9467, -1628, 23399, -8864, 2254, -12917, -21013, -2712, -1],
    poly [925, 213, -1099, 424, -73, 1047, -397, 101, -578, -940, -121],
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
theorem certificado_60649 :
    haveI : Fact (Nat.Prime 60649) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 60649 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((60649 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((60649 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((60649 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 60649) := ⟨by norm_num⟩
  have hP : poly [-10002, 1] = X - C (10002 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((60649 : ℕ) : ℤ[X]) = poly [60649] := by simp [poly]
  refine ⟨X - C (10002 : ℤ),
    poly [5427, 28512, -13598, -8060, 19118, 22480, -28394, -9444, 9610, 10097, -24945, 13374, 21582,
      -6868, -21072, -20843, 10003, 1],
    poly [895, 4702, -2243, -1329, 3153, 3707, -4683, -1557, 1585, 1665, -4114, 2206, 3559, -1133, -3475,
      -3437, 1650],
    poly [-1, 0, 0, 0, 0, 0, 0, -2, -1, 0, -1],
    poly [-30805, -714, -37463, -14552, -22099, -2605, -24687, -28097, -19972, -22524, -792, -38700,
      -33392, -31633, 4816, -27518, -8457, -45959],
    poly [29844, -30558, -36749, 22911, -7547, 19494, -22082, -65020, 37502, -45959],
    poly [5081, 118, 6179, 2400, 3645, 430, 4072, 4634, 3294, 3715, 131, 6383, 5507, 5217, -794, 4539,
      1395, 7580],
    poly [-4921, 5040, 6060, -3779, 1245, -3215, 3642, 10724, -6185, 7580],
    poly [-5427, -23085, -18539, -5538, -27178, -3362, -9775, -29804, -10002, -1],
    poly [-895, -3807, -3057, -913, -4482, -554, -1612, -4915, -1649],
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
theorem certificado_60763 :
    haveI : Fact (Nat.Prime 60763) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 60763 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((60763 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((60763 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((60763 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 60763) := ⟨by norm_num⟩
  have hP : poly [-614, 1] = X - C (614 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((60763 : ℕ) : ℤ[X]) = poly [60763] := by simp [poly]
  refine ⟨X - C (614 : ℤ),
    poly [-26423, 26281, -3124, 5042, 5847, 9312, -4834, 29384, 18158, -22237, -16464, 8385, -11466,
      -28223, -18453, 13033, 615, 1],
    poly [-267, 266, -32, 51, 59, 94, -49, 297, 183, -225, -166, 85, -116, -285, -186, 132, 6],
    poly [-1, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0, -1],
    poly [-2775, 14341, 11400, 17234, 13285, -1071, 13750, 11498, -6121, 13148, 24758, 3401, -6629,
      18887, 1907, 13359, 9815, 2486],
    poly [57988, -46422, 11400, 17234, 16060, -18187, 19466, -11452, 3544, 7329, 2486],
    poly [28, -145, -115, -174, -134, 11, -139, -116, 62, -133, -250, -34, 67, -191, -19, -135, -99, -25],
    poly [-586, 470, -116, -174, -162, 184, -197, 116, -36, -74, -25],
    poly [26423, -26281, 3124, -5042, 28493, -17371, 9769, -29277, -12418, -614, -1],
    poly [267, -266, 32, -51, 288, -176, 99, -296, -125, -6],
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
theorem certificado_60953 :
    haveI : Fact (Nat.Prime 60953) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 60953 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((60953 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((60953 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((60953 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 60953) := ⟨by norm_num⟩
  have hP : poly [-699, 1] = X - C (699 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((60953 : ℕ) : ℤ[X]) = poly [60953] := by simp [poly]
  refine ⟨X - C (699 : ℤ),
    poly [436, -6801, -21025, 24386, -26038, 15746, 22869, 25844, 8757, 22423, -23512, 11564, 17631,
      -6602, 14117, 1677, 700, 1],
    poly [5, -78, -241, 280, -299, 181, 262, 296, 100, 257, -270, 133, 202, -76, 162, 19, 8],
    poly [1, 2, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1],
    poly [-35910, -44071, -21149, -18849, -46401, -41470, 2922, -29889, -48248, -28567, -15110, -30874,
      -45459, -25511, -6560, -40541, -36404, -11546],
    poly [96863, 19028, 29310, -4073, 8191, 60861, 15069, -12203, 17597, 7786, 54582, 9828, -18298,
      28995, 36404, 11546],
    poly [412, 505, 242, 216, 532, 475, -34, 343, 553, 327, 173, 354, 521, 292, 75, 465, 417, 132],
    poly [-1111, -217, -336, 47, -94, -698, -172, 140, -202, -89, -626, -112, 210, -333, -417, -132],
    poly [436, -6365, -28262, 10162, 18937, -27441, 17924, -12444, 767, -29647, 4492, -7580, 13418, 1676,
      700, 1],
    poly [5, -73, -324, 117, 217, -315, 206, -143, 9, -340, 52, -87, 154, 19, 8],
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
theorem certificado_61333 :
    haveI : Fact (Nat.Prime 61333) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 61333 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((61333 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((61333 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((61333 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 61333) := ⟨by norm_num⟩
  have hP : poly [-1782, 1] = X - C (1782 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((61333 : ℕ) : ℤ[X]) = poly [61333] := by simp [poly]
  refine ⟨X - C (1782 : ℤ),
    poly [-22475, -9512, 2163, 15214, -19300, 18334, -919, -7779, 4883, -1787, -12185, -28505, 12168,
      -30522, 5180, -12009, 1783, 1],
    poly [-653, -276, 63, 442, -561, 533, -27, -226, 142, -52, -354, -828, 354, -887, 151, -349, 52],
    poly [-1, 0, 0, 1, 0, 0, 0, -1, 0, -1, -1, -1],
    poly [-19206, -12402, 4329, 931, -9534, 1646, -9155, -5616, -15492, -14465, 6152, 2412, -27878, 672,
      -3924, -14252, 9353, 1278],
    poly [42127, -54529, 16731, 15808, -17269, -5551, -7403, -5202, -14252, 9353, 1278],
    poly [558, 360, -126, -27, 277, -48, 266, 163, 450, 420, -179, -70, 810, -20, 114, 414, -272, -37],
    poly [-1224, 1585, -487, -459, 502, 161, 215, 151, 414, -272, -37],
    poly [22475, -12963, -11675, 25807, -13856, -25959, -29029, -5179, 12009, -1783, -1],
    poly [653, -377, -339, 750, -403, -754, -843, -150, 349, -52],
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
theorem certificado_61409 :
    haveI : Fact (Nat.Prime 61409) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 61409 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((61409 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((61409 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((61409 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 61409) := ⟨by norm_num⟩
  have hP : poly [-1087, 1] = X - C (1087 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((61409 : ℕ) : ℤ[X]) = poly [61409] := by simp [poly]
  refine ⟨X - C (1087 : ℤ),
    poly [-14180, 27895, 1551, -5422, -14072, 24110, 1717, 14916, 2104, -24234, -7536, -23000, -10981,
      8464, 12154, 15886, 1088, 1],
    poly [-251, 494, 27, -96, -249, 427, 30, 264, 37, -429, -133, -407, -194, 150, 215, 281, 19],
    poly [-1, -1, 0, 0, -1, -1, 1, 0, 0, 0, 0, -1, 0, -1],
    poly [8248, -19257, 29811, -11328, 23152, 11094, -8690, 31911, -16693, 33203, 3985, 19268, 19847,
      1261, 19209, -18456, 27326, 138],
    poly [69657, -80666, 21563, 7929, 1589, 3165, -18527, 56251, -63730, 64853, -45644, 27188, 138],
    poly [-146, 341, -528, 201, -410, -196, 154, -565, 296, -588, -70, -341, -351, -22, -340, 327, -484,
      -2],
    poly [-1233, 1429, -383, -140, -28, -56, 328, -996, 1129, -1149, 809, -482, -2],
    poly [14180, -27895, -15731, -28092, 29803, 3982, 15709, 23177, -11108, 2645, -14799, -1087, -1],
    poly [251, -494, -278, -497, 528, 70, 278, 410, -197, 47, -262, -19],
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
theorem certificado_61561 :
    haveI : Fact (Nat.Prime 61561) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 61561 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((61561 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((61561 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((61561 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 61561) := ⟨by norm_num⟩
  have hP : poly [-4623, 1] = X - C (4623 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((61561 : ℕ) : ℤ[X]) = poly [61561] := by simp [poly]
  refine ⟨X - C (4623 : ℤ),
    poly [-20001, 24937, -22286, 914, -22704, 12792, -14725, -26902, 17798, 12095, 18925, 21896, -23059,
      -8048, -6034, 15086, 4624, 1],
    poly [-1502, 1873, -1674, 69, -1705, 961, -1106, -2020, 1337, 908, 1421, 1644, -1732, -604, -453,
      1133, 347],
    poly [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, -1],
    poly [-20477, -15621, -34023, -19206, -19043, -21613, -20748, -18524, -44903, -11951, -11065, -19747,
      -4848, -26750, -20576, -25768, -17553, -15647],
    poly [82038, -45940, 13546, 3585, -14980, 22884, -3151, 15313, 9338, 13741, -15647],
    poly [1538, 1173, 2555, 1442, 1430, 1623, 1558, 1391, 3372, 897, 831, 1483, 364, 2009, 1545, 1935,
      1318, 1175],
    poly [-6161, 3451, -1018, -269, 1125, -1719, 237, -1150, -701, -1032, 1175],
    poly [-20001, 24937, -2285, -24023, -418, -8123, -8644, -25356, -5838, -4622, -1],
    poly [-1502, 1873, -172, -1804, -31, -610, -649, -1904, -438, -347],
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
theorem certificado_61637 :
    haveI : Fact (Nat.Prime 61637) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 61637 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((61637 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((61637 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((61637 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 61637) := ⟨by norm_num⟩
  have hP : poly [-3397, 1] = X - C (3397 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((61637 : ℕ) : ℤ[X]) = poly [61637] := by simp [poly]
  refine ⟨X - C (3397 : ℤ),
    poly [-16947, 10664, -13823, 6909, 21213, 12780, -26705, 13909, -1012, 29412, -30202, -16593, -30524,
      12166, -15510, 16888, 3398, 1],
    poly [-934, 588, -762, 381, 1169, 704, -1472, 767, -56, 1621, -1665, -914, -1682, 671, -855, 931,
      187],
    poly [-1, 0, -1, -1, -1, -1, 0, 0, -1, 0, -1, -1],
    poly [-16202, 1339, -6585, 12410, -9376, -11088, 6675, 1128, -7456, -17184, 1375, -12863, 4606, 9238,
      -17796, -15173, -3469, -3647],
    poly [45435, -44096, -24126, 20334, -28371, 10698, 24589, -17974, -11526, -3469, -3647],
    poly [893, -74, 363, -684, 517, 611, -368, -62, 411, 947, -76, 709, -254, -509, 981, 836, 191, 201],
    poly [-2504, 2431, 1329, -1121, 1564, -590, -1355, 991, 635, 191, 201],
    poly [16947, -27611, -20203, 30241, -481, 1524, 1325, 18907, -16887, -3398, -1],
    poly [934, -1522, -1113, 1667, -27, 84, 73, 1042, -931, -187],
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
theorem certificado_61751 :
    haveI : Fact (Nat.Prime 61751) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 61751 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((61751 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((61751 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((61751 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 61751) := ⟨by norm_num⟩
  have hP : poly [-133, 1] = X - C (133 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((61751 : ℕ) : ℤ[X]) = poly [61751] := by simp [poly]
  refine ⟨X - C (133 : ℤ),
    poly [26929, -2119, -30195, 10916, 4725, -5536, -22792, -12243, 30087, -12774, 3154, 488, -23211,
      -29425, 23922, 17823, 134, 1],
    poly [58, -5, -65, 24, 10, -12, -49, -26, 65, -28, 7, 1, -50, -63, 52, 38],
    poly [-1, -1, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0, -1],
    poly [14334, 19549, 6588, 16705, 21424, 27031, 17323, -9679, 9154, 16260, 25135, 6630, -2795, 6420,
      32954, 19689, 3339, 7859],
    poly [76085, -42202, -7746, 11490, 34385, 2580, 7389, -2325, 8745, 24209, -4520, 7859],
    poly [-31, -42, -14, -36, -46, -58, -37, 21, -20, -35, -54, -14, 6, -14, -71, -42, -7, -17],
    poly [-164, 92, 16, -25, -74, -5, -16, 5, -19, -52, 10, -17],
    poly [-26929, 2119, -4627, 21787, 28950, 11825, -12447, -26094, -6232, -17690, -133, -1],
    poly [-58, 5, -10, 47, 62, 25, -27, -56, -13, -38],
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
theorem certificado_61979 :
    haveI : Fact (Nat.Prime 61979) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 61979 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((61979 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((61979 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((61979 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 61979) := ⟨by norm_num⟩
  have hP : poly [-1382, 1] = X - C (1382 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((61979 : ℕ) : ℤ[X]) = poly [61979] := by simp [poly]
  refine ⟨X - C (1382 : ℤ),
    poly [-5875, 803, 1346, 30542, -830, 14216, 27412, 18183, 29433, -8410, -17362, 9809, -18470, 8104,
      5253, -10042, 1383, 1],
    poly [-131, 18, 30, 681, -19, 317, 611, 405, 656, -188, -387, 219, -412, 181, 117, -224, 31],
    poly [-1, 0, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1],
    poly [-16214, -11741, -11962, -8778, -20436, -24391, -17891, -9455, -31155, -27852, -22154, -15064,
      -11202, -6266, -13438, -3218, -18369, -28650],
    poly [45765, -57506, -16435, 7657, -11879, -16985, -685, 4260, -12016, -16133, -31698, 4931, 25432,
      -18369, -28650],
    poly [362, 262, 267, 196, 456, 544, 399, 211, 695, 621, 494, 336, 250, 140, 300, 72, 410, 639],
    poly [-1020, 1283, 366, -171, 265, 379, 15, -95, 268, 360, 707, -110, -567, 410, 639],
    poly [5875, -6678, 5332, 26105, 30829, 23612, 11498, -6360, 8337, 22340, -18147, -3870, 10043, -1383,
      -1],
    poly [131, -149, 119, 582, 687, 526, 256, -142, 186, 498, -405, -86, 224, -31],
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
theorem certificado_62017 :
    haveI : Fact (Nat.Prime 62017) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 62017 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((62017 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((62017 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((62017 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 62017) := ⟨by norm_num⟩
  have hP : poly [-4761, 1] = X - C (4761 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((62017 : ℕ) : ℤ[X]) = poly [62017] := by simp [poly]
  refine ⟨X - C (4761 : ℤ),
    poly [21506, -25761, -22306, -29170, -12446, 19810, -17581, 843, 912, 5406, -20072, -10399, 29098,
      -8552, -1604, -26339, 4762, 1],
    poly [1651, -1978, -1712, -2239, -955, 1521, -1350, 65, 70, 415, -1541, -798, 2234, -657, -123,
      -2022, 366],
    poly [-1, 0, 0, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0, -1],
    poly [3478, -1888, -14329, 479, -3074, 2800, 5185, 1434, -13677, -5591, -7439, -17248, 15289, 12378,
      -20826, 660, 11411, -219],
    poly [65495, -67383, -12441, 14808, -3553, 9352, -2981, -16192, 3175, 2645, -10303, -6945, 22234,
      -9856, -10970, 11630, -219],
    poly [-267, 145, 1100, -37, 236, -215, -398, -110, 1050, 429, 571, 1324, -1174, -950, 1599, -51,
      -876, 17],
    poly [-5028, 5174, 954, -1137, 273, -718, 229, 1243, -244, -203, 791, 533, -1707, 757, 842, -893, 17],
    poly [-21506, -14750, -3455, 6864, -16724, 8255, 22641, -21879, -14711, 4543, 15528, -5129, -23969,
      -29496, -30917, -4761, -1],
    poly [-1651, -1132, -265, 527, -1284, 634, 1738, -1680, -1129, 349, 1192, -394, -1840, -2264, -2373,
      -365],
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
theorem certificado_62131 :
    haveI : Fact (Nat.Prime 62131) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 62131 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((62131 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((62131 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((62131 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 62131) := ⟨by norm_num⟩
  have hP : poly [-20113, 1] = X - C (20113 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((62131 : ℕ) : ℤ[X]) = poly [62131] := by simp [poly]
  refine ⟨X - C (20113 : ℤ),
    poly [4958, 27070, -5142, 25284, 27244, 2000, 29918, -21789, -10989, -467, 21497, -22503, -12444,
      6227, 10599, 17942, 20114, 1],
    poly [1605, 8763, -1665, 8185, 8819, 647, 9685, -7054, -3557, -151, 6959, -7285, -4028, 2016, 3431,
      5808, 6511],
    poly [-1, 0, 0, -1, -1, -1, 0, 0, 0, -1, -1, -1],
    poly [-31762, 4280, -3200, -9567, -4529, -6271, -5644, -7760, -16771, -12422, -15307, -1607, -17024,
      -668, -12761, -12082, -23490, -1836],
    poly [30369, -26089, -7480, -38129, 9318, -4942, 22822, -10925, -12082, -23490, -1836],
    poly [10282, -1386, 1036, 3097, 1466, 2030, 1827, 2512, 5429, 4021, 4955, 520, 5511, 216, 4131, 3911,
      7604, 594],
    poly [-9831, 8446, 2421, 12343, -3017, 1600, -7388, 3537, 3911, 7604, 594],
    poly [-4958, -22112, -29919, 26747, -29030, 30386, 13887, -10598, -17942, -20114, -1],
    poly [-1605, -7158, -9685, 8659, -9398, 9837, 4495, -3431, -5808, -6511],
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
theorem certificado_62207 :
    haveI : Fact (Nat.Prime 62207) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 62207 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((62207 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((62207 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((62207 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 62207) := ⟨by norm_num⟩
  have hP : poly [-1428, 1] = X - C (1428 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((62207 : ℕ) : ℤ[X]) = poly [62207] := by simp [poly]
  refine ⟨X - C (1428 : ℤ),
    poly [-15726, 12230, -30790, 22, 19211, 19268, -17455, 6435, -29705, 18014, -18240, -21489, 18891,
      25715, -29343, -12218, 1429, 1],
    poly [-361, 281, -707, 1, 441, 442, -401, 148, -682, 414, -419, -493, 434, 590, -674, -280, 33],
    poly [-1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, -1],
    poly [-12152, -14600, -5715, 2873, 6364, -22951, -14564, 558, -8231, -91, -12457, -21091, -1494,
      7450, 10767, -17764, 2821, -2697],
    poly [50055, -64655, 8885, 8588, 3491, -17163, 10835, 6237, -29529, 2201, 25834, -20585, 5518, -2697],
    poly [279, 335, 131, -66, -146, 527, 334, -13, 189, 2, 286, 484, 34, -171, -247, 408, -65, 62],
    poly [-1149, 1485, -205, -197, -80, 394, -249, -143, 678, -51, -593, 473, -127, 62],
    poly [15726, -27956, -19187, -30812, -19189, -15783, 2472, -4703, 20471, 5721, 17124, 13647, -1428,
      -1],
    poly [361, -642, -440, -707, -440, -362, 57, -108, 470, 131, 393, 313, -33],
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
theorem certificado_62473 :
    haveI : Fact (Nat.Prime 62473) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 62473 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((62473 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((62473 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((62473 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 62473) := ⟨by norm_num⟩
  have hP : poly [-1014, 1] = X - C (1014 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((62473 : ℕ) : ℤ[X]) = poly [62473] := by simp [poly]
  refine ⟨X - C (1014 : ℤ),
    poly [25938, 17831, 13079, 11226, -29870, 3852, 7089, 9495, 13194, 27060, 27813, -11925, -29708,
      -12413, 8490, 29643, 1015, 1],
    poly [421, 289, 212, 182, -485, 63, 115, 154, 214, 439, 451, -194, -482, -201, 138, 481, 16],
    poly [-1, -1, 1, 0, 0, -1, 0, 0, 0, -1, -1],
    poly [2803, 17161, 910, 14017, 22717, 14593, 13476, -1250, 1816, 4037, -4155, 9268, 5523, -2182,
      -1019, 7546, 2564, 31516],
    poly [65276, -45312, -4696, -17502, 38058, -9728, -3583, -23970, 2564, 31516],
    poly [-46, -279, -15, -228, -369, -237, -219, 20, -30, -66, 67, -151, -90, 35, 16, -123, -42, -512],
    poly [-1060, 736, 76, 284, -618, 158, 58, 389, -42, -512],
    poly [-25938, -17831, -23676, -1502, -24276, -20417, -7475, -29642, -1015, -1],
    poly [-421, -289, -384, -24, -394, -331, -121, -481, -16],
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
theorem certificado_62549 :
    haveI : Fact (Nat.Prime 62549) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 62549 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((62549 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((62549 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((62549 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 62549) := ⟨by norm_num⟩
  have hP : poly [-2025, 1] = X - C (2025 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((62549 : ℕ) : ℤ[X]) = poly [62549] := by simp [poly]
  refine ⟨X - C (2025 : ℤ),
    poly [6919, -15657, 2834, -23690, -22900, 15402, 23977, -9996, -9951, -8561, 6575, -12383, -7234,
      19765, -15002, -25583, 2026, 1],
    poly [224, -507, 92, -767, -741, 499, 776, -324, -322, -277, 213, -401, -234, 640, -486, -828, 66],
    poly [-1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1],
    poly [-12520, -17005, -9594, 3877, -3962, 4096, -18047, 6869, -1891, -1432, 12746, -8004, 11291,
      -11248, 1436, -2913, 1749, 20655],
    poly [50029, -54514, 24416, 10545, -28721, 14946, -17877, 31590, -25004, 4662, 18906, -20655],
    poly [405, 550, 310, -126, 128, -133, 584, -223, 61, 46, -413, 259, -366, 364, -47, 94, -57, -669],
    poly [-1620, 1766, -791, -341, 930, -484, 579, -1023, 810, -151, -612, 669],
    poly [-6919, 29495, 28401, 22439, -8823, 5432, 7941, -25757, 10582, -27609, 2025, 1],
    poly [-224, 955, 919, 726, -286, 176, 257, -834, 343, -894, 66],
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
theorem certificado_62701 :
    haveI : Fact (Nat.Prime 62701) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 62701 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((62701 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((62701 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((62701 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 62701) := ⟨by norm_num⟩
  have hP : poly [-1328, 1] = X - C (1328 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((62701 : ℕ) : ℤ[X]) = poly [62701] := by simp [poly]
  refine ⟨X - C (1328 : ℤ),
    poly [-10340, -20735, 27180, 4978, -15341, -2750, 20914, -15329, -4072, 20252, -26000, 11548, 13276,
      11011, -21616, 9285, 1329, 1],
    poly [-219, -439, 576, 105, -325, -58, 443, -325, -86, 429, -551, 245, 281, 233, -458, 197, 28],
    poly [-2, 0, 0, -1, -1, 0, -1],
    poly [-37380, 5085, -1918, 6717, 6393, -20614, -2740, -28128, -10961, -10712, -6793, 10821, -6824,
      3786, -15564, -15673, -14115, -18552],
    poly [-12059, 22229, -14006, -20110, 4437, -18552],
    poly [792, -108, 41, -142, -135, 437, 58, 596, 232, 227, 144, -229, 145, -80, 330, 332, 299, 393],
    poly [256, -471, 297, 426, -94, 393],
    poly [20680, 20790, 29572, -7957, -1328, -1],
    poly [438, 440, 626, -169, -28],
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
theorem certificado_62929 :
    haveI : Fact (Nat.Prime 62929) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 62929 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((62929 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((62929 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((62929 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 62929) := ⟨by norm_num⟩
  have hP : poly [-1071, 1] = X - C (1071 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((62929 : ℕ) : ℤ[X]) = poly [62929] := by simp [poly]
  refine ⟨X - C (1071 : ℤ),
    poly [-26382, 21363, -19840, -1840, 11926, 23279, -3915, 17506, -19021, 20371, -12320, -24337,
      -20529, 7443, -3636, 15391, 1072, 1],
    poly [-449, 364, -338, -31, 203, 396, -67, 298, -324, 347, -210, -414, -349, 127, -62, 262, 18],
    poly [0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    poly [3933, -5582, -6531, 2693, 3818, -18920, 9321, -15977, -2839, -9055, -6593, 3163, 6345, 6583,
      -7401, 19438, 8828, 4000],
    poly [62929, -62929, -3933, 5582, 6531, 1240, -9400, 8456, -1046, 30259, -24356, 8027, 12229, -15438,
      -8828, -4000],
    poly [-67, 95, 111, -46, -65, 322, -159, 272, 48, 154, 112, -54, -108, -112, 126, -331, -150, -68],
    poly [-1071, 1072, 66, -95, -111, -21, 160, -144, 18, -515, 415, -137, -208, 263, 150, 68],
    poly [0, 0, -26382, 21363, -19840, 24542, -9437, 16737, 19288, 12122, -2574, -6877, -4707, 15390,
      1072, 1],
    poly [0, 0, -449, 364, -338, 418, -161, 285, 328, 206, -44, -117, -80, 262, 18],
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
theorem certificado_63347 :
    haveI : Fact (Nat.Prime 63347) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 63347 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((63347 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((63347 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((63347 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 63347) := ⟨by norm_num⟩
  have hP : poly [-690, 1] = X - C (690 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((63347 : ℕ) : ℤ[X]) = poly [63347] := by simp [poly]
  refine ⟨X - C (690 : ℤ),
    poly [7620, -30928, 28140, 10415, 19111, 16553, -2363, 23132, -26866, -10964, -1393, -20016, -10036,
      22111, 24820, -29985, 691, 1],
    poly [83, -337, 307, 113, 208, 180, -26, 252, -293, -119, -15, -218, -109, 241, 270, -327, 8],
    poly [1, 0, -1, 0, 1, 0, 0, -1, -1, 0, 0, 0, -1],
    poly [8174, -7605, -4231, 4771, 14332, 8562, 13144, 2501, 18001, -13191, -8095, -7904, -6343, 8073,
      1851, 29935, 16021, -2177],
    poly [55173, -47568, 4800, -24781, -14361, 30551, 1605, 4045, -28084, 13914, 18198, -2177],
    poly [-89, 83, 46, -52, -156, -93, -143, -27, -196, 144, 88, 86, 69, -88, -20, -326, -174, 24],
    poly [-601, 519, -53, 270, 156, -333, -17, -44, 306, -152, -198, 24],
    poly [7620, 24799, -11899, 20823, 20595, -23381, 31456, 2708, 8542, 30676, -690, -1],
    poly [83, 270, -130, 227, 224, -255, 343, 29, 93, 334, -8],
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
theorem certificado_63499 :
    haveI : Fact (Nat.Prime 63499) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 63499 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((63499 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((63499 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((63499 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 63499) := ⟨by norm_num⟩
  have hP : poly [-1386, 1] = X - C (1386 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((63499 : ℕ) : ℤ[X]) = poly [63499] := by simp [poly]
  refine ⟨X - C (1386 : ℤ),
    poly [6918, 26440, -27882, -15368, 25416, 7761, -27025, 24812, -4701, 16948, -20192, -2626, 12872,
      -15980, 4799, 17413, 1387, 1],
    poly [151, 577, -609, -335, 555, 169, -590, 542, -103, 370, -441, -57, 281, -349, 105, 380, 30],
    poly [-1, -1, 0, -1, -1, -1, 0, 0, -1, 0, -1],
    poly [-1057, 8884, 6463, -8795, 10711, 3578, 10949, 8068, 140, -17092, 6261, -8337, 17217, 15861,
      -1183, -8434, -10226, 4525],
    poly [62442, -54615, 7520, -18736, 13132, 18836, -7500, 6317, -14751, 4525],
    poly [23, -194, -141, 192, -234, -78, -239, -176, -3, 373, -137, 182, -376, -346, 26, 184, 223, -99],
    poly [-1363, 1193, -165, 409, -287, -411, 164, -138, 322, -99],
    poly [-6918, -26440, -28699, -28609, -16239, 4753, 11228, -16027, -1386, -1],
    poly [-151, -577, -626, -624, -354, 104, 245, -350, -30],
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
theorem certificado_63689 :
    haveI : Fact (Nat.Prime 63689) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 63689 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((63689 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((63689 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((63689 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 63689) := ⟨by norm_num⟩
  have hP : poly [-3865, 1] = X - C (3865 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((63689 : ℕ) : ℤ[X]) = poly [63689] := by simp [poly]
  refine ⟨X - C (3865 : ℤ),
    poly [5339, -30599, 11115, 20502, 26552, 15925, 6579, -27303, -8065, 10610, -21930, 29227, 436,
      -29661, -29125, -24824, 3866, 1],
    poly [324, -1857, 675, 1244, 1611, 966, 399, -1657, -489, 644, -1331, 1774, 26, -1800, -1767, -1506,
      235],
    poly [0, 0, 0, 0, -1, -2, -1, -2, -1, -1],
    poly [96, -2936, 7906, 15769, 6263, -1336, -168, 5402, 9935, 10068, 560, 3639, -3380, 21929, -18453,
      -6220, 26707, 11094],
    poly [63689, -63689, 0, 0, 96, -2840, 4874, 26707, 11094],
    poly [-6, 178, -480, -957, -380, 81, 10, -328, -603, -611, -34, -221, 205, -1331, 1120, 377, -1621,
      -673],
    poly [-3865, 3866, -1, 0, -6, 172, -296, -1621, -673],
    poly [0, 0, 0, 0, -5339, 25260, 24823, -3866, -1],
    poly [0, 0, 0, 0, -324, 1533, 1506, -235],
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
theorem certificado_63727 :
    haveI : Fact (Nat.Prime 63727) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 63727 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((63727 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((63727 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((63727 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 63727) := ⟨by norm_num⟩
  have hP : poly [-2839, 1] = X - C (2839 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((63727 : ℕ) : ℤ[X]) = poly [63727] := by simp [poly]
  refine ⟨X - C (2839 : ℤ),
    poly [18631, 25439, 2321, -17014, 28367, 1065, -4287, -23930, 24369, -9060, 2668, 18183, 23890,
      -6591, 13623, -30568, 2840, 1],
    poly [830, 1133, 103, -758, 1264, 47, -191, -1066, 1086, -404, 119, 810, 1064, -294, 607, -1362, 127],
    poly [1, 1, 1, 0, 0, 1, 0, -1, 0, 0, -1],
    poly [30899, -2379, 56, 7195, -1265, 20124, 6596, 6479, 19588, -12327, 23128, -8622, 11614, 3630,
      14716, 10657, -10063, 29818],
    poly [32828, -61348, -56, 23704, -1114, -50967, 33877, 20720, -39881, 29818],
    poly [-1377, 106, -3, -321, 56, -897, -294, -289, -873, 549, -1031, 384, -518, -162, -656, -475, 448,
      -1329],
    poly [-1462, 2734, 2, -1056, 50, 2271, -1510, -923, 1777, -1329],
    poly [18631, 25439, 2321, 28082, 2928, 17375, 19535, -30319, -2839, -1],
    poly [830, 1133, 103, 1251, 130, 774, 870, -1351, -126],
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
theorem certificado_63803 :
    haveI : Fact (Nat.Prime 63803) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 63803 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((63803 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((63803 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((63803 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 63803) := ⟨by norm_num⟩
  have hP : poly [-1431, 1] = X - C (1431 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((63803 : ℕ) : ℤ[X]) = poly [63803] := by simp [poly]
  refine ⟨X - C (1431 : ℤ),
    poly [16274, 19451, -2617, -15072, -24533, -12858, -6474, -28406, -21020, -15932, -1750, -24167,
      28340, -20802, 9304, 7497, 1432, 1],
    poly [365, 436, -59, -338, -550, -288, -145, -637, -471, -357, -39, -542, 636, -467, 209, 168, 32],
    poly [1, 0, -1, -1, 0, 0, 0, 1, 0, 0, -1, -1],
    poly [11645, -4175, 5400, -11224, 3032, -11404, -2586, -13771, -19040, -22566, 661, -26565, 1327,
      -18539, -9056, 4059, -8416, -11412],
    poly [52158, -47983, 2070, 12449, -20501, 7387, -11186, -640, 15471, -8416, -11412],
    poly [-261, 94, -121, 252, -68, 256, 58, 309, 427, 506, -15, 596, -30, 416, 203, -91, 189, 256],
    poly [-1170, 1077, -47, -279, 460, -166, 251, 14, -347, 189, 256],
    poly [16274, 3177, 25461, 31897, 9430, -17605, 28300, -7872, -7496, -1432, -1],
    poly [365, 71, 571, 715, 211, -395, 635, -177, -168, -32],
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
theorem certificado_63841 :
    haveI : Fact (Nat.Prime 63841) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 63841 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((63841 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((63841 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((63841 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 63841) := ⟨by norm_num⟩
  have hP : poly [-2826, 1] = X - C (2826 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((63841 : ℕ) : ℤ[X]) = poly [63841] := by simp [poly]
  refine ⟨X - C (2826 : ℤ),
    poly [-9601, -2398, 13802, -30515, -17767, -7416, -27902, -19867, 4240, -31919, -27120, 18718,
      -10498, 4040, 26952, 8978, 2827, 1],
    poly [-425, -106, 611, -1351, -786, -328, -1235, -879, 188, -1413, -1200, 829, -465, 179, 1193, 397,
      125],
    poly [-1, 1, 0, 0, 1, 1, -1],
    poly [-29335, -8178, -21883, -27287, -8358, -26356, -7567, -29044, -23291, -11203, -17253, -7993,
      -33246, -19181, -4831, 641, -3830, -28749],
    poly [34506, -13349, -34862, 8301, 53668, -28749],
    poly [1299, 362, 969, 1208, 370, 1167, 335, 1286, 1031, 496, 764, 354, 1472, 849, 214, -28, 170,
      1273],
    poly [-1527, 591, 1543, -368, -2376, 1273],
    poly [9601, -16804, -8997, -3324, -2825, -1],
    poly [425, -744, -398, -147, -125],
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
theorem certificado_64373 :
    haveI : Fact (Nat.Prime 64373) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 64373 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((64373 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((64373 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((64373 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 64373) := ⟨by norm_num⟩
  have hP : poly [-2362, 1] = X - C (2362 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((64373 : ℕ) : ℤ[X]) = poly [64373] := by simp [poly]
  refine ⟨X - C (2362 : ℤ),
    poly [-24610, 8847, -9426, 1822, 11202, 11424, 3139, -21420, -20313, -6822, -29246, -14157, 22669,
      3062, 14800, -19044, 2363, 1],
    poly [-903, 325, -346, 67, 411, 419, 115, -786, -745, -250, -1073, -519, 832, 112, 543, -699, 87],
    poly [-1, 0, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1],
    poly [-27608, -3473, -10794, -577, -1145, -10684, 2857, -12154, 3783, -11336, -13986, -20637, -1208,
      -16162, -13661, -4639, 4304, 247],
    poly [36765, -40238, -7321, 10217, -568, -37147, 10068, 1803, -8775, -8943, 4057, 247],
    poly [1013, 127, 396, 21, 42, 392, -105, 446, -139, 416, 513, 757, 44, 593, 501, 170, -158, -9],
    poly [-1349, 1477, 268, -375, 21, 1363, -370, -66, 322, 328, -149, -9],
    poly [24610, 30916, 18273, -11248, -9380, 24388, -562, 9375, 30528, 21407, -2362, -1],
    poly [903, 1134, 670, -413, -344, 895, -21, 344, 1120, 785, -87],
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
theorem certificado_64601 :
    haveI : Fact (Nat.Prime 64601) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 64601 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((64601 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((64601 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((64601 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 64601) := ⟨by norm_num⟩
  have hP : poly [-802, 1] = X - C (802 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((64601 : ℕ) : ℤ[X]) = poly [64601] := by simp [poly]
  refine ⟨X - C (802 : ℤ),
    poly [31495, -19776, -6227, 22224, -26151, -5510, -13942, -22813, -29993, 607, -28675, 28640, -26143,
      934, 8620, -2003, 803, 1],
    poly [391, -246, -77, 276, -325, -68, -173, -283, -372, 8, -356, 356, -325, 12, 107, -25, 10],
    poly [-1, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, -1],
    poly [-24959, -6222, 2098, -14646, -329, 736, -13520, 2250, -21412, -23858, 8520, -9805, -9264, 6605,
      -34214, 291, -16662, -9192],
    poly [39642, -70823, 27057, -33383, -8649, 17480, -2878, -17552, 9483, -16662, -9192],
    poly [310, 77, -26, 182, 4, -9, 168, -28, 266, 296, -106, 122, 115, -82, 425, -4, 207, 114],
    poly [-492, 880, -337, 415, 107, -217, 36, 218, -118, 207, 114],
    poly [-31495, 19776, -26879, -8894, -24901, -30640, -2938, -7817, 2004, -803, -1],
    poly [-391, 246, -334, -110, -309, -380, -36, -97, 25, -10],
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
theorem certificado_65171 :
    haveI : Fact (Nat.Prime 65171) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 65171 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((65171 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((65171 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((65171 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 65171) := ⟨by norm_num⟩
  have hP : poly [-1450, 1] = X - C (1450 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((65171 : ℕ) : ℤ[X]) = poly [65171] := by simp [poly]
  refine ⟨X - C (1450 : ℤ),
    poly [-25574, 1106, -24944, 15489, -19226, 3897, -10155, -23109, 20659, 31566, -29867, 25059, 6849,
      16275, 9270, 18479, 1451, 1],
    poly [-569, 25, -555, 345, -428, 87, -226, -514, 460, 702, -665, 558, 152, 362, 206, 411, 32],
    poly [-1, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1],
    poly [7240, 12189, 15833, 12959, 26171, -1776, 12003, 16552, 22443, 3525, 24097, 6942, 16144, 15611,
      5408, 18570, 15343, -5469],
    poly [72411, -52982, 15833, 5719, 13982, -10369, 3993, -5975, 21345, 4734, -13162, 3227, 20812,
      -5469],
    poly [-161, -271, -352, -288, -582, 40, -267, -368, -499, -78, -536, -154, -359, -347, -120, -413,
      -341, 122],
    poly [-1611, 1180, -353, -127, -311, 231, -89, 133, -475, -105, 293, -72, -463, 122],
    poly [25574, -1106, 24944, 24108, 20332, -3267, -1036, 29933, 7976, -7006, 9209, -17028, -1450, -1],
    poly [569, -25, 555, 536, 452, -73, -23, 666, 177, -156, 205, -379, -32],
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
theorem certificado_65323 :
    haveI : Fact (Nat.Prime 65323) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 65323 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((65323 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((65323 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((65323 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 65323) := ⟨by norm_num⟩
  have hP : poly [-3833, 1] = X - C (3833 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((65323 : ℕ) : ℤ[X]) = poly [65323] := by simp [poly]
  refine ⟨X - C (3833 : ℤ),
    poly [-21371, -2596, 24063, 6346, -11553, 406, 32619, 17545, -21196, 13918, 4588, -21046, 18741,
      -2773, 30130, -1952, 3834, 1],
    poly [-1254, -152, 1412, 372, -678, 24, 1914, 1029, -1244, 817, 269, -1235, 1100, -163, 1768, -115,
      225],
    poly [-1, -1, 0, 0, 0, 0, -1, 0, 1, -1, 0, -1],
    poly [7397, 7024, 5047, 18561, 33272, 22454, 9073, 27816, 23833, 19009, 4999, 37921, 19950, -4374,
      7856, 17863, 9958, -2519],
    poly [72720, -58299, -2350, 11537, 28225, 3893, -16802, 4989, 5386, 12477, -2519],
    poly [-434, -412, -296, -1089, -1952, -1317, -532, -1632, -1398, -1115, -293, -2225, -1170, 257,
      -461, -1048, -584, 148],
    poly [-4267, 3422, 137, -677, -1656, -228, 986, -293, -316, -732, 148],
    poly [21371, 2596, 19889, -8942, -29707, 5940, -22801, 29409, 5785, -3833, -1],
    poly [1254, 152, 1167, -525, -1743, 349, -1338, 1726, 339, -225],
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
theorem certificado_65437 :
    haveI : Fact (Nat.Prime 65437) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 65437 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((65437 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((65437 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((65437 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 65437) := ⟨by norm_num⟩
  have hP : poly [-2349, 1] = X - C (2349 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((65437 : ℕ) : ℤ[X]) = poly [65437] := by simp [poly]
  refine ⟨X - C (2349 : ℤ),
    poly [16408, 1762, 28666, 25836, 206, -26353, 8736, -16850, 19883, -20411, 13530, -21528, 18906,
      -21860, -30346, 23443, 2350, 1],
    poly [589, 63, 1029, 927, 7, -946, 314, -605, 714, -733, 486, -773, 679, -785, -1089, 842, 84],
    poly [-1, 0, 0, 0, 0, 0, 0, 1, -1, -1, -1],
    poly [-7355, 7657, -4371, -6939, -12623, 2724, -9276, -13209, -1427, -19585, -17782, -23882, 11745,
      -7350, -8946, 3422, -10585, 1527],
    poly [58082, -50425, -12028, -2568, -5684, 15347, -12000, 3422, -10585, 1527],
    poly [264, -275, 157, 249, 453, -98, 333, 474, 51, 703, 638, 857, -422, 264, 321, -123, 380, -55],
    poly [-2085, 1811, 431, 92, 204, -551, 431, -123, 380, -55],
    poly [-16408, 14646, -26904, 2830, 25630, 26559, 30348, -23443, -2350, -1],
    poly [-589, 526, -966, 102, 920, 953, 1089, -842, -84],
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
theorem certificado_65551 :
    haveI : Fact (Nat.Prime 65551) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 65551 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((65551 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((65551 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((65551 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 65551) := ⟨by norm_num⟩
  have hP : poly [-14803, 1] = X - C (14803 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((65551 : ℕ) : ℤ[X]) = poly [65551] := by simp [poly]
  refine ⟨X - C (14803 : ℤ),
    poly [1820, 32521, 6153, 12581, -18301, 9732, -11650, 31847, -12636, -9061, -26012, 15838, 19100,
      -18150, -2884, 6620, 14804, 1],
    poly [411, 7344, 1389, 2841, -4133, 2198, -2631, 7192, -2854, -2046, -5874, 3577, 4313, -4099, -651,
      1495, 3343],
    poly [1, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1],
    poly [12657, -14682, -10911, 8724, -1681, -8820, 5062, -23043, -1723, 2069, -16516, -16132, 6049,
      16045, -19048, 3538, -2505, -16813],
    poly [52894, -38212, -3771, -19635, 10405, 7139, -26539, 55444, -25091, -10770, 14308, -16813],
    poly [-2858, 3316, 2464, -1970, 380, 1992, -1143, 5204, 389, -467, 3730, 3643, -1366, -3623, 4302,
      -799, 566, 3797],
    poly [-11945, 8630, 851, 4434, -2350, -1612, 5993, -12521, 5667, 2432, -3231, 3797],
    poly [1820, 30701, -26368, 6428, -30882, 28033, -19562, 8647, -5300, 8183, -14803, -1],
    poly [411, 6933, -5955, 1452, -6974, 6331, -4418, 1953, -1197, 1848, -3343],
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
theorem certificado_66083 :
    haveI : Fact (Nat.Prime 66083) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 66083 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((66083 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((66083 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((66083 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 66083) := ⟨by norm_num⟩
  have hP : poly [-77, 1] = X - C (77 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((66083 : ℕ) : ℤ[X]) = poly [66083] := by simp [poly]
  refine ⟨X - C (77 : ℤ),
    poly [-7724, 5049, 1782, 11180, -23885, 8272, -17057, 13510, -1541, -15468, -4492, -10357, 21321,
      -3156, -41, 6007, 78, 1],
    poly [-9, 6, 2, 13, -28, 10, -20, 16, -2, -18, -5, -12, 25, -4, 0, 7],
    poly [-1, 0, 1, 0, 0, 1, 0, -1, -1, 0, 0, -1],
    poly [-77, -78, -7802, 4971, 1704, 11102, -23963, 8194, -17135, 13432, -1619, -15546, -4570, -10435,
      21243, -3234, -119, 5929],
    poly [66006, -66084, -7647, 12774, 4457, -3298, -31797, 30406, -3115, -6048, 5929],
    poly [0, 0, 9, -6, -2, -13, 28, -10, 20, -16, 2, 18, 5, 12, -25, 4, 0, -7],
    poly [-77, 78, 8, -15, -5, 4, 37, -36, 4, 7, -7],
    poly [7724, -12773, -4457, 3375, 31798, -30483, 3037, 6047, -5929, -77, -1],
    poly [9, -15, -5, 4, 37, -36, 4, 7, -7],
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
theorem certificado_66463 :
    haveI : Fact (Nat.Prime 66463) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 66463 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((66463 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((66463 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((66463 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 66463) := ⟨by norm_num⟩
  have hP : poly [-1249, 1] = X - C (1249 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((66463 : ℕ) : ℤ[X]) = poly [66463] := by simp [poly]
  refine ⟨X - C (1249 : ℤ),
    poly [5747, 9849, 30020, 18755, 23748, -25470, 30311, 7953, 26400, 19976, -14724, 17176, -7170, 4677,
      -21920, 32602, 1250, 1],
    poly [108, 185, 564, 352, 446, -479, 570, 149, 496, 375, -277, 323, -135, 88, -412, 613, 23],
    poly [-1, 0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, -1],
    poly [-5217, 2069, 1117, 22295, 6082, 1067, -22670, 11793, 12672, 12247, -4409, 10903, 9851, 7562,
      2771, 20966, 600, 2659],
    poly [61246, -59177, -952, 15961, -3710, -13253, -1607, 2289, 4791, -18195, 20366, -2059, 2659],
    poly [98, -39, -21, -419, -114, -20, 426, -222, -238, -230, 83, -205, -185, -142, -52, -394, -11,
      -50],
    poly [-1151, 1113, 17, -300, 70, 249, 30, -43, -90, 342, -383, 39, -50],
    poly [-5747, -4102, -20171, 5518, -3348, 33149, -24345, 11847, -26597, -11941, -31352, -1249, -1],
    poly [-108, -77, -379, 104, -63, 623, -458, 223, -500, -224, -589, -23],
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
theorem certificado_66653 :
    haveI : Fact (Nat.Prime 66653) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 66653 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((66653 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((66653 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((66653 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 66653) := ⟨by norm_num⟩
  have hP : poly [-8539, 1] = X - C (8539 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((66653 : ℕ) : ℤ[X]) = poly [66653] := by simp [poly]
  refine ⟨X - C (8539 : ℤ),
    poly [1366, 1694, 20217, -20714, -30835, -2720, -15682, 27365, 13109, 24129, -32266, 19089, -12885,
      5884, 28835, 4679, 8540, 1],
    poly [175, 217, 2590, -2654, -3950, -348, -2009, 3506, 1679, 3091, -4134, 2446, -1651, 754, 3694,
      599, 1094],
    poly [-1, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, -1],
    poly [7748, 21807, 13277, 982, -604, 32976, 19960, 3465, 6921, 18388, 17921, -10687, 9183, -5466,
      9168, 15024, 14088, 26257],
    poly [74401, -52594, -8530, -12295, -1586, 33580, 2480, 11623, -5856, 936, -12169, 26257],
    poly [-993, -2794, -1701, -126, 77, -4225, -2557, -444, -887, -2356, -2296, 1369, -1177, 700, -1175,
      -1925, -1805, -3364],
    poly [-9532, 6739, 1092, 1575, 203, -4302, -318, -1489, 750, -120, 1559, -3364],
    poly [-1366, -328, -18523, -25722, 10121, -28115, 10230, 22950, -24156, 3861, -8539, -1],
    poly [-175, -42, -2373, -3295, 1297, -3602, 1311, 2940, -3095, 495, -1094],
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
theorem certificado_66919 :
    haveI : Fact (Nat.Prime 66919) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 66919 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((66919 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((66919 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((66919 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 66919) := ⟨by norm_num⟩
  have hP : poly [-873, 1] = X - C (873 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((66919 : ℕ) : ℤ[X]) = poly [66919] := by simp [poly]
  refine ⟨X - C (873 : ℤ),
    poly [-26369, 4799, -25367, -6468, -4530, -27524, -3251, -28749, 16601, 8221, 2539, 5522, -32495,
      10771, -10106, 26894, 874, 1],
    poly [-344, 63, -331, -84, -59, -359, -42, -375, 217, 107, 33, 72, -424, 141, -132, 351, 11],
    poly [-1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, -1, 0, -1, 0, -1],
    poly [-20101, 2029, 14319, 612, -9752, -872, 6267, 11411, 8734, 18466, 7209, 24060, 25919, -5737,
      4805, 5277, 4511, 15395],
    poly [46818, -44789, 12290, -13707, -30465, 31010, -672, 13567, -751, 4905, 5619, -11356, 16161,
      -10884, 15395],
    poly [262, -27, -187, -8, 127, 11, -82, -149, -114, -241, -94, -314, -338, 75, -63, -69, -59, -201],
    poly [-611, 585, -161, 179, 397, -405, 9, -177, 10, -64, -73, 148, -211, 142, -201],
    poly [26369, -31168, 30166, -18899, 24431, -8174, 32262, -24569, -17122, 12475, 20021, -30792,
      -26021, -873, -1],
    poly [344, -407, 394, -247, 319, -107, 421, -321, -223, 163, 261, -402, -339, -11],
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
theorem certificado_67033 :
    haveI : Fact (Nat.Prime 67033) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 67033 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((67033 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((67033 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((67033 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 67033) := ⟨by norm_num⟩
  have hP : poly [-3974, 1] = X - C (3974 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((67033 : ℕ) : ℤ[X]) = poly [67033] := by simp [poly]
  refine ⟨X - C (3974 : ℤ),
    poly [-19280, 27338, -23119, 15850, 32306, -30236, 16641, -738, 30109, -23540, 9963, 17815, -23172,
      -495, 22839, -23137, 3975, 1],
    poly [-1143, 1621, -1371, 940, 1915, -1793, 987, -44, 1785, -1396, 591, 1056, -1374, -29, 1354,
      -1372, 236],
    poly [1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, -1, 0, -1],
    poly [14946, -1041, -12667, -3595, 15468, 8169, -14284, -9010, -15351, -1639, -12431, -11759, 7032,
      -15853, -27447, -4712, -2699, -4166],
    poly [52087, -51046, 11626, 5874, -35050, 10619, 15538, 2163, 8114, -17102, -6179, 1467, -4166],
    poly [-886, 62, 751, 213, -917, -484, 847, 534, 910, 97, 737, 697, -417, 940, 1627, 279, 160, 247],
    poly [-3088, 3027, -690, -348, 2078, -630, -921, -128, -481, 1014, 366, -87, 247],
    poly [-19280, -20415, 16576, -8784, -30162, 7195, 28323, 16622, -12613, 17084, 27111, -3974, -1],
    poly [-1143, -1210, 983, -521, -1788, 427, 1679, 985, -748, 1013, 1607, -236],
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
theorem certificado_67261 :
    haveI : Fact (Nat.Prime 67261) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 67261 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((67261 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((67261 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((67261 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 67261) := ⟨by norm_num⟩
  have hP : poly [-7784, 1] = X - C (7784 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((67261 : ℕ) : ℤ[X]) = poly [67261] := by simp [poly]
  refine ⟨X - C (7784 : ℤ),
    poly [-9289, 1053, 19183, 7209, 30417, -29237, 8136, 31912, 2052, 16876, -33516, 11756, 27592, 28389,
      33012, -3720, 7785, 1],
    poly [-1075, 122, 2220, 834, 3520, -3384, 942, 3693, 237, 1953, -3879, 1361, 3193, 3285, 3820, -431,
      901],
    poly [1, 0, 1, 0, -1, -1, 0, 0, 0, 0, 1, 1],
    poly [38163, 1539, 7341, 26058, 18586, 24530, 17065, 20771, 8173, 19491, 23450, 6834, 24805, 15622,
      1683, -263, 16552, 31045],
    poly [29098, -30637, -43965, 17907, 39833, -23122, -15885, 14869, 31308, -16552, -31045],
    poly [-4417, -178, -850, -3016, -2151, -2839, -1975, -2404, -946, -2256, -2714, -791, -2871, -1808,
      -195, 30, -1916, -3593],
    poly [-3367, 3546, 5088, -2073, -4610, 2676, 1838, -1721, -3623, 1916, 3593],
    poly [-9289, 10342, 8841, -1632, -16634, -5420, 32109, 25227, -3721, 7785, 1],
    poly [-1075, 1197, 1023, -189, -1925, -627, 3716, 2919, -431, 901],
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
theorem certificado_67489 :
    haveI : Fact (Nat.Prime 67489) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 67489 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((67489 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((67489 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((67489 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 67489) := ⟨by norm_num⟩
  have hP : poly [-3332, 1] = X - C (3332 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((67489 : ℕ) : ℤ[X]) = poly [67489] := by simp [poly]
  refine ⟨X - C (3332 : ℤ),
    poly [15819, 24270, 33610, 17571, -20128, 7549, -13771, 4776, -15534, 20716, -31490, 19820, -30356,
      33148, -30352, -30128, 3333, 1],
    poly [781, 1198, 1659, 867, -994, 373, -680, 236, -767, 1023, -1555, 979, -1499, 1637, -1499, -1487,
      165],
    poly [-1, -1, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0, -1, -1],
    poly [-15818, 27401, 9610, 16309, 2558, 12580, 6223, 8996, 10759, -5181, 10775, 11671, 10537, -2791,
      -2795, -7008, 26796, -3333],
    poly [51671, -40088, 9610, 32127, -40661, 30371, 15342, -20472, 34346, -32924, -3675, 26796, -3333],
    poly [781, -1353, -474, -805, -126, -621, -307, -444, -531, 256, -532, -576, -520, 138, 138, 346,
      -1323, 165],
    poly [-2551, 1980, -475, -1586, 2008, -1500, -757, 1011, -1696, 1626, 181, -1323, 165],
    poly [-15819, -24270, -33610, -1752, 28579, 1791, 13551, 33465, 881, 33684, 30129, -3333, -1],
    poly [-781, -1198, -1659, -86, 1411, 88, 669, 1652, 43, 1663, 1487, -165],
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
theorem certificado_67679 :
    haveI : Fact (Nat.Prime 67679) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 67679 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((67679 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((67679 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((67679 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 67679) := ⟨by norm_num⟩
  have hP : poly [-73, 1] = X - C (73 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((67679 : ℕ) : ℤ[X]) = poly [67679] := by simp [poly]
  refine ⟨X - C (73 : ℤ),
    poly [-8344, 11011, 27037, 14277, 3904, 13033, -21145, -3071, 17573, 28054, -27429, 14458, 25230,
      29086, -11654, 5403, 74, 1],
    poly [-9, 12, 29, 15, 4, 14, -23, -3, 19, 30, -30, 16, 27, 31, -13, 6],
    poly [-1, 0, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1],
    poly [-29529, -266, -15626, 4560, -16487, -5650, -866, -13780, -23228, -11305, -13923, 1802, -18379,
      -23291, 4455, -12780, -3745, -10111],
    poly [38150, -38416, -15360, 20186, -21047, 10837, -24745, -13180, 4455, -12780, -3745, -10111],
    poly [32, 0, 17, -5, 18, 6, 1, 15, 25, 12, 15, -2, 20, 25, -5, 14, 4, 11],
    poly [-41, 42, 16, -22, 23, -12, 27, 14, -5, 14, 4, 11],
    poly [8344, -19355, -16026, 12760, 10373, -9129, -25157, -29085, 11654, -5403, -74, -1],
    poly [9, -21, -17, 14, 11, -10, -27, -31, 13, -6],
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
theorem certificado_68059 :
    haveI : Fact (Nat.Prime 68059) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 68059 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((68059 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((68059 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((68059 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 68059) := ⟨by norm_num⟩
  have hP : poly [-7499, 1] = X - C (7499 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((68059 : ℕ) : ℤ[X]) = poly [68059] := by simp [poly]
  refine ⟨X - C (7499 : ℤ),
    poly [-19531, -8797, 15237, 20368, -16978, -33401, -28947, -17275, 18966, 28337, -25372, -22484,
      30192, -2755, 7233, 25767, 7500, 1],
    poly [-2152, -969, 1679, 2244, -1871, -3680, -3189, -1903, 2090, 3122, -2796, -2477, 3327, -304, 797,
      2839, 826],
    poly [-1, -1, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1, -1, -1, -1],
    poly [-21955, 14699, -8648, -3605, 9855, -14802, -5185, -18398, -1773, -8387, -10439, -1300, -26248,
      16804, -3529, -3087, -13878, 5824],
    poly [46104, -53360, 13307, -40259, 55157, -34544, -9997, -12091, -6546, 10980, -3529, -3087, -13878,
      5824],
    poly [2419, -1620, 953, 397, -1086, 1631, 571, 2027, 195, 924, 1150, 143, 2892, -1852, 389, 340,
      1529, -642],
    poly [-5080, 5880, -1467, 4436, -6078, 3807, 1101, 1332, 721, -1210, 389, 340, 1529, -642],
    poly [19531, 8797, 33291, -9634, 21481, 29735, 6838, -27308, -22693, 2756, -7233, -25767, -7500, -1],
    poly [2152, 969, 3668, -1062, 2367, 3276, 753, -3009, -2500, 304, -797, -2839, -826],
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
theorem certificado_68477 :
    haveI : Fact (Nat.Prime 68477) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 68477 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((68477 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((68477 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((68477 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 68477) := ⟨by norm_num⟩
  have hP : poly [-2166, 1] = X - C (2166 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((68477 : ℕ) : ℤ[X]) = poly [68477] := by simp [poly]
  refine ⟨X - C (2166 : ℤ),
    poly [-19190, -5984, -16221, -3738, 12486, -13873, -3484, 24879, -12824, -5412, 4139, -25100, -20972,
      -32541, 29260, -31190, 2167, 1],
    poly [-607, -189, -513, -118, 395, -439, -110, 787, -406, -171, 131, -794, -663, -1029, 926, -987,
      69],
    poly [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1],
    poly [-15865, -16473, -42903, -25464, -18153, -29436, -25932, -28586, -11958, -23458, -7087, -20073,
      -33610, -6902, -30727, -11548, -30413, -11864],
    poly [84342, -52004, 42903, 9599, 17545, -12859, 42763, -6398, 17506, 7843, -5276, 31043, -18865,
      18549, 11864],
    poly [502, 521, 1357, 805, 574, 931, 820, 904, 378, 742, 224, 635, 1063, 218, 972, 365, 962, 375],
    poly [-2668, 1646, -1358, -303, -555, 407, -1353, 203, -554, -248, 167, -982, 597, -587, -375],
    poly [-19190, -5984, -16221, 15452, -720, 15554, -29173, -30395, -12154, -21788, 8842, -8026, -33357,
      2166, 1],
    poly [-607, -189, -513, 489, -23, 492, -923, -961, -384, -689, 280, -254, -1055, 69],
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
theorem certificado_68743 :
    haveI : Fact (Nat.Prime 68743) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 68743 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((68743 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((68743 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((68743 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 68743) := ⟨by norm_num⟩
  have hP : poly [-14992, 1] = X - C (14992 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((68743 : ℕ) : ℤ[X]) = poly [68743] := by simp [poly]
  refine ⟨X - C (14992 : ℤ),
    poly [29158, -15125, -11180, -32451, -11979, 29657, 8549, 19534, -7459, 15828, -11907, -7429, -33996,
      10466, 11707, -14553, 14993, 1],
    poly [6359, -3299, -2438, -7077, -2612, 6468, 1864, 4260, -1627, 3452, -2597, -1620, -7414, 2283,
      2553, -3174, 3270],
    poly [-1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, -1],
    poly [-32345, -2052, -6539, 7478, -23073, 11191, -16502, 714, -22028, -5770, -4806, 2769, 2178,
      -19937, -107, -5874, 2934, 3118],
    poly [36398, -38450, 27858, -16276, 6281, 22299, -22948, 5767, -8808, -184, 3118],
    poly [7054, 447, 1426, -1631, 5032, -2441, 3599, -156, 4804, 1258, 1048, -604, -475, 4348, 23, 1281,
      -640, -680],
    poly [-7938, 8386, -6076, 3550, -1370, -4863, 5005, -1258, 1921, 40, -680],
    poly [-29158, -24460, 25213, -23012, 12631, -9289, 1242, -26260, 29546, -14992, -1],
    poly [-6359, -5334, 5499, -5019, 2755, -2026, 271, -5727, 6444, -3270],
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
theorem certificado_68819 :
    haveI : Fact (Nat.Prime 68819) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 68819 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((68819 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((68819 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((68819 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 68819) := ⟨by norm_num⟩
  have hP : poly [-7040, 1] = X - C (7040 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((68819 : ℕ) : ℤ[X]) = poly [68819] := by simp [poly]
  refine ⟨X - C (7040 : ℤ),
    poly [-16628, 7730, 32739, 9174, 25740, 2731, -26100, 34005, 1608, 19424, -1923, 8563, -17575, 20565,
      -23419, 18961, 7041, 1],
    poly [-1701, 791, 3349, 938, 2633, 279, -2670, 3479, 164, 1987, -197, 876, -1798, 2104, -2396, 1940,
      720],
    poly [-1, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1, -1],
    poly [-16783, -23462, -8008, -9042, 2356, 774, -15864, -20148, -26835, -6767, -19394, -14381, 1974,
      -19774, -1673, -32551, -13376, -9903],
    poly [52036, -75498, 15454, -17817, -12064, 7193, -19001, -599, 1800, -22648, -13376, -9903],
    poly [1717, 2400, 819, 925, -241, -79, 1623, 2061, 2745, 692, 1984, 1471, -202, 2023, 171, 3330,
      1368, 1013],
    poly [-5323, 7724, -1582, 1823, 1234, -736, 1944, 61, -184, 2317, 1368, 1013],
    poly [16628, -24358, -25009, -28626, -24296, -26358, -24804, -8645, 30459, -18960, -7041, -1],
    poly [1701, -2492, -2558, -2928, -2485, -2696, -2537, -884, 3116, -1940, -720],
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
theorem certificado_69313 :
    haveI : Fact (Nat.Prime 69313) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 69313 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((69313 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((69313 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((69313 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 69313) := ⟨by norm_num⟩
  have hP : poly [-5278, 1] = X - C (5278 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((69313 : ℕ) : ℤ[X]) = poly [69313] := by simp [poly]
  refine ⟨X - C (5278 : ℤ),
    poly [-25385, -20649, 13969, -27628, 16082, 31928, -10014, 9309, -4437, -25005, -8856, 16427, -12998,
      19578, -12065, -1263, 5279, 1],
    poly [-1933, -1572, 1064, -2104, 1225, 2431, -763, 709, -338, -1904, -674, 1251, -990, 1491, -919,
      -96, 402],
    poly [0, -1, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1],
    poly [20301, 19031, 10626, -4885, 15533, 3849, -4164, 19486, -14470, -11062, -1606, 8035, 617, 18108,
      8065, -276, 14654, 9220],
    poly [69313, -49012, 19031, -9675, -23916, 25208, 7464, -28102, 126, 30413, -23201, 15477, 17561,
      -14930, 5434, 9220],
    poly [-1546, -1449, -809, 372, -1183, -293, 317, -1484, 1102, 842, 122, -612, -47, -1379, -614, 21,
      -1116, -702],
    poly [-5278, 3733, -1450, 737, 1821, -1920, -568, 2140, -10, -2316, 1767, -1179, -1337, 1137, -414,
      -702],
    poly [0, 25385, 20649, 29959, 6979, 23272, 5021, -8522, -5097, -23902, -30196, 32392, 10801, 6542,
      -5278, -1],
    poly [0, 1933, 1572, 2281, 531, 1772, 382, -649, -388, -1820, -2299, 2467, 822, 498, -402],
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
theorem certificado_69389 :
    haveI : Fact (Nat.Prime 69389) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 69389 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((69389 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((69389 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((69389 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 69389) := ⟨by norm_num⟩
  have hP : poly [-3032, 1] = X - C (3032 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((69389 : ℕ) : ℤ[X]) = poly [69389] := by simp [poly]
  refine ⟨X - C (3032 : ℤ),
    poly [12198, -8990, -31791, -16305, 31714, 8501, -15834, -23646, -3967, -31858, -31707, -102, 7392,
      -19107, 1733, -32680, 3033, 1],
    poly [533, -393, -1389, -712, 1386, 371, -692, -1033, -173, -1392, -1385, -4, 323, -835, 76, -1428,
      133],
    poly [1, 1, 0, 1, 1, -1, 0, 1, 0, -1],
    poly [-21827, -21674, -14465, -33984, -14881, -25013, -16686, -3936, -27687, -12064, -39224, -4630,
      -27733, -6068, -42426, -12641, -9267, -17642],
    poly [91216, -47715, -7362, 34137, 22090, -38160, 14268, 8375, -17642],
    poly [954, 947, 632, 1485, 650, 1093, 729, 172, 1210, 527, 1714, 202, 1212, 265, 1854, 552, 405, 771],
    poly [-3986, 2086, 321, -1492, -965, 1668, -624, -366, 771],
    poly [12198, -8990, 25400, 4883, -14874, -31381, -33675, -3032, -1],
    poly [533, -393, 1110, 213, -650, -1371, -1471, -132],
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
theorem certificado_69427 :
    haveI : Fact (Nat.Prime 69427) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 69427 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((69427 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((69427 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((69427 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 69427) := ⟨by norm_num⟩
  have hP : poly [-569, 1] = X - C (569 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((69427 : ℕ) : ℤ[X]) = poly [69427] := by simp [poly]
  refine ⟨X - C (569 : ℤ),
    poly [30870, 28972, 23844, 31644, 18480, -34498, -26050, 21429, 18096, 16992, 8815, -3767, 27935,
      30187, 7374, -22804, 570, 1],
    poly [253, 237, 195, 259, 151, -283, -213, 176, 148, 139, 72, -31, 229, 247, 60, -187, 5],
    poly [-1, 0, 0, -1, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1],
    poly [-4397, 1208, -13058, 2901, 2563, 22573, 5892, 8303, 6477, 373, 5975, 14892, 25157, 9435,
      -16582, -3328, -20997, 2521],
    poly [65030, -63822, -14266, 11562, 5267, 1347, 4883, -7796, 28538, -13254, 17669, -23518, 2521],
    poly [36, -10, 107, -24, -21, -185, -48, -68, -53, -3, -49, -122, -206, -77, 136, 27, 172, -21],
    poly [-533, 524, 116, -95, -43, -11, -40, 64, -234, 109, -145, 193, -21],
    poly [-30870, 1898, 5128, 30757, 15062, 27236, -14350, 1683, -22814, -30178, 23374, -569, -1],
    poly [-253, 16, 42, 252, 123, 223, -118, 14, -187, -247, 192, -5],
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
theorem certificado_69959 :
    haveI : Fact (Nat.Prime 69959) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 69959 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((69959 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((69959 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((69959 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 69959) := ⟨by norm_num⟩
  have hP : poly [-994, 1] = X - C (994 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((69959 : ℕ) : ℤ[X]) = poly [69959] := by simp [poly]
  refine ⟨X - C (994 : ℤ),
    poly [-9783, -12960, -31755, 18971, -17717, 23208, 17126, -17930, -31760, -29944, -33602, -808,
      -9080, 8507, 32947, 9605, 995, 1],
    poly [-139, -184, -451, 270, -252, 330, 243, -255, -451, -425, -477, -11, -129, 121, 468, 136, 14],
    poly [-1, 0, 0, 1, -2, 0, 0, -1, 0, 0, 0, -1],
    poly [-31001, -41519, -29424, -4708, 13616, 42350, 51810, 43233, 15283, -19795, -38974, -37093,
      -34487, -5065, 19035, 27505, 58059, 33034],
    poly [38958, -80477, 12095, 55717, -33160, -4397, 8934, -8470, -30554, 25025, 33034],
    poly [440, 589, 417, 66, -194, -602, -736, -614, -217, 281, 553, 526, 489, 71, -271, -391, -825,
      -469],
    poly [-554, 1144, -173, -791, 471, 62, -127, 120, 434, -356, -469],
    poly [9783, 3177, 18795, 9450, -16882, 16593, 24439, -23342, -8610, -994, -1],
    poly [139, 45, 267, 134, -240, 236, 347, -332, -122, -14],
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
theorem certificado_69997 :
    haveI : Fact (Nat.Prime 69997) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 69997 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((69997 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((69997 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((69997 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 69997) := ⟨by norm_num⟩
  have hP : poly [-13022, 1] = X - C (13022 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((69997 : ℕ) : ℤ[X]) = poly [69997] := by simp [poly]
  refine ⟨X - C (13022 : ℤ),
    poly [25667, -27455, -16644, -34473, 12081, 29350, 6931, -9933, -23093, 19102, -6379, 32477, 32781,
      -320, -20539, -17224, 13023, 1],
    poly [4775, -5108, -3096, -6413, 2248, 5460, 1289, -1848, -4296, 3554, -1187, 6042, 6098, -60, -3821,
      -3204, 2423],
    poly [-1, -1, 0, -1, 0, 0, 0, -1, -1, -1, 0, 0, -1, 0, -1],
    poly [-15240, 6604, 12626, -672, 13722, 7090, -2070, -12273, 9351, -7644, -18283, -5367, -14547,
      -1389, 7750, -3016, -20250, 13785],
    poly [54757, -63393, 27866, -22516, 22940, 13784, -29090, -20209, 11393, 8095, -23269, 31019, -34035,
      13785],
    poly [2835, -1229, -2349, 125, -2553, -1319, 385, 2283, -1740, 1422, 3401, 998, 2706, 258, -1442,
      561, 3767, -2565],
    poly [-10187, 11794, -5185, 4189, -4268, -2564, 5412, 3759, -2120, -1506, 4329, -5771, 6332, -2565],
    poly [-25667, 27455, -27686, -18649, 24397, -4637, 22979, -32938, -29787, 10028, -9707, 30246,
      -13022, -1],
    poly [-4775, 5108, -5151, -3469, 4539, -863, 4275, -6128, -5541, 1866, -1806, 5627, -2423],
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
theorem certificado_70111 :
    haveI : Fact (Nat.Prime 70111) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 70111 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((70111 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((70111 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((70111 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 70111) := ⟨by norm_num⟩
  have hP : poly [-10394, 1] = X - C (10394 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((70111 : ℕ) : ℤ[X]) = poly [70111] := by simp [poly]
  refine ⟨X - C (10394 : ℤ),
    poly [-16263, 27371, -16429, -8069, 5382, 12675, -9078, 1989, 9673, -33348, 23909, -19802, 33745,
      19875, -848, 4580, 10395, 1],
    poly [-2411, 4058, -2436, -1196, 798, 1879, -1346, 295, 1434, -4944, 3545, -2936, 5003, 2946, -126,
      679, 1541],
    poly [-1, -1, -1, 0, -1, 0, 0, 0, -1, -1, 0, -1],
    poly [-3387, 21078, 15448, 19724, 10200, -3413, 18906, 28156, 2700, 17227, -4242, -1809, 23466, 9998,
      6678, -1012, 14542, 8756],
    poly [66724, -49033, 15448, 23111, -14265, 5604, -6448, 22232, -6798, 5786, 8756],
    poly [502, -3125, -2290, -2924, -1512, 506, -2803, -4174, -400, -2554, 629, 268, -3479, -1482, -990,
      150, -2156, -1298],
    poly [-9892, 7270, -2291, -3426, 2115, -831, 956, -3296, 1008, -858, -1298],
    poly [16263, -27371, 16429, -8194, -31859, -2627, -25302, -4967, 5814, -10394, -1],
    poly [2411, -4058, 2436, -1215, -4723, -389, -3751, -736, 862, -1541],
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
theorem certificado_70529 :
    haveI : Fact (Nat.Prime 70529) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 70529 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((70529 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((70529 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((70529 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 70529) := ⟨by norm_num⟩
  have hP : poly [-1745, 1] = X - C (1745 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((70529 : ℕ) : ℤ[X]) = poly [70529] := by simp [poly]
  refine ⟨X - C (1745 : ℤ),
    poly [12287, -26022, -33885, 24595, 30287, -13078, -33918, 6892, -34917, 9559, -8361, -16859, 15147,
      27129, -1682, 14024, 1746, 1],
    poly [304, -644, -838, 609, 749, -324, -839, 171, -864, 237, -207, -417, 375, 671, -42, 347, 43],
    poly [-1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1],
    poly [4995, -8340, -62, -9030, 14488, 6135, 19751, 14747, -2393, -2807, 5923, 15022, 4074, 23347,
      -18151, 13634, -9588, 29321],
    poly [75524, -83864, 3283, 4367, 15240, 615, -14897, 16684, -39034, 8563, 15687, 9588, -29321],
    poly [-124, 206, 1, 223, -359, -152, -489, -365, 59, 69, -147, -372, -101, -578, 449, -338, 237,
      -726],
    poly [-1869, 2076, -82, -108, -377, -15, 369, -413, 966, -212, -388, -237, 726],
    poly [-12287, -32220, 20150, -26260, -13555, 31316, -31710, 18574, 13106, -3428, 14023, 1746, 1],
    poly [-304, -797, 499, -650, -335, 775, -785, 460, 324, -85, 347, 43],
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
theorem certificado_71023 :
    haveI : Fact (Nat.Prime 71023) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 71023 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((71023 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((71023 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((71023 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 71023) := ⟨by norm_num⟩
  have hP : poly [-14593, 1] = X - C (14593 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((71023 : ℕ) : ℤ[X]) = poly [71023] := by simp [poly]
  refine ⟨X - C (14593 : ℤ),
    poly [31708, -34991, 5030, -12897, 19350, -21418, 31726, 33472, -1779, -23045, -13079, -33680,
      -15703, 179, -33207, -27734, 14594, 1],
    poly [6515, -7190, 1034, -2650, 3976, -4401, 6519, 6877, -366, -4735, -2687, -6920, -3226, 37, -6823,
      -5698, 2999],
    poly [-1, 0, 0, -1, 0, -1, -1, 0, 0, 0, 1, 0, -1, 0, -1, -1],
    poly [6845, 11873, 30684, 22650, 5221, 13990, 21583, 30709, 11203, 39167, 7787, 43620, 5787, 36081,
      -11019, 35160, 1596, 40276],
    poly [77868, -65995, 18811, -1189, -12401, 34425, 11432, 15536, 40, 10094, -37759, 27661, -5116,
      1596, 40276],
    poly [-1407, -2440, -6305, -4654, -1073, -2875, -4435, -6310, -2302, -8048, -1600, -8963, -1189,
      -7414, 2264, -7225, -328, -8276],
    poly [-16000, 13561, -3866, 244, 2548, -7074, -2349, -3192, -8, -2074, 7759, -5684, 1051, -328,
      -8276],
    poly [-31708, -4324, 31002, -13781, 34452, -30961, -226, -7315, -17098, 24825, 28517, -23223, 27735,
      -14594, -1],
    poly [-6515, -888, 6370, -2832, 7079, -6362, -46, -1503, -3513, 5101, 5859, -4772, 5699, -2999],
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
theorem certificado_71327 :
    haveI : Fact (Nat.Prime 71327) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 71327 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((71327 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((71327 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((71327 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 71327) := ⟨by norm_num⟩
  have hP : poly [-1495, 1] = X - C (1495 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((71327 : ℕ) : ℤ[X]) = poly [71327] := by simp [poly]
  refine ⟨X - C (1495 : ℤ),
    poly [15649, -9961, -25484, 25508, -13151, -34074, -977, -30583, 4846, 1196, -12881, 20316, -4996,
      23661, 3117, 25384, 1496, 1],
    poly [328, -209, -534, 535, -276, -714, -20, -641, 102, 25, -270, 426, -105, 496, 65, 532, 31],
    poly [-1, 0, -1, 0, 1, -1, -1],
    poly [-29236, -6450, -20891, 2382, -1133, 11985, 7509, 9319, 1448, -7002, -13210, -11592, -10589,
      -14596, -5486, 14797, 11280, -15631],
    poly [42091, -48541, -43677, 46059, 11280, -15631],
    poly [613, 135, 438, -50, 24, -251, -157, -195, -30, 147, 277, 243, 222, 306, 115, -310, -236, 328],
    poly [-882, 1018, 915, -966, -236, 328],
    poly [-15649, 25610, -126, -25382, -1496, -1],
    poly [-328, 537, -3, -532, -31],
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
theorem certificado_71479 :
    haveI : Fact (Nat.Prime 71479) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 71479 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((71479 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((71479 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((71479 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 71479) := ⟨by norm_num⟩
  have hP : poly [-3223, 1] = X - C (3223 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((71479 : ℕ) : ℤ[X]) = poly [71479] := by simp [poly]
  refine ⟨X - C (3223 : ℤ),
    poly [998, 5700, 30718, 8925, 28723, -1477, -26015, 17091, 27661, -13786, 35458, -3981, -28788,
      -3136, -14350, 26498, 3224, 1],
    poly [45, 257, 1385, 402, 1295, -67, -1173, 771, 1247, -622, 1599, -180, -1298, -141, -647, 1195,
      145],
    poly [-1, -1, 0, 0, -2, -1],
    poly [-9820, -2083, -3877, -440, 426, -6094, -3723, -11174, -8892, 1000, -7114, 13531, -4227, -8535,
      2109, -41711, 16980, -15337],
    poly [61659, -73562, 5943, 1643, -15337],
    poly [443, 94, 175, 20, -19, 275, 168, 504, 401, -45, 321, -610, 191, 385, -95, 1881, -766, 692],
    poly [-2780, 3318, -269, -74, 692],
    poly [-998, -5700, -29720, -3225, -1],
    poly [-45, -257, -1340, -145],
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
theorem certificado_71593 :
    haveI : Fact (Nat.Prime 71593) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 71593 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((71593 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((71593 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((71593 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 71593) := ⟨by norm_num⟩
  have hP : poly [-1359, 1] = X - C (1359 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((71593 : ℕ) : ℤ[X]) = poly [71593] := by simp [poly]
  refine ⟨X - C (1359 : ℤ),
    poly [16331, -1305, -6428, -34932, -33794, -4292, 19436, -21216, -15293, -21663, -17822, -29725,
      -16827, -27459, -9292, -13177, 1360, 1],
    poly [310, -25, -122, -663, -641, -81, 369, -403, -290, -411, -338, -564, -319, -521, -176, -250, 26],
    poly [0, 0, 0, -1, 0, 1, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1],
    poly [6101, 28126, 21083, -9635, -6128, -4545, -11445, -14927, 4773, 23015, 11386, -11644, 13257,
      3266, 5840, -5063, 39, 13529],
    poly [71593, -71593, 0, 6101, 22025, -13144, -46642, 32575, 31359, -19100, -8601, -2535, 24432,
      -5102, -13490, 13529],
    poly [-116, -534, -400, 183, 116, 86, 217, 283, -91, -437, -216, 221, -252, -62, -111, 96, -1, -257],
    poly [-1359, 1360, -1, -116, -418, 250, 885, -619, -595, 363, 163, 48, -464, 97, 256, -257],
    poly [0, 0, 0, -16331, 17636, 21454, -5463, 11375, 2379, 23550, 2546, 16807, -3886, 14537, -1359, -1],
    poly [0, 0, 0, -310, 335, 407, -104, 216, 45, 447, 48, 319, -74, 276, -26],
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
theorem certificado_71707 :
    haveI : Fact (Nat.Prime 71707) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 71707 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((71707 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((71707 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((71707 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 71707) := ⟨by norm_num⟩
  have hP : poly [-2177, 1] = X - C (2177 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((71707 : ℕ) : ℤ[X]) = poly [71707] := by simp [poly]
  refine ⟨X - C (2177 : ℤ),
    poly [34783, 18198, 11438, 17265, -19294, 32172, -16158, 19031, 6827, -6881, 18640, -17350, 33721,
      28639, -33617, 8845, 2178, 1],
    poly [1056, 552, 347, 524, -586, 977, -491, 578, 207, -209, 566, -527, 1024, 869, -1021, 269, 66],
    poly [-1, -1, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1],
    poly [8850, 17451, 10472, 32834, 21217, 26383, 35147, 23392, 24243, 38901, 26457, 42657, 31663,
      22534, 37945, 6957, 34644, 22733],
    poly [80557, -54256, 1622, 6533, 10994, 9129, -15411, 30988, -27687, 11911, 22733],
    poly [-269, -530, -318, -997, -644, -801, -1067, -710, -736, -1181, -803, -1295, -961, -684, -1152,
      -211, -1052, -690],
    poly [-2446, 1648, -50, -198, -334, -277, 468, -941, 841, -362, -690],
    poly [-34783, -18198, 23345, 35716, -20636, -5082, 9451, -29245, -6667, -2177, -1],
    poly [-1056, -552, 709, 1084, -627, -154, 287, -888, -202, -66],
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
theorem certificado_71821 :
    haveI : Fact (Nat.Prime 71821) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 71821 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((71821 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((71821 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((71821 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 71821) := ⟨by norm_num⟩
  have hP : poly [-2618, 1] = X - C (2618 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((71821 : ℕ) : ℤ[X]) = poly [71821] := by simp [poly]
  refine ⟨X - C (2618 : ℤ),
    poly [-13415, 7786, 8041, -18542, 33599, -31426, -3935, -13005, -22281, 5972, 20550, 15837, -6578,
      10724, -8418, 33548, 2619, 1],
    poly [-489, 284, 293, -676, 1225, -1146, -143, -474, -812, 218, 749, 577, -240, 391, -307, 1223, 95],
    poly [1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1],
    poly [9818, -1426, -15586, -5441, -11061, 8689, 7270, 3950, -4830, -2090, -17342, -4893, 14617,
      25543, 11172, -8229, 6660, 8394],
    poly [62003, -60577, 4342, -8719, 31024, -25553, -1680, 4776, 5708, 11634, -6741, -7876, -17667,
      6495, 1734, -8394],
    poly [-358, 52, 568, 198, 403, -317, -265, -144, 176, 76, 632, 178, -533, -931, -407, 300, -243,
      -306],
    poly [-2260, 2209, -159, 318, -1131, 932, 61, -174, -208, -424, 246, 287, 644, -237, -63, 306],
    poly [-13415, 21201, -13160, -18797, 1776, -32947, -10986, -13913, 19884, 666, 15171, -21749, 32473,
      30930, 2618, 1],
    poly [-489, 773, -480, -685, 65, -1201, -400, -507, 725, 24, 553, -793, 1184, 1127, 95],
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
theorem certificado_72277 :
    haveI : Fact (Nat.Prime 72277) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 72277 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((72277 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((72277 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((72277 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 72277) := ⟨by norm_num⟩
  have hP : poly [-5652, 1] = X - C (5652 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((72277 : ℕ) : ℤ[X]) = poly [72277] := by simp [poly]
  refine ⟨X - C (5652 : ℤ),
    poly [-24233, -11897, -11281, 27185, 17294, -777, 11023, 32611, 33689, -7411, -6651, -20206, 444,
      -34054, 3971, 4323, 5653, 1],
    poly [-1895, -930, -882, 2126, 1352, -61, 862, 2550, 2634, -580, -520, -1580, 35, -2663, 311, 338,
      442],
    poly [-1, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, 0, 0, 1],
    poly [-23121, -23010, -7396, -3429, 472, -4911, 8835, -9040, -17854, -28981, -4085, 4564, -7519,
      -20731, -17, -1420, -30129, 3076],
    poly [49156, -95287, 15725, -3540, 7979, -8989, -10680, 15497, -12491, 1673, -28709, 33205, -3076],
    poly [1808, 1799, 578, 268, -37, 384, -691, 707, 1396, 2266, 319, -357, 588, 1621, 1, 111, 2356,
      -241],
    poly [-3844, 7452, -1231, 277, -624, 703, 835, -1212, 977, -131, 2245, -2597, 241],
    poly [24233, 11897, -12952, -14849, 31366, -20698, -20298, 35828, 28600, -353, -1330, 5652, 1],
    poly [1895, 930, -1013, -1161, 2453, -1619, -1587, 2802, 2236, -28, -104, 442],
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
theorem certificado_72353 :
    haveI : Fact (Nat.Prime 72353) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 72353 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((72353 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((72353 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((72353 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 72353) := ⟨by norm_num⟩
  have hP : poly [-171, 1] = X - C (171 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((72353 : ℕ) : ℤ[X]) = poly [72353] := by simp [poly]
  refine ⟨X - C (171 : ℤ),
    poly [32580, -5310, -35996, 12483, 32653, 3999, -19440, 9618, -33370, -21351, -25935, -15807, 15986,
      5594, -35086, 29413, 172, 1],
    poly [77, -13, -85, 30, 77, 9, -46, 23, -79, -50, -61, -37, 38, 13, -83, 70],
    poly [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1],
    poly [11931, -19733, -15687, -7201, -20268, -22460, -19511, -13147, 11431, -9158, -4201, -11365,
      -19023, 5473, -20617, -11461, -2522, -14317],
    poly [60422, -40689, -4046, -8486, 1136, 33856, -18926, 16814, -15557, 14295, 5161, -8939, 11795,
      -14317],
    poly [-28, 47, 37, 17, 48, 53, 46, 31, -27, 22, 10, 27, 45, -13, 49, 27, 6, 34],
    poly [-143, 97, 9, 20, -3, -80, 45, -40, 37, -34, -12, 21, -28, 34],
    poly [32580, 34463, -30686, -23874, -19603, 5809, -21545, -32706, 18849, 31844, -7853, -29241, -171,
      -1],
    poly [77, 81, -73, -56, -46, 14, -51, -77, 45, 75, -19, -69],
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
theorem certificado_72467 :
    haveI : Fact (Nat.Prime 72467) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 72467 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((72467 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((72467 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((72467 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 72467) := ⟨by norm_num⟩
  have hP : poly [-7150, 1] = X - C (7150 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((72467 : ℕ) : ℤ[X]) = poly [72467] := by simp [poly]
  refine ⟨X - C (7150 : ℤ),
    poly [34997, 9755, 31299, 2599, 23879, 31078, -17033, 25356, 9480, 17363, 17881, 6185, -34986,
      -34860, -23995, -32051, 7151, 1],
    poly [3453, 962, 3088, 256, 2356, 3066, -1681, 2502, 935, 1713, 1764, 610, -3452, -3439, -2367,
      -3162, 706],
    poly [-1, 0, 0, -1, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0, -1],
    poly [13499, 1369, 3293, -9092, 3626, 4094, 3040, 4175, -5504, 19701, -11360, 25457, 4168, 22074,
      -12059, -5486, -30509, 8194],
    poly [85966, -84597, 1924, 1114, 14087, -9738, -11515, 1468, 3507, 38118, -56609, 42327, -6573,
      25023, -38703, 8194],
    poly [-1332, -135, -325, 897, -358, -404, -300, -412, 543, -1944, 1121, -2512, -411, -2178, 1190,
      541, 3010, -809],
    poly [-8482, 8348, -191, -110, -1390, 961, 1136, -145, -346, -3761, 5586, -4177, 649, -2469, 3819,
      -809],
    poly [-34997, 25242, -21544, -6297, -31035, -3501, -17200, -34969, -12603, -1968, -7024, 10864,
      -8056, -33265, -7150, -1],
    poly [-3453, 2491, -2126, -621, -3062, -345, -1697, -3450, -1243, -194, -693, 1072, -795, -3282,
      -705],
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
theorem certificado_72733 :
    haveI : Fact (Nat.Prime 72733) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 72733 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((72733 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((72733 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((72733 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 72733) := ⟨by norm_num⟩
  have hP : poly [-779, 1] = X - C (779 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((72733 : ℕ) : ℤ[X]) = poly [72733] := by simp [poly]
  refine ⟨X - C (779 : ℤ),
    poly [26703, -21907, 17805, 35409, 29176, -16862, 2686, 17183, -11182, -22049, 27515, -30309, -4894,
      9984, -9604, 25757, 780, 1],
    poly [286, -235, 191, 379, 312, -181, 29, 184, -120, -236, 295, -325, -52, 107, -103, 276, 8],
    poly [1, 1, 0, 1, 1, 1, 0, 0, 0, 0, -1, 1],
    poly [-11176, -1947, -24530, -19984, -20445, -2239, -9685, -31169, 10912, -25914, -11396, -18660,
      -26979, -11304, -2414, 8428, -28158, -21856],
    poly [83909, -70786, 13354, 29213, -2138, 6785, -1952, 47428, -42888, -15554, 21856],
    poly [120, 21, 263, 214, 219, 24, 104, 334, -117, 278, 122, 200, 289, 121, 26, -90, 302, 234],
    poly [-899, 759, -144, -313, 23, -73, 21, -508, 460, 166, -234],
    poly [26703, -21907, -8898, 11286, -10536, -34466, -17784, 12395, 24198, 778, 1],
    poly [286, -235, -95, 121, -113, -369, -190, 133, 259, 8],
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
theorem certificado_72923 :
    haveI : Fact (Nat.Prime 72923) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 72923 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((72923 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((72923 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((72923 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 72923) := ⟨by norm_num⟩
  have hP : poly [-8944, 1] = X - C (8944 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((72923 : ℕ) : ℤ[X]) = poly [72923] := by simp [poly]
  refine ⟨X - C (8944 : ℤ),
    poly [24680, -24824, -18046, -13724, 5665, 5871, 26401, 15005, 4274, -10982, 5649, 36136, -36433,
      -22393, 503, 7550, 8945, 1],
    poly [3027, -3045, -2213, -1683, 695, 720, 3238, 1840, 524, -1347, 693, 4432, -4469, -2746, 62, 926,
      1097],
    poly [0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0, -1],
    poly [7544, -5957, 13536, -673, -9260, 3662, -19019, -8887, -13680, -3546, 15224, -21480, -16266,
      11309, -22255, 4908, 3207, -19761],
    poly [72923, -65379, -13501, 27037, -27710, 18450, -14788, -4231, 2888, -30069, 38472, -23956,
      -18060, 22968, -19761],
    poly [-925, 731, -1660, 83, 1136, -449, 2333, 1090, 1678, 435, -1867, 2635, 1995, -1387, 2730, -602,
      -393, 2424],
    poly [-8944, 8020, 1655, -3316, 3399, -2263, 1814, 519, -354, 3688, -4719, 2939, 2215, -2817, 2424],
    poly [0, -24680, -23419, -31458, -27741, 22076, -27947, 1546, 31692, 13538, 15346, -1898, 1394,
      -8944, -1],
    poly [0, -3027, -2872, -3858, -3402, 2708, -3428, 190, 3887, 1660, 1882, -233, 171, -1097],
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
theorem certificado_73037 :
    haveI : Fact (Nat.Prime 73037) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 73037 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((73037 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((73037 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((73037 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 73037) := ⟨by norm_num⟩
  have hP : poly [-3682, 1] = X - C (3682 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((73037 : ℕ) : ℤ[X]) = poly [73037] := by simp [poly]
  refine ⟨X - C (3682 : ℤ),
    poly [-21681, -21310, -11729, -3296, 20966, 32914, 15263, -35225, 13003, -26458, -24981, 7650,
      -29058, -11017, 22769, -24075, 3683, 1],
    poly [-1093, -1074, -591, -166, 1057, 1659, 769, -1776, 656, -1334, -1259, 386, -1465, -555, 1148,
      -1214, 186],
    poly [-1, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1, -1],
    poly [-38039, -27794, -11466, -14437, -10054, -3368, -22647, -19895, -25012, -23486, -24041, -5891,
      -19097, -33343, -27396, -794, -16021, -25368],
    poly [34998, -62792, -21711, 7274, 20711, -34324, -42690, -2028, -794, -16021, -25368],
    poly [1918, 1401, 578, 728, 507, 170, 1142, 1003, 1261, 1184, 1212, 297, 963, 1681, 1381, 40, 808,
      1279],
    poly [-1764, 3166, 1094, -367, -1044, 1731, 2152, 102, 40, 808, 1279],
    poly [21681, -371, 12100, -8804, -33843, 1300, 14699, -22768, 24075, -3683, -1],
    poly [1093, -19, 610, -444, -1706, 66, 741, -1148, 1214, -186],
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
theorem certificado_73189 :
    haveI : Fact (Nat.Prime 73189) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 73189 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((73189 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((73189 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((73189 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 73189) := ⟨by norm_num⟩
  have hP : poly [-1073, 1] = X - C (1073 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((73189 : ℕ) : ℤ[X]) = poly [73189] := by simp [poly]
  refine ⟨X - C (1073 : ℤ),
    poly [4229, -22096, -14140, 6876, -18342, -7793, 25776, -24054, -4115, -12418, -29751, 9317, -21682,
      -8410, 265, -18621, 1074, 1],
    poly [62, -324, -207, 101, -269, -114, 378, -353, -60, -182, -436, 137, -318, -123, 4, -273, 16],
    poly [1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 1, -1],
    poly [12199, 20873, 6216, -414, 6469, 27484, 6495, -9281, 32244, 3430, -1849, 397, 16633, 5871,
      -5189, -220, -8878, 11304],
    poly [60990, -81863, 14657, 18829, 13990, -26998, -298, 16029, -13627, 28840, -31486, 11304],
    poly [-179, -306, -91, 6, -95, -403, -95, 136, -473, -50, 27, -6, -244, -86, 76, 3, 130, -166],
    poly [-894, 1201, -216, -276, -205, 396, 4, -235, 200, -423, 462, -166],
    poly [4229, -26325, 7956, 16787, -3122, 28918, 4597, 27561, 34608, 20768, -1072, -1],
    poly [62, -386, 117, 246, -46, 424, 67, 404, 507, 304, -16],
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
theorem certificado_73303 :
    haveI : Fact (Nat.Prime 73303) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 73303 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((73303 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((73303 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((73303 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 73303) := ⟨by norm_num⟩
  have hP : poly [-4604, 1] = X - C (4604 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((73303 : ℕ) : ℤ[X]) = poly [73303] := by simp [poly]
  refine ⟨X - C (4604 : ℤ),
    poly [14823, -17415, -15798, -14508, -4095, 20124, -13322, 8547, -9774, -25206, 17970, 28615, -14164,
      28003, -32060, 16854, 4605, 1],
    poly [931, -1094, -992, -911, -257, 1264, -837, 537, -614, -1583, 1129, 1797, -890, 1759, -2014,
      1059, 289],
    poly [-1, 0, -1, 1, 0, 0, 0, 0, -1, 0, 0, 1, -1],
    poly [-17733, -26032, -12389, 399, 5433, 8905, 2155, -1190, 28917, 21520, 5963, -3864, 8696, 21436,
      4944, 355, -2082, -16810],
    poly [55570, -81602, -4090, 22222, 26976, 2617, -14504, -4907, 2152, -12291, 31538, -16810],
    poly [1114, 1635, 778, -25, -341, -559, -135, 75, -1816, -1351, -374, 243, -546, -1346, -310, -22,
      131, 1056],
    poly [-3490, 5126, 256, -1396, -1694, -164, 911, 308, -135, 772, -1981, 1056],
    poly [-14823, 32238, -16440, -27532, 29035, -23892, 24323, -35675, -12140, -7645, -4603, -1],
    poly [-931, 2025, -1033, -1729, 1824, -1501, 1528, -2241, -762, -480, -289],
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
theorem certificado_73379 :
    haveI : Fact (Nat.Prime 73379) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 73379 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((73379 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((73379 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((73379 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 73379) := ⟨by norm_num⟩
  have hP : poly [-4966, 1] = X - C (4966 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((73379 : ℕ) : ℤ[X]) = poly [73379] := by simp [poly]
  refine ⟨X - C (4966 : ℤ),
    poly [-26287, -22613, -10939, -7479, 28960, 11487, -22103, -32926, 26635, 18919, 7983, 32273, -555,
      -13151, 35224, 10779, 4967, 1],
    poly [-1779, -1530, -740, -506, 1960, 777, -1496, -2228, 1803, 1280, 540, 2184, -38, -890, 2384, 729,
      336],
    poly [-1, -1, -1, 0, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1],
    poly [5173, 16537, 16096, 17411, 23307, 35011, 19912, 19510, 18712, 28080, 24772, 21491, -5831,
      14407, 12963, -8522, 13446, -6468],
    poly [78552, -56842, 16096, 12238, 11943, 30279, 2060, 2691, 961, 19431, -8522, 13446, -6468],
    poly [-350, -1119, -1089, -1178, -1577, -2369, -1347, -1320, -1266, -1900, -1676, -1454, 395, -975,
      -877, 577, -910, 438],
    poly [-5316, 3848, -1090, -828, -808, -2049, -139, -182, -65, -1315, 577, -910, 438],
    poly [26287, 22613, 10939, -18808, -25286, -26100, 2950, 11334, 18118, -35223, -10779, -4967, -1],
    poly [1779, 1530, 740, -1273, -1711, -1766, 200, 767, 1226, -2384, -729, -336],
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
theorem certificado_73417 :
    haveI : Fact (Nat.Prime 73417) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 73417 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((73417 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((73417 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((73417 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 73417) := ⟨by norm_num⟩
  have hP : poly [-1829, 1] = X - C (1829 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((73417 : ℕ) : ℤ[X]) = poly [73417] := by simp [poly]
  refine ⟨X - C (1829 : ℤ),
    poly [-17140, 18094, 612, -26091, -33933, -19286, 17571, -6734, -26376, 106, -35725, 27557, 18279,
      14581, -10268, -30111, 1830, 1],
    poly [-427, 451, 15, -650, -845, -480, 438, -168, -657, 3, -890, 687, 455, 363, -256, -750, 46],
    poly [-1, 1, 0, -1, 0, 0, -1, 0, 0, 1, -1],
    poly [1809, 26095, 13745, -4044, -6703, 9994, 17108, 5431, -3607, -5057, 30306, 21374, 1339, -27252,
      -18517, 2120, -2806, -4896],
    poly [75226, -50940, -36636, -3630, 39416, 7006, -25563, 2836, 6986, -4896],
    poly [-45, -650, -342, 101, 167, -249, -426, -135, 90, 126, -755, -532, -33, 679, 461, -53, 70, 122],
    poly [-1874, 1270, 912, 90, -982, -174, 637, -71, -174, 122],
    poly [17140, 21043, -20701, 26361, 19322, -5007, 21633, 33770, -1828, -1],
    poly [427, 524, -516, 657, 481, -125, 539, 841, -46],
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
theorem certificado_73607 :
    haveI : Fact (Nat.Prime 73607) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 73607 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((73607 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((73607 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((73607 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 73607) := ⟨by norm_num⟩
  have hP : poly [-726, 1] = X - C (726 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((73607 : ℕ) : ℤ[X]) = poly [73607] := by simp [poly]
  refine ⟨X - C (726 : ℤ),
    poly [-3143, -18254, -35612, 24588, -10409, 36485, -10494, -9849, 29997, -13139, -5493, 30003, 5719,
      11566, -13063, 12554, 727, 1],
    poly [-31, -180, -351, 243, -103, 360, -104, -97, 296, -130, -54, 296, 56, 114, -129, 124, 7],
    poly [-1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, -1],
    poly [14477, 26562, 28505, 25973, 17453, 32041, 24964, 11267, 21691, 29208, 27292, 41078, 15953,
      28389, 29420, 31145, 5902, 15499],
    poly [88084, -47045, 14028, 13888, 1033, 8011, 4979, -14817, 23400, 12807, -10628, 13774, 25243,
      -9597, 15499],
    poly [-143, -262, -281, -256, -172, -316, -246, -111, -214, -288, -269, -405, -157, -280, -290, -307,
      -58, -153],
    poly [-869, 465, -139, -137, -10, -79, -49, 146, -231, -126, 105, -136, -249, 95, -153],
    poly [3143, 18254, 32469, 33908, -10092, 5461, 13492, 10867, 1333, -5980, -25355, 25616, -11827,
      -726, -1],
    poly [31, 180, 320, 334, -100, 54, 133, 107, 13, -59, -250, 253, -117, -7],
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
theorem certificado_73721 :
    haveI : Fact (Nat.Prime 73721) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 73721 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((73721 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((73721 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((73721 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 73721) := ⟨by norm_num⟩
  have hP : poly [-2054, 1] = X - C (2054 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((73721 : ℕ) : ℤ[X]) = poly [73721] := by simp [poly]
  refine ⟨X - C (2054 : ℤ),
    poly [6281, -3945, 14570, -20128, -1266, -3841, 24835, 11282, -10080, -7578, -20067, -15802, 30177,
      1235, -10049, 18874, 2055, 1],
    poly [175, -110, 406, -561, -35, -107, 692, 314, -281, -211, -559, -440, 841, 34, -280, 526, 57],
    poly [-1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -2],
    poly [11304, 4203, 4379, 4738, 35210, 20294, 8299, 6032, 16906, -17042, 9214, 9155, 11129, -2437,
      -15867, 1139, 8182, 3699],
    poly [85025, -69518, -6925, 535, 30831, 26860, -34012, -14086, 8966, 7398],
    poly [-315, -117, -122, -132, -981, -565, -231, -168, -471, 475, -257, -255, -310, 68, 442, -32,
      -228, -103],
    poly [-2369, 1938, 192, -15, -859, -748, 948, 392, -250, -206],
    poly [-6281, 3945, -8289, 16183, 15836, -22568, -15875, -33638, -4108, -2],
    poly [-175, 110, -231, 451, 441, -629, -442, -937, -114],
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
theorem certificado_74101 :
    haveI : Fact (Nat.Prime 74101) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 74101 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((74101 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((74101 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((74101 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 74101) := ⟨by norm_num⟩
  have hP : poly [-4627, 1] = X - C (4627 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((74101 : ℕ) : ℤ[X]) = poly [74101] := by simp [poly]
  refine ⟨X - C (4627 : ℤ),
    poly [18257, 6506, 22118, -13720, -31184, 26562, -7233, 23156, 5370, 13790, -24676, -6091, -3957,
      12731, -30874, -1432, 4628, 1],
    poly [1140, 406, 1381, -857, -1947, 1659, -452, 1446, 335, 861, -1541, -380, -247, 795, -1928, -89,
      289],
    poly [-1, 0, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, 1, -1, 0, 0, -1],
    poly [2678, 17092, -6655, -22627, -9258, 1603, 6602, 32291, 13447, -2588, -24644, -13086, 12156,
      3081, -4480, -13466, -15678, -16239],
    poly [76779, -59687, -23747, -15972, 16047, 25275, -16070, 24131, -29222, -18468, 10726, 24361,
      -7253, 2212, 561, -16239],
    poly [-167, -1067, 416, 1413, 578, -100, -412, -2016, -839, 162, 1539, 817, -759, -192, 280, 841,
      979, 1014],
    poly [-4794, 3728, 1482, 997, -1002, -1578, 1004, -1507, 1825, 1153, -670, -1521, 453, -138, -35,
      1014],
    poly [-18257, 11751, -15612, 35838, -793, 28106, -74, 17200, 19638, 25516, 27375, 25870, 29441, 6060,
      -4627, -1],
    poly [-1140, 734, -975, 2238, -50, 1755, -5, 1074, 1226, 1593, 1709, 1615, 1838, 378, -289],
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
theorem certificado_74177 :
    haveI : Fact (Nat.Prime 74177) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 74177 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((74177 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((74177 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((74177 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 74177) := ⟨by norm_num⟩
  have hP : poly [-2879, 1] = X - C (2879 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((74177 : ℕ) : ℤ[X]) = poly [74177] := by simp [poly]
  refine ⟨X - C (2879 : ℤ),
    poly [21256, 15827, -4761, -30533, -18046, -36412, 31910, 16784, -22255, -27370, 27765, 628, 24348,
      13097, 17705, -16303, 2880, 1],
    poly [825, 614, -185, -1185, -700, -1413, 1239, 651, -864, -1062, 1078, 24, 945, 508, 687, -633, 112],
    poly [-1, -1, -1, 0, 0, 0, -1, 0, -1, 0, 0, -1, -1],
    poly [15456, 12653, 29090, 17888, 19430, 28912, 18429, 17369, -1079, 29987, 14745, -6439, 26275,
      -7311, 17257, 5929, 15355, 8376],
    poly [89633, -61524, 29090, 2432, 6777, -178, 15997, -4864, 1902, -2447, 15355, 8376],
    poly [-600, -491, -1129, -694, -754, -1122, -715, -674, 42, -1164, -572, 250, -1020, 284, -670, -230,
      -596, -325],
    poly [-3479, 2389, -1130, -94, -263, 7, -621, 189, -74, 95, -596, -325],
    poly [-21256, -15827, 4761, -22388, 33873, 31651, -9522, -29401, -14825, 16304, -2880, -1],
    poly [-825, -614, 185, -869, 1315, 1228, -370, -1141, -575, 633, -112],
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
theorem certificado_74747 :
    haveI : Fact (Nat.Prime 74747) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 74747 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((74747 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((74747 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((74747 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 74747) := ⟨by norm_num⟩
  have hP : poly [-3358, 1] = X - C (3358 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((74747 : ℕ) : ℤ[X]) = poly [74747] := by simp [poly]
  refine ⟨X - C (3358 : ℤ),
    poly [13645, 22397, -27684, -9513, -17009, 12015, -10859, 36146, -17819, 1909, -22704, -16590,
      -24468, -15344, 16178, -7274, 3359, 1],
    poly [613, 1006, -1244, -427, -764, 540, -488, 1624, -801, 86, -1020, -745, -1099, -689, 727, -327,
      151],
    poly [-1, -1, 1, 0, 0, 0, 1, -1],
    poly [7669, 9964, 13682, 34785, 9794, 16175, 27685, 17182, 40618, 24064, 17960, 38882, 16985, 37791,
      29027, 18607, 30713, 35213],
    poly [82416, -64783, -1656, 22526, -7606, -39713, 35213],
    poly [-345, -448, -615, -1563, -440, -727, -1244, -772, -1825, -1081, -807, -1747, -763, -1698,
      -1304, -836, -1380, -1582],
    poly [-3703, 2911, 74, -1012, 342, 1784, -1582],
    poly [-13645, -22397, -19773, -34085, 13991, -3357, -1],
    poly [-613, -1006, -888, -1531, 629, -151],
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
theorem certificado_74861 :
    haveI : Fact (Nat.Prime 74861) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 74861 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((74861 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((74861 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((74861 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 74861) := ⟨by norm_num⟩
  have hP : poly [-7241, 1] = X - C (7241 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((74861 : ℕ) : ℤ[X]) = poly [74861] := by simp [poly]
  refine ⟨X - C (7241 : ℤ),
    poly [-28741, 17313, -36875, 28922, 36778, -29563, -26574, 14708, 28681, -2591, -9977, 14793, 1253,
      -24409, 29482, 36623, 7242, 1],
    poly [-2780, 1675, -3567, 2798, 3557, -2860, -2570, 1423, 2774, -251, -965, 1431, 121, -2361, 2852,
      3542, 700],
    poly [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1],
    poly [-6739, -26931, -42731, -43705, -39425, -24568, -26675, -21413, -5491, -16582, -24875, -16564,
      -31564, -22065, -29373, -8635, -21059, -12273],
    poly [81600, -47930, 35992, 16774, 3433, 1055, 9789, 18011, -2925, 1478, 33011, -12424, 8786, 12273],
    poly [652, 2605, 4133, 4227, 3813, 2376, 2580, 2071, 531, 1604, 2406, 1602, 3053, 2134, 2841, 835,
      2037, 1187],
    poly [-7893, 4637, -3482, -1622, -332, -102, -947, -1742, 283, -143, -3193, 1202, -850, -1187],
    poly [-28741, 17313, -8134, 11609, -29949, -12431, 3441, 6400, -19818, 28211, -7140, 29381, 7241, 1],
    poly [-2780, 1675, -787, 1123, -2897, -1202, 333, 619, -1917, 2729, -691, 2842, 700],
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
theorem certificado_75013 :
    haveI : Fact (Nat.Prime 75013) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 75013 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((75013 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((75013 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((75013 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 75013) := ⟨by norm_num⟩
  have hP : poly [-5771, 1] = X - C (5771 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((75013 : ℕ) : ℤ[X]) = poly [75013] := by simp [poly]
  refine ⟨X - C (5771 : ℤ),
    poly [7500, 17250, 29925, 8896, -25943, -3722, 17664, 458, 23098, -22483, 776, -36499, 27563, 20828,
      -25434, 4441, 5772, 1],
    poly [577, 1327, 2302, 684, -1996, -286, 1359, 35, 1777, -1730, 60, -2808, 2121, 1602, -1957, 342,
      444],
    poly [0, -1, 1, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, 0, 0, -1],
    poly [33477, 24488, 5301, 32867, 23695, 26774, 38278, 23228, 3663, 15735, 16426, 9823, 23743, 41839,
      20356, 14932, 37886, 37721],
    poly [75013, -41536, -42466, -10198, 46753, -3261, 3262, -10762, 1012, 19790, 59204, 5424, -22954,
      165, 37721],
    poly [-2576, -1884, -408, -2529, -1823, -2060, -2945, -1787, -282, -1211, -1264, -756, -1827, -3219,
      -1566, -1149, -2915, -2902],
    poly [-5771, 3196, 3267, 784, -3597, 251, -251, 828, -78, -1523, -4555, -417, 1766, -13, -2902],
    poly [0, -7500, -2250, -2925, 33704, 6310, 8203, -11840, -15392, -12507, 28750, 29875, 1331, -5771,
      -1],
    poly [0, -577, -173, -225, 2593, 485, 631, -911, -1184, -962, 2212, 2298, 102, -444],
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
theorem certificado_75431 :
    haveI : Fact (Nat.Prime 75431) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 75431 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((75431 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((75431 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((75431 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 75431) := ⟨by norm_num⟩
  have hP : poly [-2431, 1] = X - C (2431 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((75431 : ℕ) : ℤ[X]) = poly [75431] := by simp [poly]
  refine ⟨X - C (2431 : ℤ),
    poly [-11853, 22491, 816, 5027, -17312, 36762, -36754, 32441, -35918, -15343, -8291, 1517, 16570,
      -29967, -6125, 28575, 2432, 1],
    poly [-382, 725, 26, 162, -558, 1185, -1185, 1046, -1158, -494, -267, 49, 534, -966, -197, 921, 78],
    poly [1, 0, 0, 1, 0, 0, 0, 0, -1, -1, -1],
    poly [19885, -5085, 16749, 11390, 4065, 1921, 9336, 22216, 16512, -6824, -2955, -5746, 26740, 8043,
      8780, -5555, 27733, 10836],
    poly [55546, -50461, -21834, -14526, 32295, -19690, -2056, -5555, 27733, 10836],
    poly [-641, 164, -540, -367, -131, -62, -301, -716, -532, 220, 95, 185, -862, -259, -283, 179, -894,
      -349],
    poly [-1790, 1627, 703, 468, -1041, 635, 66, 179, -894, -349],
    poly [-11853, 34344, -21675, -7642, 12005, 32399, 6126, -28575, -2432, -1],
    poly [-382, 1107, -699, -246, 387, 1044, 197, -921, -78],
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
theorem certificado_75583 :
    haveI : Fact (Nat.Prime 75583) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 75583 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((75583 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((75583 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((75583 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 75583) := ⟨by norm_num⟩
  have hP : poly [-158, 1] = X - C (158 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((75583 : ℕ) : ℤ[X]) = poly [75583] := by simp [poly]
  refine ⟨X - C (158 : ℤ),
    poly [35878, -16516, 26206, -6053, -20130, -11130, -22554, 36692, 29413, -29473, -13581, 11395,
      34515, -17003, -36464, 25123, 159, 1],
    poly [75, -35, 55, -13, -42, -23, -47, 77, 61, -62, -28, 24, 72, -36, -76, 53],
    poly [-1, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 1, -1],
    poly [6668, -7641, 10925, 12956, 6750, -1900, -998, -13430, 6583, 18669, 16832, 16342, -14277, 10883,
      8172, -1891, -21568, 4618],
    poly [82251, -89892, 18566, 8699, -20515, 9916, 2933, -11970, -9614, 45863, -30804, 4618],
    poly [-14, 16, -23, -27, -14, 4, 2, 28, -14, -39, -35, -34, 30, -23, -17, 4, 45, -10],
    poly [-172, 189, -40, -18, 43, -21, -6, 25, 20, -96, 65, -10],
    poly [-35878, -23189, 32861, -3619, -9112, 23861, -31900, -5464, 10968, -24806, -157, -1],
    poly [-75, -48, 69, -8, -19, 50, -67, -11, 23, -52],
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
theorem certificado_75659 :
    haveI : Fact (Nat.Prime 75659) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 75659 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((75659 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((75659 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((75659 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 75659) := ⟨by norm_num⟩
  have hP : poly [-2042, 1] = X - C (2042 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((75659 : ℕ) : ℤ[X]) = poly [75659] := by simp [poly]
  refine ⟨X - C (2042 : ℤ),
    poly [-27381, 34148, -14915, -7714, -4487, -15712, 35080, 7094, -3220, 24193, 6607, -21783, 27852,
      21170, 4790, 10562, 2043, 1],
    poly [-739, 922, -403, -208, -121, -424, 947, 191, -87, 653, 178, -588, 752, 571, 129, 285, 55],
    poly [1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1],
    poly [21898, 13461, -13109, 10665, -3477, -2817, -13858, 5885, 5413, 19270, 7902, 1820, -3963, 6001,
      3931, -6148, 24785, -1247],
    poly [53761, -67222, 26570, -45672, 22579, 4012, -4296, 20969, -23962, 11326, -30933, 26032, -1247],
    poly [-591, -363, 354, -288, 94, 76, 374, -159, -146, -520, -213, -49, 107, -162, -106, 166, -669,
      34],
    poly [-1451, 1815, -718, 1233, -610, -108, 116, -566, 647, -306, 835, -703, 34],
    poly [-27381, -14130, 26596, -20180, -10903, -12010, -31796, 1837, -14338, 5773, -8519, -2042, -1],
    poly [-739, -381, 718, -545, -294, -324, -858, 50, -387, 156, -230, -55],
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
theorem certificado_75773 :
    haveI : Fact (Nat.Prime 75773) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 75773 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((75773 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((75773 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((75773 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 75773) := ⟨by norm_num⟩
  have hP : poly [-407, 1] = X - C (407 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((75773 : ℕ) : ℤ[X]) = poly [75773] := by simp [poly]
  refine ⟨X - C (407 : ℤ),
    poly [16011, 3949, -16746, -24430, 24515, 10486, 37633, 20944, -22848, 3295, -2226, -32586, -22421,
      -13832, -4316, 14511, 408, 1],
    poly [86, 21, -90, -131, 132, 56, 202, 112, -123, 18, -12, -175, -120, -74, -23, 78, 2],
    poly [1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1],
    poly [-9399, -7188, -21518, -24532, -34779, -18607, -32158, -5196, -14997, -17069, -30851, -18225,
      -10747, -19665, 10101, -36928, -11910, -39030],
    poly [85172, -68585, 12119, 17344, 13261, 3474, -4832, 919, -4748, 19909, 14012, 27120, -39030],
    poly [51, 39, 116, 132, 187, 100, 173, 28, 81, 92, 166, 98, 58, 106, -54, 199, 64, 210],
    poly [-458, 369, -66, -93, -71, -19, 26, -5, 25, -107, -75, -146, 210],
    poly [16011, 3949, -32757, -28379, -34512, -24846, 1056, -10237, 23619, 19234, -14102, -407, -1],
    poly [86, 21, -176, -152, -185, -133, 6, -55, 127, 103, -76, -2],
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
theorem certificado_76001 :
    haveI : Fact (Nat.Prime 76001) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 76001 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((76001 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((76001 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((76001 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 76001) := ⟨by norm_num⟩
  have hP : poly [-463, 1] = X - C (463 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((76001 : ℕ) : ℤ[X]) = poly [76001] := by simp [poly]
  refine ⟨X - C (463 : ℤ),
    poly [-34143, 747, 10343, 6260, -13775, 16221, -19827, 29504, 3675, -36269, -6316, 9507, -36913,
      -30119, -17629, -13170, 464, 1],
    poly [-208, 5, 63, 38, -84, 99, -121, 180, 22, -221, -38, 58, -225, -183, -107, -80, 3],
    poly [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, -1],
    poly [-8929, -31765, -27054, 2503, 25876, 39715, 46475, 38118, 12821, -27286, -14569, -11751, -14043,
      11231, 26059, 55802, 45689, 30073],
    poly [84930, -53165, 4218, 2208, 3681, -25271, -55472, -35576, -14457, 30073],
    poly [54, 193, 164, -16, -158, -242, -283, -232, -78, 166, 88, 71, 85, -69, -159, -340, -278, -183],
    poly [-517, 325, -26, -13, -22, 154, 338, 216, 88, -183],
    poly [-34143, 34890, -24547, -3336, -9692, -5602, -8712, 14098, -462, -1],
    poly [-208, 213, -150, -20, -59, -34, -53, 86, -3],
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
theorem certificado_76039 :
    haveI : Fact (Nat.Prime 76039) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 76039 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((76039 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((76039 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((76039 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 76039) := ⟨by norm_num⟩
  have hP : poly [-3436, 1] = X - C (3436 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((76039 : ℕ) : ℤ[X]) = poly [76039] := by simp [poly]
  refine ⟨X - C (3436 : ℤ),
    poly [30960, -19045, -18285, 24205, 8505, -36822, -12647, -18770, -15917, 12521, 27622, -11566,
      -29370, -24241, 27390, 23488, 3437, 1],
    poly [1399, -861, -826, 1094, 384, -1664, -571, -848, -719, 566, 1248, -523, -1327, -1095, 1238,
      1061, 155],
    poly [1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, -1],
    poly [38723, 5517, 15997, 13610, 5222, 24517, 13701, 1305, 12632, 20580, 12704, -3409, 39231, 17910,
      21511, 7725, 15378, 16022],
    poly [37316, -42833, -10480, 2387, 8388, -58018, 5299, -3601, 13786, -7653, -644, 16022],
    poly [-1750, -249, -723, -615, -236, -1108, -619, -59, -571, -930, -574, 154, -1773, -809, -972,
      -349, -695, -724],
    poly [-1686, 1936, 473, -108, -379, 2622, -240, 163, -623, 346, 29, -724],
    poly [30960, 26034, 760, -33549, -15700, -14367, 5130, -24408, -3902, -20051, -3436, -1],
    poly [1399, 1176, 34, -1516, -709, -649, 232, -1103, -176, -906, -155],
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
theorem certificado_76343 :
    haveI : Fact (Nat.Prime 76343) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 76343 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((76343 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((76343 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((76343 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 76343) := ⟨by norm_num⟩
  have hP : poly [-4645, 1] = X - C (4645 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((76343 : ℕ) : ℤ[X]) = poly [76343] := by simp [poly]
  refine ⟨X - C (4645 : ℤ),
    poly [34794, -16691, -36096, -36018, -1602, -31951, 31122, 25038, 12595, 13184, -20558, -4064,
      -25969, 4432, -35697, -24398, 4646, 1],
    poly [2117, -1016, -2196, -2191, -97, -1944, 1894, 1523, 766, 802, -1251, -247, -1580, 270, -2172,
      -1484, 283],
    poly [-1, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, -1, 0, -1, -1],
    poly [-9299, -1527, -13589, 14168, -23940, -19412, 5308, -22134, -27087, 1444, -18141, -15269,
      -10650, -22121, -21351, -16338, 5095, -16283],
    poly [67044, -68571, -12062, 27757, -47407, 3001, 11131, -13274, -19594, 10646, -688, -42729, -55,
      5095, -16283],
    poly [566, 93, 827, -862, 1457, 1181, -323, 1347, 1648, -88, 1104, 929, 648, 1346, 1299, 994, -310,
      991],
    poly [-4079, 4173, 733, -1689, 2885, -183, -677, 808, 1192, -648, 42, 2600, 3, -310, 991],
    poly [-34794, -24858, 19405, -78, 7133, -29303, -26977, -34241, -27504, 14671, -33476, -36001, 24399,
      -4646, -1],
    poly [-2117, -1512, 1181, -5, 434, -1783, -1641, -2083, -1673, 893, -2037, -2190, 1485, -283],
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
theorem certificado_76837 :
    haveI : Fact (Nat.Prime 76837) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 76837 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((76837 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((76837 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((76837 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 76837) := ⟨by norm_num⟩
  have hP : poly [-2660, 1] = X - C (2660 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((76837 : ℕ) : ℤ[X]) = poly [76837] := by simp [poly]
  refine ⟨X - C (2660 : ℤ),
    poly [26373, 19768, 23954, -35492, 28555, 24795, -9292, -25741, -37966, -36093, -26531, -26123,
      -29127, -23582, 35781, 9257, 2661, 1],
    poly [913, 684, 829, -1229, 989, 858, -322, -891, -1314, -1249, -918, -904, -1008, -816, 1239, 320,
      92],
    poly [-1, -1, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1],
    poly [7015, 23916, 25280, 12224, 31515, 7749, 29058, 32619, 13180, 21463, 21495, 22766, 3615, 23337,
      4684, 29779, -3575, 11491],
    poly [83852, -52921, 25280, 12224, 24500, -16167, 3778, 27410, -1434, 15078, -13604, 33354, -15066,
      11491],
    poly [-243, -828, -875, -423, -1091, -268, -1006, -1129, -456, -743, -744, -788, -125, -808, -162,
      -1031, 124, -398],
    poly [-2903, 1833, -876, -423, -848, 560, -131, -949, 50, -522, 471, -1155, 522, -398],
    poly [-26373, -19768, -23954, 35492, -2182, -5027, 33246, -36124, -3711, -20135, -26525, -6596,
      -2660, -1],
    poly [-913, -684, -829, 1229, -76, -174, 1151, -1251, -128, -697, -918, -228, -92],
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
theorem certificado_76913 :
    haveI : Fact (Nat.Prime 76913) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 76913 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((76913 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((76913 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((76913 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 76913) := ⟨by norm_num⟩
  have hP : poly [-2153, 1] = X - C (2153 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((76913 : ℕ) : ℤ[X]) = poly [76913] := by simp [poly]
  refine ⟨X - C (2153 : ℤ),
    poly [-22363, -37806, 26668, -29281, 3916, 24151, -16636, -25050, 18779, -12566, 4281, 33868, 5410,
      -22682, -18694, 22783, 2154, 1],
    poly [-626, -1058, 747, -820, 110, 676, -466, -701, 526, -352, 120, 948, 151, -635, -523, 638, 60],
    poly [-1, 0, 0, -1, 0, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1],
    poly [-6758, -1867, 5280, 8427, 9393, -502, -3686, 13960, -9145, -4726, -15834, 4952, -19902, 20347,
      -4105, 27249, -19070, 13417],
    poly [70155, -72022, 7147, -3611, 5857, -2748, -37, 11854, -34867, 6515, 14965, 13832, -19070, 13417],
    poly [189, 52, -148, -236, -263, 14, 103, -391, 256, 132, 443, -139, 557, -570, 115, -763, 534, -376],
    poly [-1964, 2017, -201, 101, -164, 77, 1, -332, 976, -183, -419, -387, 534, -376],
    poly [22363, 15443, 12439, 1399, -17754, -7796, 19823, -2420, -26258, -31449, 20848, -22782, -2154,
      -1],
    poly [626, 432, 348, 39, -497, -218, 555, -68, -735, -880, 584, -638, -60],
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
theorem certificado_77141 :
    haveI : Fact (Nat.Prime 77141) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 77141 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((77141 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((77141 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((77141 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 77141) := ⟨by norm_num⟩
  have hP : poly [-2723, 1] = X - C (2723 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((77141 : ℕ) : ℤ[X]) = poly [77141] := by simp [poly]
  refine ⟨X - C (2723 : ℤ),
    poly [2408, -10481, 15549, -26199, -11738, 33906, -28062, 188, 12550, 21280, -18208, 31184, -30471,
      15485, -26369, 11917, 2724, 1],
    poly [85, -370, 549, -925, -414, 1197, -991, 7, 443, 751, -643, 1101, -1076, 547, -931, 421, 96],
    poly [-1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 1, -1],
    poly [-23999, -13016, -717, 5435, 2491, -5329, 2827, 34134, 13635, 4987, 1301, 5974, 15976, -848,
      12319, 11134, 10397, 10850],
    poly [53142, -66158, 12299, 6152, -2944, 16179, -26826, 29991, -14352, 448, 1190, -11303, 10850],
    poly [847, 459, 25, -192, -88, 188, -100, -1205, -481, -176, -46, -211, -564, 30, -435, -393, -367,
      -383],
    poly [-1876, 2336, -435, -217, 104, -571, 947, -1059, 507, -16, -42, 399, -383],
    poly [-2408, 12889, -26030, -35393, -14461, 33905, -30470, 10669, -2999, -29662, -6470, -2722, -1],
    poly [-85, 455, -919, -1249, -510, 1197, -1076, 377, -106, -1047, -228, -96],
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
theorem certificado_77369 :
    haveI : Fact (Nat.Prime 77369) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 77369 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((77369 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((77369 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((77369 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 77369) := ⟨by norm_num⟩
  have hP : poly [-9007, 1] = X - C (9007 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((77369 : ℕ) : ℤ[X]) = poly [77369] := by simp [poly]
  refine ⟨X - C (9007 : ℤ),
    poly [-18494, 1819, -33423, 34854, 10243, 16236, -18999, 23998, 11934, 32514, -16446, -33279, -9925,
      25193, -15270, -25024, 9008, 1],
    poly [-2153, 212, -3891, 4058, 1192, 1890, -2212, 2794, 1389, 3785, -1915, -3874, -1155, 2933, -1778,
      -2913, 1049],
    poly [-1, -1, 0, -1, -1, -1, 0, 0, -1, 0, -1, -1, -1],
    poly [461, 15605, 12961, 12033, 25519, -2053, 20458, 16303, 1150, -7914, 21093, -95, 23018, 11115,
      -8162, -648, 8544, 25699],
    poly [77830, -61764, 12500, -3111, 28163, -1125, 6511, 28270, -33861, -648, 8544, 25699],
    poly [-54, -1817, -1509, -1401, -2971, 239, -2382, -1898, -134, 921, -2456, 11, -2680, -1294, 950,
      75, -995, -2992],
    poly [-9061, 7191, -1456, 362, -3279, 131, -758, -3291, 3942, 75, -995, -2992],
    poly [18494, -1819, 14929, -14541, 31884, -25328, -24106, -16186, 15271, 25024, -9008, -1],
    poly [2153, -212, 1738, -1693, 3712, -2949, -2806, -1884, 1778, 2913, -1049],
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
theorem certificado_77521 :
    haveI : Fact (Nat.Prime 77521) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 77521 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((77521 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((77521 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((77521 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 77521) := ⟨by norm_num⟩
  have hP : poly [-269, 1] = X - C (269 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((77521 : ℕ) : ℤ[X]) = poly [77521] := by simp [poly]
  refine ⟨X - C (269 : ℤ),
    poly [3170, 32000, 38159, -28100, 8541, -16971, 1666, -6622, -13281, 10037, -30510, -26338, 4513,
      38345, 2448, -4890, 270, 1],
    poly [11, 111, 132, -98, 30, -59, 6, -23, -46, 35, -106, -91, 16, 133, 8, -17, 1],
    poly [-1, 0, -1, 0, 1, 0, 0, -1, -1, 1, 0, 0, -1],
    poly [-20127, -17320, -595, 5519, 4389, 20523, 39603, 22383, 34999, 43115, 52367, 26465, 41066,
      35933, 28133, 24934, 10513, -12307],
    poly [57394, -74714, -3402, 8921, 35722, 19441, 1225, -27327, 15506, 14421, 22820, -12307],
    poly [70, 60, 2, -19, -15, -71, -137, -77, -121, -149, -181, -91, -142, -124, -97, -86, -36, 43],
    poly [-199, 260, 11, -31, -124, -67, -4, 95, -54, -50, -79, 43],
    poly [-3170, -28830, -9329, 37429, 37891, -34441, 28402, -35629, -7337, 5160, -269, -1],
    poly [-11, -100, -32, 130, 131, -120, 99, -124, -25, 18, -1],
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
theorem certificado_77711 :
    haveI : Fact (Nat.Prime 77711) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 77711 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((77711 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((77711 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((77711 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 77711) := ⟨by norm_num⟩
  have hP : poly [-265, 1] = X - C (265 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((77711 : ℕ) : ℤ[X]) = poly [77711] := by simp [poly]
  refine ⟨X - C (265 : ℤ),
    poly [-1173, 21696, 36738, -37104, -6005, 26663, 34704, -13945, 38363, 3957, -22272, -15333, -35541,
      -37670, 29476, -7220, 266, 1],
    poly [-4, 74, 125, -127, -20, 91, 118, -48, 131, 13, -76, -52, -121, -128, 101, -25, 1],
    poly [1, 1, 0, 0, 1, 1, 1, 1, -1],
    poly [2752, -33014, -22592, 1787, 706, -23931, -14640, 4163, -9842, -40686, -7372, -18683, 2095,
      -26565, 4118, 15084, -21824, -29881],
    poly [74959, -44697, 25344, -34801, -26050, 58732, 37938, -29881],
    poly [-9, 113, 77, -6, -2, 82, 50, -14, 34, 139, 25, 64, -7, 91, -14, -51, 75, 102],
    poly [-256, 153, -87, 119, 88, -201, -129, 102],
    poly [-1173, 21696, 37911, 18911, 33795, 7752, -264, -1],
    poly [-4, 74, 129, 64, 115, 26, -1],
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
theorem certificado_77863 :
    haveI : Fact (Nat.Prime 77863) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 77863 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((77863 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((77863 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((77863 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 77863) := ⟨by norm_num⟩
  have hP : poly [-25272, 1] = X - C (25272 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((77863 : ℕ) : ℤ[X]) = poly [77863] := by simp [poly]
  refine ⟨X - C (25272 : ℤ),
    poly [36402, 3332, -22371, 16427, -29275, -5929, 27624, -9664, -37567, -35396, -33193, -27909, 23396,
      -37159, -15579, -10932, 25273, 1],
    poly [11815, 1081, -7261, 5332, -9502, -1924, 8966, -3137, -12193, -11488, -10773, -9058, 7594,
      -12061, -5056, -3548, 8203],
    poly [-1, 1, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, -1],
    poly [-30033, -43150, -14032, -18449, -17910, -17112, -23009, -28706, 4319, -44874, -14562, -35413,
      -25835, -13677, -15901, -35373, -2518, -14548],
    poly [47830, -60947, 72268, -20418, -24162, 4676, -7234, -30631, 31502, -47403, 12030, -14548],
    poly [9748, 14005, 4554, 5988, 5813, 5554, 7468, 9317, -1402, 14565, 4726, 11494, 8385, 4439, 5161,
      11481, 817, 4722],
    poly [-15524, 19782, -23457, 6628, 7842, -1518, 2348, 9942, -10225, 15386, -3905, 4722],
    poly [-36402, -8391, 29035, -19708, -19066, -30250, 21954, -20078, -20625, 36204, -25272, -1],
    poly [-11815, -2723, 9424, -6397, -6188, -9818, 7126, -6517, -6694, 11751, -8203],
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
theorem certificado_77977 :
    haveI : Fact (Nat.Prime 77977) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 77977 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((77977 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((77977 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((77977 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 77977) := ⟨by norm_num⟩
  have hP : poly [-4396, 1] = X - C (4396 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((77977 : ℕ) : ℤ[X]) = poly [77977] := by simp [poly]
  refine ⟨X - C (4396 : ℤ),
    poly [5623, -31821, -22109, 29192, 592, 29818, -10441, -1315, -7947, 10783, 38920, -38075, -23494,
      19347, -4643, -9083, 4397, 1],
    poly [317, -1794, -1246, 1646, 33, 1681, -589, -74, -448, 608, 2194, -2147, -1324, 1091, -262, -512,
      248],
    poly [-1, -1, 0, -1, 0, 0, 0, 0, 1, -1, 0, -1, -1, 0, -1],
    poly [-31649, -12836, 16454, 6208, -5537, -9921, 579, -12332, -10366, 7550, 12166, 22739, -10766,
      -4583, 6150, 8689, 1683, 18036],
    poly [46328, -90813, 48103, -12605, -3178, 13161, -4130, -14156, 16320, -20080, -856, 25042, -16353,
      18036],
    poly [1784, 723, -928, -350, 312, 559, -33, 695, 584, -426, -686, -1282, 607, 258, -347, -490, -95,
      -1017],
    poly [-2612, 5120, -2713, 711, 179, -742, 233, 798, -920, 1132, 48, -1412, 922, -1017],
    poly [-5623, 31821, 27732, 11341, 14743, -10338, 37709, -18244, -26097, -14906, -8837, 13479, -4396,
      -1],
    poly [-317, 1794, 1563, 639, 831, -583, 2126, -1029, -1471, -840, -498, 760, -248],
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
theorem certificado_78167 :
    haveI : Fact (Nat.Prime 78167) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 78167 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((78167 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((78167 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((78167 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 78167) := ⟨by norm_num⟩
  have hP : poly [-2003, 1] = X - C (2003 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((78167 : ℕ) : ℤ[X]) = poly [78167] := by simp [poly]
  refine ⟨X - C (2003 : ℤ),
    poly [-26576, 6660, -504, 23844, 29866, -15478, 23017, 16441, 34077, 39081, -14849, 11583, -18414,
      6547, -33246, 27496, 2004, 1],
    poly [-681, 171, -13, 611, 765, -397, 590, 421, 873, 1001, -381, 297, -472, 168, -852, 705, 51],
    poly [0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1],
    poly [-1606, -3480, -14525, -29360, -9972, -31348, -2168, -9295, -17806, 9156, -5621, -8165, -3054,
      -27364, -39669, -6621, -7385, 11971],
    poly [78167, -78167, 0, 1606, 1874, 9439, 12961, -30433, 6541, -11398, -16123, 25040, -52404, 12735,
      -19356, 11971],
    poly [41, 89, 372, 752, 255, 803, 55, 238, 456, -235, 144, 209, 78, 701, 1016, 169, 189, -307],
    poly [-2003, 2004, -1, -41, -48, -242, -332, 780, -168, 292, 413, -642, 1343, -327, 496, -307],
    poly [0, 0, 0, -26576, 33236, 19412, -8888, 13186, 8475, -19118, 5532, 12881, -19428, -25493, -2003,
      -1],
    poly [0, 0, 0, -681, 852, 497, -228, 338, 217, -490, 142, 330, -498, -653, -51],
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
theorem certificado_78509 :
    haveI : Fact (Nat.Prime 78509) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 78509 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((78509 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((78509 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((78509 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 78509) := ⟨by norm_num⟩
  have hP : poly [-830, 1] = X - C (830 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((78509 : ℕ) : ℤ[X]) = poly [78509] := by simp [poly]
  refine ⟨X - C (830 : ℤ),
    poly [12202, -23538, 36956, 30786, 26995, -35533, -19339, -11374, -6162, -10696, -35673, -38257,
      9602, -15974, -10897, -16850, 831, 1],
    poly [129, -249, 391, 325, 285, -376, -204, -120, -65, -113, -377, -404, 102, -169, -115, -178, 9],
    poly [1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    poly [7181, 663, 3682, -13435, 14259, -5193, 15404, -1881, 34515, -22573, 33355, 127, 27707, -13879,
      14826, -14935, 24662, 6454],
    poly [71328, -71991, -10200, 16454, -24195, 33550, -31174, 1862, -38204, 50094, -54423, 33143,
      -18208, -6454],
    poly [-76, -7, -39, 142, -151, 55, -163, 20, -365, 239, -353, -1, -293, 147, -157, 158, -261, -68],
    poly [-754, 762, 107, -174, 256, -355, 330, -20, 404, -530, 576, -351, 193, 68],
    poly [12202, -35740, -5813, -29708, 20963, -8204, 6233, 32357, 13849, -21928, 6784, -17680, 830, 1],
    poly [129, -378, -61, -314, 222, -87, 66, 342, 146, -232, 72, -187, 9],
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
theorem certificado_78623 :
    haveI : Fact (Nat.Prime 78623) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 78623 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((78623 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((78623 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((78623 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 78623) := ⟨by norm_num⟩
  have hP : poly [-10147, 1] = X - C (10147 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((78623 : ℕ) : ℤ[X]) = poly [78623] := by simp [poly]
  refine ⟨X - C (10147 : ℤ),
    poly [-21773, 11388, 30832, 189, 4928, 33799, -27426, -26386, -25890, 2167, -13482, 12923, 37612,
      -32865, 35128, -24373, 10148, 1],
    poly [-2810, 1470, 3979, 24, 636, 4362, -3540, -3405, -3341, 280, -1740, 1668, 4854, -4242, 4534,
      -3146, 1310],
    poly [-1, 0, -1, 0, 0, -1, 0, 0, -1, 1, 0, -1],
    poly [-13009, 20703, 7751, 24556, 8379, 17598, 18366, -6669, -465, 4913, 30460, 7566, 6324, 10570,
      -1920, 10267, 5193, -5694],
    poly [65614, -44911, -25961, 50517, -29129, 13015, 18303, -28768, 10768, 10887, -5694],
    poly [1679, -2672, -1000, -3169, -1081, -2271, -2370, 861, 60, -634, -3931, -976, -816, -1364, 248,
      -1325, -670, 735],
    poly [-8468, 5797, 3350, -6520, 3760, -1680, -2362, 3713, -1390, -1405, 735],
    poly [21773, -33161, 2329, -2518, -24183, 23545, 23325, 29268, 34522, -10147, -1],
    poly [2810, -4280, 301, -325, -3121, 3039, 3010, 3777, 4455, -1310],
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
theorem certificado_78737 :
    haveI : Fact (Nat.Prime 78737) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 78737 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((78737 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((78737 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((78737 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 78737) := ⟨by norm_num⟩
  have hP : poly [-2963, 1] = X - C (2963 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((78737 : ℕ) : ℤ[X]) = poly [78737] := by simp [poly]
  refine ⟨X - C (2963 : ℤ),
    poly [34572, 39048, 12981, -22397, -34739, -22918, 25237, 25705, -12906, 18225, 13346, 35480, -15002,
      -35640, 25339, -36211, 2964, 1],
    poly [1301, 1469, 488, -843, -1307, -862, 950, 967, -486, 686, 502, 1335, -565, -1341, 954, -1363,
      112],
    poly [1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1],
    poly [2337, -8265, 3344, -20515, -15979, 9533, 20543, -2519, 6083, 7388, 7229, -7413, -4362, 24046,
      -10729, -4682, -14831, 4325],
    poly [76400, -70472, -1007, 12250, 16986, -19446, -50468, 46513, -1685, -13897, -8427, 9007, 14831,
      -4325],
    poly [-88, 311, -126, 772, 601, -359, -773, 95, -229, -278, -272, 279, 164, -905, 404, 176, 558,
      -163],
    poly [-2875, 2653, 37, -461, -639, 732, 1899, -1751, 64, 523, 317, -339, -558, 163],
    poly [34572, 39048, -21591, 17292, -13148, 3955, -10256, 17721, 2185, 3535, 22376, -36212, 2964, 1],
    poly [1301, 1469, -813, 651, -495, 149, -386, 667, 82, 133, 842, -1363, 112],
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
theorem certificado_78889 :
    haveI : Fact (Nat.Prime 78889) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 78889 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((78889 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((78889 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((78889 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 78889) := ⟨by norm_num⟩
  have hP : poly [-1509, 1] = X - C (1509 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((78889 : ℕ) : ℤ[X]) = poly [78889] := by simp [poly]
  refine ⟨X - C (1509 : ℤ),
    poly [31106, 21455, -26073, 35, -32047, -35205, -19262, 32923, -13623, -3564, -25044, 20895, 37707,
      38816, 16755, -9190, 1510, 1],
    poly [595, 410, -499, 1, -613, -673, -368, 630, -261, -68, -479, 400, 721, 742, 320, -176, 29],
    poly [-1, -1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1],
    poly [-14117, 13111, 11247, 9416, 6644, 6799, -2402, -5388, 24775, 1374, 4077, 20233, -5373, 31519,
      -11639, 6996, 23058, 2523],
    poly [64772, -65778, 25364, -3695, -4603, -2617, 5071, -39415, 43158, -18635, -16062, 20535, 2523],
    poly [270, -251, -215, -180, -127, -130, 46, 103, -474, -26, -78, -387, 103, -603, 223, -134, -441,
      -48],
    poly [-1239, 1259, -486, 71, 88, 50, -97, 754, -826, 357, 307, -393, -48],
    poly [-31106, -21455, -21710, 21420, 5974, 35240, 18321, 1110, -22061, -25945, 10700, -1509, -1],
    poly [-595, -410, -415, 410, 114, 674, 350, 21, -422, -496, 205, -29],
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
theorem certificado_79193 :
    haveI : Fact (Nat.Prime 79193) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 79193 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((79193 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((79193 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((79193 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 79193) := ⟨by norm_num⟩
  have hP : poly [-5982, 1] = X - C (5982 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((79193 : ℕ) : ℤ[X]) = poly [79193] := by simp [poly]
  refine ⟨X - C (5982 : ℤ),
    poly [36128, -16423, -26877, -16182, -22495, -22271, -37257, 13603, -20491, 38812, 27450, -22726,
      8032, 19184, -25481, -4929, 5983, 1],
    poly [2729, -1241, -2030, -1222, -1699, -1682, -2814, 1028, -1548, 2932, 2073, -1717, 607, 1449,
      -1925, -372, 452],
    poly [1, 1, 0, 0, 1, 0, 1, 0, 0, -1],
    poly [-15166, -34285, -24399, -25377, -12271, -10892, -19007, -12773, -9833, -28340, -33943, -26067,
      -29746, -688, -25704, 1828, -10188, -32166],
    poly [94359, -44908, 9233, -8908, 3038, 4634, 12016, 21978, -32166],
    poly [1146, 2590, 1843, 1917, 927, 823, 1436, 965, 743, 2141, 2564, 1969, 2247, 52, 1942, -138, 770,
      2430],
    poly [-7128, 3393, -698, 673, -230, -350, -908, -1660, 2430],
    poly [36128, -16423, 16188, 241, -38683, 20553, 10912, -5982, -1],
    poly [2729, -1241, 1223, 18, -2922, 1553, 824, -452],
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
theorem certificado_79231 :
    haveI : Fact (Nat.Prime 79231) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 79231 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((79231 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((79231 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((79231 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 79231) := ⟨by norm_num⟩
  have hP : poly [-2557, 1] = X - C (2557 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((79231 : ℕ) : ℤ[X]) = poly [79231] := by simp [poly]
  refine ⟨X - C (2557 : ℤ),
    poly [2200, -4709, -17261, 24751, -18303, 19452, -7460, 13383, 33532, -4139, -3565, 1331, 5547, 374,
      -28290, -35366, 2558, 1],
    poly [71, -152, -557, 799, -591, 628, -241, 432, 1082, -134, -115, 43, 179, 12, -913, -1141, 83],
    poly [-1, 0, 0, 0, 0, -1, 1, 0, 0, -1, -1, 0, 1],
    poly [14468, 35730, 5620, 10504, 41120, 32270, 11444, 33126, 29788, 4905, -1116, 13507, 10693, 21475,
      -8856, 6842, 15958, 6201],
    poly [93699, -57969, -30110, 4884, 30616, 5618, -14032, -29690, 31656, 15317, -9757, -6201],
    poly [-467, -1153, -181, -339, -1327, -1041, -369, -1069, -961, -158, 36, -436, -345, -693, 286,
      -221, -515, -200],
    poly [-3024, 1872, 971, -158, -988, -181, 453, 958, -1022, -494, 315, 200],
    poly [-2200, 6909, 12552, 37219, -36177, 39276, 36021, -15200, 4518, -37925, 2557, 1],
    poly [-71, 223, 405, 1201, -1168, 1268, 1162, -491, 146, -1224, 83],
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
theorem certificado_79687 :
    haveI : Fact (Nat.Prime 79687) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 79687 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((79687 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((79687 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((79687 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 79687) := ⟨by norm_num⟩
  have hP : poly [-439, 1] = X - C (439 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((79687 : ℕ) : ℤ[X]) = poly [79687] := by simp [poly]
  refine ⟨X - C (439 : ℤ),
    poly [-23416, -6225, 39194, -11891, -36694, 14801, -1963, -9625, 32107, 26938, 34187, -36226, -23317,
      1036, 10712, 33787, 440, 1],
    poly [-129, -34, 216, -66, -202, 82, -11, -53, 177, 148, 188, -200, -128, 6, 59, 186, 2],
    poly [1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, -1],
    poly [27401, 9493, -11241, 14306, 12549, -10871, -7657, 26839, -1944, 7974, 39944, -9901, -4932,
      6152, 8537, -4890, 33380, 3698],
    poly [52286, -89180, 38642, -32214, -33283, 36418, 33301, -40766, -6083, 13427, -38270, 29682, 3698],
    poly [-151, -52, 62, -79, -69, 60, 42, -148, 11, -44, -220, 55, 27, -34, -47, 27, -184, -20],
    poly [-288, 492, -214, 178, 183, -201, -183, 225, 33, -74, 211, -164, -20],
    poly [-23416, -6225, -17077, -29082, -2426, -13801, -33431, 24792, 9677, 23075, -33347, -439, -1],
    poly [-129, -34, -94, -160, -13, -76, -184, 137, 53, 127, -184, -2],
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
theorem certificado_79801 :
    haveI : Fact (Nat.Prime 79801) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 79801 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((79801 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((79801 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((79801 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 79801) := ⟨by norm_num⟩
  have hP : poly [-4731, 1] = X - C (4731 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((79801 : ℕ) : ℤ[X]) = poly [79801] := by simp [poly]
  refine ⟨X - C (4731 : ℤ),
    poly [-14405, -35830, 7313, -7960, -4168, 35708, -37911, 35684, 15374, 290, 13393, 32743, 24600,
      32155, 13366, -36988, 4732, 1],
    poly [-854, -2124, 434, -472, -247, 2117, -2248, 2116, 911, 17, 794, 1941, 1458, 1906, 792, -2193,
      281],
    poly [-1, -1, -1, 0, 0, 1, -1, 0, 0, -1, 0, -1],
    poly [-6354, -3977, 2079, 16266, 9640, 4106, 8035, 26371, 15141, 3618, 883, 24902, 1461, -28113,
      15956, 12946, -14161, -24203],
    poly [73447, -83778, 2079, 22620, 13617, 8381, -16962, 13052, 2904, 10042, -24203],
    poly [377, 236, -123, -964, -571, -243, -476, -1563, -897, -214, -52, -1476, -86, 1667, -946, -767,
      840, 1435],
    poly [-4354, 4968, -124, -1341, -807, -497, 1006, -774, -172, -595, 1435],
    poly [14405, 35830, -7313, -6445, -31662, 37001, 22931, 24716, -38082, -4731, -1],
    poly [854, 2124, -434, -382, -1877, 2194, 1359, 1465, -2258, -280],
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
theorem certificado_80447 :
    haveI : Fact (Nat.Prime 80447) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 80447 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((80447 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((80447 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((80447 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 80447) := ⟨by norm_num⟩
  have hP : poly [-10041, 1] = X - C (10041 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((80447 : ℕ) : ℤ[X]) = poly [80447] := by simp [poly]
  refine ⟨X - C (10041 : ℤ),
    poly [25013, 11163, 36431, -421, 16929, -27503, -25192, 11158, 602, 10776, -17625, 29578, -18889,
      30339, 12157, 31632, 10042, 1],
    poly [3122, 1393, 4547, -53, 2113, -3433, -3144, 1393, 75, 1345, -2200, 3692, -2358, 3787, 1517,
      3948, 1253],
    poly [-1, 0, 0, 0, 0, 0, 0, -1, -1, 0, -2, 0, -1],
    poly [-8560, 33253, 56131, 28228, 7795, 18633, 34129, 26327, 13331, -4048, 41738, 40012, 12411, 70,
      10364, 37389, 57205, 33564],
    poly [71887, -38634, 22878, -27903, -20433, 10838, 15496, -16362, 20257, 47312, 23641, 33564],
    poly [1068, -4151, -7006, -3523, -973, -2326, -4260, -3286, -1664, 505, -5210, -4994, -1549, -9,
      -1294, -4667, -7140, -4189],
    poly [-8973, 4823, -2856, 3483, 2550, -1353, -1934, 2042, -2529, -5905, -2951, -4189],
    poly [-25013, 13850, -25268, 36852, -17350, -36015, -2311, 19084, -607, -21592, -10041, -1],
    poly [-3122, 1729, -3154, 4600, -2166, -4495, -288, 2382, -76, -2695, -1253],
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
theorem certificado_80599 :
    haveI : Fact (Nat.Prime 80599) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 80599 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((80599 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((80599 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((80599 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 80599) := ⟨by norm_num⟩
  have hP : poly [-878, 1] = X - C (878 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((80599 : ℕ) : ℤ[X]) = poly [80599] := by simp [poly]
  refine ⟨X - C (878 : ℤ),
    poly [-34608, 33467, -16302, -21224, 24486, 39593, 16936, -29448, 3363, -32860, -1598, 33321, 8667,
      4049, 12122, -34227, 879, 1],
    poly [-377, 365, -178, -231, 267, 431, 184, -321, 37, -358, -17, 363, 94, 44, 132, -373, 10],
    poly [-1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, -1],
    poly [-23578, -26726, -2862, -15503, -3859, -23307, 2558, 5984, 11863, 40419, 1529, 19110, 20507,
      8483, 14528, -15116, 10003, -12459],
    poly [57021, -83747, 23864, -12641, -11934, -22596, 26151, -12363, 17809, -6681, 46061, -7934, -2657,
      10003, -12459],
    poly [257, 291, 31, 169, 42, 254, -28, -65, -129, -440, -16, -208, -223, -92, -158, 165, -109, 136],
    poly [-621, 913, -261, 138, 130, 246, -285, 135, -194, 73, -502, 87, 29, -109, 136],
    poly [34608, 12524, -30830, 4922, -11102, -2583, 26435, -16769, 5856, 38562, -39154, -11244, 34228,
      -879, -1],
    poly [377, 136, -336, 54, -121, -28, 288, -183, 64, 420, -427, -122, 373, -10],
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
theorem certificado_80713 :
    haveI : Fact (Nat.Prime 80713) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 80713 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((80713 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((80713 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((80713 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 80713) := ⟨by norm_num⟩
  have hP : poly [-6486, 1] = X - C (6486 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((80713 : ℕ) : ℤ[X]) = poly [80713] := by simp [poly]
  refine ⟨X - C (6486 : ℤ),
    poly [21516, -27685, 30036, 35931, -766, 37320, -22680, 13598, 31573, -22544, -6910, 23730, 37274,
      -1500, 10316, 23210, 6487, 1],
    poly [1729, -2225, 2414, 2887, -62, 2999, -1823, 1093, 2537, -1812, -555, 1907, 2995, -121, 829,
      1865, 521],
    poly [-1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1],
    poly [22659, -1865, 35638, 8951, 14161, 26158, 18880, 29108, -12902, 50084, 14578, 13129, 34595,
      11925, 30986, 17263, 33177, 12099],
    poly [103372, -82578, 12979, 10816, -44136, 41731, -32784, 29637, -36992, 8979, 12099],
    poly [-1821, 150, -2864, -719, -1138, -2102, -1517, -2339, 1037, -4025, -1171, -1055, -2780, -958,
      -2490, -1387, -2666, -972],
    poly [-8307, 6637, -1044, -869, 3547, -3354, 2635, -2382, 2973, -722, -972],
    poly [-21516, 27685, -8520, 17097, -28395, 30123, -1078, 29617, -10237, -6485, -1],
    poly [-1729, 2225, -685, 1374, -2282, 2421, -87, 2380, -823, -521],
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
theorem certificado_80789 :
    haveI : Fact (Nat.Prime 80789) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 80789 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((80789 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((80789 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((80789 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 80789) := ⟨by norm_num⟩
  have hP : poly [-635, 1] = X - C (635 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((80789 : ℕ) : ℤ[X]) = poly [80789] := by simp [poly]
  refine ⟨X - C (635 : ℤ),
    poly [34224, 30970, -12165, -17322, 32670, -24885, 20826, 5758, 16803, 24454, 13779, 27121, 29941,
      -19673, 27450, -84, 636, 1],
    poly [269, 243, -96, -136, 257, -196, 164, 45, 132, 192, 108, 213, 235, -155, 216, -1, 5],
    poly [-1, 0, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, -1],
    poly [8880, 27978, 1036, 19187, 5984, 12579, 29765, 21, 17277, 15523, 18192, 46695, 6409, 9399,
      39302, -6707, 27699, 16430],
    poly [89669, -61691, -26942, 18151, -4323, 25693, -9756, -11593, -4827, -23137, 27699, 16430],
    poly [-70, -220, -8, -151, -47, -99, -234, 0, -136, -122, -143, -367, -50, -74, -309, 53, -218, -129],
    poly [-705, 486, 211, -143, 34, -202, 77, 91, 38, 182, -218, -129],
    poly [-34224, 3254, -37654, 5157, -3427, -19980, -2576, 20225, -26813, 85, -636, -1],
    poly [-269, 26, -296, 41, -27, -157, -20, 159, -211, 1, -5],
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
theorem certificado_81017 :
    haveI : Fact (Nat.Prime 81017) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81017 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81017 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81017 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81017 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81017) := ⟨by norm_num⟩
  have hP : poly [-9011, 1] = X - C (9011 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81017 : ℕ) : ℤ[X]) = poly [81017] := by simp [poly]
  refine ⟨X - C (9011 : ℤ),
    poly [8892, 13820, 24241, -36860, -26770, 19786, -40313, -28137, 22600, -28148, 39395, 26060, -8008,
      2085, 21965, 28099, 9012, 1],
    poly [989, 1537, 2696, -4100, -2977, 2201, -4484, -3129, 2514, -3131, 4382, 2898, -891, 232, 2443,
      3125, 1002],
    poly [-1, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1],
    poly [-42517, -6675, 7139, -5177, -26289, -14774, -666, -34686, -46324, -19937, -27909, -30760,
      -37989, -4202, -27170, -39571, -34016, -8706],
    poly [38500, -2658, -22028, -68647, 27046, 3924, 26119, -12909, -14261, -25310, -8706],
    poly [4729, 742, -794, 576, 2924, 1643, 74, 3858, 5152, 2217, 3104, 3421, 4225, 467, 3022, 4401,
      3783, 968],
    poly [-4282, 296, 2450, 7635, -3009, -436, -2905, 1436, 1586, 2815, 968],
    poly [-8892, 3964, -5493, -18387, 4898, 25238, 794, -2877, -19088, -9011, -1],
    poly [-989, 441, -611, -2045, 545, 2807, 88, -320, -2123, -1002],
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
theorem certificado_81131 :
    haveI : Fact (Nat.Prime 81131) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81131 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81131 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81131 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81131 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81131) := ⟨by norm_num⟩
  have hP : poly [-5953, 1] = X - C (5953 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81131 : ℕ) : ℤ[X]) = poly [81131] := by simp [poly]
  refine ⟨X - C (5953 : ℤ),
    poly [20402, -19172, 34995, 5212, -33212, 5514, -28660, 30605, 1368, 19530, 3683, 7142, 20594, 39063,
      6889, -10084, 5954, 1],
    poly [1497, -1407, 2568, 382, -2437, 405, -2103, 2246, 100, 1433, 270, 524, 1511, 2866, 505, -740,
      437],
    poly [-1, 1, -1, -1, 0, 1, -1],
    poly [-8022, 15595, 18570, 8608, 20177, -482, 8891, 6712, 2882, 13389, -2323, 5320, 6616, 14330,
      27442, 5325, -14263, -31193],
    poly [73109, -49492, -28664, 2658, 48123, -31193],
    poly [589, -1144, -1362, -631, -1480, 36, -652, -492, -211, -982, 171, -390, -485, -1051, -2013,
      -390, 1047, 2289],
    poly [-5364, 3632, 2103, -195, -3531, 2289],
    poly [-20402, -21155, -33012, 21991, -5952, -1],
    poly [-1497, -1552, -2422, 1614, -437],
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
theorem certificado_81283 :
    haveI : Fact (Nat.Prime 81283) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81283 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81283 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81283 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81283 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81283) := ⟨by norm_num⟩
  have hP : poly [-402, 1] = X - C (402 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81283 : ℕ) : ℤ[X]) = poly [81283] := by simp [poly]
  refine ⟨X - C (402 : ℤ),
    poly [-34980, -1098, 3839, -26276, -21296, -10365, 783, -38011, -32446, 39752, -18301, -19052,
      -34623, -30820, 19132, -559, 403, 1],
    poly [-173, -5, 19, -130, -105, -51, 4, -188, -160, 197, -91, -94, -171, -152, 95, -3, 2],
    poly [-1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1],
    poly [-32338, -67, -18791, -5897, -13144, 8473, -4616, 9303, 10753, 11161, -22807, -28553, -10774,
      2413, 2648, 13365, 16829, -5404],
    poly [48945, -16674, -50995, 31618, 12197, -3407, 16356, 14181, -18769, -16829, 5404],
    poly [160, 0, 93, 29, 65, -42, 23, -46, -53, -55, 113, 141, 53, -12, -13, -66, -83, 27],
    poly [-242, 83, 252, -157, -60, 17, -81, -70, 93, 83, -27],
    poly [34980, 12421, 28945, 35052, 11208, 27931, -30260, 18729, -560, 403, 1],
    poly [173, 61, 143, 173, 55, 138, -150, 93, -3, 2],
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
theorem certificado_81359 :
    haveI : Fact (Nat.Prime 81359) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81359 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81359 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81359 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81359 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81359) := ⟨by norm_num⟩
  have hP : poly [-662, 1] = X - C (662 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81359 : ℕ) : ℤ[X]) = poly [81359] := by simp [poly]
  refine ⟨X - C (662 : ℤ),
    poly [30356, 15654, -25908, -3849, 39076, -27839, 35107, -37554, 17272, -1080, 27159, 2499, -2700,
      -18316, 23446, 32112, 663, 1],
    poly [247, 127, -211, -31, 318, -227, 286, -306, 141, -9, 221, 20, -22, -149, 191, 261, 5],
    poly [-1, 0, 0, 0, -1, 0, 1, 0, -1, -1, 0, 0, -1, 0, -1],
    poly [13020, 19922, 2235, 20766, 9856, -18673, 22455, -5258, -1490, 7856, -487, -10946, 19640, 19932,
      24111, 5068, 18681, 4814],
    poly [94379, -74457, -17687, 18531, 2110, -21627, 10421, -16084, 23565, -17792, 32910, -8799, 13867,
      4814],
    poly [-106, -162, -18, -169, -80, 152, -183, 43, 12, -64, 4, 89, -160, -162, -196, -41, -152, -39],
    poly [-768, 607, 143, -151, -17, 176, -85, 131, -192, 145, -268, 72, -113, -39],
    poly [-30356, 14702, -39797, -22059, 8078, 258, 8972, 35900, -6951, 10313, 8004, -31450, -662, -1],
    poly [-247, 120, -324, -179, 66, 2, 73, 292, -57, 84, 65, -256, -5],
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
theorem certificado_81701 :
    haveI : Fact (Nat.Prime 81701) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81701 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81701 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81701 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81701 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81701) := ⟨by norm_num⟩
  have hP : poly [-3097, 1] = X - C (3097 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81701 : ℕ) : ℤ[X]) = poly [81701] := by simp [poly]
  refine ⟨X - C (3097 : ℤ),
    poly [33609, -14947, 7883, -31496, -17184, 26296, 11062, -9599, 9151, 214, 30971, 10, 24323, -19593,
      24686, 35490, 3098, 1],
    poly [1274, -567, 299, -1194, -651, 997, 419, -364, 347, 8, 1174, 0, 922, -743, 936, 1345, 117],
    poly [-1, -1, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1],
    poly [32835, 16727, 39673, 23298, 32737, 42369, 19843, 54711, 13542, 56028, 32431, 32397, 31289,
      14405, 55316, 23646, 20048, 27750],
    poly [114536, -64974, 6838, 39406, -23044, 9182, -13161, 31670, 3598, -7702, 27750],
    poly [-1245, -634, -1504, -883, -1241, -1606, -752, -2074, -513, -2124, -1229, -1228, -1186, -546,
      -2097, -896, -760, -1052],
    poly [-4342, 2464, -260, -1494, 874, -348, 499, -1201, -136, 292, -1052],
    poly [-33609, 14947, 25726, -17060, -8078, 34688, -37423, 10804, -32392, -3097, -1],
    poly [-1274, 567, 975, -647, -306, 1315, -1419, 410, -1228, -117],
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
theorem certificado_81853 :
    haveI : Fact (Nat.Prime 81853) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81853 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81853 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81853 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81853 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81853) := ⟨by norm_num⟩
  have hP : poly [-3917, 1] = X - C (3917 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81853 : ℕ) : ℤ[X]) = poly [81853] := by simp [poly]
  refine ⟨X - C (3917 : ℤ),
    poly [-4660, -29215, -25021, 38005, -31252, -22493, 31653, -786, 15965, -12137, -2657, -26477,
      -35009, -13571, 26849, 40296, 3918, 1],
    poly [-223, -1398, -1197, 1819, -1496, -1076, 1515, -38, 764, -581, -127, -1267, -1675, -649, 1285,
      1928, 187],
    poly [-1, -1, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0, -1, -1],
    poly [14264, 19868, 23401, 34728, 23363, 21354, -9344, 17020, 11907, 4550, 17337, 15773, 12450,
      -2513, 8663, 30315, 3886, 33511],
    poly [96117, -61985, 9137, 29124, 5566, 4423, -1512, -6562, 34102, -28942, 38288, -3196, 3886, 33511],
    poly [-683, -951, -1120, -1662, -1118, -1022, 447, -815, -570, -218, -830, -755, -596, 120, -415,
      -1451, -186, -1604],
    poly [-4600, 2967, -438, -1394, -266, -212, 72, 314, -1632, 1385, -1833, 153, -186, -1604],
    poly [4660, 29215, 20361, 19293, 30786, -20889, -14863, -13942, 21562, -31904, -22932, -40295, -3918,
      -1],
    poly [223, 1398, 974, 923, 1473, -1000, -711, -667, 1032, -1527, -1097, -1928, -187],
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
theorem certificado_81929 :
    haveI : Fact (Nat.Prime 81929) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81929 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81929 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81929 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81929 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81929) := ⟨by norm_num⟩
  have hP : poly [-11772, 1] = X - C (11772 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81929 : ℕ) : ℤ[X]) = poly [81929] := by simp [poly]
  refine ⟨X - C (11772 : ℤ),
    poly [14316, -29111, -5431, 13891, -7557, -27881, 624, 11393, 32767, -34531, 526, 21568, 37229,
      -7903, 9715, -32111, 11773, 1],
    poly [2057, -4183, -780, 1996, -1086, -4006, 90, 1637, 4708, -4962, 76, 3099, 5349, -1136, 1396,
      -4614, 1692],
    poly [-1, 0, 1, 0, 1, 0, 0, 0, 1, -1],
    poly [258, -6465, -26572, 8663, 21256, -16332, -16196, 3124, 10308, -14941, -21005, 28408, 6886,
      -19131, -8993, 33587, 10067, -5803],
    poly [82187, -88652, -20365, 41958, 32442, -66100, 7650, 21673, -5803],
    poly [-37, 929, 3818, -1245, -3054, 2347, 2327, -449, -1481, 2147, 3018, -4082, -989, 2749, 1292,
      -4826, -1446, 834],
    poly [-11809, 12739, 2925, -6029, -4661, 9498, -1100, -3114, 834],
    poly [-14316, -38502, -9364, 19180, -22485, -3781, -26273, -11771, -1],
    poly [-2057, -5532, -1345, 2756, -3231, -543, -3775, -1691],
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
theorem certificado_81967 :
    haveI : Fact (Nat.Prime 81967) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 81967 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((81967 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((81967 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((81967 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 81967) := ⟨by norm_num⟩
  have hP : poly [-2353, 1] = X - C (2353 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((81967 : ℕ) : ℤ[X]) = poly [81967] := by simp [poly]
  refine ⟨X - C (2353 : ℤ),
    poly [-6549, -27209, -2032, -35463, 40742, 10224, -16612, -28328, -35300, -39309, 17157, -22113,
      11103, 2269, 17105, -34793, 2354, 1],
    poly [-188, -781, -58, -1018, 1170, 293, -477, -813, -1013, -1128, 493, -635, 319, 65, 491, -999, 68],
    poly [-1, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0, -1],
    poly [16988, 42181, 31567, 28497, 4982, 21240, 19749, 9263, 24795, 22816, 13131, 28524, 17871, 5291,
      -4294, 10263, 16435, 27132],
    poly [98955, -39786, 14579, 3304, -1392, -883, 53878, -3925, 32813, -8149, -7284, 1878, 20960,
      -10697, 27132],
    poly [-488, -1211, -906, -818, -143, -610, -567, -266, -712, -655, -377, -819, -513, -152, 123, -295,
      -472, -779],
    poly [-2841, 1143, -419, -95, 40, 25, -1547, 113, -942, 234, 209, -54, -602, 307, -779],
    poly [6549, 27209, -4517, 14803, -22114, 17652, 36027, -35621, -3847, -23585, -32337, 27715, 37146,
      -2353, -1],
    poly [188, 781, -130, 425, -635, 507, 1034, -1023, -110, -677, -928, 796, 1066, -68],
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
theorem certificado_82499 :
    haveI : Fact (Nat.Prime 82499) := ⟨by norm_num⟩
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime 82499 (uff fact_prime_dezenove.out (by norm_num))) =
          P.natDegree ∧
        P * Q + ((82499 : ℕ) : ℤ[X]) * A = Φ19 ∧
        (((82499 : ℕ) : ℤ[X]) = G * Qp + Rp * Φ19 ∧ P = G * QP + RP * Φ19 ∧
          G = C1 * P + C2 * ((82499 : ℕ) : ℤ[X])) := by
  have : Fact (Nat.Prime 82499) := ⟨by norm_num⟩
  have hP : poly [-9406, 1] = X - C (9406 : ℤ) := by
    simp only [poly, C_0, C_1, map_neg, map_ofNat, mul_zero, add_zero] <;> ring
  have hc : ((82499 : ℕ) : ℤ[X]) = poly [82499] := by simp [poly]
  refine ⟨X - C (9406 : ℤ),
    poly [-15849, 2805, -26365, -17299, 38976, -37737, 8188, -15164, -30498, -17010, -607, 16191, 23420,
      4730, 40829, -39184, 9407, 1],
    poly [-1807, 320, -3006, -1972, 4444, -4303, 934, -1729, -3477, -1939, -69, 1846, 2670, 539, 4655,
      -4468, 1073],
    poly [0, 0, 1, -1, 1, 0, 1, -1, 0, -1, 0, -1],
    poly [-21059, 5804, -19848, -23324, -5116, -8026, -11675, -12877, -6106, -23726, -23991, -16527,
      -23157, 1699, 11718, -7726, -41917, 855],
    poly [82499, -82499, 21059, -47922, 73574, -49039, 25027, -23328, 35046, -42772, 855],
    poly [2401, -662, 2263, 2659, 583, 915, 1331, 1468, 696, 2705, 2735, 1884, 2640, -194, -1336, 881,
      4779, -98],
    poly [-9406, 9407, -2402, 5464, -8389, 5592, -2854, 2660, -3996, 4877, -98],
    poly [0, 0, -15849, 34503, 18826, -25609, 2190, -6920, -33909, -9406, -1],
    poly [0, 0, -1807, 3934, 2146, -2920, 250, -789, -3866, -1072],
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

end ATK.FermatDezenoveCertD

#print axioms ATK.FermatDezenoveCertD.certificado_59699
#print axioms ATK.FermatDezenoveCertD.certificado_60041
#print axioms ATK.FermatDezenoveCertD.certificado_60383
#print axioms ATK.FermatDezenoveCertD.certificado_60497
#print axioms ATK.FermatDezenoveCertD.certificado_60611
#print axioms ATK.FermatDezenoveCertD.certificado_60649
#print axioms ATK.FermatDezenoveCertD.certificado_60763
#print axioms ATK.FermatDezenoveCertD.certificado_60953
#print axioms ATK.FermatDezenoveCertD.certificado_61333
#print axioms ATK.FermatDezenoveCertD.certificado_61409
#print axioms ATK.FermatDezenoveCertD.certificado_61561
#print axioms ATK.FermatDezenoveCertD.certificado_61637
#print axioms ATK.FermatDezenoveCertD.certificado_61751
#print axioms ATK.FermatDezenoveCertD.certificado_61979
#print axioms ATK.FermatDezenoveCertD.certificado_62017
#print axioms ATK.FermatDezenoveCertD.certificado_62131
#print axioms ATK.FermatDezenoveCertD.certificado_62207
#print axioms ATK.FermatDezenoveCertD.certificado_62473
#print axioms ATK.FermatDezenoveCertD.certificado_62549
#print axioms ATK.FermatDezenoveCertD.certificado_62701
#print axioms ATK.FermatDezenoveCertD.certificado_62929
#print axioms ATK.FermatDezenoveCertD.certificado_63347
#print axioms ATK.FermatDezenoveCertD.certificado_63499
#print axioms ATK.FermatDezenoveCertD.certificado_63689
#print axioms ATK.FermatDezenoveCertD.certificado_63727
#print axioms ATK.FermatDezenoveCertD.certificado_63803
#print axioms ATK.FermatDezenoveCertD.certificado_63841
#print axioms ATK.FermatDezenoveCertD.certificado_64373
#print axioms ATK.FermatDezenoveCertD.certificado_64601
#print axioms ATK.FermatDezenoveCertD.certificado_65171
#print axioms ATK.FermatDezenoveCertD.certificado_65323
#print axioms ATK.FermatDezenoveCertD.certificado_65437
#print axioms ATK.FermatDezenoveCertD.certificado_65551
#print axioms ATK.FermatDezenoveCertD.certificado_66083
#print axioms ATK.FermatDezenoveCertD.certificado_66463
#print axioms ATK.FermatDezenoveCertD.certificado_66653
#print axioms ATK.FermatDezenoveCertD.certificado_66919
#print axioms ATK.FermatDezenoveCertD.certificado_67033
#print axioms ATK.FermatDezenoveCertD.certificado_67261
#print axioms ATK.FermatDezenoveCertD.certificado_67489
#print axioms ATK.FermatDezenoveCertD.certificado_67679
#print axioms ATK.FermatDezenoveCertD.certificado_68059
#print axioms ATK.FermatDezenoveCertD.certificado_68477
#print axioms ATK.FermatDezenoveCertD.certificado_68743
#print axioms ATK.FermatDezenoveCertD.certificado_68819
#print axioms ATK.FermatDezenoveCertD.certificado_69313
#print axioms ATK.FermatDezenoveCertD.certificado_69389
#print axioms ATK.FermatDezenoveCertD.certificado_69427
#print axioms ATK.FermatDezenoveCertD.certificado_69959
#print axioms ATK.FermatDezenoveCertD.certificado_69997
#print axioms ATK.FermatDezenoveCertD.certificado_70111
#print axioms ATK.FermatDezenoveCertD.certificado_70529
#print axioms ATK.FermatDezenoveCertD.certificado_71023
#print axioms ATK.FermatDezenoveCertD.certificado_71327
#print axioms ATK.FermatDezenoveCertD.certificado_71479
#print axioms ATK.FermatDezenoveCertD.certificado_71593
#print axioms ATK.FermatDezenoveCertD.certificado_71707
#print axioms ATK.FermatDezenoveCertD.certificado_71821
#print axioms ATK.FermatDezenoveCertD.certificado_72277
#print axioms ATK.FermatDezenoveCertD.certificado_72353
#print axioms ATK.FermatDezenoveCertD.certificado_72467
#print axioms ATK.FermatDezenoveCertD.certificado_72733
#print axioms ATK.FermatDezenoveCertD.certificado_72923
#print axioms ATK.FermatDezenoveCertD.certificado_73037
#print axioms ATK.FermatDezenoveCertD.certificado_73189
#print axioms ATK.FermatDezenoveCertD.certificado_73303
#print axioms ATK.FermatDezenoveCertD.certificado_73379
#print axioms ATK.FermatDezenoveCertD.certificado_73417
#print axioms ATK.FermatDezenoveCertD.certificado_73607
#print axioms ATK.FermatDezenoveCertD.certificado_73721
#print axioms ATK.FermatDezenoveCertD.certificado_74101
#print axioms ATK.FermatDezenoveCertD.certificado_74177
#print axioms ATK.FermatDezenoveCertD.certificado_74747
#print axioms ATK.FermatDezenoveCertD.certificado_74861
#print axioms ATK.FermatDezenoveCertD.certificado_75013
#print axioms ATK.FermatDezenoveCertD.certificado_75431
#print axioms ATK.FermatDezenoveCertD.certificado_75583
#print axioms ATK.FermatDezenoveCertD.certificado_75659
#print axioms ATK.FermatDezenoveCertD.certificado_75773
#print axioms ATK.FermatDezenoveCertD.certificado_76001
#print axioms ATK.FermatDezenoveCertD.certificado_76039
#print axioms ATK.FermatDezenoveCertD.certificado_76343
#print axioms ATK.FermatDezenoveCertD.certificado_76837
#print axioms ATK.FermatDezenoveCertD.certificado_76913
#print axioms ATK.FermatDezenoveCertD.certificado_77141
#print axioms ATK.FermatDezenoveCertD.certificado_77369
#print axioms ATK.FermatDezenoveCertD.certificado_77521
#print axioms ATK.FermatDezenoveCertD.certificado_77711
#print axioms ATK.FermatDezenoveCertD.certificado_77863
#print axioms ATK.FermatDezenoveCertD.certificado_77977
#print axioms ATK.FermatDezenoveCertD.certificado_78167
#print axioms ATK.FermatDezenoveCertD.certificado_78509
#print axioms ATK.FermatDezenoveCertD.certificado_78623
#print axioms ATK.FermatDezenoveCertD.certificado_78737
#print axioms ATK.FermatDezenoveCertD.certificado_78889
#print axioms ATK.FermatDezenoveCertD.certificado_79193
#print axioms ATK.FermatDezenoveCertD.certificado_79231
#print axioms ATK.FermatDezenoveCertD.certificado_79687
#print axioms ATK.FermatDezenoveCertD.certificado_79801
#print axioms ATK.FermatDezenoveCertD.certificado_80447
#print axioms ATK.FermatDezenoveCertD.certificado_80599
#print axioms ATK.FermatDezenoveCertD.certificado_80713
#print axioms ATK.FermatDezenoveCertD.certificado_80789
#print axioms ATK.FermatDezenoveCertD.certificado_81017
#print axioms ATK.FermatDezenoveCertD.certificado_81131
#print axioms ATK.FermatDezenoveCertD.certificado_81283
#print axioms ATK.FermatDezenoveCertD.certificado_81359
#print axioms ATK.FermatDezenoveCertD.certificado_81701
#print axioms ATK.FermatDezenoveCertD.certificado_81853
#print axioms ATK.FermatDezenoveCertD.certificado_81929
#print axioms ATK.FermatDezenoveCertD.certificado_81967
#print axioms ATK.FermatDezenoveCertD.certificado_82499
