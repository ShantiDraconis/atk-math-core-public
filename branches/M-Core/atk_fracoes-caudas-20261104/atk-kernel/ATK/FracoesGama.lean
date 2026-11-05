import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ATK — As partes imaginárias dos zeros como frações contínuas, com a cauda explícita (rodada 103)

Uma bola racional `|γ − c| ≤ r` determina os primeiros quocientes parciais de `γ` e põe o resto ("a cauda")
num intervalo racional explícito. `passo x = 1/(x − ⌊x⌋)`; `x = ⌊x⌋ + 1/passo x` (`descompoe`).

* `passo_intervalo`, `passo_iter`: um passo da fração contínua sobre um intervalo racional.
* `gama1_fc`, `gama2_fc`, `gama3_fc`: com as bolas de raio `10⁻⁶` dos três primeiros zeros (certificados em
  `ATK.TresZeros`; aqui como hipóteses), `γ₁ = [14; 7, 2, 2, 1, 2, 1, …]`, `γ₂ = [21; 45, 2, 1, 2, …]`,
  `γ₃ = [25; 92, …]`, cada um com a cauda num intervalo; `*_conv`: o último convergente aproxima `γ` a
  menos de `1/q²`. A ligação com `ζ` está em `ATK.Fracoes.GamaZeros`.
* `gigante1_fc`, `gigante2_fc`: o par mais próximo da janela de altura `3·10¹²` (bolas da Arb com raios
  `285·10⁻²⁰` e `449·10⁻²⁰`, hipóteses): 16 e 17 quocientes certificados a partir de um inteiro de 13
  dígitos — números gigantes e gigantemente pequenos na mesma fração.

Classificação: **ferramenta**. Nada aqui é sobre a parte real dos zeros: RH continua `OPEN_MATH`.
-/

namespace ATK.Fracoes.Gama

/-- Um passo da fração contínua. -/
noncomputable def passo (x : ℝ) : ℝ := (Int.fract x)⁻¹

/-- `x = ⌊x⌋ + 1/passo x`. -/
theorem descompoe (x : ℝ) : x = ⌊x⌋ + (passo x)⁻¹ := by
  rw [passo, inv_inv, Int.floor_add_fract]

/-- Um passo sobre um intervalo `[lo, hi] ⊂ (n, n + 1)`. -/
theorem passo_intervalo {x lo hi : ℝ} (n : ℤ) (hlo : (n : ℝ) < lo) (hhi : hi < n + 1)
    (h1 : lo ≤ x) (h2 : x ≤ hi) :
    ⌊x⌋ = n ∧ (hi - n)⁻¹ ≤ passo x ∧ passo x ≤ (lo - n)⁻¹ := by
  have hfl : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  have hfr : Int.fract x = x - n := by rw [Int.fract, hfl]
  refine ⟨hfl, ?_, ?_⟩ <;> rw [passo, hfr]
  · exact inv_anti₀ (by linarith) (by linarith)
  · exact inv_anti₀ (by linarith) (by linarith)

/-- O mesmo passo, na `j`-ésima iterada, com os novos extremos já calculados. -/
theorem passo_iter {x lo hi lo' hi' : ℝ} (n : ℤ) (j : ℕ) (hlo : (n : ℝ) < lo) (hhi : hi < n + 1)
    (h1 : lo ≤ passo^[j] x) (h2 : passo^[j] x ≤ hi) (e1 : (hi - n)⁻¹ = lo') (e2 : (lo - n)⁻¹ = hi') :
    ⌊passo^[j] x⌋ = n ∧ lo' ≤ passo^[j + 1] x ∧ passo^[j + 1] x ≤ hi' := by
  obtain ⟨h, a, b⟩ := passo_intervalo n hlo hhi h1 h2
  rw [Function.iterate_succ_apply']
  exact ⟨h, e1 ▸ a, e2 ▸ b⟩


/-- **Primeiro zero**: `[14; 7, 2, 2, 1, 2, 1, …]`, com a cauda `x_7 = passo^[7] γ` em
`[1.68458, 2.21447]`. -/
theorem gama1_fc {γ : ℝ} (h : |γ - 141347251417 / 10 ^ 10| ≤ 1 / 10 ^ 6) :
      ⌊passo^[0] γ⌋ = 14 ∧
      ⌊passo^[1] γ⌋ = 7 ∧
      ⌊passo^[2] γ⌋ = 2 ∧
      ⌊passo^[3] γ⌋ = 2 ∧
      ⌊passo^[4] γ⌋ = 1 ∧
      ⌊passo^[5] γ⌋ = 2 ∧
      ⌊passo^[6] γ⌋ = 1 ∧
      (36140203 / 21453481 : ℝ) ≤ passo^[7] γ ∧ passo^[7] γ ≤ (38960203 / 17593481 : ℝ) := by
  rw [abs_le] at h
  obtain ⟨ha, hb⟩ := h
  have l0 : (141347241417 / 10000000000 : ℝ) ≤ passo^[0] γ := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] γ ≤ (141347261417 / 10000000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ) (lo' := (10000000000 / 1347261417 : ℝ)) (hi' := (10000000000 / 1347241417 : ℝ)) 14 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ) (lo' := (1347241417 / 569310081 : ℝ)) (hi' := (1347261417 / 569170081 : ℝ)) 7 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  obtain ⟨f2, l3, u3⟩ := passo_iter (x := γ) (lo' := (569170081 / 208921255 : ℝ)) (hi' := (569310081 / 208621255 : ℝ)) 2 2
    (by norm_num) (by norm_num) l2 u2 (by norm_num) (by norm_num)
  obtain ⟨f3, l4, u4⟩ := passo_iter (x := γ) (lo' := (208621255 / 152067571 : ℝ)) (hi' := (208921255 / 151327571 : ℝ)) 2 3
    (by norm_num) (by norm_num) l3 u3 (by norm_num) (by norm_num)
  obtain ⟨f4, l5, u5⟩ := passo_iter (x := γ) (lo' := (151327571 / 57593684 : ℝ)) (hi' := (152067571 / 56553684 : ℝ)) 1 4
    (by norm_num) (by norm_num) l4 u4 (by norm_num) (by norm_num)
  obtain ⟨f5, l6, u6⟩ := passo_iter (x := γ) (lo' := (56553684 / 38960203 : ℝ)) (hi' := (57593684 / 36140203 : ℝ)) 2 5
    (by norm_num) (by norm_num) l5 u5 (by norm_num) (by norm_num)
  obtain ⟨f6, l7, u7⟩ := passo_iter (x := γ) (lo' := (36140203 / 21453481 : ℝ)) (hi' := (38960203 / 17593481 : ℝ)) 1 6
    (by norm_num) (by norm_num) l6 u6 (by norm_num) (by norm_num)
  exact ⟨f0, f1, f2, f3, f4, f5, f6, l7, u7⟩

/-- Convergente `2728/193`: `|γ − 2728/193| < 1/193²`. -/
theorem gama1_fc_conv {γ : ℝ} (h : |γ - 141347251417 / 10 ^ 10| ≤ 1 / 10 ^ 6) :
    |γ - 2728 / 193| < 1 / 193 ^ 2 := by
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]


/-- **Segundo zero**: `[21; 45, 2, 1, 2, …]`, com a cauda `x_5 = passo^[5] γ` em
`[3.28923, 106.053]`. -/
theorem gama2_fc {γ : ℝ} (h : |γ - 210220396388 / 10 ^ 10| ≤ 1 / 10 ^ 6) :
      ⌊passo^[0] γ⌋ = 21 ∧
      ⌊passo^[1] γ⌋ = 45 ∧
      ⌊passo^[2] γ⌋ = 2 ∧
      ⌊passo^[3] γ⌋ = 1 ∧
      ⌊passo^[4] γ⌋ = 2 ∧
      (6182808 / 1879711 : ℝ) ≤ passo^[5] γ ∧ passo^[5] γ ≤ (6862808 / 64711 : ℝ) := by
  rw [abs_le] at h
  obtain ⟨ha, hb⟩ := h
  have l0 : (52555096597 / 2500000000 : ℝ) ≤ passo^[0] γ := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] γ ≤ (52555101597 / 2500000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ) (lo' := (2500000000 / 55101597 : ℝ)) (hi' := (2500000000 / 55096597 : ℝ)) 21 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ) (lo' := (55096597 / 20653135 : ℝ)) (hi' := (55101597 / 20428135 : ℝ)) 45 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  obtain ⟨f2, l3, u3⟩ := passo_iter (x := γ) (lo' := (20428135 / 14245327 : ℝ)) (hi' := (20653135 / 13790327 : ℝ)) 2 2
    (by norm_num) (by norm_num) l2 u2 (by norm_num) (by norm_num)
  obtain ⟨f3, l4, u4⟩ := passo_iter (x := γ) (lo' := (13790327 / 6862808 : ℝ)) (hi' := (14245327 / 6182808 : ℝ)) 1 3
    (by norm_num) (by norm_num) l3 u3 (by norm_num) (by norm_num)
  obtain ⟨f4, l5, u5⟩ := passo_iter (x := γ) (lo' := (6182808 / 1879711 : ℝ)) (hi' := (6862808 / 64711 : ℝ)) 2 4
    (by norm_num) (by norm_num) l4 u4 (by norm_num) (by norm_num)
  exact ⟨f0, f1, f2, f3, f4, l5, u5⟩

/-- Convergente `7631/363`: `|γ − 7631/363| < 1/363²`. -/
theorem gama2_fc_conv {γ : ℝ} (h : |γ - 210220396388 / 10 ^ 10| ≤ 1 / 10 ^ 6) :
    |γ - 7631 / 363| < 1 / 363 ^ 2 := by
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]


/-- **Terceiro zero**: `[25; 92, …]`, com a cauda `x_2 = passo^[2] γ` em
`[9.08781, 10.7444]`. -/
theorem gama3_fc {γ : ℝ} (h : |γ - 250108575801 / 10 ^ 10| ≤ 1 / 10 ^ 6) :
      ⌊passo^[0] γ⌋ = 25 ∧
      ⌊passo^[1] γ⌋ = 92 ∧
      (108565801 / 11946308 : ℝ) ≤ passo^[2] γ ∧ passo^[2] γ ≤ (108585801 / 10106308 : ℝ) := by
  rw [abs_le] at h
  obtain ⟨ha, hb⟩ := h
  have l0 : (250108565801 / 10000000000 : ℝ) ≤ passo^[0] γ := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] γ ≤ (250108585801 / 10000000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ) (lo' := (10000000000 / 108585801 : ℝ)) (hi' := (10000000000 / 108565801 : ℝ)) 25 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ) (lo' := (108565801 / 11946308 : ℝ)) (hi' := (108585801 / 10106308 : ℝ)) 92 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  exact ⟨f0, f1, l2, u2⟩

/-- Convergente `2301/92`: `|γ − 2301/92| < 1/92²`. -/
theorem gama3_fc_conv {γ : ℝ} (h : |γ - 250108575801 / 10 ^ 10| ≤ 1 / 10 ^ 6) :
    |γ - 2301 / 92| < 1 / 92 ^ 2 := by
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]


/-- **Zero de altura `3·10¹²` (1)**: `[3000180519279; 2, 6, 1, 2, 170, 1, 1, 1, 1, 4, 8, 5, 1, 1, 5, …]`, com a cauda `x_16 = passo^[16] γ` em
`[8.29005, 13.1]`. -/
theorem gigante1_fc {γ : ℝ} (h : |γ - 300018051927946511944262498325 / 10 ^ 17| ≤ 285 / 10 ^ 20) :
      ⌊passo^[0] γ⌋ = 3000180519279 ∧
      ⌊passo^[1] γ⌋ = 2 ∧
      ⌊passo^[2] γ⌋ = 6 ∧
      ⌊passo^[3] γ⌋ = 1 ∧
      ⌊passo^[4] γ⌋ = 2 ∧
      ⌊passo^[5] γ⌋ = 170 ∧
      ⌊passo^[6] γ⌋ = 1 ∧
      ⌊passo^[7] γ⌋ = 1 ∧
      ⌊passo^[8] γ⌋ = 1 ∧
      ⌊passo^[9] γ⌋ = 1 ∧
      ⌊passo^[10] γ⌋ = 4 ∧
      ⌊passo^[11] γ⌋ = 8 ∧
      ⌊passo^[12] γ⌋ = 5 ∧
      ⌊passo^[13] γ⌋ = 1 ∧
      ⌊passo^[14] γ⌋ = 1 ∧
      ⌊passo^[15] γ⌋ = 5 ∧
      (225999550232 / 27261545769 : ℝ) ≤ passo^[16] γ ∧ passo^[16] γ ≤ (227780369768 / 17387844231 : ℝ) := by
  rw [abs_le] at h
  obtain ⟨ha, hb⟩ := h
  have l0 : (60003610385589302388852499664943 / 20000000000000000000 : ℝ) ≤ passo^[0] γ := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] γ ≤ (60003610385589302388852499665057 / 20000000000000000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ) (lo' := (20000000000000000000 / 9302388852499665057 : ℝ)) (hi' := (20000000000000000000 / 9302388852499664943 : ℝ)) 3000180519279 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ) (lo' := (9302388852499664943 / 1395222295000670114 : ℝ)) (hi' := (9302388852499665057 / 1395222295000669886 : ℝ)) 2 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  obtain ⟨f2, l3, u3⟩ := passo_iter (x := γ) (lo' := (1395222295000669886 / 931055082495645741 : ℝ)) (hi' := (1395222295000670114 / 931055082495644259 : ℝ)) 6 2
    (by norm_num) (by norm_num) l2 u2 (by norm_num) (by norm_num)
  obtain ⟨f3, l4, u4⟩ := passo_iter (x := γ) (lo' := (931055082495644259 / 464167212505025855 : ℝ)) (hi' := (931055082495645741 / 464167212505024145 : ℝ)) 1 3
    (by norm_num) (by norm_num) l3 u3 (by norm_num) (by norm_num)
  obtain ⟨f4, l5, u5⟩ := passo_iter (x := γ) (lo' := (464167212505024145 / 2720657485597451 : ℝ)) (hi' := (464167212505025855 / 2720657485592549 : ℝ)) 2 4
    (by norm_num) (by norm_num) l4 u4 (by norm_num) (by norm_num)
  obtain ⟨f5, l6, u6⟩ := passo_iter (x := γ) (lo' := (2720657485592549 / 1655439954292525 : ℝ)) (hi' := (2720657485597451 / 1655439953457475 : ℝ)) 170 5
    (by norm_num) (by norm_num) l5 u5 (by norm_num) (by norm_num)
  obtain ⟨f6, l7, u7⟩ := passo_iter (x := γ) (lo' := (1655439953457475 / 1065217532139976 : ℝ)) (hi' := (1655439954292525 / 1065217531300024 : ℝ)) 1 6
    (by norm_num) (by norm_num) l6 u6 (by norm_num) (by norm_num)
  obtain ⟨f7, l8, u8⟩ := passo_iter (x := γ) (lo' := (1065217531300024 / 590222422992501 : ℝ)) (hi' := (1065217532139976 / 590222421317499 : ℝ)) 1 7
    (by norm_num) (by norm_num) l7 u7 (by norm_num) (by norm_num)
  obtain ⟨f8, l9, u9⟩ := passo_iter (x := γ) (lo' := (590222421317499 / 474995110822477 : ℝ)) (hi' := (590222422992501 / 474995108307523 : ℝ)) 1 8
    (by norm_num) (by norm_num) l8 u8 (by norm_num) (by norm_num)
  obtain ⟨f9, l10, u10⟩ := passo_iter (x := γ) (lo' := (474995108307523 / 115227314684978 : ℝ)) (hi' := (474995110822477 / 115227310495022 : ℝ)) 1 9
    (by norm_num) (by norm_num) l9 u9 (by norm_num) (by norm_num)
  obtain ⟨f10, l11, u11⟩ := passo_iter (x := γ) (lo' := (115227310495022 / 14085868842389 : ℝ)) (hi' := (115227314684978 / 14085849567611 : ℝ)) 4 10
    (by norm_num) (by norm_num) l10 u10 (by norm_num) (by norm_num)
  obtain ⟨f11, l12, u12⟩ := passo_iter (x := γ) (lo' := (14085849567611 / 2540518144090 : ℝ)) (hi' := (14085868842389 / 2540359755910 : ℝ)) 8 11
    (by norm_num) (by norm_num) l11 u11 (by norm_num) (by norm_num)
  obtain ⟨f12, l13, u13⟩ := passo_iter (x := γ) (lo' := (2540359755910 / 1384070062839 : ℝ)) (hi' := (2540518144090 / 1383258847161 : ℝ)) 5 12
    (by norm_num) (by norm_num) l12 u12 (by norm_num) (by norm_num)
  obtain ⟨f13, l14, u14⟩ := passo_iter (x := γ) (lo' := (1383258847161 / 1157259296929 : ℝ)) (hi' := (1384070062839 / 1156289693071 : ℝ)) 1 13
    (by norm_num) (by norm_num) l13 u13 (by norm_num) (by norm_num)
  obtain ⟨f14, l15, u15⟩ := passo_iter (x := γ) (lo' := (1156289693071 / 227780369768 : ℝ)) (hi' := (1157259296929 / 225999550232 : ℝ)) 1 14
    (by norm_num) (by norm_num) l14 u14 (by norm_num) (by norm_num)
  obtain ⟨f15, l16, u16⟩ := passo_iter (x := γ) (lo' := (225999550232 / 27261545769 : ℝ)) (hi' := (227780369768 / 17387844231 : ℝ)) 5 15
    (by norm_num) (by norm_num) l15 u15 (by norm_num) (by norm_num)
  exact ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, l16, u16⟩

/-- Convergente `259849886030590292997/86611417`: `|γ − 259849886030590292997/86611417| < 1/86611417²`. -/
theorem gigante1_fc_conv {γ : ℝ} (h : |γ - 300018051927946511944262498325 / 10 ^ 17| ≤ 285 / 10 ^ 20) :
    |γ - 259849886030590292997 / 86611417| < 1 / 86611417 ^ 2 := by
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]


/-- **Zero de altura `3·10¹²` (2)**: `[3000180519279; 2, 7, 36, 1, 4, 1, 3, 1, 17, 1, 1, 1, 4, 3, 4, 1, …]`, com a cauda `x_17 = passo^[17] γ` em
`[3.75533, 4.93922]`. -/
theorem gigante2_fc {γ : ℝ} (h : |γ - 300018051927946678691400506282 / 10 ^ 17| ≤ 449 / 10 ^ 20) :
      ⌊passo^[0] γ⌋ = 3000180519279 ∧
      ⌊passo^[1] γ⌋ = 2 ∧
      ⌊passo^[2] γ⌋ = 7 ∧
      ⌊passo^[3] γ⌋ = 36 ∧
      ⌊passo^[4] γ⌋ = 1 ∧
      ⌊passo^[5] γ⌋ = 4 ∧
      ⌊passo^[6] γ⌋ = 1 ∧
      ⌊passo^[7] γ⌋ = 3 ∧
      ⌊passo^[8] γ⌋ = 1 ∧
      ⌊passo^[9] γ⌋ = 17 ∧
      ⌊passo^[10] γ⌋ = 1 ∧
      ⌊passo^[11] γ⌋ = 1 ∧
      ⌊passo^[12] γ⌋ = 1 ∧
      ⌊passo^[13] γ⌋ = 4 ∧
      ⌊passo^[14] γ⌋ = 3 ∧
      ⌊passo^[15] γ⌋ = 4 ∧
      ⌊passo^[16] γ⌋ = 1 ∧
      (1160600583088 / 309053968335 : ℝ) ≤ passo^[17] γ ∧ passo^[17] γ ≤ (1212243384912 / 245432091665 : ℝ) := by
  rw [abs_le] at h
  obtain ⟨ha, hb⟩ := h
  have l0 : (300018051927946678691400506281551 / 100000000000000000000 : ℝ) ≤ passo^[0] γ := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] γ ≤ (300018051927946678691400506282449 / 100000000000000000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ) (lo' := (100000000000000000000 / 46678691400506282449 : ℝ)) (hi' := (100000000000000000000 / 46678691400506281551 : ℝ)) 3000180519279 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ) (lo' := (46678691400506281551 / 6642617198987436898 : ℝ)) (hi' := (46678691400506282449 / 6642617198987435102 : ℝ)) 2 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  obtain ⟨f2, l3, u3⟩ := passo_iter (x := γ) (lo' := (6642617198987435102 / 180371007594236735 : ℝ)) (hi' := (6642617198987436898 / 180371007594223265 : ℝ)) 7 2
    (by norm_num) (by norm_num) l2 u2 (by norm_num) (by norm_num)
  obtain ⟨f3, l4, u4⟩ := passo_iter (x := γ) (lo' := (180371007594223265 / 149260925595399358 : ℝ)) (hi' := (180371007594236735 / 149260925594912642 : ℝ)) 36 3
    (by norm_num) (by norm_num) l3 u3 (by norm_num) (by norm_num)
  obtain ⟨f4, l5, u5⟩ := passo_iter (x := γ) (lo' := (149260925594912642 / 31110081999324093 : ℝ)) (hi' := (149260925595399358 / 31110081998823907 : ℝ)) 1 4
    (by norm_num) (by norm_num) l4 u4 (by norm_num) (by norm_num)
  obtain ⟨f5, l6, u6⟩ := passo_iter (x := γ) (lo' := (31110081998823907 / 24820597600103730 : ℝ)) (hi' := (31110081999324093 / 24820597597616270 : ℝ)) 4 5
    (by norm_num) (by norm_num) l5 u5 (by norm_num) (by norm_num)
  obtain ⟨f6, l7, u7⟩ := passo_iter (x := γ) (lo' := (24820597597616270 / 6289484401707823 : ℝ)) (hi' := (24820597600103730 / 6289484398720177 : ℝ)) 1 6
    (by norm_num) (by norm_num) l6 u6 (by norm_num) (by norm_num)
  obtain ⟨f7, l8, u8⟩ := passo_iter (x := γ) (lo' := (6289484398720177 / 5952144403943199 : ℝ)) (hi' := (6289484401707823 / 5952144392492801 : ℝ)) 3 7
    (by norm_num) (by norm_num) l7 u7 (by norm_num) (by norm_num)
  obtain ⟨f8, l9, u9⟩ := passo_iter (x := γ) (lo' := (5952144392492801 / 337340009215022 : ℝ)) (hi' := (5952144403943199 / 337339994776978 : ℝ)) 1 8
    (by norm_num) (by norm_num) l8 u8 (by norm_num) (by norm_num)
  obtain ⟨f9, l10, u10⟩ := passo_iter (x := γ) (lo' := (337339994776978 / 217364492734573 : ℝ)) (hi' := (337340009215022 / 217364235837427 : ℝ)) 17 9
    (by norm_num) (by norm_num) l9 u9 (by norm_num) (by norm_num)
  obtain ⟨f10, l11, u11⟩ := passo_iter (x := γ) (lo' := (217364235837427 / 119975773377595 : ℝ)) (hi' := (217364492734573 / 119975502042405 : ℝ)) 1 10
    (by norm_num) (by norm_num) l10 u10 (by norm_num) (by norm_num)
  obtain ⟨f11, l12, u12⟩ := passo_iter (x := γ) (lo' := (119975502042405 / 97388990692168 : ℝ)) (hi' := (119975773377595 / 97388462459832 : ℝ)) 1 11
    (by norm_num) (by norm_num) l11 u11 (by norm_num) (by norm_num)
  obtain ⟨f12, l13, u13⟩ := passo_iter (x := γ) (lo' := (97388462459832 / 22587310917763 : ℝ)) (hi' := (97388990692168 / 22586511350237 : ℝ)) 1 12
    (by norm_num) (by norm_num) l12 u12 (by norm_num) (by norm_num)
  obtain ⟨f13, l14, u14⟩ := passo_iter (x := γ) (lo' := (22586511350237 / 7042945291220 : ℝ)) (hi' := (22587310917763 / 7039218788780 : ℝ)) 4 13
    (by norm_num) (by norm_num) l13 u13 (by norm_num) (by norm_num)
  obtain ⟨f14, l15, u15⟩ := passo_iter (x := γ) (lo' := (7039218788780 / 1469654551423 : ℝ)) (hi' := (7042945291220 / 1457675476577 : ℝ)) 3 14
    (by norm_num) (by norm_num) l14 u14 (by norm_num) (by norm_num)
  obtain ⟨f15, l16, u16⟩ := passo_iter (x := γ) (lo' := (1457675476577 / 1212243384912 : ℝ)) (hi' := (1469654551423 / 1160600583088 : ℝ)) 4 15
    (by norm_num) (by norm_num) l15 u15 (by norm_num) (by norm_num)
  obtain ⟨f16, l17, u17⟩ := passo_iter (x := γ) (lo' := (1160600583088 / 309053968335 : ℝ)) (hi' := (1212243384912 / 245432091665 : ℝ)) 1 16
    (by norm_num) (by norm_num) l16 u16 (by norm_num) (by norm_num)
  exact ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, l17, u17⟩

/-- Convergente `212558034504827163898/70848415`: `|γ − 212558034504827163898/70848415| < 1/70848415²`. -/
theorem gigante2_fc_conv {γ : ℝ} (h : |γ - 300018051927946678691400506282 / 10 ^ 17| ≤ 449 / 10 ^ 20) :
    |γ - 212558034504827163898 / 70848415| < 1 / 70848415 ^ 2 := by
  rw [abs_le] at h
  rw [abs_lt]
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]


end ATK.Fracoes.Gama

#print axioms ATK.Fracoes.Gama.descompoe
#print axioms ATK.Fracoes.Gama.passo_intervalo
#print axioms ATK.Fracoes.Gama.passo_iter
#print axioms ATK.Fracoes.Gama.gama1_fc
#print axioms ATK.Fracoes.Gama.gama1_fc_conv
#print axioms ATK.Fracoes.Gama.gama2_fc
#print axioms ATK.Fracoes.Gama.gama2_fc_conv
#print axioms ATK.Fracoes.Gama.gama3_fc
#print axioms ATK.Fracoes.Gama.gama3_fc_conv
#print axioms ATK.Fracoes.Gama.gigante1_fc
#print axioms ATK.Fracoes.Gama.gigante1_fc_conv
#print axioms ATK.Fracoes.Gama.gigante2_fc
#print axioms ATK.Fracoes.Gama.gigante2_fc_conv
