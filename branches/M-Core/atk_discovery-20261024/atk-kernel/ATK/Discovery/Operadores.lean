import ATK.Discovery.Truncamento

/-!
# ATK-Discovery — Operadores e operações do truncamento

Sobre `P_N(x) = ⌊10ᴺx⌋/10ᴺ` e `T_N(x) = x − P_N(x)` (`ATK.Discovery.Truncamento`):

* **operador dígito** `d_{N+1}(x) = ⌊10ᴺ⁺¹x⌋ − 10⌊10ᴺx⌋ ∈ {0, …, 9}` e as leis de refinamento
  `P_{N+1} = P_N + d_{N+1}/10ᴺ⁺¹`, `T_N = d_{N+1}/10ᴺ⁺¹ + T_{N+1}` (`digito_nonneg`, `digito_le_nove`,
  `P_succ`, `T_succ`);
* **equivalência observacional na precisão `N`** (`indist N a b ↔ P_N a = P_N b`): é uma relação de
  equivalência, fica mais fina com `N` (`indist_mono`), e dois valores podem ser indistinguíveis em `N`
  e distinguíveis em `N + 1` (`indist_depois_dist`);
* **classe observacional do zero** `P_N(x) = 0 ↔ 0 ≤ x < 10⁻ᴺ` (`P_eq_zero_iff`) e a positividade da
  cauda oculta: `P_N(X) = 0 ∧ T_N(X) > 0 ⟹ X > 0` (`pos_de_cauda`);
* **operações**: translação por múltiplos de `10⁻ᴺ` preserva a cauda (`P_transl`, `T_transl`); a soma
  tem transporte `c ∈ {0, 1}` com `P_N(a + b) = P_N a + P_N b + c/10ᴺ` e
  `T_N(a + b) = T_N a + T_N b − c/10ᴺ`, e `c = 1 ↔ T_N a + T_N b ≥ 10⁻ᴺ` (`vaiUm_*`, `P_add`, `T_add`);
* **valores**: `P₂(1,23456789) = 1,23` e `T₂ = 0,00456789`; `A = 1` e `B = 1,08` têm `P₀` iguais,
  caudas `0` e `0,08`, e `A < B` pela cauda (`valor_123`, `valor_A_B`).

Nada aqui atribui caudas a quantidades exatas: contagens naturais têm cauda `0`
(`ATK.Discovery.Truncamento.natural_sem_cauda`).
-/

namespace ATK.Discovery.Operadores

open ATK.Discovery.Truncamento (P T reconstrucao cauda_nonneg cauda_lt dez_pow_pos lt_iff_cauda_de_P_eq)

theorem pot_succ_mul (N : ℕ) (x : ℝ) : (10 : ℝ) ^ (N + 1) * x = 10 * ((10 : ℝ) ^ N * x) := by ring

/-! ## O operador dígito -/

/-- Dígito de ordem `N + 1`: `d_{N+1}(x) = ⌊10ᴺ⁺¹x⌋ − 10⌊10ᴺx⌋`. -/
noncomputable def digito (N : ℕ) (x : ℝ) : ℤ := ⌊(10 : ℝ) ^ (N + 1) * x⌋ - 10 * ⌊(10 : ℝ) ^ N * x⌋

theorem digito_nonneg (N : ℕ) (x : ℝ) : 0 ≤ digito N x := by
  unfold digito
  rw [pot_succ_mul]
  have h : (((10 * ⌊(10 : ℝ) ^ N * x⌋ : ℤ)) : ℝ) ≤ 10 * ((10 : ℝ) ^ N * x) := by
    push_cast
    linarith [Int.floor_le ((10 : ℝ) ^ N * x)]
  have := Int.le_floor.mpr h
  omega

theorem digito_le_nove (N : ℕ) (x : ℝ) : digito N x ≤ 9 := by
  unfold digito
  rw [pot_succ_mul]
  have h1 := Int.lt_floor_add_one ((10 : ℝ) ^ N * x)
  have h : 10 * ((10 : ℝ) ^ N * x) < (((10 * ⌊(10 : ℝ) ^ N * x⌋ + 10 : ℤ)) : ℝ) := by
    push_cast
    linarith
  have := Int.floor_lt.mpr h
  omega

/-- O dígito é o resto de `⌊10ᴺ⁺¹x⌋` por `10`. -/
theorem digito_eq_emod (N : ℕ) (x : ℝ) : digito N x = ⌊(10 : ℝ) ^ (N + 1) * x⌋ % 10 := by
  have h0 := digito_nonneg N x
  have h9 := digito_le_nove N x
  have hF : ⌊(10 : ℝ) ^ (N + 1) * x⌋ = digito N x + 10 * ⌊(10 : ℝ) ^ N * x⌋ := by
    unfold digito; ring
  rw [hF, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 (by omega)]

/-- **Refinamento**: `P_{N+1}(x) = P_N(x) + d_{N+1}(x)/10ᴺ⁺¹`. -/
theorem P_succ (N : ℕ) (x : ℝ) :
    P (N + 1) x = P N x + (digito N x : ℝ) / (10 : ℝ) ^ (N + 1) := by
  have hd : ((⌊(10 : ℝ) ^ (N + 1) * x⌋ : ℤ) : ℝ) =
      10 * ((⌊(10 : ℝ) ^ N * x⌋ : ℤ) : ℝ) + (digito N x : ℝ) := by
    unfold digito; push_cast; ring
  have h10 : (10 : ℝ) ^ N ≠ 0 := (dez_pow_pos N).ne'
  unfold P
  rw [hd, pow_succ]
  field_simp

/-- **Cauda em cascata**: `T_N(x) = d_{N+1}(x)/10ᴺ⁺¹ + T_{N+1}(x)`. -/
theorem T_succ (N : ℕ) (x : ℝ) :
    T N x = (digito N x : ℝ) / (10 : ℝ) ^ (N + 1) + T (N + 1) x := by
  unfold T
  rw [P_succ]
  ring

/-! ## Equivalência observacional na precisão `N` -/

/-- `a ∼_N b`: mesma observação na precisão `N`. -/
def indist (N : ℕ) (a b : ℝ) : Prop := P N a = P N b

theorem indist_equivalence (N : ℕ) : Equivalence (indist N) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

theorem floor_eq_of_P_eq {N : ℕ} {a b : ℝ} (h : P N a = P N b) :
    ⌊(10 : ℝ) ^ N * a⌋ = ⌊(10 : ℝ) ^ N * b⌋ := by
  unfold P at h
  have h10 : (10 : ℝ) ^ N ≠ 0 := (dez_pow_pos N).ne'
  have h' : ((⌊(10 : ℝ) ^ N * a⌋ : ℤ) : ℝ) = ((⌊(10 : ℝ) ^ N * b⌋ : ℤ) : ℝ) := by
    field_simp at h
    exact h
  exact_mod_cast h'

/-- A observação fica mais fina com a precisão: `a ∼_{N+1} b ⟹ a ∼_N b`. -/
theorem indist_mono {N : ℕ} {a b : ℝ} (h : indist (N + 1) a b) : indist N a b := by
  unfold indist at *
  have hF := floor_eq_of_P_eq h
  have hd : digito N a = digito N b := by rw [digito_eq_emod, digito_eq_emod, hF]
  have ha := P_succ N a
  have hb := P_succ N b
  rw [hd] at ha
  linarith

/-- Indistinguíveis na precisão `N`, distinguíveis em `N + 1`: `0` e `10⁻⁽ᴺ⁺¹⁾`. -/
theorem indist_depois_dist (N : ℕ) :
    indist N 0 (1 / (10 : ℝ) ^ (N + 1)) ∧ ¬ indist (N + 1) 0 (1 / (10 : ℝ) ^ (N + 1)) := by
  have h10 := dez_pow_pos N
  have h11 := dez_pow_pos (N + 1)
  refine ⟨?_, ?_⟩
  · unfold indist P
    have hx : (10 : ℝ) ^ N * (1 / (10 : ℝ) ^ (N + 1)) = 1 / 10 := by
      rw [pow_succ]; field_simp
    rw [hx, mul_zero, Int.floor_zero]
    have : ⌊(1 / 10 : ℝ)⌋ = 0 := by
      rw [Int.floor_eq_iff]; norm_num
    rw [this]
  · unfold indist P
    have hx : (10 : ℝ) ^ (N + 1) * (1 / (10 : ℝ) ^ (N + 1)) = 1 := by field_simp
    rw [hx, mul_zero, Int.floor_zero, Int.floor_one]
    intro h
    have : (0 : ℝ) = 1 / (10 : ℝ) ^ (N + 1) := by simpa using h
    have hpos : (0 : ℝ) < 1 / (10 : ℝ) ^ (N + 1) := by positivity
    linarith

/-! ## A classe observacional do zero -/

/-- `P_N(x) = 0 ↔ 0 ≤ x < 10⁻ᴺ`. -/
theorem P_eq_zero_iff (N : ℕ) (x : ℝ) : P N x = 0 ↔ 0 ≤ x ∧ x < 1 / (10 : ℝ) ^ N := by
  have h10 := dez_pow_pos N
  unfold P
  rw [div_eq_zero_iff, or_iff_left h10.ne', Int.cast_eq_zero, Int.floor_eq_iff]
  constructor
  · rintro ⟨h0, h1⟩
    push_cast at h0 h1
    refine ⟨?_, ?_⟩
    · by_contra hx
      push Not at hx
      have : (10 : ℝ) ^ N * x < 0 := mul_neg_of_pos_of_neg h10 hx
      linarith
    · rw [lt_div_iff₀ h10]; linarith
  · rintro ⟨h0, h1⟩
    push_cast
    refine ⟨by positivity, ?_⟩
    rw [lt_div_iff₀ h10] at h1
    linarith

/-- **Positividade da cauda oculta**: observação `0` e cauda positiva dão um valor positivo. -/
theorem pos_de_cauda {N : ℕ} {X : ℝ} (hP : P N X = 0) (hT : 0 < T N X) : 0 < X := by
  rw [reconstrucao N X, hP, zero_add]
  exact hT

/-! ## Operações -/

/-- Translação por `m/10ᴺ` (`m` inteiro) desloca a observação e preserva a cauda. -/
theorem P_transl (N : ℕ) (x : ℝ) (m : ℤ) :
    P N (x + m / (10 : ℝ) ^ N) = P N x + m / (10 : ℝ) ^ N := by
  have h10 := (dez_pow_pos N).ne'
  unfold P
  have : (10 : ℝ) ^ N * (x + m / (10 : ℝ) ^ N) = (10 : ℝ) ^ N * x + m := by field_simp
  rw [this, Int.floor_add_intCast]
  push_cast
  field_simp

theorem T_transl (N : ℕ) (x : ℝ) (m : ℤ) : T N (x + m / (10 : ℝ) ^ N) = T N x := by
  unfold T
  rw [P_transl]
  ring

/-- Transporte da soma na precisão `N`. -/
noncomputable def vaiUm (N : ℕ) (a b : ℝ) : ℤ :=
  ⌊(10 : ℝ) ^ N * a + (10 : ℝ) ^ N * b⌋ - ⌊(10 : ℝ) ^ N * a⌋ - ⌊(10 : ℝ) ^ N * b⌋

theorem vaiUm_nonneg (N : ℕ) (a b : ℝ) : 0 ≤ vaiUm N a b := by
  unfold vaiUm
  have := Int.le_floor_add ((10 : ℝ) ^ N * a) ((10 : ℝ) ^ N * b)
  omega

theorem vaiUm_le_one (N : ℕ) (a b : ℝ) : vaiUm N a b ≤ 1 := by
  unfold vaiUm
  have := Int.le_floor_add_floor ((10 : ℝ) ^ N * a) ((10 : ℝ) ^ N * b)
  omega

/-- `P_N(a + b) = P_N a + P_N b + c/10ᴺ`. -/
theorem P_add (N : ℕ) (a b : ℝ) :
    P N (a + b) = P N a + P N b + (vaiUm N a b : ℝ) / (10 : ℝ) ^ N := by
  have h10 := (dez_pow_pos N).ne'
  unfold P vaiUm
  rw [mul_add]
  push_cast
  field_simp
  ring

/-- `T_N(a + b) = T_N a + T_N b − c/10ᴺ`. -/
theorem T_add (N : ℕ) (a b : ℝ) :
    T N (a + b) = T N a + T N b - (vaiUm N a b : ℝ) / (10 : ℝ) ^ N := by
  unfold T
  rw [P_add]
  ring

/-- O transporte vale `1` exatamente quando as caudas somadas atingem `10⁻ᴺ`. -/
theorem vaiUm_eq_one_iff (N : ℕ) (a b : ℝ) :
    vaiUm N a b = 1 ↔ 1 / (10 : ℝ) ^ N ≤ T N a + T N b := by
  have h0 := vaiUm_nonneg N a b
  have h1 := vaiUm_le_one N a b
  have hT := T_add N a b
  have hlo := cauda_nonneg N (a + b)
  have hhi := cauda_lt N (a + b)
  have hpos := dez_pow_pos N
  have hq : 0 < 1 / (10 : ℝ) ^ N := by positivity
  rcases (show vaiUm N a b = 0 ∨ vaiUm N a b = 1 by omega) with h | h
  · rw [h] at hT
    simp only [Int.cast_zero, zero_div, sub_zero] at hT
    constructor
    · intro h'; omega
    · intro h'; rw [← hT] at h'; linarith
  · rw [h] at hT
    simp only [Int.cast_one] at hT
    refine ⟨fun _ => ?_, fun _ => h⟩
    have : T N a + T N b = T N (a + b) + 1 / (10 : ℝ) ^ N := by rw [hT]; ring
    rw [this]; linarith

/-! ## Valores -/

/-- `P₂(1,23456789) = 1,23` e `T₂(1,23456789) = 0,00456789`. -/
theorem valor_123 :
    P 2 (123456789 / 100000000 : ℝ) = 123 / 100 ∧
      T 2 (123456789 / 100000000 : ℝ) = 456789 / 100000000 := by
  have hP : P 2 (123456789 / 100000000 : ℝ) = 123 / 100 := by
    unfold P
    have : ⌊(10 : ℝ) ^ 2 * (123456789 / 100000000 : ℝ)⌋ = 123 := by
      rw [Int.floor_eq_iff]; norm_num
    rw [this]; norm_num
  refine ⟨hP, ?_⟩
  unfold T
  rw [hP]; norm_num

/-- `A = 1` e `B = 1,08`: `P₀` iguais (`1`), caudas `0` e `0,08`, e `A < B` decidido pela cauda. -/
theorem valor_A_B :
    P 0 (1 : ℝ) = 1 ∧ P 0 (27 / 25 : ℝ) = 1 ∧ T 0 (1 : ℝ) = 0 ∧ T 0 (27 / 25 : ℝ) = 2 / 25 ∧
      (1 : ℝ) < 27 / 25 := by
  have hA : P 0 (1 : ℝ) = 1 := by unfold P; norm_num
  have hB : P 0 (27 / 25 : ℝ) = 1 := by
    unfold P
    have : ⌊(10 : ℝ) ^ 0 * (27 / 25 : ℝ)⌋ = 1 := by
      rw [Int.floor_eq_iff]; norm_num
    rw [this]; norm_num
  have hTA : T 0 (1 : ℝ) = 0 := by unfold T; rw [hA]; ring
  have hTB : T 0 (27 / 25 : ℝ) = 2 / 25 := by unfold T; rw [hB]; norm_num
  refine ⟨hA, hB, hTA, hTB, ?_⟩
  rw [lt_iff_cauda_de_P_eq (hA.trans hB.symm), hTA, hTB]
  norm_num

end ATK.Discovery.Operadores

#print axioms ATK.Discovery.Operadores.pot_succ_mul
#print axioms ATK.Discovery.Operadores.digito_nonneg
#print axioms ATK.Discovery.Operadores.digito_le_nove
#print axioms ATK.Discovery.Operadores.digito_eq_emod
#print axioms ATK.Discovery.Operadores.P_succ
#print axioms ATK.Discovery.Operadores.T_succ
#print axioms ATK.Discovery.Operadores.indist_equivalence
#print axioms ATK.Discovery.Operadores.floor_eq_of_P_eq
#print axioms ATK.Discovery.Operadores.indist_mono
#print axioms ATK.Discovery.Operadores.indist_depois_dist
#print axioms ATK.Discovery.Operadores.P_eq_zero_iff
#print axioms ATK.Discovery.Operadores.pos_de_cauda
#print axioms ATK.Discovery.Operadores.P_transl
#print axioms ATK.Discovery.Operadores.T_transl
#print axioms ATK.Discovery.Operadores.vaiUm_nonneg
#print axioms ATK.Discovery.Operadores.vaiUm_le_one
#print axioms ATK.Discovery.Operadores.P_add
#print axioms ATK.Discovery.Operadores.T_add
#print axioms ATK.Discovery.Operadores.vaiUm_eq_one_iff
#print axioms ATK.Discovery.Operadores.valor_123
#print axioms ATK.Discovery.Operadores.valor_A_B
