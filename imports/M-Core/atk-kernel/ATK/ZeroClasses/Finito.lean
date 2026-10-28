import ATK.ZeroClasses.Rouche

/-!
# ATK-ZERO-CLASSES — o finito exato, a aritmética terminal e a faixa tolerante (rodada 26)

Três blocos, todos sem limites nem indeterminações onde o material enviado pede isso.

**1. SAT finito exato** (`Fpol_eval_zero`, `ordem_Fpol`, `codificacao_inteira`, `Zp_cotas`, `Zp_limite`,
`exemplo_A`, `exemplo_B`, `exemplo_C`). Para `r : ι → ℕ` num tipo finito:
* `F(z) = Σ z^{rᵢ}` tem `F(0) = N` e **`ord_{z=0} F = min rᵢ`** (o mínimo de cláusulas violadas — outra ordem
  de anulação, diferente de `ord₀ det(L + tI) = N`);
* **codificação inteira**: com `rᵢ ≤ m` e `B > |ι|`, `⌊(Σᵢ B^{m − rᵢ}) / B^m⌋ = N` — `#SAT` é o dígito principal de
  um inteiro, sem aproximação (ATK-FINITE-1);
* **função de partição**: `Z(τ) = Σ e^{−τ rᵢ}` satisfaz `μ − log|ι|/τ ≤ −log Z(τ)/τ ≤ μ` (`μ = min r`) e
  `−log Z(τ)/τ → μ`;
* os três casos enviados: `M_A = 704 = (1300)₈`, `M_B = 8 = (020)₄`, `M_C = 81 = (121)₈`, `det(L + I) = 8, 4, 20`,
  `#SAT = 1, 0, 1`.

**2. Aritmética terminal** (`satAdd_assoc`, `terminal_absorve`, `cancelamento_falha`, `colapso_congruencia`,
`zero_um_trivial`, `Ev_nao_aditivo`, `boxplus_tabela`, `boxplus_nao_assoc`, `arredonda_um_iff`, `E01_unifica`,
`E01_soma_mal_definida`). A soma saturada `min(Z, a + b)` é associativa, absorve (`Z ⊕ 1 = Z`) e **perde o
cancelamento**. Uma congruência com `0 ∼ 1` colapsa **todos** os naturais; num anel, `0 = 1` força o anel
trivial. O avaliador `E(1) = 0` não é aditivo e torna `⊞` **não associativa** (`(0⊞1)⊞1 = 0 ≠ 2 = 0⊞(1⊞1)`).
O estado intervalar "01" (`[0, 3/2)`) unifica `0` e `1`, mas a soma **não** fica bem definida nas classes.

**3. A faixa tolerante** (`Tol`, `exemplos_tolerancia`, `torcao_tol`, `fora_em_tol`, `tol_refuta`,
`rh_iff_tolerancias`, `tol_verificada`). `T_ε = {|Re s − ½| ≤ ε}` contém pontos fora da linha (`9/20 + 10i`,
`11/20 + 10i`), é invariante pela torção, e um zero de `ζ` em `T_ε` fora da linha refuta RH; RH ⟺ todo zero está
em toda `T_ε`. Com `VerificadoAte H` (Platt–Trudgian), nenhum ponto de `T_ε` fora da linha com `|t| ≤ H` é zero.
A tolerância **não** impõe zeros.
-/

open Complex Metric Set Filter Topology Polynomial
open scoped Real

namespace ATK.ZeroClasses.Finito

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Pontes ATK.ZeroClasses.Forcar

/-! ## 1. SAT finito exato -/

section Generico

variable {ι : Type*} [Fintype ι] (r : ι → ℕ)

/-- `F(X) = Σᵢ X^{rᵢ}` como polinômio. -/
noncomputable def Fpol : ℚ[X] := ∑ i, X ^ (r i)

theorem Fpol_eval_zero : (Fpol r).eval 0 = Nz r := by
  unfold Fpol Nz
  rw [eval_finsetSum, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : r i = 0
  · simp [h]
  · simp [h, zero_pow h]

/-- **`ord_{z=0} F = min rᵢ`**: o mínimo de cláusulas violadas. -/
theorem ordem_Fpol [Nonempty ι] : rootMultiplicity 0 (Fpol r) = Finset.univ.inf' Finset.univ_nonempty r := by
  classical
  set μ := Finset.univ.inf' Finset.univ_nonempty r with hμ
  have hle : ∀ i, μ ≤ r i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set q : ℚ[X] := ∑ i, X ^ (r i - μ) with hq
  have hfac : Fpol r = X ^ μ * q := by
    unfold Fpol; rw [hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_add, Nat.add_sub_cancel' (hle i)]
  have hq0 : q.eval 0 ≠ 0 := by
    obtain ⟨i0, hi0, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty r
    rw [hq, eval_finsetSum]
    have hnn : ∀ i, (0 : ℚ) ≤ (X ^ (r i - μ) : ℚ[X]).eval 0 := fun i => by
      simp only [eval_pow, eval_X]; exact pow_nonneg le_rfl _
    have hpos : (0 : ℚ) < (X ^ (r i0 - μ) : ℚ[X]).eval 0 := by
      rw [← hmin, Nat.sub_self]; simp
    have := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i0)
    linarith
  have hqne : q ≠ 0 := fun h => hq0 (by rw [h, eval_zero])
  rw [hfac, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hqne)]
  have h1 : rootMultiplicity 0 (X ^ μ : ℚ[X]) = μ := by
    simpa using rootMultiplicity_X_sub_C_pow (0 : ℚ) μ
  have h2 : rootMultiplicity 0 q = 0 := rootMultiplicity_eq_zero hq0
  rw [h1, h2, add_zero]

/-- **Codificação inteira (ATK-FINITE-1)**: `⌊(Σᵢ B^{m − rᵢ}) / B^m⌋ = N` se `rᵢ ≤ m` e `B > |ι|`. -/
theorem codificacao_inteira {B m : ℕ} (hB : Fintype.card ι < B) (hm : ∀ i, r i ≤ m) :
    (∑ i, B ^ (m - r i)) / B ^ m = Nz r := by
  classical
  have hB1 : 1 ≤ B := by omega
  have hBpos : 0 < B ^ m := pow_pos (by omega) m
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => r i = 0)]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i => r i = 0), B ^ (m - r i) = Nz r * B ^ m := by
    rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2, Nat.sub_zero],
      Finset.sum_const, smul_eq_mul]
    rfl
  set rest := ∑ i ∈ Finset.univ.filter (fun i => ¬ r i = 0), B ^ (m - r i) with hrest
  have hlt : rest < B ^ m := by
    by_cases hm0 : m = 0
    · have : Finset.univ.filter (fun i => ¬ r i = 0) = ∅ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_not]
        have := hm i; omega
      rw [hrest, this, Finset.sum_empty]; exact hBpos
    · have hterm : ∀ i ∈ Finset.univ.filter (fun i => ¬ r i = 0), B ^ (m - r i) ≤ B ^ (m - 1) := by
        intro i hi
        have := (Finset.mem_filter.mp hi).2
        exact Nat.pow_le_pow_right hB1 (by omega)
      have hs := Finset.sum_le_card_nsmul _ _ _ hterm
      have hc : (Finset.univ.filter (fun i => ¬ r i = 0)).card ≤ Fintype.card ι :=
        (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])
      calc rest ≤ (Finset.univ.filter (fun i => ¬ r i = 0)).card * B ^ (m - 1) := by
            simpa using hs
        _ ≤ Fintype.card ι * B ^ (m - 1) := Nat.mul_le_mul_right _ hc
        _ < B * B ^ (m - 1) := Nat.mul_lt_mul_of_pos_right hB (pow_pos (by omega) _)
        _ = B ^ m := by rw [← pow_succ']; congr 1; omega
  rw [h0, add_comm, Nat.add_mul_div_right _ _ hBpos, Nat.div_eq_of_lt hlt, zero_add]

/-- Função de partição `Z(τ) = Σᵢ e^{−τ rᵢ}`. -/
noncomputable def Zp (τ : ℝ) : ℝ := ∑ i, Real.exp (-τ * r i)

/-- **Cotas da função de partição**: `e^{−τμ} ≤ Z(τ) ≤ |ι| e^{−τμ}` para `τ ≥ 0`. -/
theorem Zp_cotas [Nonempty ι] {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.exp (-τ * (Finset.univ.inf' Finset.univ_nonempty r : ℕ)) ≤ Zp r τ ∧
      Zp r τ ≤ Fintype.card ι * Real.exp (-τ * (Finset.univ.inf' Finset.univ_nonempty r : ℕ)) := by
  set μ := Finset.univ.inf' Finset.univ_nonempty r
  obtain ⟨i0, -, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty r
  have hle : ∀ i, μ ≤ r i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hterm : ∀ i, Real.exp (-τ * r i) ≤ Real.exp (-τ * μ) := fun i => by
    apply Real.exp_le_exp.mpr
    have : (μ : ℝ) ≤ r i := by exact_mod_cast hle i
    nlinarith
  constructor
  · have := Finset.single_le_sum (fun i _ => (Real.exp_pos (-τ * r i)).le) (Finset.mem_univ i0)
    have hμ : ((μ : ℕ) : ℝ) = r i0 := by exact_mod_cast hmin
    rw [hμ]
    exact this
  · calc Zp r τ ≤ ∑ _i : ι, Real.exp (-τ * μ) := Finset.sum_le_sum fun i _ => hterm i
      _ = Fintype.card ι * Real.exp (-τ * μ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`μ − log|ι|/τ ≤ −log Z(τ)/τ ≤ μ`** para `τ > 0`. -/
theorem Zp_log_cotas [Nonempty ι] {τ : ℝ} (hτ : 0 < τ) :
    ((Finset.univ.inf' Finset.univ_nonempty r : ℕ) : ℝ) - Real.log (Fintype.card ι) / τ ≤
        -Real.log (Zp r τ) / τ ∧
      -Real.log (Zp r τ) / τ ≤ ((Finset.univ.inf' Finset.univ_nonempty r : ℕ) : ℝ) := by
  set μ : ℝ := ((Finset.univ.inf' Finset.univ_nonempty r : ℕ) : ℝ)
  obtain ⟨h1, h2⟩ := Zp_cotas r hτ.le
  have hZ : 0 < Zp r τ := lt_of_lt_of_le (Real.exp_pos _) h1
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have l1 : -τ * μ ≤ Real.log (Zp r τ) := by
    rw [← Real.log_exp (-τ * μ)]; exact Real.log_le_log (Real.exp_pos _) h1
  have l2 : Real.log (Zp r τ) ≤ Real.log (Fintype.card ι) + -τ * μ := by
    rw [← Real.log_exp (-τ * μ), ← Real.log_mul hc.ne' (Real.exp_pos _).ne']
    exact Real.log_le_log hZ h2
  constructor
  · have e : μ - Real.log (Fintype.card ι) / τ = (μ * τ - Real.log (Fintype.card ι)) / τ := by
      field_simp
    rw [e, div_le_div_iff_of_pos_right hτ]
    linarith
  · rw [div_le_iff₀ hτ]; linarith

/-- **`−log Z(τ)/τ → min r`** quando `τ → ∞`. -/
theorem Zp_limite [Nonempty ι] :
    Tendsto (fun τ => -Real.log (Zp r τ) / τ) atTop
      (𝓝 ((Finset.univ.inf' Finset.univ_nonempty r : ℕ) : ℝ)) := by
  set μ : ℝ := ((Finset.univ.inf' Finset.univ_nonempty r : ℕ) : ℝ)
  have hlow : Tendsto (fun τ : ℝ => μ - Real.log (Fintype.card ι) / τ) atTop (𝓝 μ) := by
    have := (tendsto_const_nhds (x := Real.log (Fintype.card ι))).div_atTop tendsto_id
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with τ hτ using (Zp_log_cotas r hτ).1
  · filter_upwards [eventually_gt_atTop 0] with τ hτ using (Zp_log_cotas r hτ).2

end Generico

/-- Caso A: `(x∨y)∧(¬x∨y)∧(x∨¬y)`. -/
def φA : List (List (Lit 2)) := [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)]]
/-- Caso B: `x ∧ ¬x`. -/
def φB : List (List (Lit 1)) := [[(0, true)], [(0, false)]]
/-- Caso C: `x ∧ y`. -/
def φC : List (List (Lit 2)) := [[(0, true)], [(1, true)]]

/-- **Caso A**: `M = 704 = (1300)₈`, `⌊704/512⌋ = 1 = #SAT`, `det(L + I) = 8`. -/
theorem exemplo_A : (∑ x, 8 ^ (3 - Rphi φA x)) = 704 ∧ 704 / 8 ^ 3 = 1 ∧ Nz (Rphi φA) = 1 ∧
    (∏ x, (Rphi φA x ^ 2 + 1)) = 8 := by decide

/-- **Caso B**: `M = 8 = (020)₄`, `⌊8/16⌋ = 0 = #SAT`, `det(L + I) = 4`. -/
theorem exemplo_B : (∑ x, 4 ^ (2 - Rphi φB x)) = 8 ∧ 8 / 4 ^ 2 = 0 ∧ Nz (Rphi φB) = 0 ∧
    (∏ x, (Rphi φB x ^ 2 + 1)) = 4 := by decide

/-- **Caso C**: `M = 81 = (121)₈`, `⌊81/64⌋ = 1 = #SAT`, `det(L + I) = 20`, mínimo de violações `0`. -/
theorem exemplo_C : (∑ x, 8 ^ (2 - Rphi φC x)) = 81 ∧ 81 / 8 ^ 2 = 1 ∧ Nz (Rphi φC) = 1 ∧
    (∏ x, (Rphi φC x ^ 2 + 1)) = 20 := by decide

/-- A codificação recupera `#SAT` nos três casos, pelo teorema geral. -/
theorem exemplos_pela_codificacao :
    (∑ x, 8 ^ (3 - Rphi φA x)) / 8 ^ 3 = Nz (Rphi φA) ∧ (∑ x, 4 ^ (2 - Rphi φB x)) / 4 ^ 2 = Nz (Rphi φB) ∧
      (∑ x, 8 ^ (2 - Rphi φC x)) / 8 ^ 2 = Nz (Rphi φC) :=
  ⟨codificacao_inteira _ (by decide) (fun x => (Rphi_le φA x).trans_eq rfl),
    codificacao_inteira _ (by decide) (fun x => (Rphi_le φB x).trans_eq rfl),
    codificacao_inteira _ (by decide) (fun x => (Rphi_le φC x).trans_eq rfl)⟩

/-! ## 2. Aritmética terminal -/

/-- Soma saturada em `Z`. -/
def satAdd (Z a b : ℕ) : ℕ := min Z (a + b)

theorem satAdd_assoc (Z a b c : ℕ) : satAdd Z (satAdd Z a b) c = satAdd Z a (satAdd Z b c) := by
  unfold satAdd; omega

theorem satAdd_comm (Z a b : ℕ) : satAdd Z a b = satAdd Z b a := by unfold satAdd; omega

/-- **`Z ⊕ 1 = Z`** e `Z − Z = 0` (subtração truncada). -/
theorem terminal_absorve (Z : ℕ) : satAdd Z Z 1 = Z ∧ Z - Z = 0 := by unfold satAdd; omega

/-- **O cancelamento falha**: `Z ⊕ 1 = (Z − 1) ⊕ 1` com `Z ≠ Z − 1`. -/
theorem cancelamento_falha {Z : ℕ} (hZ : 1 ≤ Z) : satAdd Z Z 1 = satAdd Z (Z - 1) 1 ∧ Z ≠ Z - 1 := by
  unfold satAdd; omega

/-- **Colapso**: uma congruência aditiva com `0 ∼ 1` identifica **todos** os naturais. -/
theorem colapso_congruencia (c : AddCon ℕ) (h : c 0 1) (a b : ℕ) : c a b := by
  have step : ∀ n, c n (n + 1) := fun n => by
    have := c.add h (c.refl n)
    simpa [add_comm] using this
  have h0 : ∀ n, c 0 n := by
    intro n
    induction n with
    | zero => exact c.refl 0
    | succ k ih => exact c.trans ih (step k)
  exact c.trans (c.symm (h0 a)) (h0 b)

/-- Num semianel, `0 = 1` força o semianel trivial. -/
theorem zero_um_trivial {R : Type*} [Semiring R] (h : (0 : R) = 1) : Subsingleton R :=
  subsingleton_of_zero_eq_one h

/-- Avaliador terminal `E(1) = 0`, `E(k) = k` para `k ≠ 1`. -/
def Ev (k : ℕ) : ℕ := if k = 1 then 0 else k

/-- **`E` não é aditivo**: `E(1 + 1) = 2 ≠ 0 = E(E(1) + E(1))`. -/
theorem Ev_nao_aditivo : Ev (1 + 1) = 2 ∧ Ev (Ev 1 + Ev 1) = 0 := by decide

/-- `a ⊞ b = E(min(Z, a + b))`. -/
def boxplus (Z a b : ℕ) : ℕ := Ev (min Z (a + b))

/-- A tabela enviada (`Z = 7`). -/
theorem boxplus_tabela : boxplus 7 0 1 = 0 ∧ boxplus 7 1 1 = 2 ∧ boxplus 7 1 2 = 3 ∧ boxplus 7 3 4 = 7 ∧
    boxplus 7 4 4 = 7 ∧ boxplus 7 7 7 = 7 := by decide

/-- **`⊞` não é associativa**: `(0 ⊞ 1) ⊞ 1 = 0 ≠ 2 = 0 ⊞ (1 ⊞ 1)`. -/
theorem boxplus_nao_assoc : boxplus 7 (boxplus 7 0 1) 1 = 0 ∧ boxplus 7 0 (boxplus 7 1 1) = 2 := by decide

/-- `Z/Z = 1 ≠ 0` num corpo; o "`≡ 0`" é a leitura `E(1) = 0`, não a divisão. -/
theorem divisao_terminal {Z : ℚ} (hZ : Z ≠ 0) : Z / Z = 1 ∧ (1 : ℚ) ≠ 0 ∧ Ev 1 = 0 :=
  ⟨div_self hZ, one_ne_zero, by decide⟩

/-- **Arredondamento**: `round x = 1 ⟺ ½ ≤ x < 3/2`. -/
theorem arredonda_um_iff (x : ℝ) : round x = 1 ↔ 1 / 2 ≤ x ∧ x < 3 / 2 := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> push_cast at * <;> linarith

/-- Estado intervalar: `[0, 3/2)` recebe o rótulo `1` ("01"); fora dele, o arredondamento. -/
noncomputable def E01 (x : ℝ) : ℤ := if 0 ≤ x ∧ x < 3 / 2 then 1 else round x

/-- **`E(0) = E(1) = E(1,49999)`.** -/
theorem E01_unifica : E01 0 = E01 1 ∧ E01 1 = E01 (149999 / 100000) := by
  norm_num [E01]

/-- **A soma não fica bem definida nas classes**: `E(0) = E(1)`, mas `E(0 + 1) ≠ E(1 + 1)`. -/
theorem E01_soma_mal_definida : E01 0 = E01 1 ∧ E01 (0 + 1) ≠ E01 (1 + 1) := by
  refine ⟨E01_unifica.1, ?_⟩
  have : round ((1 : ℝ) + 1) = 2 := by
    rw [show ((1 : ℝ) + 1) = ((2 : ℤ) : ℝ) by norm_num, round_intCast]
  norm_num [E01, this]

/-! ## 3. A faixa tolerante -/

/-- `T_ε = {s | 0 < Re s < 1, |Re s − ½| ≤ ε}`. -/
def Tol (ε : ℝ) : Set ℂ := {s | 0 < s.re ∧ s.re < 1 ∧ |s.re - 1 / 2| ≤ ε}

/-- **`9/20 + 10i` e `11/20 + 10i` estão em `T_{1/10}` e fora da linha.** -/
theorem exemplos_tolerancia :
    ((9 / 20 : ℂ) + 10 * I) ∈ Tol (1 / 10) ∧ ((9 / 20 : ℂ) + 10 * I).re ≠ 1 / 2 ∧
      ((11 / 20 : ℂ) + 10 * I) ∈ Tol (1 / 10) ∧ ((11 / 20 : ℂ) + 10 * I).re ≠ 1 / 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩ <;> norm_num [abs_le]

/-- **A torção preserva `T_ε`** e a distância à linha. -/
theorem torcao_tol {ε : ℝ} {s : ℂ} (h : s ∈ Tol ε) :
    ATK.ZetaSimetria.torcao s ∈ Tol ε ∧
      |(ATK.ZetaSimetria.torcao s).re - 1 / 2| = |s.re - 1 / 2| := by
  have e := ATK.ZetaSimetria.re_torcao s
  have hd : |(ATK.ZetaSimetria.torcao s).re - 1 / 2| = |s.re - 1 / 2| := by
    rw [e, show 1 - s.re - 1 / 2 = -(s.re - 1 / 2) by ring, abs_neg]
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨⟨by rw [e]; linarith, by rw [e]; linarith, hd ▸ h2⟩, hd⟩

/-- Todo zero fora da linha está numa faixa tolerante. -/
theorem fora_em_tol {ρ : ℂ} (h : ForaCritico ρ) : ρ ∈ Tol |ρ.re - 1 / 2| ∧ 0 < |ρ.re - 1 / 2| :=
  ⟨⟨h.1.2.1, h.1.2.2, le_rfl⟩, abs_pos.mpr (sub_ne_zero.mpr h.2)⟩

/-- **Um zero de `ζ` em `T_ε` fora da linha refuta RH.** -/
theorem tol_refuta {ε : ℝ} {s : ℂ} (hs : s ∈ Tol ε) (h0 : riemannZeta s = 0) (hre : s.re ≠ 1 / 2) :
    ¬ RiemannHypothesis :=
  ATK.ZeroClasses.Hipotetico.hFora_iff.mp ⟨s, h0, hs.1, hs.2.1, hre⟩

/-- **RH ⟺ todo zero não trivial está em todas as faixas tolerantes, com folga estrita.** -/
theorem rh_iff_tolerancias : RiemannHypothesis ↔
    ∀ ε : ℝ, 0 < ε → ∀ ρ ∈ ATK.ZetaSimetria.Z, |ρ.re - 1 / 2| < ε :=
  ATK.ZetaSimetria.riemann_iff_colares

/-- **Com `VerificadoAte H`**: nenhum ponto de `T_ε` fora da linha, com `|t| ≤ H`, é zero. -/
theorem tol_verificada {H : ℝ} (hV : ATK.ZeroClasses.Escalas.VerificadoAte H) {ε : ℝ} {s : ℂ}
    (hs : s ∈ Tol ε) (hre : s.re ≠ 1 / 2) (ht : |s.im| ≤ H) : riemannZeta s ≠ 0 := fun h0 =>
  hre (hV s ⟨h0, hs.1, hs.2.1⟩ ht)

/-- Os dois pontos enviados não são zeros, com Platt–Trudgian como hipótese nomeada. -/
theorem exemplos_nao_zeros (hV : ATK.ZeroClasses.Escalas.VerificadoAte 3000175332800) :
    riemannZeta ((9 / 20 : ℂ) + 10 * I) ≠ 0 ∧ riemannZeta ((11 / 20 : ℂ) + 10 * I) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := exemplos_tolerancia
  exact ⟨tol_verificada hV h1 h2 (by norm_num), tol_verificada hV h3 h4 (by norm_num)⟩

end ATK.ZeroClasses.Finito

#print axioms ATK.ZeroClasses.Finito.Fpol_eval_zero
#print axioms ATK.ZeroClasses.Finito.ordem_Fpol
#print axioms ATK.ZeroClasses.Finito.codificacao_inteira
#print axioms ATK.ZeroClasses.Finito.Zp_cotas
#print axioms ATK.ZeroClasses.Finito.Zp_log_cotas
#print axioms ATK.ZeroClasses.Finito.Zp_limite
#print axioms ATK.ZeroClasses.Finito.exemplo_A
#print axioms ATK.ZeroClasses.Finito.exemplo_B
#print axioms ATK.ZeroClasses.Finito.exemplo_C
#print axioms ATK.ZeroClasses.Finito.exemplos_pela_codificacao
#print axioms ATK.ZeroClasses.Finito.satAdd_assoc
#print axioms ATK.ZeroClasses.Finito.satAdd_comm
#print axioms ATK.ZeroClasses.Finito.terminal_absorve
#print axioms ATK.ZeroClasses.Finito.cancelamento_falha
#print axioms ATK.ZeroClasses.Finito.colapso_congruencia
#print axioms ATK.ZeroClasses.Finito.zero_um_trivial
#print axioms ATK.ZeroClasses.Finito.Ev_nao_aditivo
#print axioms ATK.ZeroClasses.Finito.boxplus_tabela
#print axioms ATK.ZeroClasses.Finito.boxplus_nao_assoc
#print axioms ATK.ZeroClasses.Finito.divisao_terminal
#print axioms ATK.ZeroClasses.Finito.arredonda_um_iff
#print axioms ATK.ZeroClasses.Finito.E01_unifica
#print axioms ATK.ZeroClasses.Finito.E01_soma_mal_definida
#print axioms ATK.ZeroClasses.Finito.exemplos_tolerancia
#print axioms ATK.ZeroClasses.Finito.torcao_tol
#print axioms ATK.ZeroClasses.Finito.fora_em_tol
#print axioms ATK.ZeroClasses.Finito.tol_refuta
#print axioms ATK.ZeroClasses.Finito.rh_iff_tolerancias
#print axioms ATK.ZeroClasses.Finito.tol_verificada
#print axioms ATK.ZeroClasses.Finito.exemplos_nao_zeros
