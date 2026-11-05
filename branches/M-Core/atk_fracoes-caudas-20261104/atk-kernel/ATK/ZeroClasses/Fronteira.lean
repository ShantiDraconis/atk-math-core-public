import ATK.ZeroClasses.Finito

/-!
# A fronteira entre estados, antes do colapso (rodada 27)

**1. Quantização e células** (`Q`, `cel`, `Q_eq_round`, `Q_eq_iff`, `celulas_particao`, `celulas_disjuntas`,
`celulas_exemplos`, `Q_int`, `Q_add_int`, `Q_monotone`, `Q_proximo`, `Q_nao_aditivo`, `Q_soma_cotas`,
`Q_soma_cotas_atingidas`). `Q(x) = ⌊x + ½⌋` e `C_k = [k − ½, k + ½)`: as células particionam `ℝ`, `Q` é o
arredondamento, é monótona, comuta com translações inteiras, escolhe o inteiro mais próximo — e **não é aditiva**:
`Q(x + y) − Q x − Q y ∈ {−1, 0, 1}`, com os dois extremos atingidos.

**2. O produtor multivalorado** (`P`, `Q_mem_P`, `P_interior`, `P_fronteira`, `P_exemplos`, `P_sub`, `P_dois_iff`,
`P_eq_argmin`, `colapso_fronteira`). `P(x) = {k ∈ ℤ | |x − k| ≤ ½}`: é `{k}` no interior da célula, `{k, k + 1}`
na fronteira `k + ½`, sempre contém `Q x`, tem no máximo dois elementos, e é exatamente o conjunto dos inteiros
mais próximos de `x`. `P(½) = {0, 1}`, `P(3/2) = {1, 2}`. O colapso `Q` desempata a fronteira para cima.

**3. Adjacência e fecho** (`Adj`, `adj_iff`, `adj_exemplos`, `adj_nao_transitiva`, `adj_symm`, `adj_irrefl`,
`colapso_fecho`, `fecho_tudo`). Dois estados são adjacentes se compartilham uma fronteira; isso equivale a
`|a − b| = 1`. A adjacência **não é transitiva** (`0 ∼ 1`, `1 ∼ 2`, `¬ 0 ∼ 2`); toda relação de equivalência que a
contém identifica **todos** os inteiros.

**4. Competição entre estados** (`Dif`, `Dif_fatora`, `Dif_zero_iff`, `Dif_equidistante`, `Dif_neg_iff`,
`Dif_lado`, `Dif01`, `Dif01_zero_iff`, `Dif12_zero_iff`, `meio_equidistante`, `Dif_reflexao`, `Dif01_antissim`,
`reflexao_fixa`, `fronteira_iff`, `fronteira_iff_Dif`). `Δ_ab(x) = (x − a)² − (x − b)² = (b − a)(2x − a − b)`;
para `a ≠ b`, `Δ_ab(x) = 0 ⟺ x = (a + b)/2 ⟺ |x − a| = |x − b|`. A reflexão `x ↦ a + b − x` troca o sinal e fixa só
o ponto médio. A fronteira de `P` entre `k` e `k + 1` é exatamente o zero de `Δ_{k,k+1}`.

**5. A ponte com RH** (`Dif01_re`, `ponte_iff_RH`, `zero_iff_re_im`, `nao_rh_iff_produtor`, `dl`, `dl_zero_iff`,
`classifica`, `regiao_decimo`, `distancias_exemplos`, `reflexo_zero`, `simetria_permite_pares`,
`tolerancia_independente`). **ATK-RH-BRIDGE ⟺ RH** (não é um lema disponível: é a própria hipótese). O
"produtor que falta" — um zero `Re ζ = Im ζ = 0` com `0 < |σ − ½| ≤ ε < ½` — existe **se e só se** RH é falsa. A
reflexão dos zeros preserva a distância à linha e troca o sinal de `Δ₀₁`; a simetria sozinha admite pares fora da
linha; a tolerância é uma condição sobre `s`, independente da função: existe função sem zeros em `T_ε` e função
com zero em `T_ε` fora da linha.

**6. Aritmética de intervalos antes do colapso** (`Intervalo`, `pts`, `soma`, `neg`, `sub`, `pt`, `larg`,
`soma_correta`, `pts_soma`, `soma_assoc`, `soma_comm`, `soma_zero`, `pt_soma`, `larg_soma`, `sub_auto`,
`zero_mem_sub_auto`, `sub_auto_eq_zero_iff`, `sem_inverso`, `estados`, `estados_iff`, `estados_pt`,
`estados_tolerancia`, `estados_unidade`). A soma de intervalos é **exata** (é a soma de Minkowski), associativa,
comutativa, com neutro, e as larguras somam; `I − I = [−w, w]` contém `0` mas só é `{0}` para estado fixo (`w = 0`);
um intervalo de largura positiva **não tem inverso aditivo**. Os estados de `[lo, hi]` são os `k` com
`lo ≤ k + ½` e `k − ½ ≤ hi`; a faixa tolerante `[2/5, 3/5]` tem exatamente os estados `{0, 1}`.

**7. Semântica de três valores** (`Valor`, `aval`, `aval_ne_falso_iff`, `aval_fronteira_iff`, `aval_meio`,
`aval_colapso`). "`x` está no estado `k`" é verdadeiro (`|x − k| < ½`), fronteira (`= ½`) ou falso (`> ½`). Em
`½`, os estados `0` e `1` valem *fronteira*: não é `0 = 1`, é a fronteira entre eles.
-/

open Complex Set
open scoped Real Pointwise

namespace ATK.ZeroClasses.Fronteira

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Finito

/-! ## 1. Quantização e células -/

/-- A quantização `Q(x) = ⌊x + ½⌋`. -/
noncomputable def Q (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

/-- A célula `C_k = [k − ½, k + ½)`. -/
def cel (k : ℤ) : Set ℝ := Ico ((k : ℝ) - 1 / 2) (k + 1 / 2)

/-- `Q` é o arredondamento de Mathlib. -/
theorem Q_eq_round (x : ℝ) : Q x = round x := (round_eq x).symm

/-- **`Q x = k ⟺ x ∈ C_k`.** -/
theorem Q_eq_iff {x : ℝ} {k : ℤ} : Q x = k ↔ x ∈ cel k := by
  unfold Q cel
  rw [Int.floor_eq_iff, mem_Ico]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **As células particionam `ℝ`.** -/
theorem celulas_particao (x : ℝ) : ∃! k : ℤ, x ∈ cel k :=
  ⟨Q x, Q_eq_iff.mp rfl, fun _ hk => (Q_eq_iff.mpr hk).symm⟩

theorem celulas_disjuntas {j k : ℤ} (h : j ≠ k) : Disjoint (cel j) (cel k) := by
  rw [Set.disjoint_left]
  intro x hj hk
  exact h ((Q_eq_iff.mpr hj).symm.trans (Q_eq_iff.mpr hk))

/-- `C₀ = [−½, ½)`, `C₁ = [½, 3/2)`, `C₂ = [3/2, 5/2)`. -/
theorem celulas_exemplos :
    cel 0 = Ico (-1 / 2) (1 / 2) ∧ cel 1 = Ico (1 / 2) (3 / 2) ∧ cel 2 = Ico (3 / 2) (5 / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold cel; congr 1 <;> norm_num)

theorem Q_int (k : ℤ) : Q k = k := Q_eq_iff.mpr ⟨by linarith, by linarith⟩

theorem Q_add_int (x : ℝ) (k : ℤ) : Q (x + k) = Q x + k := by
  unfold Q
  rw [show x + k + 1 / 2 = (x + 1 / 2) + k by ring]
  exact Int.floor_add_intCast _ _

theorem Q_monotone : Monotone Q := fun x y h => Int.floor_mono (by linarith)

/-- **`Q x` é um inteiro mais próximo de `x`**, a distância no máximo `½`. -/
theorem Q_proximo (x : ℝ) : |x - Q x| ≤ 1 / 2 ∧ ∀ k : ℤ, |x - Q x| ≤ |x - k| := by
  rw [Q_eq_round]
  exact ⟨abs_sub_round x, round_le x⟩

/-- **O colapso não é aditivo**: `Q(½ + ½) = 1`, mas `Q(½) + Q(½) = 2`. -/
theorem Q_nao_aditivo : Q (1 / 2 + 1 / 2) ≠ Q (1 / 2) + Q (1 / 2) := by
  have h1 : Q (1 / 2 + 1 / 2) = 1 := by
    rw [show (1 / 2 + 1 / 2 : ℝ) = ((1 : ℤ) : ℝ) by norm_num, Q_int]
  have h2 : Q (1 / 2) = 1 := Q_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [h1, h2]
  norm_num

/-- **O erro do colapso numa soma é `−1`, `0` ou `1`.** -/
theorem Q_soma_cotas (x y : ℝ) : Q x + Q y - 1 ≤ Q (x + y) ∧ Q (x + y) ≤ Q x + Q y + 1 := by
  have hx1 := Int.floor_le (x + 1 / 2)
  have hx2 := Int.lt_floor_add_one (x + 1 / 2)
  have hy1 := Int.floor_le (y + 1 / 2)
  have hy2 := Int.lt_floor_add_one (y + 1 / 2)
  have hs1 := Int.floor_le (x + y + 1 / 2)
  have hs2 := Int.lt_floor_add_one (x + y + 1 / 2)
  unfold Q
  constructor
  · have : ((⌊x + 1 / 2⌋ + ⌊y + 1 / 2⌋ - 1 : ℤ) : ℝ) < ⌊x + y + 1 / 2⌋ + 1 := by push_cast; linarith
    have := (Int.cast_lt (R := ℝ)).mp (by push_cast at this ⊢; linarith :
      ((⌊x + 1 / 2⌋ + ⌊y + 1 / 2⌋ - 1 : ℤ) : ℝ) < ((⌊x + y + 1 / 2⌋ + 1 : ℤ) : ℝ))
    omega
  · have := (Int.cast_lt (R := ℝ)).mp (by push_cast; linarith :
      ((⌊x + y + 1 / 2⌋ : ℤ) : ℝ) < ((⌊x + 1 / 2⌋ + ⌊y + 1 / 2⌋ + 2 : ℤ) : ℝ))
    omega

/-- Os dois extremos são atingidos: `Q(½ + ½) = Q ½ + Q ½ − 1` e `Q(2/5 + 2/5) = Q(2/5) + Q(2/5) + 1`. -/
theorem Q_soma_cotas_atingidas :
    Q (1 / 2 + 1 / 2) = Q (1 / 2) + Q (1 / 2) - 1 ∧ Q (2 / 5 + 2 / 5) = Q (2 / 5) + Q (2 / 5) + 1 := by
  have a : Q (1 / 2 + 1 / 2) = 1 := Q_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  have b : Q (1 / 2) = 1 := Q_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  have c : Q (2 / 5 + 2 / 5) = 1 := Q_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  have d : Q (2 / 5) = 0 := Q_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [a, b, c, d]
  norm_num

/-! ## 2. O produtor multivalorado -/

/-- `P(x) = {k ∈ ℤ | |x − k| ≤ ½}`: os estados admissíveis antes do colapso. -/
def P (x : ℝ) : Set ℤ := {k | |x - k| ≤ 1 / 2}

theorem Q_mem_P (x : ℝ) : Q x ∈ P x := (Q_proximo x).1

/-- **No interior da célula, `P(x) = {k}`.** -/
theorem P_interior {x : ℝ} {k : ℤ} (h1 : (k : ℝ) - 1 / 2 < x) (h2 : x < k + 1 / 2) : P x = {k} := by
  ext j
  simp only [P, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro hj
    obtain ⟨a, b⟩ := abs_le.mp hj
    have h3 : (j : ℝ) < k + 1 := by linarith
    have h4 : (k : ℝ) - 1 < j := by linarith
    have h5 : j < k + 1 := by exact_mod_cast h3
    have h6 : k - 1 < j := by exact_mod_cast h4
    omega
  · rintro rfl
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Na fronteira, `P(k + ½) = {k, k + 1}`.** -/
theorem P_fronteira (k : ℤ) : P (k + 1 / 2) = {k, k + 1} := by
  ext j
  simp only [P, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hj
    obtain ⟨a, b⟩ := abs_le.mp hj
    have h3 : (j : ℝ) ≤ k + 1 := by linarith
    have h4 : (k : ℝ) ≤ j := by linarith
    have h5 : j ≤ k + 1 := by exact_mod_cast h3
    have h6 : k ≤ j := by exact_mod_cast h4
    omega
  · rintro (rfl | rfl)
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · push_cast
      exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **`P(½) = {0, 1}` e `P(3/2) = {1, 2}`.** -/
theorem P_exemplos : P (1 / 2) = {0, 1} ∧ P (3 / 2) = {1, 2} := by
  have h0 := P_fronteira 0
  have h1 := P_fronteira 1
  norm_num at h0 h1
  exact ⟨h0, h1⟩

/-- `P(x)` tem no máximo dois elementos: `Q x − 1` e `Q x`. -/
theorem P_sub (x : ℝ) : P x ⊆ {Q x - 1, Q x} := by
  intro j hj
  have hj' : |x - j| ≤ 1 / 2 := hj
  obtain ⟨a, b⟩ := abs_le.mp hj'
  have hq : x ∈ cel (Q x) := Q_eq_iff.mp rfl
  obtain ⟨c, d⟩ := hq
  have h3 : (j : ℝ) < Q x + 1 := by linarith
  have h4 : ((Q x : ℤ) : ℝ) - 1 - 1 < j := by linarith
  have h5 : j < Q x + 1 := by exact_mod_cast h3
  have h6 : Q x - 1 - 1 < j := by exact_mod_cast h4
  simp only [mem_insert_iff, mem_singleton_iff]
  omega

/-- **`P(x)` tem dois estados exatamente nas fronteiras `k + ½`.** -/
theorem P_dois_iff (x : ℝ) : (∃ a b : ℤ, a ≠ b ∧ a ∈ P x ∧ b ∈ P x) ↔ ∃ k : ℤ, x = k + 1 / 2 := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' : |x - a| ≤ 1 / 2 := ha
    have hb' : |x - b| ≤ 1 / 2 := hb
    obtain ⟨a1, a2⟩ := abs_le.mp ha'
    obtain ⟨b1, b2⟩ := abs_le.mp hb'
    rcases lt_or_gt_of_ne hab with h | h
    · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      exact ⟨a, by linarith⟩
    · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      exact ⟨b, by linarith⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, k + 1, by omega, ?_, ?_⟩ <;> rw [P_fronteira] <;> simp

/-- **`P(x)` é exatamente o conjunto dos inteiros mais próximos de `x`.** -/
theorem P_eq_argmin (x : ℝ) : P x = {k : ℤ | ∀ j : ℤ, |x - k| ≤ |x - j|} := by
  ext k
  simp only [P, mem_ofPred_eq]
  constructor
  · intro hk j
    by_cases hjk : j = k
    · rw [hjk]
    · have h1 : (1 : ℤ) ≤ |k - j| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hjk))
      have h2 : (1 : ℝ) ≤ |(k : ℝ) - j| := by exact_mod_cast h1
      have h3 : |(k : ℝ) - j| ≤ |x - j| + |x - k| := by
        rw [show (k : ℝ) - j = (x - j) - (x - k) by ring]
        exact abs_sub _ _
      linarith
  · intro hk
    exact (hk (Q x)).trans (Q_proximo x).1

/-- **O colapso desempata a fronteira para cima**: `Q(k + ½) = k + 1`, embora `k ∈ P(k + ½)`. -/
theorem colapso_fronteira (k : ℤ) : Q (k + 1 / 2) = k + 1 ∧ k ∈ P (k + 1 / 2) ∧ k ≠ k + 1 := by
  refine ⟨Q_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩, ?_, by omega⟩
  rw [P_fronteira]
  simp

/-! ## 3. Adjacência e fecho -/

/-- Dois estados distintos são adjacentes se compartilham uma fronteira. -/
def Adj (a b : ℤ) : Prop := a ≠ b ∧ ∃ x : ℝ, a ∈ P x ∧ b ∈ P x

/-- **Adjacência ⟺ `|a − b| = 1`.** -/
theorem adj_iff {a b : ℤ} : Adj a b ↔ |a - b| = 1 := by
  constructor
  · rintro ⟨hne, x, ha, hb⟩
    have ha' : |x - a| ≤ 1 / 2 := ha
    have hb' : |x - b| ≤ 1 / 2 := hb
    obtain ⟨a1, a2⟩ := abs_le.mp ha'
    obtain ⟨b1, b2⟩ := abs_le.mp hb'
    have h1 : (a : ℝ) - b ≤ 1 := by linarith
    have h2 : (b : ℝ) - a ≤ 1 := by linarith
    have h1' : a - b ≤ 1 := by exact_mod_cast h1
    have h2' : b - a ≤ 1 := by exact_mod_cast h2
    have h3 : a - b ≠ 0 := sub_ne_zero.mpr hne
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
    omega
  · intro h
    have hne : a ≠ b := by
      rintro rfl
      simp at h
    have hr : |(a : ℝ) - b| = 1 := by exact_mod_cast h
    refine ⟨hne, ((a : ℝ) + b) / 2, ?_, ?_⟩
    · show |((a : ℝ) + b) / 2 - a| ≤ 1 / 2
      rw [show ((a : ℝ) + b) / 2 - a = -(((a : ℝ) - b) / 2) by ring, abs_neg, abs_div, hr]
      norm_num
    · show |((a : ℝ) + b) / 2 - b| ≤ 1 / 2
      rw [show ((a : ℝ) + b) / 2 - b = ((a : ℝ) - b) / 2 by ring, abs_div, hr]
      norm_num

/-- **`0 ∼ 1`, `1 ∼ 2`, mas não `0 ∼ 2`.** -/
theorem adj_exemplos : Adj 0 1 ∧ Adj 1 2 ∧ ¬ Adj 0 2 := by
  refine ⟨adj_iff.mpr ?_, adj_iff.mpr ?_, fun h => ?_⟩
  · norm_num
  · norm_num
  · have := adj_iff.mp h
    norm_num at this

/-- **A adjacência não é transitiva.** -/
theorem adj_nao_transitiva : ¬ ∀ a b c : ℤ, Adj a b → Adj b c → Adj a c := fun h =>
  adj_exemplos.2.2 (h 0 1 2 adj_exemplos.1 adj_exemplos.2.1)

theorem adj_symm {a b : ℤ} (h : Adj a b) : Adj b a := by
  rw [adj_iff] at h ⊢
  rw [abs_sub_comm]
  exact h

theorem adj_irrefl (a : ℤ) : ¬ Adj a a := fun h => h.1 rfl

/-- **Toda equivalência que contém a adjacência identifica todos os inteiros.** -/
theorem colapso_fecho (r : ℤ → ℤ → Prop) (hr : Equivalence r) (h : ∀ a b, Adj a b → r a b) :
    ∀ a b, r a b := by
  have h0 : ∀ n : ℤ, r 0 n := by
    intro n
    induction n using Int.induction_on with
    | zero => exact hr.refl 0
    | succ n ih => exact hr.trans ih (h n (n + 1) (adj_iff.mpr (by norm_num)))
    | pred n ih => exact hr.trans ih (h (-n) (-n - 1) (adj_iff.mpr (by norm_num)))
  intro a b
  exact hr.trans (hr.symm (h0 a)) (h0 b)

/-- **O fecho de equivalência da adjacência é a relação total**: `0 ∼ 1 ∼ 2 ⟹ 0 ∼ 2`, e assim por diante. -/
theorem fecho_tudo (a b : ℤ) : Relation.EqvGen Adj a b :=
  colapso_fecho _ (Relation.EqvGen.is_equivalence Adj) (fun a b h => Relation.EqvGen.rel a b h) a b

/-! ## 4. Competição entre estados -/

/-- `Δ_ab(x) = (x − a)² − (x − b)²`. -/
def Dif (a b x : ℝ) : ℝ := (x - a) ^ 2 - (x - b) ^ 2

/-- **`Δ_ab(x) = (b − a)(2x − a − b)`.** -/
theorem Dif_fatora (a b x : ℝ) : Dif a b x = (b - a) * (2 * x - a - b) := by
  unfold Dif
  ring

/-- **Para `a ≠ b`: `Δ_ab(x) = 0 ⟺ x = (a + b)/2`.** -/
theorem Dif_zero_iff {a b : ℝ} (h : a ≠ b) (x : ℝ) : Dif a b x = 0 ↔ x = (a + b) / 2 := by
  rw [Dif_fatora, mul_eq_zero]
  constructor
  · rintro (h1 | h2)
    · exact absurd (sub_eq_zero.mp h1).symm h
    · linarith
  · intro hx
    right
    rw [hx]
    ring

/-- **`Δ_ab(x) = 0 ⟺ x é equidistante de `a` e `b`.** -/
theorem Dif_equidistante (a b x : ℝ) : Dif a b x = 0 ↔ |x - a| = |x - b| := by
  unfold Dif
  rw [sub_eq_zero]
  exact sq_eq_sq_iff_abs_eq_abs _ _

/-- **`Δ_ab(x) < 0 ⟺ x está mais perto de `a`.** -/
theorem Dif_neg_iff (a b x : ℝ) : Dif a b x < 0 ↔ |x - a| < |x - b| := by
  unfold Dif
  rw [sub_neg]
  exact sq_lt_sq

/-- Para `a < b`: `Δ_ab(x) < 0 ⟺ x < (a + b)/2`. -/
theorem Dif_lado {a b : ℝ} (h : a < b) (x : ℝ) : Dif a b x < 0 ↔ x < (a + b) / 2 := by
  rw [Dif_fatora]
  have hba : 0 < b - a := sub_pos.mpr h
  constructor
  · intro h1
    by_contra h2
    have h2 := not_lt.mp h2
    have : 0 ≤ (b - a) * (2 * x - a - b) := mul_nonneg hba.le (by linarith)
    linarith
  · intro h1
    exact mul_neg_of_pos_of_neg hba (by linarith)

theorem Dif01 (x : ℝ) : Dif 0 1 x = 2 * x - 1 := by
  unfold Dif
  ring

/-- **`Δ₀₁(x) = 0 ⟺ x = ½`.** -/
theorem Dif01_zero_iff (x : ℝ) : Dif 0 1 x = 0 ↔ x = 1 / 2 := by
  rw [Dif01]
  constructor <;> intro h <;> linarith

/-- **`Δ₁₂(x) = 0 ⟺ x = 3/2`.** -/
theorem Dif12_zero_iff (x : ℝ) : Dif 1 2 x = 0 ↔ x = 3 / 2 := by
  rw [Dif_zero_iff (by norm_num)]
  norm_num

/-- **`½` é equidistante de `0` e `1`; `3/2`, de `1` e `2`.** -/
theorem meio_equidistante : |(1 / 2 : ℝ) - 0| = |1 / 2 - 1| ∧ |(3 / 2 : ℝ) - 1| = |3 / 2 - 2| :=
  ⟨(Dif_equidistante 0 1 _).mp ((Dif01_zero_iff _).mpr rfl),
    (Dif_equidistante 1 2 _).mp ((Dif12_zero_iff _).mpr rfl)⟩

/-- **A reflexão `x ↦ a + b − x` troca o sinal de `Δ_ab`.** -/
theorem Dif_reflexao (a b x : ℝ) : Dif a b (a + b - x) = -Dif a b x := by
  unfold Dif
  ring

/-- **`Δ₀₁(1 − x) = −Δ₀₁(x)`.** -/
theorem Dif01_antissim (x : ℝ) : Dif 0 1 (1 - x) = -Dif 0 1 x := by
  unfold Dif
  ring

/-- **A reflexão `x ↦ 1 − x` fixa exatamente `½`.** -/
theorem reflexao_fixa (x : ℝ) : 1 - x = x ↔ x = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- **`k` e `k + 1` são ambos admissíveis em `x` ⟺ `x = k + ½`.** -/
theorem fronteira_iff (k : ℤ) (x : ℝ) : (k ∈ P x ∧ k + 1 ∈ P x) ↔ x = k + 1 / 2 := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : |x - k| ≤ 1 / 2 := h1
    have h2' : |x - ((k + 1 : ℤ) : ℝ)| ≤ 1 / 2 := h2
    push_cast at h2'
    obtain ⟨a, b⟩ := abs_le.mp h1'
    obtain ⟨c, d⟩ := abs_le.mp h2'
    linarith
  · rintro rfl
    rw [P_fronteira]
    simp

/-- **A fronteira de `P` entre `k` e `k + 1` é o zero de `Δ_{k,k+1}`.** -/
theorem fronteira_iff_Dif (k : ℤ) (x : ℝ) : (k ∈ P x ∧ k + 1 ∈ P x) ↔ Dif k (k + 1) x = 0 := by
  rw [fronteira_iff, Dif_zero_iff (by linarith)]
  constructor <;> intro h <;> linarith

/-! ## 5. A ponte com RH -/

theorem Dif01_re (s : ℂ) : Dif 0 1 s.re = 2 * s.re - 1 := Dif01 _

/-- **ATK-RH-BRIDGE ⟺ RH.** A ponte "todo zero na faixa está na fronteira `Δ₀₁ = 0`" é a própria hipótese,
não um lema disponível. -/
theorem ponte_iff_RH :
    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → Dif 0 1 ρ.re = 0) ↔ RiemannHypothesis := by
  constructor
  · intro h
    by_contra hRH
    obtain ⟨ρ, h0, h1, h2, h3⟩ := ATK.ZeroClasses.Hipotetico.hFora_iff.mpr hRH
    exact h3 ((Dif01_zero_iff _).mp (h ρ h1 h2 h0))
  · intro hRH ρ h1 h2 h0
    by_contra hd
    exact (ATK.ZeroClasses.Hipotetico.hFora_iff.mp
      ⟨ρ, h0, h1, h2, fun he => hd ((Dif01_zero_iff _).mpr he)⟩) hRH

/-- `ζ(s) = 0 ⟺ Re ζ(s) = 0 ∧ Im ζ(s) = 0`. -/
theorem zero_iff_re_im (s : ℂ) :
    riemannZeta s = 0 ↔ (riemannZeta s).re = 0 ∧ (riemannZeta s).im = 0 := by
  rw [Complex.ext_iff]
  simp

/-- **O produtor que falta existe ⟺ RH é falsa**: um `σ + it` com `0 < |σ − ½| ≤ ε < ½` e
`Re ζ = Im ζ = 0`. -/
theorem nao_rh_iff_produtor : ¬ RiemannHypothesis ↔
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∃ σ t : ℝ, 0 < |σ - 1 / 2| ∧ |σ - 1 / 2| ≤ ε ∧
      (riemannZeta (σ + t * I)).re = 0 ∧ (riemannZeta (σ + t * I)).im = 0 := by
  rw [← ATK.ZeroClasses.Hipotetico.hFora_iff]
  constructor
  · rintro ⟨ρ, h0, h1, h2, h3⟩
    have hd : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr h3)
    have hlt : |ρ.re - 1 / 2| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    refine ⟨|ρ.re - 1 / 2|, hd, hlt, ρ.re, ρ.im, hd, le_rfl, ?_⟩
    rw [Complex.re_add_im]
    exact (zero_iff_re_im ρ).mp h0
  · rintro ⟨ε, _, hε2, σ, t, hd, hle, hre, him⟩
    refine ⟨σ + t * I, (zero_iff_re_im _).mpr ⟨hre, him⟩, ?_, ?_, ?_⟩ <;> simp only [add_re, ofReal_re,
      mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_self, add_zero]
    · linarith [(abs_le.mp hle).1]
    · linarith [(abs_le.mp hle).2]
    · intro h
      rw [h, sub_self, abs_zero] at hd
      exact lt_irrefl _ hd

/-- A distância à linha crítica, `d(s) = |Re s − ½|`. -/
noncomputable def dl (s : ℂ) : ℝ := |s.re - 1 / 2|

theorem dl_zero_iff (s : ℂ) : dl s = 0 ↔ s.re = 1 / 2 := by
  unfold dl
  rw [abs_eq_zero, sub_eq_zero]

/-- **Classificação exata**: central (`d = 0`), tolerante fora da linha (`0 < d ≤ ε`) ou fora da tolerância. -/
theorem classifica (ε : ℝ) (s : ℂ) : dl s = 0 ∨ (0 < dl s ∧ dl s ≤ ε) ∨ ε < dl s := by
  rcases (abs_nonneg (s.re - 1 / 2)).eq_or_lt with h | h
  · exact Or.inl h.symm
  · rcases le_or_gt (dl s) ε with h' | h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr h')

/-- **`T_{1/10} = {2/5 ≤ Re s ≤ 3/5}`.** -/
theorem regiao_decimo (s : ℂ) : s ∈ Tol (1 / 10) ↔ 2 / 5 ≤ s.re ∧ s.re ≤ 3 / 5 := by
  unfold Tol
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨_, _, h⟩
    obtain ⟨a, b⟩ := abs_le.mp h
    constructor <;> linarith
  · rintro ⟨a, b⟩
    exact ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- **`d(9/20 + 10i) = d(11/20 + 10i) = 1/20`.** -/
theorem distancias_exemplos : dl ((9 / 20 : ℂ) + 10 * I) = 1 / 20 ∧ dl ((11 / 20 : ℂ) + 10 * I) = 1 / 20 := by
  have h1 : ((9 / 20 : ℂ) + 10 * I).re = 9 / 20 := by norm_num
  have h2 : ((11 / 20 : ℂ) + 10 * I).re = 11 / 20 := by norm_num
  unfold dl
  rw [h1, h2]
  constructor
  · rw [abs_of_neg (by norm_num)]
    norm_num
  · rw [abs_of_pos (by norm_num)]
    norm_num

/-- **A reflexão dos zeros**: `β + iγ ∈ Z ⟹ (1 − β) + iγ ∈ Z`, com a mesma distância à linha e `Δ₀₁` trocado
de sinal. -/
theorem reflexo_zero {ρ : ℂ} (h : ρ ∈ ATK.ZetaSimetria.Z) :
    ATK.ZetaSimetria.torcao ρ ∈ ATK.ZetaSimetria.Z ∧ (ATK.ZetaSimetria.torcao ρ).re = 1 - ρ.re ∧
      (ATK.ZetaSimetria.torcao ρ).im = ρ.im ∧ dl (ATK.ZetaSimetria.torcao ρ) = dl ρ ∧
      Dif 0 1 (ATK.ZetaSimetria.torcao ρ).re = -Dif 0 1 ρ.re := by
  have e := ATK.ZetaSimetria.re_torcao ρ
  have ei : (ATK.ZetaSimetria.torcao ρ).im = ρ.im := by
    unfold ATK.ZetaSimetria.torcao
    simp
  refine ⟨ATK.ZetaSimetria.torcao_mem_Z h, e, ei, ?_, ?_⟩
  · unfold dl
    rw [e, show 1 - ρ.re - 1 / 2 = -(ρ.re - 1 / 2) by ring, abs_neg]
  · rw [e, Dif01_antissim]

/-- **A simetria sozinha admite pares fora da linha**: `{9/20, 11/20}` é invariante por `x ↦ 1 − x`, está na
faixa e não contém `½`. -/
theorem simetria_permite_pares :
    ∃ A : Set ℝ, A.Nonempty ∧ (∀ x ∈ A, 1 - x ∈ A) ∧ ∀ x ∈ A, 0 < x ∧ x < 1 ∧ x ≠ 1 / 2 := by
  refine ⟨{9 / 20, 11 / 20}, ⟨9 / 20, by simp⟩, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · right
      norm_num
    · rw [mem_singleton_iff] at hx
      subst hx
      left
      norm_num
  · intro x hx
    rcases hx with rfl | hx
    · norm_num
    · rw [mem_singleton_iff] at hx
      subst hx
      norm_num

/-- **A tolerância não impõe zeros**: para `0 < ε < ½`, existe função sem zeros em `T_ε` e função com zero em
`T_ε` fora da linha. A condição `|Re s − ½| ≤ ε` é sobre `s`, não sobre a função. -/
theorem tolerancia_independente {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    ∃ F G : ℂ → ℂ, (∀ s ∈ Tol ε, F s ≠ 0) ∧ ∃ s ∈ Tol ε, s.re ≠ 1 / 2 ∧ G s = 0 := by
  refine ⟨fun _ => 1, fun s => s - ((1 / 2 + ε : ℝ) : ℂ), fun _ _ => one_ne_zero,
    ((1 / 2 + ε : ℝ) : ℂ), ⟨?_, ?_, ?_⟩, ?_, sub_self _⟩
  · rw [ofReal_re]; linarith
  · rw [ofReal_re]; linarith
  · rw [ofReal_re, show 1 / 2 + ε - 1 / 2 = ε by ring, abs_of_pos h0]
  · rw [ofReal_re]; linarith

/-! ## 6. Aritmética de intervalos antes do colapso -/

/-- Um intervalo fechado `[lo, hi]`: um estado tolerante. -/
@[ext]
structure Intervalo where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi

namespace Intervalo

/-- Os pontos de `[lo, hi]`. -/
def pts (I : Intervalo) : Set ℝ := Icc I.lo I.hi

/-- `[a, b] + [c, d] = [a + c, b + d]`. -/
def soma (I J : Intervalo) : Intervalo := ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.le J.le⟩

/-- `−[a, b] = [−b, −a]`. -/
def neg (I : Intervalo) : Intervalo := ⟨-I.hi, -I.lo, neg_le_neg I.le⟩

/-- `I − J = I + (−J)`. -/
def sub (I J : Intervalo) : Intervalo := soma I (neg J)

/-- O estado fixo `[x, x]`. -/
def pt (x : ℝ) : Intervalo := ⟨x, x, le_rfl⟩

/-- A largura (tolerância total). -/
def larg (I : Intervalo) : ℝ := I.hi - I.lo

theorem larg_nonneg (I : Intervalo) : 0 ≤ larg I := sub_nonneg.mpr I.le

/-- **Correção**: `x ∈ I`, `y ∈ J ⟹ x + y ∈ I + J`. -/
theorem soma_correta {I J : Intervalo} {x y : ℝ} (hx : x ∈ I.pts) (hy : y ∈ J.pts) :
    x + y ∈ (soma I J).pts :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

/-- **Exatidão**: a soma de intervalos é exatamente a soma de Minkowski dos pontos. -/
theorem pts_soma (I J : Intervalo) : (soma I J).pts = I.pts + J.pts := by
  ext z
  rw [Set.mem_add]
  constructor
  · intro hz
    obtain ⟨h1, h2⟩ := hz
    simp only [soma] at h1 h2
    refine ⟨max I.lo (z - J.hi), ⟨le_max_left _ _, max_le I.le (by linarith)⟩,
      z - max I.lo (z - J.hi), ⟨?_, ?_⟩, by ring⟩
    · have : max I.lo (z - J.hi) ≤ z - J.lo := max_le (by linarith) (by linarith [J.le])
      linarith
    · have := le_max_right I.lo (z - J.hi)
      linarith
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact soma_correta hx hy

theorem soma_assoc (I J K : Intervalo) : soma (soma I J) K = soma I (soma J K) := by
  ext <;> simp only [soma] <;> ring

theorem soma_comm (I J : Intervalo) : soma I J = soma J I := by
  ext <;> simp only [soma] <;> ring

theorem soma_zero (I : Intervalo) : soma I (pt 0) = I := by
  ext <;> simp [soma, pt]

/-- **Os estados fixos formam uma cópia de `ℝ`**: `[x, x] + [y, y] = [x + y, x + y]`. -/
theorem pt_soma (x y : ℝ) : soma (pt x) (pt y) = pt (x + y) := rfl

/-- **As tolerâncias somam**: `w(I + J) = w(I) + w(J)`. -/
theorem larg_soma (I J : Intervalo) : larg (soma I J) = larg I + larg J := by
  simp only [larg, soma]
  ring

/-- **`I − I = [−w, w]`.** -/
theorem sub_auto (I : Intervalo) : (sub I I).lo = -larg I ∧ (sub I I).hi = larg I := by
  simp only [sub, soma, neg, larg]
  constructor <;> ring

theorem zero_mem_sub_auto (I : Intervalo) : (0 : ℝ) ∈ (sub I I).pts := by
  obtain ⟨h1, h2⟩ := sub_auto I
  have := larg_nonneg I
  exact ⟨by rw [h1]; linarith, by rw [h2]; linarith⟩

/-- **`I − I = 0` só para estado fixo**: "`Z − Z = 0`" vale exatamente quando a tolerância é zero. -/
theorem sub_auto_eq_zero_iff (I : Intervalo) : sub I I = pt 0 ↔ larg I = 0 := by
  obtain ⟨h1, h2⟩ := sub_auto I
  constructor
  · intro h
    have : (sub I I).hi = 0 := by rw [h]; rfl
    linarith
  · intro h
    ext
    · rw [h1, h, neg_zero]; rfl
    · rw [h2, h]; rfl

/-- **Sem inverso aditivo**: um estado de tolerância positiva não se cancela com nenhum outro. -/
theorem sem_inverso {I : Intervalo} (h : 0 < larg I) (J : Intervalo) : soma I J ≠ pt 0 := by
  intro e
  have h1 := larg_soma I J
  rw [e] at h1
  have h2 : larg (pt 0) = 0 := by simp [larg, pt]
  have := larg_nonneg J
  linarith

/-- Os estados admissíveis de um intervalo: `⋃_{x ∈ I} P(x)`. -/
def estados (I : Intervalo) : Set ℤ := {k | ∃ x ∈ I.pts, k ∈ P x}

/-- **`k` é admissível em `[lo, hi]` ⟺ `lo ≤ k + ½` e `k − ½ ≤ hi`.** -/
theorem estados_iff (I : Intervalo) (k : ℤ) :
    k ∈ estados I ↔ I.lo ≤ k + 1 / 2 ∧ (k : ℝ) - 1 / 2 ≤ I.hi := by
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, hk⟩
    have hk' : |x - k| ≤ 1 / 2 := hk
    obtain ⟨a, b⟩ := abs_le.mp hk'
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rcases le_total (k : ℝ) I.lo with h | h
    · refine ⟨I.lo, ⟨le_rfl, I.le⟩, ?_⟩
      show |I.lo - k| ≤ 1 / 2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rcases le_total (k : ℝ) I.hi with h' | h'
      · refine ⟨k, ⟨h, h'⟩, ?_⟩
        show |(k : ℝ) - k| ≤ 1 / 2
        rw [sub_self, abs_zero]
        norm_num
      · refine ⟨I.hi, ⟨I.le, le_rfl⟩, ?_⟩
        show |I.hi - k| ≤ 1 / 2
        exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Para estado fixo, os estados são os de `P`. -/
theorem estados_pt (x : ℝ) : estados (pt x) = P x := by
  ext k
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, hk⟩
    have : y = x := le_antisymm h2 h1
    rw [← this]
    exact hk
  · intro hk
    exact ⟨x, ⟨le_rfl, le_rfl⟩, hk⟩

/-- **A faixa tolerante `[2/5, 3/5]` tem exatamente os estados `{0, 1}`**: é o estado "01". -/
theorem estados_tolerancia : estados ⟨2 / 5, 3 / 5, by norm_num⟩ = {0, 1} := by
  ext k
  rw [estados_iff]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have a : (-1 : ℝ) < k := by linarith
    have b : (k : ℝ) < 2 := by linarith
    have a' : -1 < k := by exact_mod_cast a
    have b' : k < 2 := by exact_mod_cast b
    omega
  · rintro (rfl | rfl) <;> norm_num

/-- `[0, 1]` tem os estados `{0, 1}`; `[0, 3/2]` já toca o estado `2`. -/
theorem estados_unidade :
    estados ⟨0, 1, by norm_num⟩ = {0, 1} ∧ estados ⟨0, 3 / 2, by norm_num⟩ = {0, 1, 2} := by
  constructor
  · ext k
    rw [estados_iff]
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have a : (-1 : ℝ) < k := by linarith
      have b : (k : ℝ) < 2 := by linarith
      have a' : -1 < k := by exact_mod_cast a
      have b' : k < 2 := by exact_mod_cast b
      omega
    · rintro (rfl | rfl) <;> norm_num
  · ext k
    rw [estados_iff]
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have a : (-1 : ℝ) < k := by linarith
      have b : (k : ℝ) < 3 := by linarith
      have a' : -1 < k := by exact_mod_cast a
      have b' : k < 3 := by exact_mod_cast b
      omega
    · rintro (rfl | rfl | rfl) <;> norm_num

end Intervalo

/-! ## 7. Semântica de três valores -/

/-- Os três valores de "`x` está no estado `k`". -/
inductive Valor
  | verdadeiro
  | fronteira
  | falso
  deriving DecidableEq

/-- A avaliação: verdadeiro se `|x − k| < ½`, fronteira se `= ½`, falso se `> ½`. -/
noncomputable def aval (x : ℝ) (k : ℤ) : Valor :=
  if |x - k| < 1 / 2 then .verdadeiro else if |x - k| = 1 / 2 then .fronteira else .falso

/-- **Não falso ⟺ admissível.** -/
theorem aval_ne_falso_iff (x : ℝ) (k : ℤ) : aval x k ≠ .falso ↔ k ∈ P x := by
  show _ ↔ |x - k| ≤ 1 / 2
  unfold aval
  split_ifs with h1 h2
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    exact h1.le
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    exact h2.le
  · simp only [ne_eq, not_true_eq_false, false_iff, not_le]
    exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)

/-- **Fronteira ⟺ `x = k ± ½`.** -/
theorem aval_fronteira_iff (x : ℝ) (k : ℤ) : aval x k = .fronteira ↔ x = k + 1 / 2 ∨ x = k - 1 / 2 := by
  unfold aval
  have key : |x - k| = 1 / 2 ↔ x = k + 1 / 2 ∨ x = k - 1 / 2 := by
    rw [abs_eq (by norm_num)]
    constructor <;> rintro (h | h)
    · left; linarith
    · right; linarith
    · left; linarith
    · right; linarith
  split_ifs with h1 h2
  · simp only [false_iff]
    intro h
    have := key.mpr h
    linarith
  · simp only [true_iff]
    exact key.mp h2
  · simp only [false_iff]
    exact fun h => h2 (key.mpr h)

/-- **Em `½`, os estados `0` e `1` valem fronteira**, e o estado `2` é falso. -/
theorem aval_meio : aval (1 / 2) 0 = .fronteira ∧ aval (1 / 2) 1 = .fronteira ∧ aval (1 / 2) 2 = .falso := by
  refine ⟨(aval_fronteira_iff _ _).mpr (Or.inl (by norm_num)),
    (aval_fronteira_iff _ _).mpr (Or.inr (by norm_num)), ?_⟩
  unfold aval
  have : |(1 / 2 : ℝ) - ((2 : ℤ) : ℝ)| = 3 / 2 := by
    rw [abs_of_neg (by norm_num)]
    norm_num
  rw [this]
  norm_num

/-- **O colapso respeita a verdade**: se "`x` está em `k`" é verdadeiro, então `Q x = k`. -/
theorem aval_colapso {x : ℝ} {k : ℤ} (h : aval x k = .verdadeiro) : Q x = k := by
  unfold aval at h
  split_ifs at h with h1
  obtain ⟨a, b⟩ := abs_lt.mp h1
  exact Q_eq_iff.mpr ⟨by linarith, by linarith⟩

end ATK.ZeroClasses.Fronteira

#print axioms ATK.ZeroClasses.Fronteira.Q_eq_round
#print axioms ATK.ZeroClasses.Fronteira.Q_eq_iff
#print axioms ATK.ZeroClasses.Fronteira.celulas_particao
#print axioms ATK.ZeroClasses.Fronteira.celulas_disjuntas
#print axioms ATK.ZeroClasses.Fronteira.celulas_exemplos
#print axioms ATK.ZeroClasses.Fronteira.Q_int
#print axioms ATK.ZeroClasses.Fronteira.Q_add_int
#print axioms ATK.ZeroClasses.Fronteira.Q_monotone
#print axioms ATK.ZeroClasses.Fronteira.Q_proximo
#print axioms ATK.ZeroClasses.Fronteira.Q_nao_aditivo
#print axioms ATK.ZeroClasses.Fronteira.Q_soma_cotas
#print axioms ATK.ZeroClasses.Fronteira.Q_soma_cotas_atingidas
#print axioms ATK.ZeroClasses.Fronteira.Q_mem_P
#print axioms ATK.ZeroClasses.Fronteira.P_interior
#print axioms ATK.ZeroClasses.Fronteira.P_fronteira
#print axioms ATK.ZeroClasses.Fronteira.P_exemplos
#print axioms ATK.ZeroClasses.Fronteira.P_sub
#print axioms ATK.ZeroClasses.Fronteira.P_dois_iff
#print axioms ATK.ZeroClasses.Fronteira.P_eq_argmin
#print axioms ATK.ZeroClasses.Fronteira.colapso_fronteira
#print axioms ATK.ZeroClasses.Fronteira.adj_iff
#print axioms ATK.ZeroClasses.Fronteira.adj_exemplos
#print axioms ATK.ZeroClasses.Fronteira.adj_nao_transitiva
#print axioms ATK.ZeroClasses.Fronteira.adj_symm
#print axioms ATK.ZeroClasses.Fronteira.adj_irrefl
#print axioms ATK.ZeroClasses.Fronteira.colapso_fecho
#print axioms ATK.ZeroClasses.Fronteira.fecho_tudo
#print axioms ATK.ZeroClasses.Fronteira.Dif_fatora
#print axioms ATK.ZeroClasses.Fronteira.Dif_zero_iff
#print axioms ATK.ZeroClasses.Fronteira.Dif_equidistante
#print axioms ATK.ZeroClasses.Fronteira.Dif_neg_iff
#print axioms ATK.ZeroClasses.Fronteira.Dif_lado
#print axioms ATK.ZeroClasses.Fronteira.Dif01
#print axioms ATK.ZeroClasses.Fronteira.Dif01_zero_iff
#print axioms ATK.ZeroClasses.Fronteira.Dif12_zero_iff
#print axioms ATK.ZeroClasses.Fronteira.meio_equidistante
#print axioms ATK.ZeroClasses.Fronteira.Dif_reflexao
#print axioms ATK.ZeroClasses.Fronteira.Dif01_antissim
#print axioms ATK.ZeroClasses.Fronteira.reflexao_fixa
#print axioms ATK.ZeroClasses.Fronteira.fronteira_iff
#print axioms ATK.ZeroClasses.Fronteira.fronteira_iff_Dif
#print axioms ATK.ZeroClasses.Fronteira.Dif01_re
#print axioms ATK.ZeroClasses.Fronteira.ponte_iff_RH
#print axioms ATK.ZeroClasses.Fronteira.zero_iff_re_im
#print axioms ATK.ZeroClasses.Fronteira.nao_rh_iff_produtor
#print axioms ATK.ZeroClasses.Fronteira.dl_zero_iff
#print axioms ATK.ZeroClasses.Fronteira.classifica
#print axioms ATK.ZeroClasses.Fronteira.regiao_decimo
#print axioms ATK.ZeroClasses.Fronteira.distancias_exemplos
#print axioms ATK.ZeroClasses.Fronteira.reflexo_zero
#print axioms ATK.ZeroClasses.Fronteira.simetria_permite_pares
#print axioms ATK.ZeroClasses.Fronteira.tolerancia_independente
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.larg_nonneg
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.soma_correta
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.pts_soma
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.soma_assoc
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.soma_comm
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.soma_zero
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.pt_soma
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.larg_soma
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.sub_auto
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.zero_mem_sub_auto
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.sub_auto_eq_zero_iff
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.sem_inverso
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.estados_iff
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.estados_pt
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.estados_tolerancia
#print axioms ATK.ZeroClasses.Fronteira.Intervalo.estados_unidade
#print axioms ATK.ZeroClasses.Fronteira.aval_ne_falso_iff
#print axioms ATK.ZeroClasses.Fronteira.aval_fronteira_iff
#print axioms ATK.ZeroClasses.Fronteira.aval_meio
#print axioms ATK.ZeroClasses.Fronteira.aval_colapso
