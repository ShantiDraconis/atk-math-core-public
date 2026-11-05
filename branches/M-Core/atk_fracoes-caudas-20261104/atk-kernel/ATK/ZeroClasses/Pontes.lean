import ATK.ZeroClasses.Forcar
import ATK.CookLevinNP

/-!
# ATK-ZERO-CLASSES — as pontes B1–B23 no kernel: SAT, divisibilidade, determinantes, espectro, ordem de
anulação, função geradora, e as relações entre P e NP no modelo genuíno

Rodada 24. As pontes enviadas (B1–B23) passam a ser **teoremas do kernel**, e a parte de P vs NP é ligada ao modelo
genuíno que o kernel já tem (`ATK.LigacaoPNP.classeP`, `classeNP` sobre `Turing.FinTM2`, `P_sub_NP`, e o teorema
de Cook–Levin `ATK.CookLevinNP.cookLevin`).

**1. Contagem genérica** (`Nz`, `Zpol`, `ordem_Zpol`, `det_diag_zero_iff`, `nucleo_iff`, `posto_mais_nucleo`,
`det_regularizado`, `lacuna_espectral`, `Fger_zero`, `Fger_aprox`, `recupera_contagem`). Para `r : ι → ℕ` num tipo
finito: `ord_{t=0} ∏(t + rᵢ²) = #{rᵢ = 0}`; `det diag(r) = 0 ⟺ ∃ rᵢ = 0 ⟺ núcleo não trivial`; posto + `N` = `|ι|`;
`det(diag(r²) + tI) = ∏(rᵢ² + t)`; lacuna `0` ou `≥ 1`; `F(z) = Σ z^{rᵢ}` tem `F(0) = N` e `0 ≤ F(z) − N ≤ |ι|·z`;
com `|ι|·z ≤ ¼`, todo `v` a menos de `¼` de `F(z)` arredonda para `N` (**T2 / ATK-CLOSED-3**).

**2. SAT no formato `Fin n`** (`Rphi_le`, `B1_divisibilidade`, `S_um_iff`, `sat_iff_raiz_real`, `cadeia_sat`,
`exemplo_um`, `exemplo_zero`). `B > m ⟹ (R = 0 ⟺ B ∣ R)`; `∏(1 − q_C) = 1 ⟺ R = 0`; **SAT ⟺ o polinômio real
`Q_φ = R_φ² + Σ(xᵢ(1 − xᵢ))²` tem raiz real**; e a cadeia `SAT ⟺ N > 0 ⟺ det D = 0 ⟺ núcleo ≠ 0 ⟺ ord Z > 0 ⟺ F(0) > 0`.
Exemplos: `(x∨y)∧(¬x∨y)∧(x∨¬y)` tem `N = 1`; `x ∧ ¬x` tem `N = 0`.

**3. A ordem de anulação no modelo genuíno** (`RK_zero_iff`, `var_lt`, `satisfativel_iff_fin`,
`satisfativel_iff_ordem`, `ZERO_ORDER`, `zero_order_eq_sat`). Para as fórmulas `CNF` do kernel, `ZERO_ORDER =
{cod ψ | ord_{t=0} Z_ψ(t) > 0}` **é** a linguagem `SAT`.

**4. As relações entre P e NP** (`p_le_np`, `p_ge_np_iff`, `p_gt_np_falso`, `p_lt_np_iff`, `dicotomia`,
`p_eq_np_iff_sat`, `p_ne_np_iff_sat`, `p_eq_np_iff_zero_order`, `p_ne_np_iff_zero_order`, `aproximacao_nao_basta`,
`aproximacao_com_retorno`, `troca_quantificadores`). `P ≤ NP` é teorema; `P > NP` é falso; `P ≥ NP ⟺ P = NP`;
`P < NP ⟺ P ≠ NP`; **exatamente um** de `P = NP`, `P < NP`. Com Cook–Levin: `P = NP ⟺ SAT ∈ P ⟺ ZERO_ORDER ∈ P`.
"`P ≈ NP`" (uma classe `R` com `P ⊆ R ⊇ NP`) não dá igualdade; e trocar `∀k ∃A_k` por `∃A ∃c` falha (`n^{n+1}`).
Nada disso decide P vs NP.

**5. Pendência fechada** (`xi_deriv_simples`, `xi_deriv_primeiro_zero`): num zero simples não trivial,
`ξ′(ρ) = ½ρ(ρ−1)Γℝ(ρ)ζ′(ρ) ≠ 0`; em particular `ξ′(ρ₁) ≠ 0` (era BUILD_PENDING na rodada 21).
-/

open Polynomial Matrix Filter Topology

namespace ATK.ZeroClasses.Pontes

open ATK.ZeroClasses.Forcar

/-! ## 1. Contagem genérica -/

section Generico

variable {ι : Type*} [Fintype ι] (r : ι → ℕ)

/-- `N = #{i | rᵢ = 0}`. -/
def Nz : ℕ := (Finset.univ.filter fun i => r i = 0).card

theorem Nz_pos_iff : 0 < Nz r ↔ ∃ i, r i = 0 := by
  unfold Nz
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- `Z(t) = ∏ᵢ (t + rᵢ²)`. -/
noncomputable def Zpol : ℚ[X] := ∏ i, (X - C (-((r i : ℚ) ^ 2)))

theorem Zpol_ne_zero : Zpol r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => X_sub_C_ne_zero _

/-- **A ordem de anulação em `t = 0` é o número de zeros**: `ord₀ Z = N`. -/
theorem ordem_Zpol : rootMultiplicity 0 (Zpol r) = Nz r := by
  rw [← count_roots, Zpol, roots_prod _ _ (Zpol_ne_zero r), Multiset.count_bind]
  simp only [roots_X_sub_C, Multiset.count_singleton]
  unfold Nz
  rw [Finset.card_filter]
  rw [← Finset.sum_eq_multiset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : r i = 0
  · simp [h]
  · have : (0 : ℚ) ≠ -((r i : ℚ) ^ 2) := by
      have : (0 : ℚ) < (r i : ℚ) ^ 2 := by positivity
      linarith
    simp [h, this]

theorem det_diag_zero_iff [DecidableEq ι] : (diagonal fun i => (r i : ℚ)).det = 0 ↔ ∃ i, r i = 0 := by
  rw [det_diagonal, Finset.prod_eq_zero_iff]
  simp

/-- **Núcleo não trivial ⟺ algum `rᵢ = 0`.** -/
theorem nucleo_iff [DecidableEq ι] : (∃ v ≠ 0, (diagonal fun i => (r i : ℚ)) *ᵥ v = 0) ↔ ∃ i, r i = 0 := by
  rw [exists_mulVec_eq_zero_iff, det_diag_zero_iff]

/-- **Posto + `N` = dimensão**: a nulidade de `diag(r)` é o número de zeros. -/
theorem posto_mais_nucleo [DecidableEq ι] : Nz r + (diagonal fun i => (r i : ℚ)).rank = Fintype.card ι := by
  rw [rank_diagonal, Fintype.card_subtype]
  unfold Nz
  have e : (Finset.univ.filter fun i => (r i : ℚ) ≠ 0) = Finset.univ.filter fun i => ¬ r i = 0 := by
    ext i; simp
  rw [e, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- **Determinante regularizado**: `det(diag(r²) + tI) = Z(t)`. -/
theorem det_regularizado [DecidableEq ι] (t : ℚ) :
    (diagonal (fun i => (r i : ℚ) ^ 2) + t • (1 : Matrix ι ι ℚ)).det = (Zpol r).eval t := by
  rw [smul_one_eq_diagonal, diagonal_add, det_diagonal, Zpol, eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp; ring

/-- **Lacuna espectral**: ou algum `rᵢ² = 0`, ou todos `rᵢ² ≥ 1`. -/
theorem lacuna_espectral : (∃ i, (r i : ℚ) ^ 2 = 0) ∨ ∀ i, 1 ≤ (r i : ℚ) ^ 2 := by
  by_cases h : ∃ i, r i = 0
  · obtain ⟨i, hi⟩ := h; exact Or.inl ⟨i, by simp [hi]⟩
  · push Not at h
    right; intro i
    have : (1 : ℚ) ≤ r i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (h i)
    nlinarith

/-- Função geradora `F(z) = Σᵢ z^{rᵢ}`. -/
noncomputable def Fger (z : ℝ) : ℝ := ∑ i, z ^ (r i)

theorem Nz_eq_sum : (Nz r : ℝ) = ∑ i, if r i = 0 then (1 : ℝ) else 0 := by
  unfold Nz; rw [Finset.card_filter]; push_cast; rfl

/-- **`F(0) = N`** (o termo constante conta os zeros). -/
theorem Fger_zero : Fger r 0 = Nz r := by
  rw [Nz_eq_sum, Fger]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : r i = 0
  · simp [h]
  · simp [h, zero_pow h]

/-- **Aproximação**: `0 ≤ F(z) − N ≤ |ι|·z` para `0 ≤ z ≤ 1`. -/
theorem Fger_aprox {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    0 ≤ Fger r z - Nz r ∧ Fger r z - Nz r ≤ Fintype.card ι * z := by
  have e : Fger r z - Nz r = ∑ i, (z ^ (r i) - if r i = 0 then (1 : ℝ) else 0) := by
    rw [Nz_eq_sum, Fger, ← Finset.sum_sub_distrib]
  have hterm : ∀ i, 0 ≤ z ^ (r i) - (if r i = 0 then (1 : ℝ) else 0) ∧
      z ^ (r i) - (if r i = 0 then (1 : ℝ) else 0) ≤ z := by
    intro i
    by_cases h : r i = 0
    · simp [h, h0]
    · simp only [h, ↓reduceIte, sub_zero]
      exact ⟨pow_nonneg h0 _, pow_le_of_le_one h0 h1 h⟩
  rw [e]
  refine ⟨Finset.sum_nonneg fun i _ => (hterm i).1, ?_⟩
  calc ∑ i, (z ^ (r i) - if r i = 0 then (1 : ℝ) else 0) ≤ ∑ _i : ι, z :=
        Finset.sum_le_sum fun i _ => (hterm i).2
    _ = Fintype.card ι * z := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Recuperação exata (T2)**: se `|ι|·z ≤ ¼`, todo `v` com `|v − F(z)| < ¼` arredonda para `N`. -/
theorem recupera_contagem {z v : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) (hz : Fintype.card ι * z ≤ 1 / 4)
    (hv : |v - Fger r z| < 1 / 4) :
    |v - Nz r| < 1 / 2 ∧ ∀ k : ℕ, |v - k| < 1 / 2 → k = Nz r := by
  obtain ⟨a, b⟩ := Fger_aprox r h0 h1
  rw [abs_lt] at hv
  have hN : |v - Nz r| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
  refine ⟨hN, fun k hk => ?_⟩
  rw [abs_lt] at hk hN
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (k : ℝ) + 1 ≤ Nz r := by exact_mod_cast h
    linarith
  · have : (Nz r : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith

end Generico

/-! ## 2. SAT no formato `Fin n` (as pontes B1, B2, B10–B19) -/

section FinN

variable {n : ℕ}

theorem viol_le (x : Fin n → Bool) (C : List (Lit n)) : viol x C ≤ 1 := by
  unfold viol; split <;> omega

theorem Rphi_le (φ : List (List (Lit n))) (x : Fin n → Bool) : Rphi φ x ≤ φ.length := by
  unfold Rphi
  have := List.sum_le_length_nsmul (φ.map (viol x)) 1 (by
    intro a ha
    obtain ⟨C, -, rfl⟩ := List.mem_map.mp ha
    exact viol_le x C)
  simpa using this

/-- **B1 (divisibilidade)**: se `B` excede o número de cláusulas, `R = 0 ⟺ B ∣ R`. -/
theorem B1_divisibilidade (φ : List (List (Lit n))) (x : Fin n → Bool) {B : ℕ} (hB : φ.length < B) :
    Rphi φ x = 0 ↔ B ∣ Rphi φ x :=
  ⟨fun h => h ▸ dvd_zero B, fun h => Nat.eq_zero_of_dvd_of_lt h (lt_of_le_of_lt (Rphi_le φ x) hB)⟩

/-- `S_φ(x) = ∏_C (1 − q_C(x))`. -/
def Sphi (φ : List (List (Lit n))) (x : Fin n → Bool) : ℕ := (φ.map fun C => 1 - viol x C).prod

/-- **B10**: `S_φ(x) = 1 ⟺ R_φ(x) = 0`. -/
theorem S_um_iff (φ : List (List (Lit n))) (x : Fin n → Bool) : Sphi φ x = 1 ↔ Rphi φ x = 0 := by
  induction φ with
  | nil => simp [Sphi, Rphi]
  | cons C φ ih =>
    simp only [Sphi, Rphi, List.map_cons, List.prod_cons, List.sum_cons] at ih ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (viol_le x C) with h | h
    · simp only [h, Nat.sub_zero, one_mul, zero_add]; exact ih
    · simp [h]

/-- Relaxação real de um literal. -/
noncomputable def litR (x : Fin n → ℝ) (l : Lit n) : ℝ := if l.2 then x l.1 else 1 - x l.1

/-- `q_C(x) = ∏_{ℓ ∈ C} (1 − ℓ(x))` sobre os reais. -/
noncomputable def qR (x : Fin n → ℝ) (C : List (Lit n)) : ℝ := (C.map fun l => 1 - litR x l).prod

noncomputable def RR (φ : List (List (Lit n))) (x : Fin n → ℝ) : ℝ := (φ.map (qR x)).sum

/-- **`Q_φ(x) = R_φ(x)² + Σᵢ (xᵢ(1 − xᵢ))²`.** -/
noncomputable def QR (φ : List (List (Lit n))) (x : Fin n → ℝ) : ℝ :=
  RR φ x ^ 2 + ∑ i, (x i * (1 - x i)) ^ 2

def boolR (b : Fin n → Bool) : Fin n → ℝ := fun i => if b i then 1 else 0

theorem um_menos_litR (b : Fin n → Bool) (l : Lit n) :
    1 - litR (boolR b) l = if litVal b l then 0 else 1 := by
  rcases l with ⟨i, p⟩
  unfold litR boolR litVal
  cases hb : b i <;> cases p <;> simp

theorem qR_bool (b : Fin n → Bool) (C : List (Lit n)) : qR (boolR b) C = viol b C := by
  rw [viol_eq_prod, qR, Nat.cast_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp, um_menos_litR]
  split <;> simp

theorem RR_bool (φ : List (List (Lit n))) (b : Fin n → Bool) : RR φ (boolR b) = Rphi φ b := by
  rw [RR, Rphi, Nat.cast_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun C _ => qR_bool b C

theorem QR_zero_iff (φ : List (List (Lit n))) (x : Fin n → ℝ) :
    QR φ x = 0 ↔ RR φ x = 0 ∧ ∀ i, x i * (1 - x i) = 0 := by
  unfold QR
  have hs : 0 ≤ ∑ i, (x i * (1 - x i)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  constructor
  · intro h
    have h1 : RR φ x ^ 2 = 0 := by nlinarith [sq_nonneg (RR φ x)]
    have h2 : ∑ i, (x i * (1 - x i)) ^ 2 = 0 := by nlinarith [sq_nonneg (RR φ x)]
    refine ⟨pow_eq_zero_iff (by norm_num) |>.mp h1, fun i => ?_⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j * (1 - x j))).mp h2 i
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

/-- **B2: SAT ⟺ o polinômio real `Q_φ` tem raiz real.** -/
theorem sat_iff_raiz_real (φ : List (List (Lit n))) : Sat φ ↔ ∃ x : Fin n → ℝ, QR φ x = 0 := by
  rw [sat_iff_zero]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨boolR b, (QR_zero_iff φ _).mpr ⟨by rw [RR_bool, hb]; simp, fun i => ?_⟩⟩
    unfold boolR; split <;> simp
  · rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := (QR_zero_iff φ x).mp hx
    have hx01 : ∀ i, x i = 0 ∨ x i = 1 := fun i => by
      rcases mul_eq_zero.mp (h2 i) with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    let b : Fin n → Bool := fun i => decide (x i = 1)
    have hxb : x = boolR b := by
      funext i
      unfold boolR
      rcases hx01 i with h | h
      · have : x i ≠ 1 := by rw [h]; norm_num
        simp [b, h]
      · simp [b, h]
    refine ⟨b, ?_⟩
    have := RR_bool φ b
    rw [← hxb, h1] at this
    exact_mod_cast this.symm

/-- **A cadeia (ATK-CLOSED-1)**: `SAT ⟺ N > 0 ⟺ det D = 0 ⟺ núcleo ≠ 0 ⟺ ord₀ Z > 0 ⟺ F(0) > 0`. -/
theorem cadeia_sat (φ : List (List (Lit n))) :
    (Sat φ ↔ 0 < Nz (Rphi φ)) ∧ (Sat φ ↔ (diagonal fun x => (Rphi φ x : ℚ)).det = 0) ∧
    (Sat φ ↔ ∃ v ≠ 0, (diagonal fun x => (Rphi φ x : ℚ)) *ᵥ v = 0) ∧
    (Sat φ ↔ 0 < rootMultiplicity 0 (Zpol (Rphi φ))) ∧ (Sat φ ↔ 0 < Fger (Rphi φ) 0) := by
  have h0 : Sat φ ↔ ∃ x, Rphi φ x = 0 := sat_iff_zero φ
  refine ⟨h0.trans (Nz_pos_iff _).symm, h0.trans (det_diag_zero_iff _).symm,
    h0.trans (nucleo_iff _).symm, ?_, ?_⟩
  · rw [ordem_Zpol]; exact h0.trans (Nz_pos_iff _).symm
  · rw [Fger_zero]; exact_mod_cast h0.trans (Nz_pos_iff _).symm

/-- **ATK-CLOSED-2**: `#SAT = ord₀ Z = F(0)`. -/
theorem contagem_unificada (φ : List (List (Lit n))) :
    rootMultiplicity 0 (Zpol (Rphi φ)) = Nz (Rphi φ) ∧ Fger (Rphi φ) 0 = Nz (Rphi φ) :=
  ⟨ordem_Zpol _, Fger_zero _⟩

/-- `(x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y)`: exatamente uma atribuição satisfaz (`N = 1`). -/
theorem exemplo_um :
    Nz (Rphi [[((0 : Fin 2), true), ((1 : Fin 2), true)], [((0 : Fin 2), false), ((1 : Fin 2), true)],
      [((0 : Fin 2), true), ((1 : Fin 2), false)]]) = 1 := by decide

/-- `x ∧ ¬x`: nenhuma (`N = 0`). -/
theorem exemplo_zero : Nz (Rphi [[((0 : Fin 1), true)], [((0 : Fin 1), false)]]) = 0 := by decide

end FinN

/-! ## 3. A ordem de anulação no modelo genuíno -/

section Genuino

open ATK.ModeloPNP ATK.LigacaoPNP

/-- Violação de uma cláusula do kernel por `τ : ℕ → Bool`. -/
def violK (τ : ℕ → Bool) (C : Clausula) : ℕ := if C.any (fun l => τ l.1 == l.2) then 0 else 1

/-- `R(τ, ψ)`: número de cláusulas violadas. -/
def RK (τ : ℕ → Bool) (ψ : CNF) : ℕ := (ψ.map (violK τ)).sum

theorem RK_zero_iff (τ : ℕ → Bool) (ψ : CNF) : RK τ ψ = 0 ↔ Satisfaz τ ψ := by
  unfold RK Satisfaz
  rw [List.sum_eq_zero_iff]
  constructor
  · intro h C hC
    have := h (violK τ C) (List.mem_map.mpr ⟨C, hC, rfl⟩)
    unfold violK at this
    split at this
    · rename_i hany
      obtain ⟨l, hl, hb⟩ := List.any_eq_true.mp hany
      exact ⟨l, hl, by simpa using hb⟩
    · exact absurd this (by norm_num)
  · intro h k hk
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hk
    obtain ⟨l, hl, hb⟩ := h C hC
    have : C.any (fun l => τ l.1 == l.2) = true := List.any_eq_true.mpr ⟨l, hl, by simpa using hb⟩
    simp [violK, this]

/-- Quantas variáveis bastam: `nv ψ = Σ (índice + 1)` sobre os literais. -/
def nv (ψ : CNF) : ℕ := (ψ.flatMap fun C => C.map fun l => l.1 + 1).sum

theorem var_lt {ψ : CNF} {C : Clausula} {l : Literal} (hC : C ∈ ψ) (hl : l ∈ C) : l.1 < nv ψ := by
  have hm : l.1 + 1 ∈ ψ.flatMap fun C => C.map fun l => l.1 + 1 :=
    List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
  have := List.le_sum_of_mem hm
  unfold nv; omega

/-- Extensão de uma atribuição finita. -/
def extA (ψ : CNF) (x : Fin (nv ψ) → Bool) : ℕ → Bool := fun k => if h : k < nv ψ then x ⟨k, h⟩ else false

theorem satisfativel_iff_fin (ψ : CNF) : Satisfativel ψ ↔ ∃ x : Fin (nv ψ) → Bool, RK (extA ψ x) ψ = 0 := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i => τ i.val, (RK_zero_iff _ _).mpr fun C hC => ?_⟩
    obtain ⟨l, hl, he⟩ := hτ C hC
    exact ⟨l, hl, by simp [extA, var_lt hC hl, he]⟩
  · rintro ⟨x, hx⟩
    exact ⟨extA ψ x, (RK_zero_iff _ _).mp hx⟩

/-- `r_ψ(x) = R(ext x, ψ)` sobre as atribuições finitas. -/
def rK (ψ : CNF) : (Fin (nv ψ) → Bool) → ℕ := fun x => RK (extA ψ x) ψ

/-- **Satisfatível ⟺ ordem de anulação positiva.** -/
theorem satisfativel_iff_ordem (ψ : CNF) : Satisfativel ψ ↔ 0 < rootMultiplicity 0 (Zpol (rK ψ)) := by
  rw [ordem_Zpol, Nz_pos_iff, satisfativel_iff_fin]; rfl

/-- `ZERO_ORDER = {cod ψ | ord_{t=0} Z_ψ(t) > 0}`. -/
def ZERO_ORDER : Linguagem := {w | ∃ ψ : CNF, codCNF ψ = w ∧ 0 < rootMultiplicity 0 (Zpol (rK ψ))}

/-- **`ZERO_ORDER = SAT`** (B19 + B23 no modelo genuíno). -/
theorem zero_order_eq_sat : ZERO_ORDER = SAT := by
  ext w
  constructor
  · rintro ⟨ψ, hψ, h⟩; exact ⟨ψ, hψ, (satisfativel_iff_ordem ψ).mpr h⟩
  · rintro ⟨ψ, hψ, h⟩; exact ⟨ψ, hψ, (satisfativel_iff_ordem ψ).mp h⟩

/-! ## 4. As relações entre P e NP no modelo genuíno -/

/-- `P ≤ NP` (teorema). -/
theorem p_le_np : classeP ⊆ classeNP := P_sub_NP

/-- `P ≥ NP ⟺ P = NP`. -/
theorem p_ge_np_iff : classeNP ⊆ classeP ↔ classeP = classeNP :=
  ⟨fun h => Set.Subset.antisymm P_sub_NP h, fun h => h ▸ le_rfl⟩

/-- `P > NP` é falso. -/
theorem p_gt_np_falso : ¬ (classeNP ⊂ classeP) := fun h => h.2 P_sub_NP

/-- `P < NP ⟺ P ≠ NP`. -/
theorem p_lt_np_iff : classeP ⊂ classeNP ↔ classeP ≠ classeNP := by
  rw [Set.ssubset_iff_subset_ne]
  exact ⟨fun h => h.2, fun h => ⟨P_sub_NP, h⟩⟩

/-- **Exatamente um** de `P = NP` e `P < NP`. -/
theorem dicotomia : (classeP = classeNP ∨ classeP ⊂ classeNP) ∧
    ¬ (classeP = classeNP ∧ classeP ⊂ classeNP) := by
  refine ⟨?_, fun ⟨h1, h2⟩ => (p_lt_np_iff.mp h2) h1⟩
  by_cases h : classeP = classeNP
  · exact Or.inl h
  · exact Or.inr (p_lt_np_iff.mpr h)

/-- **Com Cook–Levin: `P = NP ⟺ SAT ∈ P`.** -/
theorem p_eq_np_iff_sat : classeP = classeNP ↔ SAT ∈ classeP := by
  constructor
  · intro h; rw [h]; exact ATK.SATemNP.sat_em_NP
  · intro h
    refine Set.Subset.antisymm P_sub_NP fun L hL => ?_
    exact P_fechada_red (ATK.CookLevinNP.red_SAT hL) h

theorem p_ne_np_iff_sat : classeP ≠ classeNP ↔ SAT ∉ classeP := not_congr p_eq_np_iff_sat

/-- **B22: `P = NP ⟺ ZERO_ORDER ∈ P`.** -/
theorem p_eq_np_iff_zero_order : classeP = classeNP ↔ ZERO_ORDER ∈ classeP := by
  rw [zero_order_eq_sat]; exact p_eq_np_iff_sat

/-- **B23: `P ≠ NP ⟺ ZERO_ORDER ∉ P`.** -/
theorem p_ne_np_iff_zero_order : classeP ≠ classeNP ↔ ZERO_ORDER ∉ classeP :=
  not_congr p_eq_np_iff_zero_order

/-- **"`P ≈ NP`" não dá igualdade**: uma classe intermediária `A ⊆ B ⊆ R` com `A ⊂ B` existe. -/
theorem aproximacao_nao_basta : ∃ A B R : Set ℕ, A ⊆ B ∧ B ⊆ R ∧ A ⊂ B :=
  ⟨∅, {0}, {0}, Set.empty_subset _, le_rfl, Set.empty_ssubset.mpr ⟨0, rfl⟩⟩

/-- Só com retorno `R ⊆ P` a aproximação vira igualdade. -/
theorem aproximacao_com_retorno {R : Set Linguagem} (h1 : classeNP ⊆ R) (h2 : R ⊆ classeP) :
    classeP = classeNP :=
  Set.Subset.antisymm P_sub_NP (h1.trans h2)

/-- **Troca de quantificadores**: cada `n^{k+1}` é polinomial, mas `n^{n+1}` supera todo `C·n^c`. -/
theorem troca_quantificadores :
    (∀ k : ℕ, ∃ c : ℕ, ∀ m : ℕ, m ^ (k + 1) ≤ m ^ c) ∧ ∀ c C : ℕ, ∃ m : ℕ, C * m ^ c < m ^ (m + 1) := by
  refine ⟨fun k => ⟨k + 1, fun m => le_rfl⟩, fun c C => ⟨c + C + 2, ?_⟩⟩
  set m := c + C + 2
  have hm : 1 ≤ m := by omega
  have hpos : 0 < m ^ c := pow_pos (by omega) _
  have h1 : m ^ (c + 1) ≤ m ^ (m + 1) := Nat.pow_le_pow_right hm (by omega)
  have h2 : C * m ^ c < m * m ^ c := Nat.mul_lt_mul_of_pos_right (by omega) hpos
  calc C * m ^ c < m * m ^ c := h2
    _ = m ^ (c + 1) := by ring
    _ ≤ m ^ (m + 1) := h1

end Genuino

/-! ## 5. Pendência fechada: `ξ′(ρ) ≠ 0` nos zeros simples -/

open Complex in
/-- **Num zero não trivial simples, `ξ′(ρ) = ½ρ(ρ−1)Γℝ(ρ)ζ′(ρ) ≠ 0`.** -/
theorem xi_deriv_simples {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) (hd : deriv riemannZeta ρ ≠ 0) :
    deriv ATK.BaseRiemannXi.riemannXi ρ ≠ 0 := by
  have hre : 0 < ρ.re := hρ.2.1
  have h0 : ρ ≠ 0 := fun h => by rw [h, zero_re] at hre; exact lt_irrefl _ hre
  have h1 : ρ ≠ 1 := fun h => by have := hρ.2.2; rw [h, one_re] at this; exact lt_irrefl _ this
  have hG : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  set h : ℂ → ℂ := fun s => s * (s - 1) / 2 * Gammaℝ s
  -- `ξ = h·ζ` perto de `ρ`
  have hev : ATK.BaseRiemannXi.riemannXi =ᶠ[𝓝 ρ] fun s => h s * riemannZeta s := by
    have hopen : ∀ᶠ s in 𝓝 ρ, 0 < s.re ∧ s ≠ 1 := by
      have a : ∀ᶠ s in 𝓝 ρ, 0 < s.re :=
        (Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hre))
      have b : ∀ᶠ s in 𝓝 ρ, s ≠ 1 := isOpen_compl_singleton.mem_nhds h1
      exact a.and b
    filter_upwards [hopen] with s ⟨hs, hs1⟩
    have hs0 : s ≠ 0 := fun e => by rw [e, zero_re] at hs; exact lt_irrefl _ hs
    exact ATK.BaseRiemannXi.riemannXi_eq_zeta hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hs)
  -- derivabilidade de `Γℝ` em `ρ`
  have hGd : DifferentiableAt ℂ Gammaℝ ρ := by
    have := (differentiable_Gammaℝ_inv ρ).inv (inv_ne_zero hG)
    have e : (fun s => (Gammaℝ s)⁻¹)⁻¹ = Gammaℝ := funext fun s => by simp
    rwa [e] at this
  have hhd : DifferentiableAt ℂ h ρ := by
    have : DifferentiableAt ℂ (fun s : ℂ => s * (s - 1) / 2) ρ := by fun_prop
    exact this.mul hGd
  have hzd : DifferentiableAt ℂ riemannZeta ρ := differentiableAt_riemannZeta h1
  rw [hev.deriv_eq, deriv_fun_mul hhd hzd, hρ.1, mul_zero, zero_add]
  refine mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero) hG) hd

/-- **`ξ′(ρ₁) ≠ 0`** no primeiro zero certificado. -/
theorem xi_deriv_primeiro_zero : ∃ ρ ∈ ATK.ZetaSimetria.Z, ρ.re = 1 / 2 ∧
    deriv ATK.BaseRiemannXi.riemannXi ρ ≠ 0 := by
  obtain ⟨ρ, hρ, hre, -, hd⟩ := ATK.ZeroClasses.Escalas.primeiro_zero_simples
  exact ⟨ρ, hρ, hre, xi_deriv_simples hρ hd⟩

end ATK.ZeroClasses.Pontes

#print axioms ATK.ZeroClasses.Pontes.Nz_pos_iff
#print axioms ATK.ZeroClasses.Pontes.Zpol_ne_zero
#print axioms ATK.ZeroClasses.Pontes.ordem_Zpol
#print axioms ATK.ZeroClasses.Pontes.det_diag_zero_iff
#print axioms ATK.ZeroClasses.Pontes.nucleo_iff
#print axioms ATK.ZeroClasses.Pontes.posto_mais_nucleo
#print axioms ATK.ZeroClasses.Pontes.det_regularizado
#print axioms ATK.ZeroClasses.Pontes.lacuna_espectral
#print axioms ATK.ZeroClasses.Pontes.Nz_eq_sum
#print axioms ATK.ZeroClasses.Pontes.Fger_zero
#print axioms ATK.ZeroClasses.Pontes.Fger_aprox
#print axioms ATK.ZeroClasses.Pontes.recupera_contagem
#print axioms ATK.ZeroClasses.Pontes.viol_le
#print axioms ATK.ZeroClasses.Pontes.Rphi_le
#print axioms ATK.ZeroClasses.Pontes.B1_divisibilidade
#print axioms ATK.ZeroClasses.Pontes.S_um_iff
#print axioms ATK.ZeroClasses.Pontes.um_menos_litR
#print axioms ATK.ZeroClasses.Pontes.qR_bool
#print axioms ATK.ZeroClasses.Pontes.RR_bool
#print axioms ATK.ZeroClasses.Pontes.QR_zero_iff
#print axioms ATK.ZeroClasses.Pontes.sat_iff_raiz_real
#print axioms ATK.ZeroClasses.Pontes.cadeia_sat
#print axioms ATK.ZeroClasses.Pontes.contagem_unificada
#print axioms ATK.ZeroClasses.Pontes.exemplo_um
#print axioms ATK.ZeroClasses.Pontes.exemplo_zero
#print axioms ATK.ZeroClasses.Pontes.RK_zero_iff
#print axioms ATK.ZeroClasses.Pontes.var_lt
#print axioms ATK.ZeroClasses.Pontes.satisfativel_iff_fin
#print axioms ATK.ZeroClasses.Pontes.satisfativel_iff_ordem
#print axioms ATK.ZeroClasses.Pontes.zero_order_eq_sat
#print axioms ATK.ZeroClasses.Pontes.p_le_np
#print axioms ATK.ZeroClasses.Pontes.p_ge_np_iff
#print axioms ATK.ZeroClasses.Pontes.p_gt_np_falso
#print axioms ATK.ZeroClasses.Pontes.p_lt_np_iff
#print axioms ATK.ZeroClasses.Pontes.dicotomia
#print axioms ATK.ZeroClasses.Pontes.p_eq_np_iff_sat
#print axioms ATK.ZeroClasses.Pontes.p_ne_np_iff_sat
#print axioms ATK.ZeroClasses.Pontes.p_eq_np_iff_zero_order
#print axioms ATK.ZeroClasses.Pontes.p_ne_np_iff_zero_order
#print axioms ATK.ZeroClasses.Pontes.aproximacao_nao_basta
#print axioms ATK.ZeroClasses.Pontes.aproximacao_com_retorno
#print axioms ATK.ZeroClasses.Pontes.troca_quantificadores
#print axioms ATK.ZeroClasses.Pontes.xi_deriv_simples
#print axioms ATK.ZeroClasses.Pontes.xi_deriv_primeiro_zero
