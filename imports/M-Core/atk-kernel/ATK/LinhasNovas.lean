import Mathlib.Data.ENat.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Finite.List

/-!
# Linhas de pesquisa novas: como o kernel reage

Propostas do autor (números finais, maior negativo, frações sem cauda finita, o ciclo pelo
infinito, a constante ½ que conecta as conjecturas, "P aproximado de NP") formalizadas do jeito
mais fiel possível. Para cada uma o kernel decide uma de três coisas:

| linha | dentro do conjunto padrão | numa extensão |
|---|---|---|
| **N final sem N+1** | **CONTRADITÓRIA** em `ℕ` (`natural_final_vazio`) | **CONSISTENTE** em `ℕ∞`: `⊤ + 1 = ⊤` (`enat_final`), ao preço de perder o cancelamento (`enat_sem_cancelamento`) |
| **maior real negativo** | **CONTRADITÓRIA** em `ℝ` (`sem_maior_negativo`) | **CONSISTENTE** em `ℤ`: é `−1` (`int_maior_negativo`) |
| **fração sem cauda finita** | **JÁ EXISTE** em `ℝ`: `1/3` (`um_terco_cauda_infinita`) e `√2` (`raiz_dois_cauda_infinita`) | — |
| **ciclo `+∞ = −∞`, `∞ ↔ 0`** | — | **CONSISTENTE** na reta projetiva `ℝ ∪ {∞}`: `−∞ = ∞` (`neg_inf`), `1/0 = ∞`, `1/∞ = 0`, inversão involutiva (`inv_inv`) |
| **½ conecta as conjecturas** | **NORMALIZÁVEL** para RH, BSD e Hodge: os centros `½`, `1`, `p = q` viram `½` por mudança de escala (`centro_bsd_normalizado`, `centro_hodge_normalizado`) | não se aplica a P vs NP, Beal, NS e YM (não há involução no enunciado) |
| **P aproximado de NP** | **VAZIA**: toda linguagem é limite dos seus truncamentos finitos (`aproximacao_trivial`), seja de P ou não; não distingue P de NP | — |
-/

open Filter

namespace ATK.LinhasNovas

/-! ## 1. O número natural final -/

/-- Uma proposta de natural final: um `N` sem sucessor novo. -/
structure NaturalFinal where
  N : ℕ
  final : N + 1 = N

/-- **Em `ℕ` a linha é contraditória**: não existe natural final. -/
theorem natural_final_vazio : IsEmpty NaturalFinal := ⟨fun h => by have := h.final; omega⟩

/-- Em `ℕ` não há último elemento. -/
theorem sem_ultimo_natural : ¬ ∃ N : ℕ, ∀ n : ℕ, n ≤ N := fun ⟨N, h⟩ => by
  have := h (N + 1); omega

/-- **Em `ℕ∞` a linha é consistente**: `⊤ + 1 = ⊤`, e `⊤` está acima de todo natural. -/
theorem enat_final : (⊤ : ℕ∞) + 1 = ⊤ ∧ ∀ n : ℕ, (n : ℕ∞) < ⊤ :=
  ⟨by simp, fun n => ENat.natCast_lt_top n⟩

/-- **O preço**: em `ℕ∞` o cancelamento falha (`⊤ + 1 = ⊤ + 0` com `1 ≠ 0`). -/
theorem enat_sem_cancelamento : (⊤ : ℕ∞) + 1 = ⊤ + 0 ∧ (1 : ℕ∞) ≠ 0 := ⟨by simp, one_ne_zero⟩

/-! ## 2. O maior número real negativo -/

/-- **Em `ℝ` a linha é contraditória**: não existe maior negativo (`r/2` fica entre `r` e `0`). -/
theorem sem_maior_negativo : ¬ ∃ r : ℝ, r < 0 ∧ ∀ x : ℝ, x < 0 → x ≤ r := by
  rintro ⟨r, hr, h⟩
  have := h (r / 2) (by linarith)
  linarith

/-- **Em `ℤ` a linha é consistente**: o maior negativo é `−1`. -/
theorem int_maior_negativo : (-1 : ℤ) < 0 ∧ ∀ x : ℤ, x < 0 → x ≤ -1 :=
  ⟨by norm_num, fun x hx => by omega⟩

/-! ## 3. Frações sem cauda finita -/

/-- Expansão decimal finita: `x = k / 10ⁿ`. -/
def CaudaFinita (x : ℝ) : Prop := ∃ (k : ℤ) (n : ℕ), x = k / 10 ^ n

/-- **`1/3` não tem cauda finita** (`3 ∤ 10ⁿ`): já é um número de `ℝ`, não um conjunto novo. -/
theorem um_terco_cauda_infinita : ¬ CaudaFinita (1 / 3) := by
  rintro ⟨k, n, h⟩
  have h10 : (10 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h' : ((10 : ℤ) ^ n : ℝ) = ((3 * k : ℤ) : ℝ) := by
    push_cast
    field_simp at h
    linarith
  have hz : (10 : ℤ) ^ n = 3 * k := by exact_mod_cast h'
  have := congrArg (Int.cast : ℤ → ZMod 3) hz
  push_cast at this
  have h1 : (10 : ZMod 3) = 1 := by decide
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [h1, h3, one_pow, zero_mul] at this
  exact absurd this (by decide)

/-- **`√2` não tem cauda finita** (é irracional). -/
theorem raiz_dois_cauda_infinita : ¬ CaudaFinita (Real.sqrt 2) := by
  rintro ⟨k, n, h⟩
  apply irrational_sqrt_two
  refine ⟨(k : ℚ) / 10 ^ n, ?_⟩
  rw [h]
  push_cast
  ring

/-! ## 4. O ciclo pelo infinito: a reta projetiva -/

/-- A reta projetiva real `ℝ ∪ {∞}`: `none` é o único ponto no infinito. -/
abbrev RetaProj := Option ℝ

/-- O ponto no infinito. -/
def infinito : RetaProj := none

/-- Inversão `x ↦ 1/x`, com `1/0 = ∞` e `1/∞ = 0`. -/
noncomputable def inv : RetaProj → RetaProj
  | none => some 0
  | some x => if x = 0 then none else some x⁻¹

/-- Negação `x ↦ −x`, com `−∞ = ∞`. -/
def neg : RetaProj → RetaProj
  | none => none
  | some x => some (-x)

theorem inv_inf : inv infinito = some 0 := rfl

theorem inv_zero : inv (some 0) = infinito := by simp [inv, infinito]

/-- **`+∞ = −∞`**: na reta projetiva há um só infinito. -/
theorem neg_inf : neg infinito = infinito := rfl

/-- A inversão é involutiva: o ciclo `0 → ∞ → 0` fecha. -/
theorem inv_inv (x : RetaProj) : inv (inv x) = x := by
  rcases x with _ | x
  · simp [inv]
  · by_cases hx : x = 0
    · subst hx; simp [inv]
    · simp [inv, hx]

/-- Inverter e negar comutam: passar pelo infinito leva do positivo ao negativo e vice-versa. -/
theorem inv_neg (x : RetaProj) : inv (neg x) = neg (inv x) := by
  rcases x with _ | x
  · simp [inv, neg]
  · by_cases hx : x = 0
    · subst hx; simp [inv, neg]
    · simp [inv, neg, hx]

/-! ## 5. A constante ½: centros de simetria normalizados -/

/-- O ponto fixo de `x ↦ a − x` é `a/2`, e é único. -/
theorem centro_reflexao (a x : ℝ) : a - x = x ↔ x = a / 2 := by
  constructor <;> intro h <;> linarith

/-- RH: `s ↦ 1 − s` tem centro `½`. -/
theorem centro_rh (σ : ℝ) : 1 - σ = σ ↔ σ = 1 / 2 := centro_reflexao 1 σ

/-- BSD: `s ↦ 2 − s` tem centro `1`, que **não** é `½` … -/
theorem centro_bsd (s : ℝ) : 2 - s = s ↔ s = 1 := by
  rw [centro_reflexao]; norm_num

/-- … mas, normalizando `t = s − ½`, a simetria vira `t ↦ 1 − t`, de centro `½`. -/
theorem centro_bsd_normalizado (s : ℝ) : (2 - s) - 1 / 2 = 1 - (s - 1 / 2) := by ring

/-- Hodge: em peso `n > 0`, `(p, q) ↦ (q, p)` com `p + q = n`; normalizando `x = p/n`, a simetria é
`x ↦ 1 − x` e o centro `p = q` vira `x = ½`. -/
theorem centro_hodge_normalizado {n p q : ℝ} (hn : n ≠ 0) (hpq : p + q = n) :
    q / n = 1 - p / n ∧ (p = q ↔ p / n = 1 / 2) := by
  constructor
  · field_simp; linarith
  · constructor
    · intro h; field_simp; linarith
    · intro h; field_simp at h; linarith

/-! ## 6. "P aproximado de NP" -/

/-- O truncamento de uma linguagem em comprimento `≤ k` (sempre uma linguagem finita). -/
def truncamento (L : Set (List Bool)) (k : ℕ) : Set (List Bool) := {w ∈ L | w.length ≤ k}

/-- **Toda** linguagem é o limite dos seus truncamentos finitos: palavra a palavra, o truncamento
acaba concordando com a linguagem. Vale para qualquer `L`, esteja em P ou não; essa noção de
aproximação não distingue P de NP. -/
theorem aproximacao_trivial (L : Set (List Bool)) (w : List Bool) :
    ∀ᶠ k in atTop, (w ∈ truncamento L k ↔ w ∈ L) := by
  filter_upwards [eventually_ge_atTop w.length] with k hk
  exact ⟨fun h => h.1, fun h => ⟨h, hk⟩⟩

theorem truncamento_finito (L : Set (List Bool)) (k : ℕ) : (truncamento L k).Finite := by
  apply Set.Finite.subset (List.finite_length_le (α := Bool) (n := k))
  exact fun w hw => hw.2

end ATK.LinhasNovas

#print axioms ATK.LinhasNovas.natural_final_vazio
#print axioms ATK.LinhasNovas.sem_ultimo_natural
#print axioms ATK.LinhasNovas.enat_final
#print axioms ATK.LinhasNovas.enat_sem_cancelamento
#print axioms ATK.LinhasNovas.sem_maior_negativo
#print axioms ATK.LinhasNovas.int_maior_negativo
#print axioms ATK.LinhasNovas.um_terco_cauda_infinita
#print axioms ATK.LinhasNovas.raiz_dois_cauda_infinita
#print axioms ATK.LinhasNovas.inv_inf
#print axioms ATK.LinhasNovas.inv_zero
#print axioms ATK.LinhasNovas.neg_inf
#print axioms ATK.LinhasNovas.inv_inv
#print axioms ATK.LinhasNovas.inv_neg
#print axioms ATK.LinhasNovas.centro_reflexao
#print axioms ATK.LinhasNovas.centro_rh
#print axioms ATK.LinhasNovas.centro_bsd
#print axioms ATK.LinhasNovas.centro_bsd_normalizado
#print axioms ATK.LinhasNovas.centro_hodge_normalizado
#print axioms ATK.LinhasNovas.aproximacao_trivial
#print axioms ATK.LinhasNovas.truncamento_finito
