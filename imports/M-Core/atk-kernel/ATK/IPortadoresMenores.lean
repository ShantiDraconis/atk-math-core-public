import ATK.IPortadores
import ATK.IGeometria

/-!
# ATK — Portadores menores de `I`: rodas, multiestado e a lógica `{T, F, I}`

Continuação de `ATK/IPortadores.lean`, mesma referência (`RI = Option ℝ`, `I = none`
absorvente) e mesma fonte (`ShantiDraconis/The-Algebra-of-Ideterminate-I`):

| portador | fonte | veredito |
|---|---|---|
| rodas `ℝ × ℝ` | `main:lean/WheelTheory.lean` (`c681d5cd`) | QUOCIENTE: `toRI` preserva `+` e `·` em todos os pares; a relação `∼` da fonte **não é transitiva**; a inversão só passa fora do denominador nulo |
| multiestado | `copilot/add-annotated-labels-arrows:…/MultiStateI.lean` (`5493bb58`) | COMPATÍVEL no contexto `standard` (`I − I`, `I/I`, `I/0` ↦ `I`, como em `RI`); INCOMPATÍVEL no contexto `limit` (`I − I ↦ 0`, `I/I ↦ 1`) |
| lógica `{T, F, I}` | `main:book/parts/part1/chapter01_preliminary_logic.tex` (`fb45f2e2`) | EQUIVALENTE à lógica K3 de `ATK.IGeometria` (`I ↦ N`), preservando `¬`, `∧`, `∨`; `→` é a implicação de Kleene. Com designado `{T}` a explosão **vale**; só com `{T, I}` (LP) ela falha |

Fidelidade: rodas e lógica transcritas da fonte. No multiestado, a `resolve` da fonte usa `sorry`
no caso residual (quando nenhum estado preferido aparece); aqui esse caso devolve `none`. Os três
conjuntos de estados (`I − I`, `I/I`, `I/0`) são os da fonte.
-/

noncomputable section

namespace ATK.IPortadoresMenores

open ATK.Indeterminacy (RI addI mulI divI)
open ATK.IPortadores (addI_some mulI_some addI_none_left addI_none_right mulI_none_left
  mulI_none_right subI)

/-! ## Rodas (`lean/WheelTheory.lean`) -/

namespace Roda

structure W where
  numerator : ℝ
  denominator : ℝ

/-- A relação `∼` da fonte. -/
def equiv (w₁ w₂ : W) : Prop :=
  (w₁.numerator * w₂.denominator = w₂.numerator * w₁.denominator) ∨
  (w₁.denominator = 0 ∧ w₂.denominator = 0)

def add (w₁ w₂ : W) : W :=
  ⟨w₁.numerator * w₂.denominator + w₂.numerator * w₁.denominator,
   w₁.denominator * w₂.denominator⟩

def mul (w₁ w₂ : W) : W :=
  ⟨w₁.numerator * w₂.numerator, w₁.denominator * w₂.denominator⟩

def inv (w : W) : W := ⟨w.denominator, w.numerator⟩

/-- **A relação da fonte não é transitiva** (por isso `wheel_equiv_trans` e `wheel_setoid` ficaram
com `sorry`): `[1,1] ∼ [0,0] ∼ [2,1]`, mas `[1,1] ≁ [2,1]`. -/
theorem equiv_nao_transitiva :
    equiv ⟨1, 1⟩ ⟨0, 0⟩ ∧ equiv ⟨0, 0⟩ ⟨2, 1⟩ ∧ ¬ equiv ⟨1, 1⟩ ⟨2, 1⟩ := by
  refine ⟨Or.inl (by norm_num), Or.inl (by norm_num), ?_⟩
  intro h
  unfold equiv at h
  rcases h with h | ⟨h, _⟩ <;> norm_num at h

/-- Projeção em `RI` (a `wheel_to_extended` da fonte): denominador nulo ↦ `I`, senão `a/b`. -/
def toRI (w : W) : RI := if w.denominator = 0 then none else some (w.numerator / w.denominator)

/-- **Soma**: `toRI` preserva a soma de pares em todos os casos. -/
theorem toRI_add (w₁ w₂ : W) : toRI (add w₁ w₂) = addI (toRI w₁) (toRI w₂) := by
  obtain ⟨a, b⟩ := w₁
  obtain ⟨c, d⟩ := w₂
  by_cases hb : b = 0
  · subst hb
    simp [toRI, add, addI_none_left]
  · by_cases hd : d = 0
    · subst hd
      simp [toRI, add, hb, addI_none_right]
    · have hbd : b * d ≠ 0 := mul_ne_zero hb hd
      have e1 : toRI ⟨a, b⟩ = some (a / b) := by simp [toRI, hb]
      have e2 : toRI ⟨c, d⟩ = some (c / d) := by simp [toRI, hd]
      have e3 : toRI (add ⟨a, b⟩ ⟨c, d⟩) = some ((a * d + c * b) / (b * d)) := by
        simp [toRI, add, hbd]
      rw [e1, e2, e3, addI_some, div_add_div _ _ hb hd]
      congr 1
      ring

/-- **Produto**: `toRI` preserva o produto de pares em todos os casos. -/
theorem toRI_mul (w₁ w₂ : W) : toRI (mul w₁ w₂) = mulI (toRI w₁) (toRI w₂) := by
  obtain ⟨a, b⟩ := w₁
  obtain ⟨c, d⟩ := w₂
  by_cases hb : b = 0
  · subst hb
    simp [toRI, mul, mulI_none_left]
  · by_cases hd : d = 0
    · subst hd
      simp [toRI, mul, hb, mulI_none_right]
    · have hbd : b * d ≠ 0 := mul_ne_zero hb hd
      have e1 : toRI ⟨a, b⟩ = some (a / b) := by simp [toRI, hb]
      have e2 : toRI ⟨c, d⟩ = some (c / d) := by simp [toRI, hd]
      have e3 : toRI (mul ⟨a, b⟩ ⟨c, d⟩) = some ((a * c) / (b * d)) := by
        simp [toRI, mul, hbd]
      rw [e1, e2, e3, mulI_some, div_mul_div_comm]

/-- A relação certa: o núcleo de `toRI`, que é uma equivalência. -/
def equivK (w₁ w₂ : W) : Prop := toRI w₁ = toRI w₂

theorem equivK_equivalence : Equivalence equivK :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- A `∼` da fonte é grossa demais: identifica `[1,1]` com `[0,0]`; o núcleo não. -/
theorem equiv_grosseira : equiv ⟨1, 1⟩ ⟨0, 0⟩ ∧ ¬ equivK ⟨1, 1⟩ ⟨0, 0⟩ := by
  refine ⟨Or.inl (by norm_num), ?_⟩
  simp [equivK, toRI]

/-- `toRI` identifica `1/0` e `0/0`: estas rodas **não** são a roda de Carlström (`1/0 = ∞ ≠ ⊥`). -/
theorem toRI_um_zero_eq_zero_zero : toRI ⟨1, 0⟩ = toRI ⟨0, 0⟩ := by simp [toRI]

/-- A inversão não passa ao quociente: `/[1,0] = [0,1] ↦ 0`, mas `I⁻¹ = I` em `RI`. -/
theorem toRI_inv_falha :
    toRI (inv ⟨1, 0⟩) ≠ ATK.IPortadores.Nexus.invI (toRI ⟨1, 0⟩) := by
  simp [toRI, inv, ATK.IPortadores.Nexus.invI]

end Roda

/-! ## Multiestado (`MultiStateI.lean`) -/

namespace Multiestado

inductive Estado where
  | zero | one | I | infinity | indeterminate
  deriving DecidableEq

open Estado

/-- `I − I ↦ {0, I, ?}`, `I/I ↦ {1, I, ?}`, `I/0 ↦ {I, ∞, ?}` (seções 106.1–106.3 da fonte). -/
def menosII : Finset Estado := {zero, I, indeterminate}
def divII : Finset Estado := {one, I, indeterminate}
def divI0 : Finset Estado := {I, infinity, indeterminate}

/-- Contexto `standard`: prefere `I`, depois `?`. -/
def resolveStandard (s : Finset Estado) : Option Estado :=
  if I ∈ s then some I else if indeterminate ∈ s then some indeterminate else none

/-- Contexto `limit`: prefere `0`, depois `1`, depois `I`. -/
def resolveLimit (s : Finset Estado) : Option Estado :=
  if zero ∈ s then some zero else if one ∈ s then some one else if I ∈ s then some I else none

/-- Leitura de um valor de `RI` como estado. -/
def estadoDe : RI → Option Estado
  | none => some I
  | some x => if x = 0 then some zero else if x = 1 then some one else none

theorem subI_none : subI none none = none := rfl
theorem divI_none_none : divI none none = none := rfl
theorem divI_none_zero : divI none (some 0) = none := rfl

/-- **Compatível no contexto `standard`**: as três formas resolvem para `I`, o valor de `RI`. -/
theorem standard_eq_RI :
    resolveStandard menosII = estadoDe (subI none none) ∧
      resolveStandard divII = estadoDe (divI none none) ∧
      resolveStandard divI0 = estadoDe (divI none (some 0)) := by
  rw [subI_none, divI_none_none, divI_none_zero]
  refine ⟨?_, ?_, ?_⟩ <;> simp [resolveStandard, menosII, divII, divI0, estadoDe]

/-- **Incompatível no contexto `limit`**: `I − I ↦ 0` e `I/I ↦ 1`, enquanto `RI` dá `I`. -/
theorem limit_difere_de_RI :
    resolveLimit menosII ≠ estadoDe (subI none none) ∧
      resolveLimit divII ≠ estadoDe (divI none none) := by
  rw [subI_none, divI_none_none]
  refine ⟨?_, ?_⟩ <;> simp [resolveLimit, menosII, divII, estadoDe]

end Multiestado

/-! ## A lógica `{T, F, I}` (cap. 1 do livro) -/

namespace LogicaI

inductive V where
  | T | F | I
  deriving DecidableEq

open V

def neg : V → V
  | T => F
  | F => T
  | I => I

/-- O operador de consistência `P°`. -/
def consist : V → V
  | T => T
  | F => T
  | I => F

def conj : V → V → V
  | T, T => T
  | T, F => F
  | T, I => I
  | F, _ => F
  | I, T => I
  | I, F => F
  | I, I => I

def disj : V → V → V
  | T, _ => T
  | F, T => T
  | F, F => F
  | F, I => I
  | I, T => T
  | I, F => I
  | I, I => I

def imp : V → V → V
  | T, T => T
  | T, F => F
  | T, I => I
  | F, _ => T
  | I, T => T
  | I, F => I
  | I, I => I

/-- Tradução para a K3 de `ATK.IGeometria` (`I ↦ N`). -/
def paraK3 : V → ATK.IGeometria.K3
  | T => .T
  | F => .F
  | I => .N

theorem paraK3_bijective : Function.Bijective paraK3 := by
  constructor
  · intro a b h
    cases a <;> cases b <;> first | rfl | cases h
  · intro k
    cases k
    · exact ⟨F, rfl⟩
    · exact ⟨I, rfl⟩
    · exact ⟨T, rfl⟩

theorem paraK3_neg (a : V) : paraK3 (neg a) = ATK.IGeometria.K3.neg (paraK3 a) := by
  cases a <;> rfl

theorem paraK3_conj (a b : V) :
    paraK3 (conj a b) = ATK.IGeometria.K3.e (paraK3 a) (paraK3 b) := by
  cases a <;> cases b <;> rfl

theorem paraK3_disj (a b : V) :
    paraK3 (disj a b) = ATK.IGeometria.K3.ou (paraK3 a) (paraK3 b) := by
  cases a <;> cases b <;> rfl

/-- A implicação da tabela é a de Kleene: `P → Q = ¬P ∨ Q`. -/
theorem imp_eq_kleene (a b : V) : imp a b = disj (neg a) b := by
  cases a <;> cases b <;> rfl

/-- **Com designado `{T}` a explosão vale**: `P ∧ ¬P` nunca é `T`, logo implica tudo
(o "Controlled Indeterminacy" do capítulo não vale nesta leitura). -/
theorem explosao_vale_designado_T (a : V) : conj a (neg a) ≠ T := by
  cases a <;> decide

/-- **Só com designado `{T, I}` (lógica LP) a explosão falha**: `P = I` torna `P ∧ ¬P = I`
designado, e `Q = F` não é designado. -/
theorem explosao_falha_designado_TI : conj I (neg I) = I ∧ F ≠ T ∧ F ≠ I := by
  decide

end LogicaI

end ATK.IPortadoresMenores

end

#print axioms ATK.IPortadoresMenores.Roda.equiv_nao_transitiva
#print axioms ATK.IPortadoresMenores.Roda.toRI_add
#print axioms ATK.IPortadoresMenores.Roda.toRI_mul
#print axioms ATK.IPortadoresMenores.Roda.equivK_equivalence
#print axioms ATK.IPortadoresMenores.Roda.equiv_grosseira
#print axioms ATK.IPortadoresMenores.Roda.toRI_um_zero_eq_zero_zero
#print axioms ATK.IPortadoresMenores.Roda.toRI_inv_falha
#print axioms ATK.IPortadoresMenores.Multiestado.subI_none
#print axioms ATK.IPortadoresMenores.Multiestado.divI_none_none
#print axioms ATK.IPortadoresMenores.Multiestado.divI_none_zero
#print axioms ATK.IPortadoresMenores.Multiestado.standard_eq_RI
#print axioms ATK.IPortadoresMenores.Multiestado.limit_difere_de_RI
#print axioms ATK.IPortadoresMenores.LogicaI.paraK3_bijective
#print axioms ATK.IPortadoresMenores.LogicaI.paraK3_neg
#print axioms ATK.IPortadoresMenores.LogicaI.paraK3_conj
#print axioms ATK.IPortadoresMenores.LogicaI.paraK3_disj
#print axioms ATK.IPortadoresMenores.LogicaI.imp_eq_kleene
#print axioms ATK.IPortadoresMenores.LogicaI.explosao_vale_designado_T
#print axioms ATK.IPortadoresMenores.LogicaI.explosao_falha_designado_TI
