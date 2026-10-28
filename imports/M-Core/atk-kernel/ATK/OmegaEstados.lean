/-
ATK-I — Álgebra finita de estados e indicadores.

Formaliza os enunciados do bloco "ATK-I": inversão Todo ↔ Nada, invariância de I,
fechamento idempotente, detecção exata do zero real, indicadores GREEN/OPEN e o
fato de que inverter um indicador não produz certificado.

Nenhum destes teoremas diz algo sobre os sete problemas.  Eles fixam a semântica
dos operadores; a obrigação matemática (`detectarZero D_∞ = nada`) permanece aberta.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Function.Basic

namespace ATK.OmegaEstados

/-! ### Estados -/

inductive Estado
  | todo
  | nada
  | indeterminado
  deriving DecidableEq, Repr

open Estado

/-- Operador de inversão C_I. -/
def inverter : Estado → Estado
  | todo => nada
  | nada => todo
  | indeterminado => indeterminado

/-- Operador de colapso Z_I. -/
def fechar (_ : Estado) : Estado := nada

theorem inverter_involutive : Function.Involutive inverter := by
  intro x; cases x <;> rfl

theorem inverter_duas_vezes (x : Estado) : inverter (inverter x) = x :=
  inverter_involutive x

theorem inverter_bijective : Function.Bijective inverter :=
  inverter_involutive.bijective

theorem inverter_indeterminado : inverter indeterminado = indeterminado := rfl

theorem fechar_idempotente (x : Estado) : fechar (fechar x) = fechar x := rfl

/-- O colapso não reflete o zero: envia estados distintos ao mesmo valor. -/
theorem fechar_nao_injetivo : ¬ Function.Injective fechar := by
  intro h
  have := h (a₁ := todo) (a₂ := nada) rfl
  cases this

/-! ### Detecção exata do zero real -/

noncomputable def detectarZero (x : ℝ) : Estado :=
  if x = 0 then nada else todo

theorem detectarZero_iff (x : ℝ) : detectarZero x = nada ↔ x = 0 := by
  unfold detectarZero
  by_cases h : x = 0 <;> simp [h]

theorem detectarZero_pos {x : ℝ} (hx : x ≠ 0) : detectarZero x = todo := by
  simp [detectarZero, hx]

/-- A ponte com D_∞: `detectarZero D = nada ↔ D = 0`.  É uma equivalência; não
decide qual lado vale. -/
theorem ponte_D_infty (D : ℝ) (_h0 : 0 ≤ D) (_h1 : D ≤ 1) :
    detectarZero D = nada ↔ D = 0 :=
  detectarZero_iff D

/-! ### Indicadores booleanos -/

def invert (b : Bool) : Bool := !b

theorem invert_true : invert true = false := rfl
theorem invert_false : invert false = true := rfl

theorem invert_involutive (b : Bool) : invert (invert b) = b := by
  cases b <;> rfl

theorem invert_bijective : Function.Bijective invert :=
  (Function.Involutive.bijective invert_involutive)

/-- GREEN universal: todos os certificados verdadeiros. -/
def universalGreen (certs : Fin 7 → Bool) : Bool :=
  decide (∀ i, certs i = true)

def openMath (certs : Fin 7 → Bool) : Bool := !universalGreen certs

theorem green_iff_not_open (certs : Fin 7 → Bool) :
    universalGreen certs = true ↔ openMath certs = false := by
  cases h : universalGreen certs <;> simp [openMath, h]

theorem green_iff_all (certs : Fin 7 → Bool) :
    universalGreen certs = true ↔ ∀ i, certs i = true := by
  simp [universalGreen]

/-- Com um único certificado falso, não há GREEN. -/
theorem not_green_of_false (certs : Fin 7 → Bool) (i : Fin 7) (hi : certs i = false) :
    universalGreen certs = false := by
  have : ¬ ∀ j, certs j = true := fun h => by simp [h i] at hi
  simpa [universalGreen] using this

/-! ### A inversão não cria certificados -/

/-- Um indicador de uma proposição: `true` só quando há prova. -/
def indicador (P : Prop) [Decidable P] : Bool := decide P

/-- Teorema 4 do texto: `invert (indicador P) = true` não implica `P`.
Testemunha: P = (0 = 1). -/
theorem invert_nao_certifica :
    ∃ (P : Prop) (_ : Decidable P), invert (indicador P) = true ∧ ¬ P :=
  ⟨(0 : ℕ) = 1, inferInstance, by decide, by decide⟩

/-- Já o indicador honesto é fiel: `indicador P = true ↔ P`. -/
theorem indicador_fiel (P : Prop) [Decidable P] : indicador P = true ↔ P := by
  simp [indicador]

end ATK.OmegaEstados

#print axioms ATK.OmegaEstados.inverter_involutive
#print axioms ATK.OmegaEstados.inverter_duas_vezes
#print axioms ATK.OmegaEstados.inverter_bijective
#print axioms ATK.OmegaEstados.inverter_indeterminado
#print axioms ATK.OmegaEstados.fechar_idempotente
#print axioms ATK.OmegaEstados.fechar_nao_injetivo
#print axioms ATK.OmegaEstados.detectarZero_iff
#print axioms ATK.OmegaEstados.detectarZero_pos
#print axioms ATK.OmegaEstados.ponte_D_infty
#print axioms ATK.OmegaEstados.invert_true
#print axioms ATK.OmegaEstados.invert_false
#print axioms ATK.OmegaEstados.invert_involutive
#print axioms ATK.OmegaEstados.invert_bijective
#print axioms ATK.OmegaEstados.green_iff_not_open
#print axioms ATK.OmegaEstados.green_iff_all
#print axioms ATK.OmegaEstados.not_green_of_false
#print axioms ATK.OmegaEstados.invert_nao_certifica
#print axioms ATK.OmegaEstados.indicador_fiel
