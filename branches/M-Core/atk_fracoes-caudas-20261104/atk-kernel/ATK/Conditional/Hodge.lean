import Mathlib.Order.Basic

/-!
# Condicional — Conjectura de Hodge

A Mathlib não tem cohomologia de Hodge de variedades projetivas; o enunciado é relativo a
um `HodgeModel` (fidelidade: PARAMÉTRICA).

Forma condicional:

  `KnownCases M → MiddleCodimension M → HodgeConjecture M`

* `KnownCases` (PONTE; casos já provados):
  p = 0 e p ≥ dim X (triviais), p = 1 (Lefschetz (1,1), 1924),
  p = dim X − 1 (Lefschetz difícil + (1,1)).
* `MiddleCodimension` (ABERTA): 2 ≤ p ≤ dim X − 2. O primeiro caso em aberto é p = 2 em
  dimensão 4. O terminal `ConcreteAlgebraicityPayload` do `m-core-hodge` mira aqui.
-/

namespace ATK.Conditional.Hodge

universe u v

/-- Interface: classes racionais em H^{2p}(X, ℚ), tipo (p,p), e classes algébricas. -/
structure HodgeModel where
  Variety : Type u
  SmoothProjective : Variety → Prop
  dim : Variety → ℕ
  /-- `Class X p` = H^{2p}(X, ℚ) -/
  Class : Variety → ℕ → Type v
  /-- α é de tipo (p,p) -/
  IsHodge : {X : Variety} → {p : ℕ} → Class X p → Prop
  /-- α é combinação ℚ-linear de classes de subvariedades -/
  IsAlgebraic : {X : Variety} → {p : ℕ} → Class X p → Prop

/-- Enunciado-alvo. -/
def HodgeConjecture (M : HodgeModel.{u, v}) : Prop :=
  ∀ X, M.SmoothProjective X → ∀ (p : ℕ) (α : M.Class X p), M.IsHodge α → M.IsAlgebraic α

/-- PONTE: casos conhecidos (p ≤ 1 ou p ≥ dim X − 1). -/
def KnownCases (M : HodgeModel.{u, v}) : Prop :=
  ∀ X, M.SmoothProjective X → ∀ (p : ℕ) (α : M.Class X p),
    (p ≤ 1 ∨ M.dim X ≤ p + 1) → M.IsHodge α → M.IsAlgebraic α

/-- HIPÓTESE ABERTA: codimensões do meio, 2 ≤ p ≤ dim X − 2. -/
def MiddleCodimension (M : HodgeModel.{u, v}) : Prop :=
  ∀ X, M.SmoothProjective X → ∀ (p : ℕ) (α : M.Class X p),
    2 ≤ p → p + 2 ≤ M.dim X → M.IsHodge α → M.IsAlgebraic α

/-- **Condicional Hodge.** -/
theorem hodge_conditional {M : HodgeModel.{u, v}}
    (hBridge : KnownCases M) (hOpen : MiddleCodimension M) : HodgeConjecture M := by
  intro X hX p α hα
  by_cases h1 : p ≤ 1
  · exact hBridge X hX p α (Or.inl h1) hα
  by_cases h2 : M.dim X ≤ p + 1
  · exact hBridge X hX p α (Or.inr h2) hα
  exact hOpen X hX p α (by omega) (by omega) hα

end ATK.Conditional.Hodge

#print axioms ATK.Conditional.Hodge.hodge_conditional
