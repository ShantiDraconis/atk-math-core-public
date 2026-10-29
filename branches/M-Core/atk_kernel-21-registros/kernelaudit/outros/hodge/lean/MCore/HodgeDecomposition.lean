import MCore.HodgeReduction

namespace MCore

structure HodgeClassDecomposition (D : HodgeSemanticData) where
  Degree : {X : D.Variety} → D.Class X → Nat
  Codimension : {X : D.Variety} → D.Class X → Nat
  isRational : {X : D.Variety} → D.Class X → Prop
  isTypePP : {X : D.Variety} → D.Class X → Prop
  hodge_iff : ∀ {X : D.Variety} (α : D.Class X),
    D.isRationalHodgeClass α ↔
      isRational α ∧ isTypePP α ∧ Degree α = 2 * Codimension α

def DecomposedAlgebraicityObligation
    (D : HodgeSemanticData) (H : HodgeClassDecomposition D)
    (X : D.Variety) (α : D.Class X) : Prop :=
  D.isSmoothProjective X →
  H.isRational α →
  H.isTypePP α →
  H.Degree α = 2 * H.Codimension α →
  AlgebraicityAt D α

theorem decomposed_implies_pointwise
    {D : HodgeSemanticData} (H : HodgeClassDecomposition D)
    (h : ∀ (X : D.Variety) (α : D.Class X),
      DecomposedAlgebraicityObligation D H X α) :
    PointwiseHodgeAlgebraicity D := by
  intro X hsp α hh
  have hd := (H.hodge_iff α).1 hh
  exact h X α hsp hd.1 hd.2.1 hd.2.2

theorem pointwise_implies_decomposed
    {D : HodgeSemanticData} (H : HodgeClassDecomposition D)
    (h : PointwiseHodgeAlgebraicity D) :
    ∀ (X : D.Variety) (α : D.Class X),
      DecomposedAlgebraicityObligation D H X α := by
  intro X α hsp hr hpp hdeg
  apply h X hsp α
  exact (H.hodge_iff α).2 ⟨hr, hpp, hdeg⟩

theorem hodge_iff_all_decomposed
    {D : HodgeSemanticData} (H : HodgeClassDecomposition D) :
    RationalHodgeConjecture D ↔
      ∀ (X : D.Variety) (α : D.Class X),
        DecomposedAlgebraicityObligation D H X α := by
  rw [rationalHodge_iff_pointwise D]
  constructor
  · exact pointwise_implies_decomposed H
  · exact decomposed_implies_pointwise H

def hodge_decomposition_status : SignatureStatus := .definitionInterface

def decomposed_algebraicity_status : SignatureStatus := .openBridge

theorem decomposed_algebraicity_still_open :
    decomposed_algebraicity_status = .openBridge := rfl

end MCore
