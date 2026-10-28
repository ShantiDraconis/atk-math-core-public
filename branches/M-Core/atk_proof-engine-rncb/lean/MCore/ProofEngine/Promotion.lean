import MCore.ProofEngine.CanonicalNode

namespace MCore.ProofEngine

inductive PromotionLayer
  | source | build | kernel | semantic | scientific
  deriving DecidableEq, Repr

def PromotionLayer.rank : PromotionLayer → Nat
  | .source => 0
  | .build => 1
  | .kernel => 2
  | .semantic => 3
  | .scientific => 4

def nextLayer? : PromotionLayer → Option PromotionLayer
  | .source => some .build
  | .build => some .kernel
  | .kernel => some .semantic
  | .semantic => some .scientific
  | .scientific => none

def legalPromotion (src dst : PromotionLayer) : Prop :=
  nextLayer? src = some dst

theorem no_layer_skip (src dst : PromotionLayer)
    (h : legalPromotion src dst) :
    dst.rank = src.rank + 1 := by
  cases src <;> simp [legalPromotion, nextLayer?, PromotionLayer.rank] at h
  all_goals subst dst <;> rfl

inductive RouteDisposition
  | live
  | formulationFalsified
  | superseded
  deriving DecidableEq, Repr

end MCore.ProofEngine
