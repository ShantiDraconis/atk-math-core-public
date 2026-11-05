import MCore.ATL.V3.Core

namespace MCore.ATL.V3

structure FirewallEvidence where
  axiom : Bool
  circularity : Bool
  semantic : Bool
  interface : Bool
  vacuous : Bool
  deriving Repr

def FirewallEvidence.allGreen (e : FirewallEvidence) : Bool :=
  e.axiom && e.circularity && e.semantic && e.interface && e.vacuous

structure PromotionEvidence where
  sourceCompiles : Bool
  buildLinks : Bool
  kernelAxiomsClean : Bool
  semanticIdentity : Bool
  firewall : FirewallEvidence
  egcEmitted : Bool
  conditionalOnExplicit : Bool
  deriving Repr

def mayReach (e : PromotionEvidence) : PromotionLayer → Bool
  | .source => e.sourceCompiles
  | .build => e.sourceCompiles && e.buildLinks
  | .kernel => e.sourceCompiles && e.buildLinks && e.kernelAxiomsClean
  | .semantic =>
      e.sourceCompiles && e.buildLinks && e.kernelAxiomsClean &&
      e.semanticIdentity && e.firewall.allGreen
  | .scientific =>
      e.sourceCompiles && e.buildLinks && e.kernelAxiomsClean &&
      e.semanticIdentity && e.firewall.allGreen &&
      e.egcEmitted && e.conditionalOnExplicit

theorem scientific_implies_semantic (e : PromotionEvidence)
    (h : mayReach e .scientific = true) : mayReach e .semantic = true := by
  simp [mayReach, FirewallEvidence.allGreen] at h ⊢
  aesop

theorem semantic_implies_kernel (e : PromotionEvidence)
    (h : mayReach e .semantic = true) : mayReach e .kernel = true := by
  simp [mayReach, FirewallEvidence.allGreen] at h ⊢
  aesop

end MCore.ATL.V3
