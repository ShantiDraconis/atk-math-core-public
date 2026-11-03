import Mathlib
import MCore.ExternalPromotionGuard

namespace MCore
namespace ATKThreeRuleClosure

universe u

inductive SearchResultType
  | found
  | exhausted
  | loopDetected
  | open
  deriving DecidableEq, Repr

structure CompleteSearchSpace (α : Type u) where
  domain : Finset α
  complete : ∀ x : α, x ∈ domain

structure DecidableBlocking (α : Type u) where
  isBlocking : α → Prop
  decidableBlocking : DecidablePred isBlocking

structure LoopMeasure (S : Type u) where
  measure : S → Nat
  LoopEdge : S → S → Prop
  decreases : ∀ {a b}, LoopEdge a b → measure b < measure a

theorem loopMeasure_wellFounded
    {S : Type u}
    (M : LoopMeasure S) :
    WellFounded (fun b a => M.LoopEdge a b) := by
  exact WellFounded.onFun M.measure Nat.lt_wfRel.wf

structure CanonicalStateInvariant (S : Type u) where
  inv : S → Prop
  preserves :
    ∀ {a b}, inv a → inv b

structure ConcreteClosureWitness
    (S : Type u)
    (Target : Prop) where
  state : S
  invariant : CanonicalStateInvariant S
  state_is_canonical : invariant.inv state
  closes : Target

structure CertifiedMaterialProducer
    (S : Type u)
    (Target : Prop) where
  produce : ConcreteClosureWitness S Target

structure LoopInvariant
    (S : Type u)
    (Target : Prop)
    (M : LoopMeasure S) where
  state : S
  canonical : CanonicalStateInvariant S
  canonical_at_state : canonical.inv state
  closureWitness : ConcreteClosureWitness S Target

inductive SearchResult
    (α S : Type u)
    (Target : Prop)
    (space : CompleteSearchSpace α)
    (blocking : DecidableBlocking α)
    (M : LoopMeasure S)
    where
  | found :
      CertifiedMaterialProducer S Target →
      SearchResult α S Target space blocking M
  | exhausted :
      (∀ c ∈ space.domain, ¬ blocking.isBlocking c) →
      CertifiedMaterialProducer S Target →
      SearchResult α S Target space blocking M
  | loopDetected :
      LoopInvariant S Target M →
      SearchResult α S Target space blocking M
  | open :
      SearchResult α S Target space blocking M

def SearchResult.close?
    {α S : Type u}
    {Target : Prop}
    {space : CompleteSearchSpace α}
    {blocking : DecidableBlocking α}
    {M : LoopMeasure S} :
    SearchResult α S Target space blocking M →
      Option (ConcreteClosureWitness S Target)
  | .found P => some P.produce
  | .exhausted _ P => some P.produce
  | .loopDetected L => some L.closureWitness
  | .open => none

theorem found_closes
    {α S : Type u}
    {Target : Prop}
    {space : CompleteSearchSpace α}
    {blocking : DecidableBlocking α}
    {M : LoopMeasure S}
    (P : CertifiedMaterialProducer S Target) :
    (SearchResult.found (space := space) (blocking := blocking) (M := M) P).close? =
      some P.produce := by
  rfl

theorem exhausted_closes
    {α S : Type u}
    {Target : Prop}
    {space : CompleteSearchSpace α}
    {blocking : DecidableBlocking α}
    {M : LoopMeasure S}
    (h : ∀ c ∈ space.domain, ¬ blocking.isBlocking c)
    (P : CertifiedMaterialProducer S Target) :
    (SearchResult.exhausted (space := space) (blocking := blocking) (M := M) h P).close? =
      some P.produce := by
  rfl

theorem loop_detected_closes
    {α S : Type u}
    {Target : Prop}
    {space : CompleteSearchSpace α}
    {blocking : DecidableBlocking α}
    {M : LoopMeasure S}
    (L : LoopInvariant S Target M) :
    (SearchResult.loopDetected (space := space) (blocking := blocking) L).close? =
      some L.closureWitness := by
  rfl

theorem open_does_not_close
    {α S : Type u}
    {Target : Prop}
    {space : CompleteSearchSpace α}
    {blocking : DecidableBlocking α}
    {M : LoopMeasure S} :
    (SearchResult.open :
      SearchResult α S Target space blocking M).close? = none := by
  rfl

theorem closureWitness_proves_target
    {S : Type u}
    {Target : Prop}
    (W : ConcreteClosureWitness S Target) :
    Target :=
  W.closes

theorem materialProducer_proves_target
    {S : Type u}
    {Target : Prop}
    (P : CertifiedMaterialProducer S Target) :
    Target :=
  P.produce.closes

/--
External promotion is one-way: a material producer proves the target.
No theorem converts ATK/search status alone into Target.
-/
def toExternalCertificate
    {S : Type u}
    {Target : Prop}
    (P : CertifiedMaterialProducer S Target)
    (audit : ExternalPromotion.AxiomAudit)
    (haudit : audit.clean)
    (buildGreen reproducibleBuild falsificationPassed : Prop)
    (hbuild : buildGreen)
    (hrepro : reproducibleBuild)
    (hfals : falsificationPassed) :
    ExternalPromotion.ExternalCertificate Target where
  producer := ⟨P.produce.closes⟩
  searchStatus := .closedByMaterialProducer
  search_is_material := rfl
  audit := audit
  audit_clean := haudit
  buildGreen := buildGreen
  build_green := hbuild
  reproducibleBuild := reproducibleBuild
  reproducible := hrepro
  falsificationPassed := falsificationPassed
  falsification_passed := hfals

#print axioms MCore.ATKThreeRuleClosure.loopMeasure_wellFounded
#print axioms MCore.ATKThreeRuleClosure.found_closes
#print axioms MCore.ATKThreeRuleClosure.exhausted_closes
#print axioms MCore.ATKThreeRuleClosure.loop_detected_closes
#print axioms MCore.ATKThreeRuleClosure.open_does_not_close
#print axioms MCore.ATKThreeRuleClosure.materialProducer_proves_target
#print axioms MCore.ATKThreeRuleClosure.toExternalCertificate

end ATKThreeRuleClosure
end MCore
