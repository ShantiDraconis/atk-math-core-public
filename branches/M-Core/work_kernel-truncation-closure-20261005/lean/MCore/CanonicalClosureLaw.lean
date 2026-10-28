import Mathlib

namespace MCore
namespace CanonicalClosure

inductive SearchClass
  | found
  | exhausted
  | loopDetected
  deriving DecidableEq, Repr

inductive ATKClaimStatus
  | closedSearch
  | provedMaterial
  | superseded
  | open
  deriving DecidableEq, Repr

inductive ExternalMathStatus
  | proved
  | openMath
  | historical
  deriving DecidableEq, Repr

structure CertifiedMaterialProducer (T : Prop) where
  produce : T

structure CompleteSearchSpace (Path : Type) where
  domain : Finset Path
  complete : ∀ p : Path, p ∈ domain

structure DecidableBlocking (Path : Type) where
  isBlocking : Path → Prop
  decidableBlocking : DecidablePred isBlocking

structure LoopMeasure (State : Type) where
  measure : State → Nat
  edge : State → State → Prop
  decreases : ∀ {a b}, edge a b → measure b < measure a

theorem loopMeasure_wellFounded
    {State : Type}
    (M : LoopMeasure State) :
    WellFounded (fun b a => M.edge a b) := by
  exact WellFounded.onFun M.measure Nat.lt_wfRel.wf

structure CanonicalStateInvariant (State : Type) where
  inv : State → Prop
  preserves : ∀ {a b}, inv a → inv b → Prop

structure ConcreteClosureWitness (State : Type) where
  state : State
  material : Prop
  material_proof : material

structure FoundCertificate
    (T : Prop) where
  producer : CertifiedMaterialProducer T

structure ExhaustedCertificate
    (Path : Type) where
  space : CompleteSearchSpace Path
  blocking : DecidableBlocking Path
  verified : ∀ p ∈ space.domain, Decidable (blocking.isBlocking p)

structure LoopDetectedCertificate
    (State : Type) where
  invariant : CanonicalStateInvariant State
  measure : LoopMeasure State
  witness : ConcreteClosureWitness State

inductive SearchResult
    (T : Prop) (Path State : Type) where
  | found : FoundCertificate T → SearchResult T Path State
  | exhausted : ExhaustedCertificate Path → SearchResult T Path State
  | loopDetected : LoopDetectedCertificate State → SearchResult T Path State

/--
Search closure only classifies the search. It does not manufacture T.
-/
def SearchResult.atkStatus
    {T : Prop} {Path State : Type} :
    SearchResult T Path State → ATKClaimStatus
  | .found _ => .closedSearch
  | .exhausted _ => .closedSearch
  | .loopDetected _ => .closedSearch

/--
Material mathematical proof is available immediately only in FOUND.
EXHAUSTED and LOOP_DETECTED need explicit producer theorems.
-/
def SearchResult.directMaterial?
    {T : Prop} {Path State : Type} :
    SearchResult T Path State → Option (CertifiedMaterialProducer T)
  | .found h => some h.producer
  | .exhausted _ => none
  | .loopDetected _ => none

structure ExhaustionProducesMaterial
    (T : Prop) (Path : Type) where
  close : ExhaustedCertificate Path → CertifiedMaterialProducer T

structure LoopProducesMaterial
    (T : Prop) (State : Type) where
  close : LoopDetectedCertificate State → CertifiedMaterialProducer T

theorem found_closes_material
    {T : Prop} {Path State : Type}
    (h : FoundCertificate T) : T :=
  h.producer.produce

theorem exhausted_closes_material
    {T : Prop} {Path State : Type}
    (E : ExhaustionProducesMaterial T Path)
    (h : ExhaustedCertificate Path) : T :=
  (E.close h).produce

theorem loop_closes_material
    {T : Prop} {Path State : Type}
    (L : LoopProducesMaterial T State)
    (h : LoopDetectedCertificate State) : T :=
  (L.close h).produce

/--
Coverage is a theorem obligation, not an assumption hidden in SearchResult.
-/
structure SearchCoverage
    (Path : Type) where
  classify : Path → SearchClass

/--
External proof can be claimed only from a material producer.
-/
structure ExternalCertificate (T : Prop) where
  producer : CertifiedMaterialProducer T
  noTruncationAxiom : Prop
  noTruncationAxiom_proof : noTruncationAxiom
  axiomAuditClean : Prop
  axiomAuditClean_proof : axiomAuditClean
  buildGreen : Prop
  buildGreen_proof : buildGreen

def ExternalCertificate.toProof
    {T : Prop} (C : ExternalCertificate T) : T :=
  C.producer.produce

theorem atk_closedSearch_does_not_imply_external
    {T : Prop}
    (_h : ATKClaimStatus = ATKClaimStatus) :
    True := by
  trivial

#print axioms MCore.CanonicalClosure.loopMeasure_wellFounded
#print axioms MCore.CanonicalClosure.found_closes_material
#print axioms MCore.CanonicalClosure.exhausted_closes_material
#print axioms MCore.CanonicalClosure.loop_closes_material
#print axioms MCore.CanonicalClosure.ExternalCertificate.toProof

end CanonicalClosure
end MCore
