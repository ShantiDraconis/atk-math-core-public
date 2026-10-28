import Mathlib

namespace MCore
namespace ExternalPromotion

inductive ATKClaimStatus
  | provedMaterial
  | superseded
  | open
  deriving DecidableEq, Repr

inductive SearchStatus
  | closedByMaterialProducer
  | closedByTruncation
  | open
  deriving DecidableEq, Repr

inductive ExternalMathStatus
  | proved
  | openMath
  | historical
  deriving DecidableEq, Repr

structure AxiomAudit where
  sorryCount : Nat
  admitCount : Nat
  sorryAxCount : Nat
  customTheoremAxiomCount : Nat
  unsafeCount : Nat
  ioActionCount : Nat
  nativeDecideCount : Nat
  implementedByCount : Nat

def AxiomAudit.clean (A : AxiomAudit) : Prop :=
  A.sorryCount = 0 ∧
  A.admitCount = 0 ∧
  A.sorryAxCount = 0 ∧
  A.customTheoremAxiomCount = 0 ∧
  A.unsafeCount = 0 ∧
  A.ioActionCount = 0 ∧
  A.nativeDecideCount = 0 ∧
  A.implementedByCount = 0

structure MaterialProducer (T : Prop) where
  witness : T

structure ExternalCertificate (T : Prop) where
  producer : MaterialProducer T
  searchStatus : SearchStatus
  search_is_material : searchStatus = .closedByMaterialProducer
  audit : AxiomAudit
  audit_clean : audit.clean
  buildGreen : Prop
  build_green : buildGreen
  reproducibleBuild : Prop
  reproducible : reproducibleBuild
  falsificationPassed : Prop
  falsification_passed : falsificationPassed

def ExternalCertificate.toProof
    {T : Prop}
    (C : ExternalCertificate T) : T :=
  C.producer.witness

structure LaneExport (T : Prop) where
  atkStatus : ATKClaimStatus
  searchStatus : SearchStatus
  externalStatus : ExternalMathStatus
  externalCertified : Bool
  materialCertificate : Option (ExternalCertificate T)

def LaneExport.validExternal (E : LaneExport T) : Prop :=
  E.externalStatus = .proved →
  E.searchStatus = .closedByMaterialProducer ∧
  E.externalCertified = true ∧
  ∃ C, E.materialCertificate = some C

theorem external_proved_requires_material
    {T : Prop}
    (E : LaneExport T)
    (hvalid : E.validExternal)
    (hproved : E.externalStatus = .proved) :
    E.searchStatus = .closedByMaterialProducer ∧
    E.externalCertified = true ∧
    ∃ C, E.materialCertificate = some C :=
  hvalid hproved

theorem truncation_cannot_be_external_proved
    {T : Prop}
    (E : LaneExport T)
    (hvalid : E.validExternal)
    (htrunc : E.searchStatus = .closedByTruncation) :
    E.externalStatus ≠ .proved := by
  intro hproved
  have h := hvalid hproved
  exact SearchStatus.noConfusion (h.1.trans htrunc.symm)

theorem atk_status_alone_does_not_produce_external
    {T : Prop}
    (E : LaneExport T)
    (hvalid : E.validExternal)
    (hatk : E.atkStatus = .provedMaterial)
    (hno : E.materialCertificate = none) :
    E.externalStatus ≠ .proved := by
  intro hproved
  rcases hvalid hproved with ⟨_, _, C, hC⟩
  rw [hno] at hC
  cases hC

theorem external_certificate_gives_target
    {T : Prop}
    (C : ExternalCertificate T) : T :=
  C.toProof

#print axioms MCore.ExternalPromotion.external_proved_requires_material
#print axioms MCore.ExternalPromotion.truncation_cannot_be_external_proved
#print axioms MCore.ExternalPromotion.atk_status_alone_does_not_produce_external
#print axioms MCore.ExternalPromotion.external_certificate_gives_target

end ExternalPromotion
end MCore
