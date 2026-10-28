import MCore.CertificateKernel

namespace MCore

/-- K10: `dependency` is necessary for this declared derivation route exactly
when it occurs in the typed dependency list.  This deliberately talks about a
`DerivedNode`, not an arbitrary `ProofCertificate`: certificates contain proof
terms, not dependency metadata. -/
def IsNecessaryDependency (dependency : CertNode) (target : DerivedNode) : Prop :=
  dependency ∈ target.dependencies

/-- The dependency IDs carried by the proposition-level node agree with the
typed dependencies consumed by its derivation.  This prevents a derivation
from silently bypassing the audit metadata. -/
def DependencyIdsConsistent (target : DerivedNode) : Prop :=
  target.node.deps = target.dependencies.map CertNode.id

/-- A derivation route is ready only when every typed dependency has a proof
certificate.  `Nonempty` propositionalizes the Type-valued certificate. -/
def DerivationReady (target : DerivedNode) : Prop :=
  ∀ dependency, dependency ∈ target.dependencies →
    Nonempty (ProofCertificate dependency)

/-- K11: if a necessary dependency has no certificate, this derivation route
is blocked.  We intentionally do NOT conclude that the target proposition has
no certificate at all: an independent derivation could exist. -/
theorem blocked_necessary {dependency : CertNode} {target : DerivedNode}
    (hnecessary : IsNecessaryDependency dependency target)
    (hblocked : ¬ Nonempty (ProofCertificate dependency)) :
    ¬ DerivationReady target := by
  intro hready
  exact hblocked (hready dependency hnecessary)

/-- Decidable metadata used by K12-K13 frontier reports.  It contains no proof
term and therefore cannot promote a node to PROVED. -/
structure AuditNode where
  id : String
  deps : List String
  status : NodeStatus
  deriving DecidableEq, Repr

/-- All declared dependency IDs are present and PROVED in the supplied audit
registry. -/
def dependenciesProved (nodes : List AuditNode) (n : AuditNode) : Bool :=
  n.deps.all fun depId =>
    nodes.any fun d => d.id == depId && d.status == .proved

/-- At least one declared dependency is absent or not PROVED. -/
def hasBlockedDependency (nodes : List AuditNode) (n : AuditNode) : Bool :=
  !dependenciesProved nodes n

/-- K12: first audit frontier: non-PROVED nodes whose declared dependencies are
all represented by PROVED nodes. -/
def frontier (nodes : List AuditNode) : List AuditNode :=
  nodes.filter fun n => n.status != .proved && dependenciesProved nodes n

/-- K13: nodes blocked by at least one missing/non-PROVED dependency. -/
def blocked (nodes : List AuditNode) : List AuditNode :=
  nodes.filter fun n => hasBlockedDependency nodes n

/-- K14: an illegal promotion is exactly a certificate claim for a node whose
status is not `proved`.  This is proposition-level: proof inhabitants are not
inspected as runtime metadata. -/
def IllegalPromotion (n : CertNode) : Prop :=
  n.status ≠ .proved ∧ Nonempty (ProofCertificate n)

/-- The certificate kernel rules out every illegal promotion. -/
theorem audit_illegal_promotions (n : CertNode) : ¬ IllegalPromotion n := by
  rintro ⟨hstatus, hcert⟩
  exact (no_promotion n hstatus) hcert

/-- Regression fixtures lock the distinction between frontier and blocked. -/
def auditProved : AuditNode := ⟨"K_PROVED", [], .proved⟩
def auditOpenReady : AuditNode := ⟨"K_OPEN_READY", ["K_PROVED"], .openBridge⟩
def auditBlocked : AuditNode := ⟨"K_BLOCKED", ["K_OPEN_READY"], .provedConditional⟩
def auditFixture : List AuditNode := [auditProved, auditOpenReady, auditBlocked]

example : auditOpenReady ∈ frontier auditFixture := by decide
example : auditBlocked ∈ blocked auditFixture := by decide
example : auditBlocked ∉ frontier auditFixture := by decide

/-- K14 regressions cover every non-PROVED status explicitly. -/
example : ¬ IllegalPromotion kernelConditionalNode := audit_illegal_promotions _
example : ¬ IllegalPromotion kernelRefutedNode := audit_illegal_promotions _
example : ¬ IllegalPromotion kernelDefinitionNode := audit_illegal_promotions _
example : ¬ IllegalPromotion kernelNumericalNode := audit_illegal_promotions _
example : ¬ IllegalPromotion kernelOpenNode := audit_illegal_promotions _

end MCore
