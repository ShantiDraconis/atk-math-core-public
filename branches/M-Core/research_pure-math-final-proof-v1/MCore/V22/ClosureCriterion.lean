import MCore.V22.RecursiveDecomposition

namespace MCore.V22

structure ClosureAudit where
  statementMatch : Prop
  quantifierMatch : Prop
  directionality : Prop
  noCircularity : Prop
  dependenciesClosed : Prop

structure ClosureAuditProof (a : ClosureAudit) where
  statementMatch : a.statementMatch
  quantifierMatch : a.quantifierMatch
  directionality : a.directionality
  noCircularity : a.noCircularity
  dependenciesClosed : a.dependenciesClosed

def CertifiedClosed (Goal : Prop) (a : ClosureAudit) : Prop :=
  Goal ∧ a.statementMatch ∧ a.quantifierMatch ∧ a.directionality ∧
    a.noCircularity ∧ a.dependenciesClosed

theorem certifiedClosed_implies_goal
    {Goal : Prop} {a : ClosureAudit}
    (h : CertifiedClosed Goal a) : Goal :=
  h.1

theorem certificate_to_certifiedClosed
    {Goal : Prop} (c : ClosureCertificate Goal) :
    CertifiedClosed Goal
      { statementMatch := c.statementMatch
        quantifierMatch := c.quantifierMatch
        directionality := c.directionality
        noCircularity := c.noCircularity
        dependenciesClosed := c.dependenciesClosed } := by
  exact ⟨c.finalProof, c.statementMatchProof, c.quantifierMatchProof,
    c.directionalityProof, c.noCircularityProof, c.dependenciesClosedProof⟩

theorem certifiedClosed_to_certificate
    {Goal : Prop} {a : ClosureAudit}
    (h : CertifiedClosed Goal a) :
    ClosureCertificate Goal where
  finalProof := h.1
  statementMatch := a.statementMatch
  statementMatchProof := h.2.1
  quantifierMatch := a.quantifierMatch
  quantifierMatchProof := h.2.2.1
  directionality := a.directionality
  directionalityProof := h.2.2.2.1
  noCircularity := a.noCircularity
  noCircularityProof := h.2.2.2.2.1
  dependenciesClosed := a.dependenciesClosed
  dependenciesClosedProof := h.2.2.2.2.2

end MCore.V22
