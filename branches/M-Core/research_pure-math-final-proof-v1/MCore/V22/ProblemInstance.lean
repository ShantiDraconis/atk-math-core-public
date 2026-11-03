import MCore.V22.ClosureCriterion

namespace MCore.V22

/-- A concrete repository plugs its mathematical propositions into this
    interface.  No field contains a proof of the final goal. -/
structure ProblemInstance where
  problem : ProblemId
  obligation : ResearchObligation
  audit : ClosureAudit

namespace ProblemInstance

def Goal (p : ProblemInstance) : Prop :=
  p.obligation.Final

def ReadyForPromotion (p : ProblemInstance) : Prop :=
  CertifiedClosed p.Goal p.audit

theorem promotion_requires_goal
    (p : ProblemInstance) (h : p.ReadyForPromotion) :
    p.Goal :=
  certifiedClosed_implies_goal h

/-- A structurally represented problem can remain open: defining an instance
    does not construct ReadyForPromotion. -/
structure OpenInstanceEvidence (p : ProblemInstance) where
  residual : MathematicalResidual
  exactBlocker : HasExactBlocker p.problem

end ProblemInstance

end MCore.V22
