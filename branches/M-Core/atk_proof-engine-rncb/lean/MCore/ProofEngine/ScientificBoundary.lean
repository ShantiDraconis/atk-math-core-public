import MCore.ProofEngine.Registry

namespace MCore.ProofEngine

inductive ScientificEvidence (S : Prop)
  | unknown
  | proved (proof : S)
  | disproved (refutation : ¬ S)
  | conflict (proof : S) (refutation : ¬ S)

def CanIssue {S : Prop} : ScientificEvidence S → Prop
  | .proved _ => True
  | _ => False

theorem unknown_cannot_issue (S : Prop) :
    ¬ CanIssue (ScientificEvidence.unknown (S := S)) := by
  simp [CanIssue]

theorem conflict_cannot_issue {S : Prop} (hS : S) (hnS : ¬ S) :
    ¬ CanIssue (ScientificEvidence.conflict hS hnS) := by
  simp [CanIssue]

end MCore.ProofEngine
