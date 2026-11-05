import MCore.FinalFail.RelationalHardAtom

namespace MCore.FinalFail

/-- Brain kernel: encode/reconstruct and generate/feedback share one center.
Branching is preserved explicitly at the center. -/
structure ClosedCenterBrain where
  Input : Type
  Center : Type
  Output : Type
  Branch : Type
  encode : Input → Center → Prop
  reconstruct : Center → Input → Prop
  generate : Center → Output → Prop
  feedback : Output → Center → Prop
  branchAt : Center → Branch → Prop
  identityBranch : Branch

namespace ClosedCenterBrain

def asHardAtom (B : ClosedCenterBrain) : RelationalHardAtom where
  Start := B.Input
  Center := B.Center
  Finish := B.Output
  Branch := B.Branch
  start_to_center := B.encode
  center_to_start := B.reconstruct
  center_to_finish := B.generate
  finish_to_center := B.feedback
  branchAt := B.branchAt
  identityBranch := B.identityBranch

def identityLoop (B : ClosedCenterBrain) : B.Center → B.Center → Prop :=
  RelComp B.reconstruct B.encode

def generativeLoop (B : ClosedCenterBrain) : B.Center → B.Center → Prop :=
  RelComp B.generate B.feedback

def IdentityStable (B : ClosedCenterBrain) (c : B.Center) : Prop :=
  B.identityLoop c c

def GenerativelyStable (B : ClosedCenterBrain) (c : B.Center) : Prop :=
  B.generativeLoop c c

def GloballyStable (B : ClosedCenterBrain) (c : B.Center) : Prop :=
  B.IdentityStable c ∧ B.GenerativelyStable c

def FailAt (B : ClosedCenterBrain) (c : B.Center) : Prop :=
  ∃ a b : B.Branch, B.branchAt c a ∧ B.branchAt c b ∧ a ≠ b

theorem global_stability_contains_both_loops
    (B : ClosedCenterBrain)
    {c : B.Center}
    (h : B.GloballyStable c) :
    B.IdentityStable c ∧ B.GenerativelyStable c :=
  h

theorem brain_fail_is_relational_hard_fail
    (B : ClosedCenterBrain)
    {c : B.Center}
    (h : B.FailAt c) :
    B.asHardAtom.FailAt c :=
  h

end ClosedCenterBrain

#print axioms MCore.FinalFail.ClosedCenterBrain.global_stability_contains_both_loops
#print axioms MCore.FinalFail.ClosedCenterBrain.brain_fail_is_relational_hard_fail

end MCore.FinalFail
