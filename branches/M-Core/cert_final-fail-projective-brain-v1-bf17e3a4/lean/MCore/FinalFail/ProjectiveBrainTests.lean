import MCore.FinalFail.BrainKernel

namespace MCore.FinalFail

def twoBranchResolution : ResolvedCenter where
  Branch := Bool
  identity := false
  admissible := fun _ => True
  identity_admissible := trivial

theorem false_ne_true : false ≠ true := by
  intro h
  cases h

theorem twoBranchResolution_is_indeterminate :
    FundamentalIndeterminacy twoBranchResolution := by
  exact ⟨false, true, trivial, trivial, false_ne_true⟩

def singletonResolution : ResolvedCenter where
  Branch := Unit
  identity := ()
  admissible := fun _ => True
  identity_admissible := trivial

theorem singletonResolution_is_determined :
    CenterDetermined singletonResolution := by
  intro a b _ _
  cases a
  cases b
  rfl

theorem singletonResolution_not_fail :
    ¬ FundamentalIndeterminacy singletonResolution :=
  determined_not_fundamentally_indeterminate singletonResolution_is_determined

def toyBrain : ClosedCenterBrain where
  Input := Bool
  Center := Bool
  Output := Bool
  Branch := Bool
  encode := fun i c => i = c
  reconstruct := fun c i => c = i
  generate := fun _ _ => True
  feedback := fun o c => o = c
  branchAt := fun _ _ => True
  identityBranch := false

theorem toyBrain_center_is_fail (c : toyBrain.Center) :
    toyBrain.FailAt c := by
  exact ⟨false, true, trivial, trivial, false_ne_true⟩

theorem toyBrain_identity_loop_fixed (c : toyBrain.Center) :
    toyBrain.IdentityStable c := by
  exact ⟨c, rfl, rfl⟩

#print axioms MCore.FinalFail.false_ne_true
#print axioms MCore.FinalFail.twoBranchResolution_is_indeterminate
#print axioms MCore.FinalFail.singletonResolution_not_fail
#print axioms MCore.FinalFail.toyBrain_center_is_fail
#print axioms MCore.FinalFail.toyBrain_identity_loop_fixed

end MCore.FinalFail
