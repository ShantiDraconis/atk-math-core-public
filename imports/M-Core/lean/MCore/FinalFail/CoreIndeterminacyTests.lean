import MCore.FinalFail.RelationalHardAtom

namespace MCore.FinalFail

def twoBranchResolution : ResolvedCenter where
  Branch := Bool
  identity := false
  admissible := fun _ => True
  identity_admissible := trivial

theorem twoBranchResolution_is_indeterminate :
    FundamentalIndeterminacy twoBranchResolution := by
  exact ⟨false, true, trivial, trivial, by
    intro h
    cases h⟩

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

theorem singletonResolution_not_indeterminate :
    ¬ FundamentalIndeterminacy singletonResolution :=
  determined_not_fundamentally_indeterminate singletonResolution_is_determined

def toyHardAtom : RelationalHardAtom where
  Start := Bool
  Center := Bool
  Finish := Bool
  Branch := Bool
  start_to_center := fun s c => s = c
  center_to_start := fun c s => c = s
  center_to_finish := fun _ _ => True
  finish_to_center := fun f c => f = c
  branchAt := fun _ _ => True
  identityBranch := false

theorem toyHardAtom_center_is_fail (c : toyHardAtom.Center) :
    toyHardAtom.FailAt c := by
  exact ⟨false, true, trivial, trivial, by
    intro h
    cases h⟩

theorem toyHardAtom_left_loop_fixed (c : toyHardAtom.Center) :
    toyHardAtom.leftLoop c c := by
  exact ⟨c, rfl, rfl⟩

#print axioms MCore.FinalFail.twoBranchResolution_is_indeterminate
#print axioms MCore.FinalFail.singletonResolution_not_indeterminate
#print axioms MCore.FinalFail.toyHardAtom_center_is_fail
#print axioms MCore.FinalFail.toyHardAtom_left_loop_fixed

end MCore.FinalFail
