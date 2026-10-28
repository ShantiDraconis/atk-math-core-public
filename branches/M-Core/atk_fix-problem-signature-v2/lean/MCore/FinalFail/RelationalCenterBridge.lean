import MCore.FinalFail.RelationalHardAtom

namespace MCore.FinalFail

/--
Turn the branch relation at one concrete center of a relational HARD atom into
the existing ResolvedCenter representation.  The identity branch must be
proved admissible at that center; the core does not manufacture this premise.
-/
def RelationalHardAtom.centerResolution
    (H : RelationalHardAtom)
    (c : H.Center)
    (hIdentity : H.branchAt c H.identityBranch) :
    ResolvedCenter where
  Branch := H.Branch
  identity := H.identityBranch
  admissible := H.branchAt c
  identity_admissible := hIdentity

/--
The two existing notions of structural non-uniqueness are exactly the same
after the relational center is viewed as a ResolvedCenter.
-/
theorem RelationalHardAtom.failAt_iff_fundamentalIndeterminacy
    (H : RelationalHardAtom)
    (c : H.Center)
    (hIdentity : H.branchAt c H.identityBranch) :
    H.FailAt c ↔
      FundamentalIndeterminacy (H.centerResolution c hIdentity) := by
  rfl

/--
Likewise, uniqueness of admissible relational branches is exactly
CenterDetermined for the induced resolution.
-/
theorem RelationalHardAtom.determinedAt_iff_centerDetermined
    (H : RelationalHardAtom)
    (c : H.Center)
    (hIdentity : H.branchAt c H.identityBranch) :
    H.DeterminedAt c ↔
      CenterDetermined (H.centerResolution c hIdentity) := by
  rfl

/--
IFail is therefore not a second notion at the relational layer: it is the same
branching invariant transported through centerResolution.
-/
theorem RelationalHardAtom.failAt_iff_IFail
    (H : RelationalHardAtom)
    (c : H.Center)
    (hIdentity : H.branchAt c H.identityBranch) :
    H.FailAt c ↔ IFail (H.centerResolution c hIdentity) := by
  exact H.failAt_iff_fundamentalIndeterminacy c hIdentity

/--
A determined relational center and a failing relational center cannot coexist.
This is inherited from the already-certified fundamental-indeterminacy core.
-/
theorem RelationalHardAtom.determinedAt_not_failAt
    (H : RelationalHardAtom)
    (c : H.Center)
    (hIdentity : H.branchAt c H.identityBranch)
    (hDet : H.DeterminedAt c) :
    ¬ H.FailAt c := by
  intro hFail
  have hCenterDet :
      CenterDetermined (H.centerResolution c hIdentity) :=
    (H.determinedAt_iff_centerDetermined c hIdentity).mp hDet
  have hIFail :
      FundamentalIndeterminacy (H.centerResolution c hIdentity) :=
    (H.failAt_iff_fundamentalIndeterminacy c hIdentity).mp hFail
  exact determined_not_fundamentally_indeterminate hCenterDet hIFail

#print axioms MCore.FinalFail.RelationalHardAtom.failAt_iff_fundamentalIndeterminacy
#print axioms MCore.FinalFail.RelationalHardAtom.determinedAt_iff_centerDetermined
#print axioms MCore.FinalFail.RelationalHardAtom.failAt_iff_IFail
#print axioms MCore.FinalFail.RelationalHardAtom.determinedAt_not_failAt

end MCore.FinalFail
