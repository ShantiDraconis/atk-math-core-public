import MCore.FinalFail.FundamentalIndeterminacy

namespace MCore.FinalFail

/-- Relation composition keeps all admissible continuations instead of selecting one. -/
def RelComp {A B C : Type}
    (R : A → B → Prop)
    (Q : B → C → Prop) :
    A → C → Prop :=
  fun a c => ∃ b, R a b ∧ Q b c

/-- The operational HARD atom uses relations, not necessarily functions. -/
structure RelationalHardAtom where
  Start : Type
  Center : Type
  Finish : Type
  Branch : Type
  start_to_center : Start → Center → Prop
  center_to_start : Center → Start → Prop
  center_to_finish : Center → Finish → Prop
  finish_to_center : Finish → Center → Prop
  branchAt : Center → Branch → Prop
  identityBranch : Branch

namespace RelationalHardAtom

def leftLoop (H : RelationalHardAtom) : H.Center → H.Center → Prop :=
  RelComp H.center_to_start H.start_to_center

def rightLoop (H : RelationalHardAtom) : H.Center → H.Center → Prop :=
  RelComp H.center_to_finish H.finish_to_center

def CommonFixed (H : RelationalHardAtom) (c : H.Center) : Prop :=
  H.leftLoop c c ∧ H.rightLoop c c

def FailAt (H : RelationalHardAtom) (c : H.Center) : Prop :=
  ∃ a b : H.Branch, H.branchAt c a ∧ H.branchAt c b ∧ a ≠ b

def DeterminedAt (H : RelationalHardAtom) (c : H.Center) : Prop :=
  ∀ a b : H.Branch, H.branchAt c a → H.branchAt c b → a = b

theorem failAt_not_determined
    (H : RelationalHardAtom)
    {c : H.Center}
    (h : H.FailAt c) :
    ¬ H.DeterminedAt c := by
  intro hdet
  rcases h with ⟨a, b, ha, hb, hab⟩
  exact hab (hdet a b ha hb)

theorem common_fixed_has_both_loops
    (H : RelationalHardAtom)
    {c : H.Center}
    (h : H.CommonFixed c) :
    H.leftLoop c c ∧ H.rightLoop c c :=
  h

end RelationalHardAtom

#print axioms MCore.FinalFail.RelationalHardAtom.failAt_not_determined
#print axioms MCore.FinalFail.RelationalHardAtom.common_fixed_has_both_loops

end MCore.FinalFail
