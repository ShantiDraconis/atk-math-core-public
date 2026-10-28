import Mathlib

namespace MCore.ATK.TwoSidedMaterial

inductive EvidenceState (P : Prop) where
  | open
  | positive (h : P)
  | negative (h : ¬ P)
  | both (hp : P) (hn : ¬ P)

structure TwoSidedClosure (P Q : Prop) where
  viaPositive : P → Q
  viaNegative : ¬ P → Q

theorem TwoSidedClosure.close
    {P Q : Prop}
    (W : TwoSidedClosure P Q) :
    Q := by
  classical
  by_cases hP : P
  · exact W.viaPositive hP
  · exact W.viaNegative hP

def closeEvidence
    {P Q : Prop}
    (W : TwoSidedClosure P Q) :
    EvidenceState P → Option Q
  | .open => none
  | .positive hp => some (W.viaPositive hp)
  | .negative hn => some (W.viaNegative hn)
  | .both hp _ => some (W.viaPositive hp)

theorem both_implies_false
    {P : Prop}
    (hp : P)
    (hn : ¬ P) :
    False :=
  hn hp

theorem twoSided_self_iff
    (P : Prop) :
    Nonempty (TwoSidedClosure P P) ↔ P := by
  constructor
  · rintro ⟨W⟩
    exact W.close
  · intro hP
    refine ⟨{
      viaPositive := fun _ => hP
      viaNegative := fun _ => hP
    }⟩

theorem twoSided_neg_self_iff
    (P : Prop) :
    Nonempty (TwoSidedClosure P (¬ P)) ↔ ¬ P := by
  constructor
  · rintro ⟨W⟩
    exact W.close
  · intro hn
    refine ⟨{
      viaPositive := fun hp => False.elim (hn hp)
      viaNegative := fun _ => hn
    }⟩

structure TwoBranchMaterializer
    (P : Prop)
    (A B : Type)
    (Q : Prop) where
  positiveObject : P → A
  negativeObject : ¬ P → B
  closePositive : A → Q
  closeNegative : B → Q

theorem TwoBranchMaterializer.close
    {P Q : Prop}
    {A B : Type}
    (M : TwoBranchMaterializer P A B Q) :
    Q := by
  classical
  by_cases hP : P
  · exact M.closePositive (M.positiveObject hP)
  · exact M.closeNegative (M.negativeObject hP)

structure DefectTarget where
  State : Type
  defect : State → Nat
  Terminal : State → Prop

structure TwoBranchDefectClosure
    (P : Prop)
    (D : DefectTarget) where
  positiveState : P → D.State
  negativeState : ¬ P → D.State
  positiveZero :
    ∀ hp, D.defect (positiveState hp) = 0
  negativeZero :
    ∀ hn, D.defect (negativeState hn) = 0
  terminal_of_zero :
    ∀ s, D.defect s = 0 → D.Terminal s

theorem TwoBranchDefectClosure.close
    {P : Prop}
    {D : DefectTarget}
    (M : TwoBranchDefectClosure P D) :
    ∃ s : D.State, D.Terminal s := by
  classical
  by_cases hP : P
  · refine ⟨M.positiveState hP, ?_⟩
    exact M.terminal_of_zero _ (M.positiveZero hP)
  · refine ⟨M.negativeState hP, ?_⟩
    exact M.terminal_of_zero _ (M.negativeZero hP)

structure BranchDynamics (S : Type) where
  defect : S → Nat
  contraction : S → S
  tension : S → S
  torsion : S → S
  excitation : S → S
  contraction_decreases :
    ∀ s, 0 < defect s → defect (contraction s) < defect s
  tension_nonincrease :
    ∀ s, defect (tension s) ≤ defect s
  torsion_preserves :
    ∀ s, defect (torsion s) = defect s
  ExcitationValid : S → Prop
  excitation_decreases :
    ∀ s, ExcitationValid s → 0 < defect s →
      defect (excitation s) < defect s

theorem torsion_is_not_strict_progress
    {S : Type}
    (D : BranchDynamics S)
    (s : S)
    (hpos : 0 < D.defect s) :
    ¬ D.defect (D.torsion s) < D.defect s := by
  rw [D.torsion_preserves s]
  exact Nat.lt_irrefl _

inductive Gate where
  | open
  | closed
  deriving DecidableEq, Repr

def combine : Gate → Gate → Gate
  | .closed, .closed => .closed
  | _, _ => .open

theorem combine_closed_iff
    (a b : Gate) :
    combine a b = .closed ↔
      a = .closed ∧ b = .closed := by
  cases a <;> cases b <;> simp [combine]

#print axioms MCore.ATK.TwoSidedMaterial.TwoSidedClosure.close
#print axioms MCore.ATK.TwoSidedMaterial.twoSided_self_iff
#print axioms MCore.ATK.TwoSidedMaterial.twoSided_neg_self_iff
#print axioms MCore.ATK.TwoSidedMaterial.TwoBranchMaterializer.close
#print axioms MCore.ATK.TwoSidedMaterial.TwoBranchDefectClosure.close
#print axioms MCore.ATK.TwoSidedMaterial.torsion_is_not_strict_progress
#print axioms MCore.ATK.TwoSidedMaterial.combine_closed_iff

end MCore.ATK.TwoSidedMaterial
