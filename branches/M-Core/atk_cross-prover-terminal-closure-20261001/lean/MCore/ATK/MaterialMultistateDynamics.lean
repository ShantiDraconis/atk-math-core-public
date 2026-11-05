import MCore.ATK.UniversalProducerTheorem

namespace MCore.ATK.MaterialMultistate

open MCore.ATK.UniversalProducer
open MCore.ATK.StructuralDefect

inductive GateState
  | open
  | closed
  deriving DecidableEq, Repr

def combine : GateState → GateState → GateState
  | .closed, .closed => .closed
  | _, _ => .open

theorem combine_eq_closed_iff (a b : GateState) :
    combine a b = .closed ↔ a = .closed ∧ b = .closed := by
  cases a <;> cases b <;> simp [combine]

theorem open_closed_is_open :
    combine .open .closed = .open := rfl

theorem closed_open_is_open :
    combine .closed .open = .open := rfl

theorem open_open_is_open :
    combine .open .open = .open := rfl

theorem closed_closed_is_closed :
    combine .closed .closed = .closed := rfl

inductive MaterialTriState
  | C0_sourceClosed
  | O_materialOpen
  | C2_terminalClosed
  deriving DecidableEq, Repr

inductive MaterialOperatorKind
  | traction
  | contraction
  | repression
  | torsion
  | excitation
  deriving DecidableEq, Repr

structure MaterialOperatorSystem where
  State : Type
  defect : State → Nat

  traction : State → State
  contraction : State → State
  repression : State → State
  torsion : State → State
  excitation : State → State

  traction_contract :
    ∀ x, 0 < defect x → defect (traction x) < defect x
  contraction_contract :
    ∀ x, 0 < defect x → defect (contraction x) < defect x
  repression_nonincrease :
    ∀ x, defect (repression x) ≤ defect x
  torsion_preserves :
    ∀ x, defect (torsion x) = defect x

  ExcitationCertified : State → Prop
  excitation_contract :
    ∀ x, ExcitationCertified x → 0 < defect x →
      defect (excitation x) < defect x

  freezeTraction :
    ∀ x, defect x = 0 → traction x = x
  freezeContraction :
    ∀ x, defect x = 0 → contraction x = x
  freezeRepression :
    ∀ x, defect x = 0 → repression x = x
  freezeTorsion :
    ∀ x, defect x = 0 → torsion x = x
  freezeExcitation :
    ∀ x, defect x = 0 → excitation x = x

namespace MaterialOperatorSystem

variable (S : MaterialOperatorSystem)

structure CertifiedStep (x : S.State) where
  kind : MaterialOperatorKind
  next : S.State
  realizes :
    next =
      match kind with
      | .traction => S.traction x
      | .contraction => S.contraction x
      | .repression => S.repression x
      | .torsion => S.torsion x
      | .excitation => S.excitation x
  strict : 0 < S.defect x → S.defect next < S.defect x

def tractionStep (x : S.State) : S.CertifiedStep x where
  kind := .traction
  next := S.traction x
  realizes := rfl
  strict := S.traction_contract x

def contractionStep (x : S.State) : S.CertifiedStep x where
  kind := .contraction
  next := S.contraction x
  realizes := rfl
  strict := S.contraction_contract x

def excitationStep
    (x : S.State)
    (h : S.ExcitationCertified x) :
    S.CertifiedStep x where
  kind := .excitation
  next := S.excitation x
  realizes := rfl
  strict := S.excitation_contract x h

theorem torsion_cannot_strictly_close
    (x : S.State) (hpos : 0 < S.defect x) :
    ¬ S.defect (S.torsion x) < S.defect x := by
  rw [S.torsion_preserves x]
  exact Nat.lt_irrefl _

theorem repression_is_nonexpansive (x : S.State) :
    S.defect (S.repression x) ≤ S.defect x :=
  S.repression_nonincrease x

def tractionLane : ReductionLane where
  State := S.State
  step := S.traction
  defect := S.defect
  contract := S.traction_contract
  freeze := S.freezeTraction

def contractionLane : ReductionLane where
  State := S.State
  step := S.contraction
  defect := S.defect
  contract := S.contraction_contract
  freeze := S.freezeContraction

end MaterialOperatorSystem

structure MaterialClosureWitness
    (R : ReductionLane)
    (T : TerminalSpec R) where
  state : R.State
  zeroDefect : R.defect state = 0
  inhabitant : T.Inhabitant

theorem zero_defect_does_not_erase_terminal_type :
    ¬ (∀ (R : ReductionLane) (T : TerminalSpec R)
        (x : R.State), R.defect x = 0 → Nonempty T.Inhabitant) := by
  intro h
  let R : ReductionLane :=
    { State := Unit
      step := id
      defect := fun _ => 0
      contract := by intro x hp; omega
      freeze := by intro x hz; rfl }
  let T : TerminalSpec R :=
    { Inhabitant := Empty
      Certificate := Unit
      certify := fun e => nomatch e }
  have bad : Nonempty T.Inhabitant := h R T () rfl
  rcases bad with ⟨e⟩
  exact nomatch e

def closeWithExactMaterializer
    (R : ReductionLane)
    (T : TerminalSpec R)
    (M : ExactMaterializer R T)
    (x : R.State)
    (hz : R.defect x = 0) :
    MaterialClosureWitness R T where
  state := x
  zeroDefect := hz
  inhabitant := M.extract x hz

theorem pair_terminal_requires_both
    (a b : GateState)
    (h : combine a b = .closed) :
    a = .closed ∧ b = .closed :=
  (combine_eq_closed_iff a b).mp h

structure TriStateExecution
    (R : ReductionLane)
    (T : TerminalSpec R) where
  source : R.State
  openState : R.State
  reachedOpen : True
  terminal : MaterialClosureWitness R T

#print axioms MCore.ATK.MaterialMultistate.combine_eq_closed_iff
#print axioms MCore.ATK.MaterialMultistate.MaterialOperatorSystem.torsion_cannot_strictly_close
#print axioms MCore.ATK.MaterialMultistate.zero_defect_does_not_erase_terminal_type
#print axioms MCore.ATK.MaterialMultistate.closeWithExactMaterializer
#print axioms MCore.ATK.MaterialMultistate.pair_terminal_requires_both

end MCore.ATK.MaterialMultistate
