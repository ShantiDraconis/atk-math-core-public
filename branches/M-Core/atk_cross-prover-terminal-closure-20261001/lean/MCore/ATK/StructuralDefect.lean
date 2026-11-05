import Mathlib

namespace MCore.ATK.StructuralDefect

/-- The mathematical problems remain distinct. -/
inductive ProblemKind
  | riemann
  | pnp
  | yangMills
  | navierStokes
  | bsd
  | hodge
  | beal
deriving DecidableEq, Repr

/-- Closed taxonomy of structural gap shapes. -/
inductive GapShape
  | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8
deriving DecidableEq, Repr

/--
A problem-independent dynamical core.

The structural defect is deliberately discrete here.  This gives a
well-founded quantity: whenever the defect is non-zero, one structural
step must reduce it strictly.
-/
structure StructuralCore where
  State : Type
  step : State → State
  defect : State → Nat
  contract : ∀ x, 0 < defect x → defect (step x) < defect x

namespace StructuralCore

variable (C : StructuralCore)

/-- Terminality is intrinsic vanishing of the structural defect. -/
def Terminal (x : C.State) : Prop :=
  C.defect x = 0

/--
The contraction law cannot decrease forever: every state reaches
zero defect in finitely many structural steps.
-/
theorem zero_after_steps (x : C.State) :
    ∀ n : Nat, C.defect x ≤ n →
      ∃ k : Nat, k ≤ n ∧ C.defect ((C.step^[k]) x) = 0 := by
  intro n
  induction n generalizing x with
  | zero =>
      intro hx
      have hz : C.defect x = 0 := Nat.eq_zero_of_le_zero hx
      exact ⟨0, Nat.zero_le 0, by simpa using hz⟩
  | succ n ih =>
      intro hx
      by_cases hz : C.defect x = 0
      · exact ⟨0, Nat.zero_le (Nat.succ n), by simpa using hz⟩
      · have hpos : 0 < C.defect x := Nat.pos_of_ne_zero hz
        have hdec : C.defect (C.step x) < C.defect x :=
          C.contract x hpos
        have hnext : C.defect (C.step x) ≤ n := by
          omega
        obtain ⟨k, hk_le, hk_zero⟩ := ih (C.step x) hnext
        refine ⟨k + 1, ?_, ?_⟩
        · omega
        · simpa [Function.iterate_succ_apply] using hk_zero

/-- Canonical finite-time intrinsic closure theorem. -/
theorem intrinsic_vanishing (x : C.State) :
    ∃ k : Nat, k ≤ C.defect x ∧
      C.defect ((C.step^[k]) x) = 0 :=
  C.zero_after_steps x (C.defect x) (Nat.le_refl _)

end StructuralCore

/--
A manifestation does not identify the concrete mathematical object with
the structural core.  It only supplies an encoding and proves that
zero structural defect transports to that problem's terminal condition.
-/
structure Manifestation (P : ProblemKind) (C : StructuralCore) where
  ConcreteState : Type
  encode : ConcreteState → C.State
  terminal : ConcreteState → Prop
  decode : C.State → ConcreteState
  decode_encode : ∀ x, decode (encode x) = x
  terminal_of_zero :
    ∀ s : C.State, C.defect s = 0 → terminal (decode s)

/--
Universal structural transport.  This theorem is non-circular:
vanishing is obtained from strict descent of the intrinsic Nat-valued
defect, then transported through the problem-specific manifestation.
-/
theorem structural_number_closure
    {P : ProblemKind}
    (C : StructuralCore)
    (M : Manifestation P C)
    (x : M.ConcreteState) :
    ∃ k : Nat,
      k ≤ C.defect (M.encode x) ∧
      M.terminal (M.decode ((C.step^[k]) (M.encode x))) := by
  obtain ⟨k, hk, hz⟩ := C.intrinsic_vanishing (M.encode x)
  exact ⟨k, hk, M.terminal_of_zero _ hz⟩

/--
The shared object is the structural dynamics, not the concrete carrier.
Each problem may have a different concrete state type.
-/
theorem same_structure_not_same_object
    {P Q : ProblemKind}
    {C : StructuralCore}
    (MP : Manifestation P C)
    (MQ : Manifestation Q C) :
    Nonempty MP.ConcreteState → Nonempty MQ.ConcreteState →
      Nonempty MP.ConcreteState ∧ Nonempty MQ.ConcreteState := by
  intro hp hq
  exact ⟨hp, hq⟩

end MCore.ATK.StructuralDefect
