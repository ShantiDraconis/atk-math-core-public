import MCore.FinalFail.TriadicObstructionCalculus
import MCore.FinalFail.SevenProblemSignatures

namespace MCore.FinalFail

/--
The common structural signature only.

Every problem is represented through the same three structural sites:
start -> middle -> finish. This does not identify the mathematical objects
living at those sites.
-/
structure CommonMultiStateShape where
  State : Type
  start : State
  middle : State
  finish : State
  start_ne_middle : start ≠ middle
  middle_ne_finish : middle ≠ finish
  start_ne_finish : start ≠ finish

/-- Canonical common 0/1/2 shape used only as structural coordinates. -/
def canonical012Shape : CommonMultiStateShape where
  State := Fin3
  start := .start
  middle := .middle
  finish := .finish
  start_ne_middle := by decide
  middle_ne_finish := by decide
  start_ne_finish := by decide

/--
A problem-specific manifestation.

Scalar and object are intentionally local to the problem. Two problems
need not have the same scalar type or the same mathematical object. What is
shared is only the three-state shape and its transport geometry.
-/
structure ProblemMultiStateManifestation (p : ProblemId) where
  Scalar : Type
  object : Scalar
  stateValue : Fin3 → Scalar
  shape : CommonMultiStateShape
  shape_is_common : shape = canonical012Shape
  signature : ProblemSignature
  signature_eq : signature = signatureOf p

/--
A family of concrete manifestations, one different object per problem,
all respecting the same structural 0/1/2 shape.
-/
structure CrossProblemMultiStateFamily where
  manifestation : ∀ p : ProblemId, ProblemMultiStateManifestation p

/--
The common structure is inherited by every member of a supplied family.
No equality between problem-specific objects is asserted.
-/
theorem every_manifestation_has_common_shape
    (F : CrossProblemMultiStateFamily)
    (p : ProblemId) :
    (F.manifestation p).shape = canonical012Shape :=
  (F.manifestation p).shape_is_common

/--
Each manifestation also preserves the already-audited qualitative signature
of its own problem.
-/
theorem every_manifestation_preserves_problem_signature
    (F : CrossProblemMultiStateFamily)
    (p : ProblemId) :
    (F.manifestation p).signature = signatureOf p :=
  (F.manifestation p).signature_eq

/--
Exact theorem matching the intended claim:

IF each problem supplies its own mathematical manifestation, THEN there exists
a cross-problem family in which every manifestation has the same multistate
shape while retaining its problem-specific object and signature.

This closes the structural transport theorem, not the individual OPEN_MATH
producer of any problem.
-/
theorem exists_common_signature_from_problem_manifestations
    (H : ∀ p : ProblemId, Nonempty (ProblemMultiStateManifestation p)) :
    ∃ F : CrossProblemMultiStateFamily,
      ∀ p : ProblemId,
        (F.manifestation p).shape = canonical012Shape ∧
        (F.manifestation p).signature = signatureOf p := by
  choose M hM using H
  let F : CrossProblemMultiStateFamily :=
    { manifestation := fun p => M p }
  refine ⟨F, ?_⟩
  intro p
  exact ⟨(M p).shape_is_common, (M p).signature_eq⟩

/--
The seven problem-specific signatures remain distinct. Sharing the multistate
shape therefore does not collapse the mathematical problems into one object.
-/
theorem problem_specific_signatures_remain_distinct :
    Function.Injective signatureOf :=
  signature_assignment_injective

/-- Likewise, the terminal slots remain problem-specific. -/
theorem problem_specific_terminal_slots_remain_distinct :
    Function.Injective slotOf :=
  slotOf_injective

/--
A full structural signature consists of the shared shape plus the local
qualitative signature. Since the common component is identical, uniqueness is
carried by the problem-specific signature.
-/
def structuralSignature (p : ProblemId) :
    CommonMultiStateShape × ProblemSignature :=
  (canonical012Shape, signatureOf p)

theorem structural_signature_injective :
    Function.Injective structuralSignature := by
  intro a b h
  have hs : signatureOf a = signatureOf b := congrArg Prod.snd h
  exact signature_assignment_injective hs

/--
Fail-closed status: the generic structural theorem is proved, but existence of
a concrete manifestation for each named problem must come from that problem's
own certified adapter.
-/
def universalMultiStateStructureTheoremClosed : Bool := true

theorem universal_multistate_structure_theorem_closed :
    universalMultiStateStructureTheoremClosed = true := by
  rfl

#print axioms MCore.FinalFail.every_manifestation_has_common_shape
#print axioms MCore.FinalFail.exists_common_signature_from_problem_manifestations
#print axioms MCore.FinalFail.problem_specific_signatures_remain_distinct
#print axioms MCore.FinalFail.structural_signature_injective
#print axioms MCore.FinalFail.universal_multistate_structure_theorem_closed

end MCore.FinalFail
