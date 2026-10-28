import MCore.IBoundaryProvenance

/-!
# BSD Logic Open-Math Gate

Single fail-closed gate for the structural closure-logic claim.

This module deliberately does not assert BSD, its negation, or any arithmetic
statement about elliptic curves.  It packages the exact remaining bridge:
a BSD-facing observation must be shown to require preservation of the
provenance information that terminal projection erases.
-/

namespace MCore.BSDLogic

open MCore.IBoundary

/-- Minimal abstract BSD-facing interface.  The adapter supplies observations
and states; no mathematical BSD conclusion is built into this structure. -/
structure BSDLogicAdapter where
  State : Type
  observe : State → ℝ
  encode : State → INumber
  observe_eq_terminal : ∀ x, observe x = terminalProjection (encode x)

/-- A representation is complete for provenance when provenance can be
reconstructed from the observable alone. -/
def CompleteForProvenance (observe : α → ℝ) (encode : α → INumber) : Prop :=
  ∃ decode : ℝ → ℤ × ℤ, ∀ x, decode (observe x) = provenanceCode (encode x)

/-- Independent witness condition: two domain states have the same observable
but genuinely different encoded provenance. -/
structure BoundaryCollision (A : BSDLogicAdapter) where
  left : A.State
  right : A.State
  same_observation : A.observe left = A.observe right
  different_provenance :
    provenanceCode (A.encode left) ≠ provenanceCode (A.encode right)

/-- Generic, axiom-free information-loss theorem. -/
theorem collision_refutes_complete_representation
    (A : BSDLogicAdapter) (h : BoundaryCollision A) :
    ¬ CompleteForProvenance A.observe A.encode := by
  intro hc
  rcases hc with ⟨decode, hdecode⟩
  have hl := hdecode h.left
  have hr := hdecode h.right
  apply h.different_provenance
  calc
    provenanceCode (A.encode h.left)
        = decode (A.observe h.left) := hl.symm
    _ = decode (A.observe h.right) := by rw [h.same_observation]
    _ = provenanceCode (A.encode h.right) := hr

/-- The single OPEN_MATH obligation.  To close it, construct this witness from
the actual BSD adapter without assuming the desired conclusion. -/
structure BSDLogicOpenMathWitness (A : BSDLogicAdapter) where
  collision : BoundaryCollision A

/-- Terminal theorem of the logic layer.  It is conditional only on the
explicit witness that remains OPEN_MATH. -/
theorem BSDClosureLogicRefutation
    (A : BSDLogicAdapter)
    (w : BSDLogicOpenMathWitness A) :
    ¬ CompleteForProvenance A.observe A.encode :=
  collision_refutes_complete_representation A w.collision

/-- Fail-closed status: issuance requires a concrete witness. -/
def ExternalLogicCertificateReady (A : BSDLogicAdapter) : Prop :=
  Nonempty (BSDLogicOpenMathWitness A)

theorem certificate_ready_implies_logic_refutation
    (A : BSDLogicAdapter)
    (h : ExternalLogicCertificateReady A) :
    ¬ CompleteForProvenance A.observe A.encode := by
  rcases h with ⟨w⟩
  exact BSDClosureLogicRefutation A w

end MCore.BSDLogic

