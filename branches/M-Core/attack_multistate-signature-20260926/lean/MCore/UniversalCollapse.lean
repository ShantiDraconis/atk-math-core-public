import MCore.FinalFail.SevenLocalNuclei
import MCore.UniversalMultistateEvidence

namespace MCore.UniversalCollapse

open MCore.FinalFail
open MCore.UniversalMultistateEvidence

/-- A family of concrete terminal nuclei, one per tracked problem. -/
structure NucleusFamily where
  nucleus : ProblemId → OpenRigidNucleus
  problem_ok : ∀ p, (nucleus p).problem = p

/-- The exact universal material law:
for every tracked problem, produce the missing Core proposition of its nucleus.
This is the only form strong enough to close every downstream endpoint through
the already-certified local transport. -/
def UniversalCollapseLaw (F : NucleusFamily) : Prop :=
  ∀ p : ProblemId, (F.nucleus p).Core

/-- If the universal law is inhabited, every endpoint closes. -/
theorem universal_collapse_closes_all
    (F : NucleusFamily)
    (hU : UniversalCollapseLaw F) :
    ∀ p : ProblemId, (F.nucleus p).Endpoint := by
  intro p
  exact close_local_nucleus (F.nucleus p) (hU p)

/-- The multistate/signature theorem supplies classification evidence only.
It does not manufacture any nucleus Core. -/
theorem structural_evidence_is_classification_only
    (p : ProblemId) :
    (realize p .start).number = 0 ∧
    (realize p .obstruction).number = 1 ∧
    (realize p .terminal).number = 2 ∧
    (realize p .terminal).obstruction = obstructionOf p := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact fail-closed boundary:
a proposed cross-problem argument closes all endpoints iff it actually supplies
the missing Core for every problem-specific nucleus. -/
theorem universal_collapse_exact
    (F : NucleusFamily) :
    UniversalCollapseLaw F ↔
      (∀ p : ProblemId, (F.nucleus p).Core) := by
  rfl

#print axioms universal_collapse_closes_all
#print axioms structural_evidence_is_classification_only
#print axioms universal_collapse_exact

end MCore.UniversalCollapse
