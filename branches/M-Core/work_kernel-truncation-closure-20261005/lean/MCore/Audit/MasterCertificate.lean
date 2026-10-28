import MCore.Canonical.Rules
import MCore.Reuse.Registry
import MCore.OpenMath.All
import MCore.Problems.Registry
import MCore.Audit.MasterDependencies
import MCore.Audit.WorkQueue
import MCore.Audit.StatusSummary

namespace MCore.Audit

/-- Administrative inventory invariant: eight material terminal producer slots are tracked.
This theorem does not assert that any producer is inhabited. -/
theorem tracks_eight_terminal_producer_slots :
    terminalClaims.length = 8 := by
  rfl

/-- All terminal records in the initial master inventory are intentionally OPEN_MATH.
This is an administrative status statement, not a theorem about the conjectures. -/
def terminalStates : List MCore.Canonical.ClaimState :=
  terminalClaims.map (fun c => c.state)

def expectedOpenStates : List MCore.Canonical.ClaimState :=
  List.replicate 8 .openMath

theorem initial_terminal_states_are_open :
    terminalStates = expectedOpenStates := by
  rfl

theorem problem_registry_tracks_eight_slots :
    MCore.Problems.totalOpenTerminalSlots = 8 := by
  exact MCore.Problems.totalOpenTerminalSlots_eq_eight

theorem open_math_registry_tracks_eight_frontiers :
    MCore.OpenMath.allTerminalFrontiers.length = 8 := by
  exact MCore.OpenMath.allTerminalFrontiers_length

#print axioms MCore.Canonical.certified_is_closed
#print axioms MCore.Canonical.frozen_is_closed
#print axioms MCore.Canonical.openMath_requires_material_producer
#print axioms MCore.Reuse.nonempty_map
#print axioms MCore.Reuse.implication_comp
#print axioms MCore.Problems.totalOpenTerminalSlots_eq_eight
#print axioms MCore.OpenMath.allTerminalFrontiers_length
#print axioms MCore.Audit.tracks_eight_terminal_producer_slots
#print axioms MCore.Audit.initial_terminal_states_are_open
#print axioms MCore.Audit.problem_registry_tracks_eight_slots
#print axioms MCore.Audit.open_math_registry_tracks_eight_frontiers

end MCore.Audit
