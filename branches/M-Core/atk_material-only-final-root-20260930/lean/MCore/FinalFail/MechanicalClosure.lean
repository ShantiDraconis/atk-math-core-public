import MCore.FinalFail.DirectProducerCuts

namespace MCore.FinalFail.Semantic

/-!
# Mechanical closure ledger

Mechanical obligations may block executable packaging, but never increment
OPEN_MATH.  All P01 wiring has been compressed through the already-proved
integrated assembly theorem:

  P01PrepPhase + P01VerifierPhase -> P01MachineConstruction.

The prep phase, canonical bounded evaluator, exact global canonical fuel and
verifier-phase assembly are already structurally reduced on the advanced P01
line. Therefore the only remaining mechanical min-cut is raw-source
totalization: decoder failure must halt and reject at the same fixed global
fuel.
-/

inductive MechanicalState where
  | recoveredCandidate
  | pending
  | closed
  deriving DecidableEq, Repr

structure MechanicalClosure where
  problem : ProblemId
  target : String
  evidence : String
  state : MechanicalState
  deriving Repr

def mechanicalClosures : List MechanicalClosure := [
  { problem := .pVsNP
    target := "P01RawTotalizationMinCut.RawDecodeNoneFailClosed"
    evidence := "Forward-only reduction on atk/p01-verifier-phase-mincut-clean-20260930: exact_encoding_or_decode_none splits every raw BitString into canonical encodeCircuit phi or decoder failure; exact bounded canonical execution supplies halts/correct on the canonical side; RawDecodeNoneFailClosed.toGlobalCore -> p01ConstructionGap_of_core -> P01ConstructionGap. Source theorem added at f25f362c and kernel audit is required before promotion."
    state := .pending }
]

def mechanicalClosureCount : Nat := mechanicalClosures.length

def pendingMechanicalCount : Nat :=
  mechanicalClosures.foldl
    (fun n lane => if lane.state = .closed then n else n + 1) 0

def closedMechanicalCount : Nat :=
  mechanicalClosures.foldl
    (fun n lane => if lane.state = .closed then n + 1 else n) 0

theorem mechanicalClosureCount_eq_one :
    mechanicalClosureCount = 1 := by
  decide

theorem pendingMechanicalCount_eq_one :
    pendingMechanicalCount = 1 := by
  decide

theorem closedMechanicalCount_eq_zero :
    closedMechanicalCount = 0 := by
  decide

/-- Mechanical obligations are explicitly outside the seven OPEN_MATH slots. -/
theorem material_count_ignores_mechanical :
    openDirectCount = 7 := openDirectCount_eq_seven

end MCore.FinalFail.Semantic
