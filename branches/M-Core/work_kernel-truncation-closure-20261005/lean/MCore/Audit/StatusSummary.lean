import MCore.Audit.MasterClaims
import MCore.Problems.Registry

namespace MCore.Audit

structure StatusSummary where
  terminalSlots : Nat
  historicalClaims : Nat
  certifiedByThisInventory : Nat
  frozenByThisInventory : Nat
  greenByThisInventory : Nat
  openMathByThisInventory : Nat
  deriving Repr, DecidableEq

/-- This summary describes only the new master inventory records.
It deliberately does not infer certification from historical branch names. -/
def initialSummary : StatusSummary where
  terminalSlots := 8
  historicalClaims := 6
  certifiedByThisInventory := 0
  frozenByThisInventory := 0
  greenByThisInventory := 0
  openMathByThisInventory := 8

theorem initialSummary_terminalSlots :
    initialSummary.terminalSlots = 8 := by
  rfl

theorem initialSummary_openMath :
    initialSummary.openMathByThisInventory = 8 := by
  rfl

end MCore.Audit
