import MCore.Problems.Lane

namespace MCore.Problems

structure LaneRegistryEntry where
  lane : Lane
  openTerminalSlots : Nat
  role : String
  deriving Repr, DecidableEq

def registry : List LaneRegistryEntry := [
  ⟨.rh, 1, "Millennium lane"⟩,
  ⟨.pnp, 1, "Millennium lane"⟩,
  ⟨.ns, 1, "Millennium lane"⟩,
  ⟨.bsd, 2, "Millennium lane with independent rank/refined producers"⟩,
  ⟨.hodge, 1, "Millennium lane"⟩,
  ⟨.ym, 1, "Millennium lane"⟩,
  ⟨.beal, 1, "Beal terminal lane"⟩,
  ⟨.poincare, 0, "control lane; not counted as an open terminal producer slot"⟩,
  ⟨.historical, 0, "historical claims awaiting canonicalization"⟩
]

def totalOpenTerminalSlots : Nat :=
  registry.foldl (fun n e => n + e.openTerminalSlots) 0

theorem totalOpenTerminalSlots_eq_eight :
    totalOpenTerminalSlots = 8 := by
  rfl

end MCore.Problems
