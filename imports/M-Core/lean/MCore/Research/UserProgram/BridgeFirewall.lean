import MCore.Research.UserProgram.LocalGlobal
import MCore.Research.UserProgram.Operators
import MCore.Research.UserProgram.IRegime

namespace MCore.Research.UserProgram

inductive EvidenceState where
  | definition
  | provedLaw
  | counterprobe
  | openMath
  | material
deriving DecidableEq, Repr

structure BridgeRecord where
  name : String
  state : EvidenceState
  note : String

def millenniumBridgeFirewall : List BridgeRecord :=
  [ ⟨"RH", .openMath, "No bridge supplied by the universal framework."⟩
  , ⟨"PNP", .openMath, "No bridge supplied by the universal framework."⟩
  , ⟨"BSD", .openMath, "No bridge supplied by the universal framework."⟩
  , ⟨"Hodge", .openMath, "No bridge supplied by the universal framework."⟩
  , ⟨"YM", .openMath, "No bridge supplied by the universal framework."⟩
  , ⟨"NS", .openMath, "No bridge supplied by the universal framework."⟩ ]

theorem firewall_has_six_entries : millenniumBridgeFirewall.length = 6 := by
  native_decide

end MCore.Research.UserProgram
