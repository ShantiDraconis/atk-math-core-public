import MCore.OpenMath.RH
import MCore.OpenMath.PNP
import MCore.OpenMath.NS
import MCore.OpenMath.BSD
import MCore.OpenMath.Hodge
import MCore.OpenMath.YM
import MCore.OpenMath.Beal

namespace MCore.OpenMath

def allTerminalFrontiers : List MCore.Canonical.ClaimRecord := [
  RH.terminal,
  PNP.terminal,
  NS.terminal,
  BSD.rankTerminal,
  BSD.refinedTerminal,
  Hodge.terminal,
  YM.terminal,
  Beal.terminal
]

theorem allTerminalFrontiers_length :
    allTerminalFrontiers.length = 8 := by
  rfl

end MCore.OpenMath
