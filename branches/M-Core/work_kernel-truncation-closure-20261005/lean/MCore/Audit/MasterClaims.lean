import MCore.OpenMath.RH
import MCore.OpenMath.PNP
import MCore.OpenMath.NS
import MCore.OpenMath.BSD
import MCore.OpenMath.Hodge
import MCore.OpenMath.YM
import MCore.OpenMath.Beal
import MCore.Audit.HistoricalClaims

namespace MCore.Audit

def terminalClaims : List MCore.Canonical.ClaimRecord := [
  MCore.OpenMath.RH.terminal,
  MCore.OpenMath.PNP.terminal,
  MCore.OpenMath.NS.terminal,
  MCore.OpenMath.BSD.rankTerminal,
  MCore.OpenMath.BSD.refinedTerminal,
  MCore.OpenMath.Hodge.terminal,
  MCore.OpenMath.YM.terminal,
  MCore.OpenMath.Beal.terminal
]

theorem terminalClaims_length : terminalClaims.length = 8 := by
  rfl

def inventory : List MCore.Canonical.ClaimRecord :=
  terminalClaims ++ historicalClaims

end MCore.Audit
