import MCore.FinalFail.ArtifactAttachment

namespace MCore.FinalFail.Attack.NavierStokes

structure CompensatorContract where
  construction : String
  independentOfTrivialNegation : Prop
  budgetStatement : String

structure SignedGainContract where
  cancellationStatement : String
  openCZStatement : String

def compensatorTarget : String :=
  "construct C_N independently of the tautological choice C_N = -T_N and prove a quantitative budget"

def signedGainTarget : String :=
  "derive the signed far-field positive scale gain required by OPEN_CZ from a legitimate cancellation mechanism"

def forbidden : List String :=
  ["C_N := -T_N", "replace signed cancellation by an absolute-value bound", "use hDynamic circularly"]

end MCore.FinalFail.Attack.NavierStokes
