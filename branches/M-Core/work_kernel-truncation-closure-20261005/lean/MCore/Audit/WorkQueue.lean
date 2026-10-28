import MCore.Audit.MasterClaims

namespace MCore.Audit

inductive WorkAction
  | reuse
  | freeze
  | certify
  | build
  | formalizeSource
  | produceMath
  | archive
  | noAction
  deriving Repr, DecidableEq

def actionForState : MCore.Canonical.ClaimState → WorkAction
  | .certified => .reuse
  | .frozen => .reuse
  | .green => .freeze
  | .buildPending => .build
  | .sourceReady => .formalizeSource
  | .openMath => .produceMath
  | .falsified => .archive
  | .superseded => .archive
  | .duplicate => .reuse

theorem openMath_action :
    actionForState .openMath = .produceMath := by
  rfl

theorem green_action :
    actionForState .green = .freeze := by
  rfl

end MCore.Audit
