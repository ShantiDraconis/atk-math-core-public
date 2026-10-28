import MCore.Canonical.Claim

namespace MCore.Canonical

/-- Administrative transition relation only. It does not prove mathematical claims. -/
def forwardTransition : ClaimState → ClaimState → Prop
  | .sourceReady, .buildPending => True
  | .buildPending, .green => True
  | .green, .frozen => True
  | .frozen, .certified => True
  | .openMath, .sourceReady => True
  | .duplicate, .superseded => True
  | s, t => s = t

theorem certified_is_closed : ClaimState.certified.isClosed = true := by
  rfl

theorem frozen_is_closed : ClaimState.frozen.isClosed = true := by
  rfl

theorem openMath_requires_material_producer :
    ClaimState.openMath.needsMaterialProducer = true := by
  rfl

end MCore.Canonical
