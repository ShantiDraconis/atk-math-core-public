import MCore.Canonical.ClaimState

namespace MCore.Canonical

structure ClaimRecord where
  id : String
  lane : String
  statement : String
  kind : ClaimKind
  state : ClaimState
  producer : Option String := none
  dependencies : List String := []
  evidence : List String := []
  reusable : Bool := false
  notes : String := ""
  deriving Repr, DecidableEq

def ClaimRecord.isTerminalOpen (c : ClaimRecord) : Bool :=
  c.state == .openMath && c.producer.isSome

def ClaimRecord.isReusableClosed (c : ClaimRecord) : Bool :=
  c.reusable && c.state.isClosed

end MCore.Canonical
