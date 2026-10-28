namespace MCore.Problems

inductive Lane
  | rh
  | pnp
  | ns
  | bsd
  | hodge
  | ym
  | beal
  | poincare
  | historical
  deriving Repr, DecidableEq

def Lane.code : Lane → String
  | .rh => "RH"
  | .pnp => "PNP"
  | .ns => "NS"
  | .bsd => "BSD"
  | .hodge => "HODGE"
  | .ym => "YM"
  | .beal => "BEAL"
  | .poincare => "POINCARE"
  | .historical => "HISTORICAL"

end MCore.Problems
