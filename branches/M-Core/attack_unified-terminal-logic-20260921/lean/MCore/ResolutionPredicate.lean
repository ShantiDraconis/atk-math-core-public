namespace MCore.Resolution

inductive ResolutionKind
  | nonexistence | elimination | vanishingEstimate | quotientZero
  | separation | equalityZero | bridgeAndVanishing | positivity
  deriving DecidableEq, Repr

structure ResolutionClaim where
  kind : ResolutionKind
  obstruction : Prop
  endpoint : Prop

/-- Fail-closed: a resolution is an implication that must actually be proved. -/
def Resolved (c : ResolutionClaim) : Prop := c.obstruction → c.endpoint

end MCore.Resolution
