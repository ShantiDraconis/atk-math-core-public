namespace MCore.ProofEngine

/-- Cross-domain proof-obligation classes. These classify bridges; they do not
assert that any scientific target is solved. -/
inductive Pattern
  | realizability
  | uniformization
  | localToGlobal
  | endpointBridge
  deriving DecidableEq, Repr

end MCore.ProofEngine
