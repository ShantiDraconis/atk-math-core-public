import MCore.ProofEngine.Composition

namespace MCore.ProofEngine

/-- Provenance for a reusable producer. A registry entry cannot manufacture
`proof`; it must receive the producer explicitly. -/
structure RegistryEntry (P Q : Prop) where
  pattern : Pattern
  sourceRepo : String
  sourceRef : String
  theoremName : String
  proof : Producer P Q

def RegistryEntry.apply {P Q : Prop} (e : RegistryEntry P Q) (h : P) : Q :=
  e.proof.run h

end MCore.ProofEngine
