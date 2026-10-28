import MCore.V21.Control

namespace MCore.V21

/-- The mathematical motor: no open edge is permitted.
    constructMiddle must construct the real middle obligation from START;
    compression.close then reaches FINAL. -/
structure ClosedChain (Start Middle Final : Prop) where
  constructMiddle : Start → Middle
  compression : Compression Middle Final
  controls : ControlPack
  controlsClosed : controls.Closed

theorem ClosedChain.closes
    {Start Middle Final : Prop}
    (C : ClosedChain Start Middle Final) :
    Start → Final :=
  fun hStart => C.compression.close (C.constructMiddle hStart)

/-- A TARGET certificate contains the mathematical chain itself, not merely a
    successful build. -/
structure TargetCertificate (Start Middle Final : Prop) where
  chain : ClosedChain Start Middle Final

theorem TargetCertificate.endpoint
    {Start Middle Final : Prop}
    (cert : TargetCertificate Start Middle Final) :
    Start → Final :=
  cert.chain.closes

/-- If the middle constructor is only hypothetical, the result remains
    explicitly conditional and is not a TargetCertificate. -/
structure ConditionalChain (Hyp Start Middle Final : Prop) where
  constructMiddle : Hyp → Start → Middle
  compression : Compression Middle Final

theorem ConditionalChain.closes_under
    {Hyp Start Middle Final : Prop}
    (C : ConditionalChain Hyp Start Middle Final) :
    Hyp → Start → Final :=
  fun hHyp hStart => C.compression.close (C.constructMiddle hHyp hStart)

end MCore.V21
