import MCore.V21.CoreIdentity

namespace MCore.V21

/-- A problem enters the M-Core only through a typed adapter. The adapter
    records where its completed closure belongs in the core process. -/
structure ProblemEmbedding where
  problemId : String
  site : ClosureSite

/-- Registration cannot create a proof. It requires a TargetCertificate and
    merely places that already-closed result into the core closed locus. -/
def ProblemEmbedding.register
    (E : ProblemEmbedding)
    {Start Middle Final : Prop}
    (cert : TargetCertificate Start Middle Final) :
    CoreClosedLocus :=
  absorb E.problemId E.site cert

/-- Interior closure: the problem's own mathematical chain closes inside the
    central process and is then absorbed by the closed identity. -/
def interiorEmbedding (problemId : String) : ProblemEmbedding :=
  { problemId := problemId, site := .interior }

/-- Left-edge closure: the problem arrives already carrying its complete
    certificate. -/
def leftBoundaryEmbedding (problemId : String) : ProblemEmbedding :=
  { problemId := problemId, site := .leftBoundary }

/-- Right-edge closure: the last problem-specific edge closes at the egress and
    the completed certificate is absorbed back into the same closed locus. -/
def rightBoundaryEmbedding (problemId : String) : ProblemEmbedding :=
  { problemId := problemId, site := .rightBoundary }

theorem registered_endpoint
    (E : ProblemEmbedding)
    {Start Middle Final : Prop}
    (cert : TargetCertificate Start Middle Final) :
    (E.register cert).Start → (E.register cert).Final :=
  (E.register cert).endpoint

end MCore.V21
