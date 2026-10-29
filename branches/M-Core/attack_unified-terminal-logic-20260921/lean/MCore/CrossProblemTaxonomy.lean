namespace MCore.CrossProblemTaxonomy

inductive Similarity
  | exact
  | structural
  | analogical
  | disjoint
  deriving DecidableEq, Repr

inductive EvidenceClass
  | certified
  | reuse
  | openMath
  | discarded
  | negativeControl
  | provenanceOnly
  deriving DecidableEq, Repr

inductive FailureMode
  | trivialInterface
  | axiomGate
  | circularReformulation
  | finiteToUniversal
  | semanticMismatch
  | domainMismatch
  | quantifierMismatch
  deriving DecidableEq, Repr

structure CrossEdge where
  source : String
  target : String
  similarity : Similarity
  evidence : EvidenceClass
  mechanism : String
  theoremTransferAllowed : Bool

def rhBsd : CrossEdge :=
  { source := "RH"
    target := "BSD"
    similarity := .structural
    evidence := .reuse
    mechanism := "L-functions / zeros / analytic order / normalization"
    theoremTransferAllowed := false }

def nsYm : CrossEdge :=
  { source := "NS"
    target := "YM"
    similarity := .structural
    evidence := .reuse
    mechanism := "PDE / energy / scaling / uniformity"
    theoremTransferAllowed := false }

def hodgeBsdYm : CrossEdge :=
  { source := "HODGE"
    target := "BSD+YM"
    similarity := .structural
    evidence := .reuse
    mechanism := "cohomology / realization / moduli vocabulary"
    theoremTransferAllowed := false }

def bealPnp : CrossEdge :=
  { source := "BEAL"
    target := "PNP"
    similarity := .structural
    evidence := .reuse
    mechanism := "nontrivial terminal witness pattern"
    theoremTransferAllowed := false }

def allEdges : List CrossEdge := [rhBsd, nsYm, hodgeBsdYm, bealPnp]

theorem allEdges_no_automatic_theorem_transfer :
    ∀ e ∈ allEdges, e.theoremTransferAllowed = false := by
  decide

def universalFailureModes : List FailureMode :=
  [.trivialInterface, .axiomGate, .circularReformulation,
   .finiteToUniversal, .semanticMismatch, .domainMismatch, .quantifierMismatch]

theorem universalFailureMode_count :
    universalFailureModes.length = 7 := by
  decide

end MCore.CrossProblemTaxonomy
