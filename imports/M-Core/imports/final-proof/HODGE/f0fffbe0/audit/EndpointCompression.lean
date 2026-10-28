import MCore.K26
import MCore.Frontier.CandidateBridge

namespace HodgeBackwardAudit

open MCore
open MCore.Frontier

def FINAL_STATEMENT (G : GradedRationalHodgeData) : Prop :=
  GradedRationalHodgeConjecture G

def REAL_ALGEBRAICITY_FRONTIER
    {G : GradedRationalHodgeData} (M : CycleSpanMechanics G) : Prop :=
  ConcreteAlgebraicityPayload M

inductive CompressionRole where
  | wiring
  | frontierReal
  deriving Repr, DecidableEq

inductive CompressionProvenance where
  | internalLean
  | externalClassical
  | externalFormalization
  | openMathematics
  deriving Repr, DecidableEq

structure CompressionNode where
  id : String
  source : String
  role : CompressionRole
  provenance : CompressionProvenance
  reference : String
  deriving Repr

def endpointNodes : List CompressionNode :=
  [ { id := "G1"
      source := "K13 graded quantifier normalization"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K13.lean::gradedHodge_iff_pointwise" }
  , { id := "G2"
      source := "K14 algebraicity payload normalization"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K14.lean::gradedHodge_iff_algebraicityPayload" }
  , { id := "G3"
      source := "K15 finite cycle-span mechanics"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K15.lean" }
  , { id := "G4"
      source := "K16 concrete surjectivity transport"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K16.lean::hodge_iff_concreteSurjectivity" }
  , { id := "G5"
      source := "K17 finite combination witnesses"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K17.lean" }
  , { id := "G6"
      source := "K18 concrete payload normalization"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K18.lean::hodge_iff_concretePayload" }
  , { id := "G7"
      source := "cycle-class soundness implementation"
      role := .wiring
      provenance := .externalFormalization
      reference := "lean/MCore/K19.lean::CycleClassGeometryInterface; classical cycle-class fact not imported as a concrete theorem" }
  , { id := "G8"
      source := "K20 certification boundary"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K20.lean::hodge_iff_payload_at_boundary" }
  , { id := "G9"
      source := "K21-K24 coefficient/span realization interfaces"
      role := .wiring
      provenance := .externalFormalization
      reference := "lean/MCore/K21.lean through lean/MCore/K24.lean" }
  , { id := "G10"
      source := "K25 concrete cohomology realization"
      role := .wiring
      provenance := .externalFormalization
      reference := "lean/MCore/K25.lean::RealizedConcreteModelObligation" }
  , { id := "G11"
      source := "K26 minimal-cut equivalence"
      role := .wiring
      provenance := .internalLean
      reference := "lean/MCore/K26.lean::k26_minimal_cut" }
  , { id := "G12"
      source := "general algebraicity of arbitrary rational (p,p) classes"
      role := .frontierReal
      provenance := .openMathematics
      reference := "ConcreteAlgebraicityPayload M" }
  , { id := "G13"
      source := "algebraicity of the Hodge locus"
      role := .wiring
      provenance := .externalClassical
      reference := "Cattani-Deligne-Kaplan, JAMS 8 (1995), Theorem 1.1 / Corollary 1.2, DOI 10.1090/S0894-0347-1995-1273413-2" }
  , { id := "G14"
      source := "construct a suitable spread for every endpoint input"
      role := .frontierReal
      provenance := .openMathematics
      reference := "CandidateBridge.C_Spread instantiated uniformly in X,p,alpha" }
  , { id := "G15"
      source := "spread produces an algebraic point on the relevant Hodge locus"
      role := .frontierReal
      provenance := .openMathematics
      reference := "CandidateBridge.spreadProducesPoint input" }
  , { id := "G16"
      source := "specialization from one algebraic fiber to the general endpoint payload"
      role := .frontierReal
      provenance := .openMathematics
      reference := "CandidateBridge.specialization input; no unrestricted theorem is present" }
  ]

/-- Certified compression already present in K26: after the explicit formal
    boundary is supplied, the full endpoint is exactly the real algebraicity
    frontier. -/
theorem endpoint_compression
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) :
    FINAL_STATEMENT G ↔ REAL_ALGEBRAICITY_FRONTIER M := by
  exact k26_minimal_cut B

theorem real_frontier_closes_endpoint
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (hA : REAL_ALGEBRAICITY_FRONTIER M) :
    FINAL_STATEMENT G := by
  exact (endpoint_compression B).2 hA

/-- Dense candidate compression. Every non-wiring mathematical input is visible
    in the type. The theorem itself proves only the composition. -/
theorem spread_variational_compression
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    {V : AlgebraicityCandidateVocabulary}
    (hLocus : V.hodgeLocusAlgebraic)
    (hSpread : C_Spread V)
    (spreadProducesPoint :
      C_Spread V → V.hasAlgebraicPointOnHodgeLocus)
    (specialization :
      V.hasAlgebraicPointOnHodgeLocus → REAL_ALGEBRAICITY_FRONTIER M) :
    FINAL_STATEMENT G := by
  apply real_frontier_closes_endpoint B
  exact specialization (spreadProducesPoint hSpread)

/-- Current compression is audit-only and cannot itself promote the endpoint. -/
def compressionMathematicalPromotion : Bool := false

theorem compression_is_nonpromoting :
    compressionMathematicalPromotion = false := by
  rfl

#print axioms HodgeBackwardAudit.endpoint_compression
#print axioms HodgeBackwardAudit.real_frontier_closes_endpoint
#print axioms HodgeBackwardAudit.spread_variational_compression
#print axioms HodgeBackwardAudit.compression_is_nonpromoting

end HodgeBackwardAudit
