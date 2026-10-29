import MCore.ResolutionPredicate
import MCore.SevenDeltasFormal
import MCore.SevenParallelAttack

namespace MCore.UnifiedTerminalLogic

/-- The seven active mathematical endpoints tracked by the compact ATK route. -/
inductive Problem
  | beal | riemann | pnp | hodge | yangMills | bsd | navierStokes
  deriving DecidableEq, Repr

/-- Four reusable proof shapes. These classify the terminal payload, not the
scientific content of any particular problem. -/
inductive ProducerClass
  | witness
  | vanishing
  | realization
  | control
  deriving DecidableEq, Repr

/-- Six HARD stages retained in the compact route. -/
inductive HardStage
  | build
  | hygiene
  | circularitySemantic
  | adversarial
  | cleanRebuild
  | freeze
  deriving DecidableEq, Repr

def requiredStages : List HardStage :=
  [.build, .hygiene, .circularitySemantic, .adversarial, .cleanRebuild, .freeze]

theorem requiredStages_count : requiredStages.length = 6 := by decide

/-- A terminal chain contains the exact mathematical producer and a previously
certified consumer from that producer to the endpoint. Merely constructing the
record does not prove the producer. -/
structure TerminalChain where
  producer : Prop
  endpoint : Prop
  semanticExact : Prop
  nonCircular : Prop
  nonTrivial : Prop
  consume : producer → endpoint

/-- The only object allowed to close a terminal chain in the unified route.
The substantive field is producerProof; the other fields are certification
obligations. -/
structure HardCertificate (C : TerminalChain) : Prop where
  producerProof : C.producer
  semanticExactProof : C.semanticExact
  nonCircularProof : C.nonCircular
  nonTrivialProof : C.nonTrivial

theorem hardCertificate_closes_endpoint
    {C : TerminalChain}
    (cert : HardCertificate C) :
    C.endpoint :=
  C.consume cert.producerProof

/-- Reuse is fail-closed: an upstream certificate can be consumed only through
an explicit compatibility proof. -/
structure ReuseCompatibility (old new : Prop) : Prop where
  exactTransfer : old → new

theorem reuse
    {old new : Prop}
    (compat : ReuseCompatibility old new)
    (h : old) :
    new :=
  compat.exactTransfer h

/-- Metadata for scheduling the seven terminal producers. statement is only
a human-readable locator; mathematical closure still requires HardCertificate. -/
structure ProblemSpec where
  problem : Problem
  producerClass : ProducerClass
  statement : String
  frozenBackbone : Bool
  infrastructureRemaining : Nat

def bealSpec : ProblemSpec :=
  { problem := .beal
    producerClass := .witness
    statement := "UniversalTripleGCDLowerBound: forall BealData, 1 < gcd(a,gcd(b,c))"
    frozenBackbone := true
    infrastructureRemaining := 0 }

def riemannSpec : ProblemSpec :=
  { problem := .riemann
    producerClass := .vanishing
    statement := "ZERO_RESIDUE_SUM_UNCONDITIONAL_CONTROL -> VanishingUpperBound -> DNLimit=0"
    frozenBackbone := true
    infrastructureRemaining := 0 }

def pnpSpec : ProblemSpec :=
  { problem := .pnp
    producerClass := .witness
    statement := "canonical NP language + UniversalFailure / not_in_p"
    frozenBackbone := true
    infrastructureRemaining := 0 }

def hodgeSpec : ProblemSpec :=
  { problem := .hodge
    producerClass := .realization
    statement := "general rational Hodge algebraicity / surjectivity"
    frozenBackbone := true
    infrastructureRemaining := 0 }

def yangMillsSpec : ProblemSpec :=
  { problem := .yangMills
    producerClass := .realization
    statement := "genuine 4D physical realization + spectral-transfer witness"
    frozenBackbone := true
    infrastructureRemaining := 0 }

def bsdSpec : ProblemSpec :=
  { problem := .bsd
    producerClass := .control
    statement := "universal rank equality + refined leading-coefficient arithmetic package"
    frozenBackbone := true
    infrastructureRemaining := 0 }

def navierStokesSpec : ProblemSpec :=
  { problem := .navierStokes
    producerClass := .control
    statement := "theta<1 + terminal a in L1 + variable-coefficient Gronwall/semantic adapter"
    frozenBackbone := true
    infrastructureRemaining := 0 }

def allSpecs : List ProblemSpec :=
  [bealSpec, riemannSpec, pnpSpec, hodgeSpec, yangMillsSpec, bsdSpec, navierStokesSpec]

theorem allSpecs_count : allSpecs.length = 7 := by decide

theorem all_backbones_frozen :
    ∀ s ∈ allSpecs, s.frozenBackbone = true := by
  decide

theorem all_infrastructure_zero :
    ∀ s ∈ allSpecs, s.infrastructureRemaining = 0 := by
  decide

/-- The compact scheduler attacks only the terminal producer payloads. -/
def activeProducerCount : Nat := allSpecs.length

theorem activeProducerCount_eq_seven : activeProducerCount = 7 := by decide

/-- No endpoint is promoted by this architecture itself. -/
def finalProofCount : Nat := 0

theorem finalProofCount_eq_zero : finalProofCount = 0 := rfl

end MCore.UnifiedTerminalLogic
