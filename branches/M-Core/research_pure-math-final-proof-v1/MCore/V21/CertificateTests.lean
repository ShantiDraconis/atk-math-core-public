import MCore.V21.ClosedChain
import MCore.V21.ResidueClassifier
import MCore.V21.CrossRepo
import MCore.V21.Examples
import MCore.V21.ProblemEmbedding

namespace MCore.V21.CertificateTests

def greenControls : ControlPack where
  headExact := ⟨"TEST_HEAD", "TEST_HEAD"⟩
  frozenS1 :=
    { sha := "TEST_S1"
      untouched := true
      noK27 := true
      noK31 := true
      noK32 := true }
  endpoint :=
    { name := "FinalEndpoint"
      kind := .definitionOnly
      assumptionSubstituteCount := 0 }
  compressionAuditGreen := true
  audit6d :=
    { sourceSHA := "TEST_SOURCE"
      literalDeclaration := "Start -> Middle"
      hypothesisMatch := true
      conclusionMatch := true
      quantifierMatch := true
      scalingMatch := true
      constantMatch := true
      axiomAudit := true }
  residues := {}
  build :=
    { lakeBuildGreen := true
      printAxiomsRun := true
      unexpectedAxiomCount := 0 }
  noPlacebo := {}

theorem greenControls_closed : greenControls.Closed := by
  simp [greenControls, ControlPack.Closed, HeadExact.Closed, FrozenS1.Closed,
    EndpointDefinition.Closed, Audit6D.Closed, ResidueLedger.Closed,
    BuildGate.Closed, NoPlacebo.Closed]

def badHeadControls : ControlPack :=
  { greenControls with
    headExact := ⟨"EXPECTED", "ACTUAL"⟩ }

theorem badHead_fails_closed : ¬ badHeadControls.Closed := by
  simp [badHeadControls, greenControls, ControlPack.Closed, HeadExact.Closed,
    FrozenS1.Closed, EndpointDefinition.Closed, Audit6D.Closed,
    ResidueLedger.Closed, BuildGate.Closed, NoPlacebo.Closed]

def placeboControls : ControlPack :=
  { greenControls with
    noPlacebo := { external := 1 } }

theorem placebo_fails_closed : ¬ placeboControls.Closed := by
  simp [placeboControls, greenControls, ControlPack.Closed, HeadExact.Closed,
    FrozenS1.Closed, EndpointDefinition.Closed, Audit6D.Closed,
    ResidueLedger.Closed, BuildGate.Closed, NoPlacebo.Closed]

def blockingResidueControls : ControlPack :=
  { greenControls with
    residues := { blocking := 1 } }

theorem blockingResidue_fails_closed : ¬ blockingResidueControls.Closed := by
  simp [blockingResidueControls, greenControls, ControlPack.Closed,
    HeadExact.Closed, FrozenS1.Closed, EndpointDefinition.Closed,
    Audit6D.Closed, ResidueLedger.Closed, BuildGate.Closed, NoPlacebo.Closed]

def demoChain : ClosedChain True True True where
  constructMiddle := fun _ => True.intro
  compression := ⟨fun _ => True.intro⟩
  controls := greenControls
  controlsClosed := greenControls_closed

theorem demo_chain_closes : True → True :=
  demoChain.closes

def demoTarget : TargetCertificate True True True :=
  ⟨demoChain⟩

def demoInterior : ProblemEmbedding :=
  interiorEmbedding "DEMO"

def packedDemo : CoreClosedLocus :=
  demoInterior.register demoTarget

theorem packed_demo_identity :
    coreIdentity packedDemo = packedDemo := rfl

theorem packed_demo_endpoint :
    packedDemo.Start → packedDemo.Final :=
  packedDemo.endpoint

#check demoChain
#check packedDemo
#print axioms greenControls_closed
#print axioms badHead_fails_closed
#print axioms placebo_fails_closed
#print axioms blockingResidue_fails_closed
#print axioms demo_chain_closes
#print axioms packed_demo_identity
#print axioms packed_demo_endpoint

end MCore.V21.CertificateTests
