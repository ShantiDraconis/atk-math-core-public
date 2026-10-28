import MCore.V22.Operators

namespace MCore.V22

inductive FrontierKind where
  | algebraicityWitnessConstructor
  | rankWitnessConstructor
  | commonPrimeWitnessConstructor
  | materialOrientation
  | classicalSemanticAdapter
  | concreteTheoryAdapter
  | uniformizationBridge
  | noneClosedControl
  deriving DecidableEq, Repr

inductive IntegrationStatus where
  | candidateBranch
  | integrated
  deriving DecidableEq, Repr

inductive EvidenceScope where
  | mainVerified
  | candidateBranch
  | externalReference
  deriving DecidableEq, Repr

inductive VerificationState where
  | success
  | partialSuccess
  | failure
  | notRun
  deriving DecidableEq, Repr

/-- Provenance is intentionally split between the repository main line and a
    candidate branch. A GREEN candidate branch is not the state of main. -/
structure FrontierRecord where
  problem : ProblemId
  proofState : ProofState
  frontier : FrontierKind
  sourceRepo : String
  mainRevision : String
  candidateBranchName : String
  candidateRevision : String
  artifactPath : String
  evidenceScope : EvidenceScope
  verificationRun : String
  verification : VerificationState
  integration : IntegrationStatus
  deriving Repr

def FrontierRecord.MainCertified (r : FrontierRecord) : Prop :=
  r.evidenceScope = .mainVerified ∧
  r.verification = .success ∧
  r.integration = .integrated

theorem candidate_scope_not_main :
    EvidenceScope.candidateBranch ≠ EvidenceScope.mainVerified := by
  decide

theorem candidate_record_not_mainCertified
    (r : FrontierRecord)
    (hScope : r.evidenceScope = .candidateBranch) :
    ¬ r.MainCertified := by
  intro h
  rcases h with ⟨hMain, _, _⟩
  have hBad : EvidenceScope.candidateBranch = EvidenceScope.mainVerified := by
    rw [← hScope]
    exact hMain
  exact candidate_scope_not_main hBad

def primaryFrontiers : List FrontierRecord :=
  [
    { problem := .hodge
      proofState := .open
      frontier := .algebraicityWitnessConstructor
      sourceRepo := "ShantiDraconis/m-core-hodge"
      mainRevision := "28f5a92c10938c7487937e080950aeabc05bd6ff"
      candidateBranchName := "attack/witness-kernel-v1"
      candidateRevision := "860f329f20cb7393013981b8ef5074deb8ae2050"
      artifactPath := "lean/MCore/BackwardAudit/WitnessKernel.lean"
      evidenceScope := .candidateBranch
      verificationRun := "35434622519"
      verification := .success
      integration := .candidateBranch },
    { problem := .bsd
      proofState := .open
      frontier := .rankWitnessConstructor
      sourceRepo := "ShantiDraconis/m-core-bsd"
      mainRevision := "5d929a5f51e5f5699ca485c9e183b9acb0560b14"
      candidateBranchName := "attack/witness-kernel-v1"
      candidateRevision := "fd9401e7c05b5fcb2a84e6ea22418c596e55b650"
      artifactPath := "lean/MCore/BackwardAudit/WitnessKernel.lean"
      evidenceScope := .candidateBranch
      verificationRun := "35434624015"
      verification := .success
      integration := .candidateBranch },
    { problem := .beal
      proofState := .open
      frontier := .commonPrimeWitnessConstructor
      sourceRepo := "ShantiDraconis/m-core-beal"
      mainRevision := "063d9f213d05d6f9cc416d53066228552989d965"
      candidateBranchName := "attack/witness-kernel-v1"
      candidateRevision := "a8da5b8c89d00c6b2369c867d748d0d3855dc509"
      artifactPath := "lean/MCore/BackwardAudit/WitnessKernel.lean"
      evidenceScope := .candidateBranch
      verificationRun := "35434625441"
      verification := .success
      integration := .candidateBranch },
    { problem := .pVsNP
      proofState := .open
      frontier := .materialOrientation
      sourceRepo := "ShantiDraconis/m-core-p-vs-np"
      mainRevision := "3668d7ab9102310779222dbecb78d655a8009373"
      candidateBranchName := "attack/material-orientation-v1"
      candidateRevision := "f14c2e1854d6b62dc3e5b567a6769a04075f76d5"
      artifactPath := "lean/MCore/BackwardAudit/MaterialOrientationKernel.lean"
      evidenceScope := .candidateBranch
      verificationRun := "35434631321"
      verification := .success
      integration := .candidateBranch },
    { problem := .riemann
      proofState := .open
      frontier := .classicalSemanticAdapter
      sourceRepo := "ShantiDraconis/m-core-riemann"
      mainRevision := "28033534e714b442d9cc6383f43a12917ee5cf53"
      candidateBranchName := "attack/typed-final-endpoint-v1"
      candidateRevision := "7f482b6e19fc73dffe319fa1e0716a9b634b5211"
      artifactPath := "lean/MCore/BackwardAudit/FinalEndpoint.lean"
      evidenceScope := .candidateBranch
      verificationRun := "35434627621"
      verification := .success
      integration := .candidateBranch },
    { problem := .yangMills
      proofState := .open
      frontier := .concreteTheoryAdapter
      sourceRepo := "ShantiDraconis/m-core-yang-mills"
      mainRevision := "e9dba44f8a115981326f8a144f50cb7a064b1522"
      candidateBranchName := "attack/typed-final-endpoint-v1"
      candidateRevision := "bf51318ce56b9fcb3c67c692104a37ab98661666"
      artifactPath := "lean/MCore/BackwardAudit/FinalEndpoint.lean"
      evidenceScope := .candidateBranch
      verificationRun := "35434630249"
      verification := .success
      integration := .candidateBranch },
    { problem := .navierStokes
      proofState := .open
      frontier := .uniformizationBridge
      sourceRepo := "ShantiDraconis/navier-stokes-critical-barrier-audit"
      mainRevision := "a9875aa8c8264e2ee77979e1186f5f64479ed9e3"
      candidateBranchName := "attack/g1-uniformity-v1"
      candidateRevision := "7e4f8d1bd149132d7fd00f3e2de84ee2599dc9f8"
      artifactPath := "formal/millennium/lean/MillenniumAudit/G1Uniformity.lean"
      evidenceScope := .candidateBranch
      verificationRun := "G1=35436856529;AUDIT=35436856528;MULTIPROVER=35436856547"
      verification := .partialSuccess
      integration := .candidateBranch },
    { problem := .poincare
      proofState := .provedTrue
      frontier := .noneClosedControl
      sourceRepo := "classical-reference"
      mainRevision := "external-accepted-result"
      candidateBranchName := ""
      candidateRevision := ""
      artifactPath := ""
      evidenceScope := .externalReference
      verificationRun := ""
      verification := .notRun
      integration := .integrated }
  ]

theorem primary_frontier_count :
    primaryFrontiers.length = 8 := by rfl

end MCore.V22
