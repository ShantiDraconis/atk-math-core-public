import MCore.V21.Control

namespace MCore.V21

inductive ResidueStage where
  | raw
  | reviewed
  | blocking
  deriving DecidableEq, Repr

structure Residue where
  id : String
  stage : ResidueStage
  detail : String

def IsBlocking (r : Residue) : Prop :=
  r.stage = .blocking

inductive CertificateDisposition where
  | targetCertificate
  | residueOpenBridge
  deriving DecidableEq, Repr

/-- Fail closed: only a complete proof of all eight controls can return
    targetCertificate. -/
def classify (c : ControlPack) [Decidable c.Closed] : CertificateDisposition :=
  if c.Closed then .targetCertificate else .residueOpenBridge

theorem classify_target_iff
    (c : ControlPack) [Decidable c.Closed] :
    classify c = .targetCertificate ↔ c.Closed := by
  unfold classify
  by_cases h : c.Closed
  · simp [h]
  · simp [h]

end MCore.V21
