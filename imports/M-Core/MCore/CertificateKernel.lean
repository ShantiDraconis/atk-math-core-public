import Mathlib

namespace MCore

/-- Status carried by certificate-DAG nodes. Only `proved` may inhabit
`ProofCertificate`; computational/numerical evidence remains separate. -/
inductive NodeStatus where
  | proved
  | provedConditional
  | refuted
  | definitionInterface
  | numericalEvidence
  | openBridge
  deriving DecidableEq, Repr

structure CertNode where
  id : String
  statement : Prop
  deps : List String
  status : NodeStatus

/-- Construction requires both a proof of the exact node proposition and a
witness that its status is `proved`. -/
inductive ProofCertificate : CertNode → Type where
  | mk (n : CertNode) (hstatus : n.status = .proved)
      (proof : n.statement) : ProofCertificate n

/-- OPEN_BRIDGE cannot produce an unconditional proof certificate. -/
theorem no_open (n : CertNode) (hopen : n.status = .openBridge) :
    ¬ Nonempty (ProofCertificate n) := by
  rintro ⟨c⟩
  cases c with
  | mk hproved _ =>
      have : NodeStatus.openBridge = NodeStatus.proved := hopen.symm.trans hproved
      cases this

/-- Every non-PROVED status is un-certifiable. -/
theorem no_promotion (n : CertNode) (h : n.status ≠ .proved) :
    ¬ Nonempty (ProofCertificate n) := by
  rintro ⟨c⟩
  cases c with
  | mk hproved _ =>
      exact h hproved

/-- Policy datum for the later K15 environment audit. It is not itself an
axiom-audit theorem. -/
def allowedAxioms : List String :=
  ["propext", "Quot.sound", "Classical.choice"]

/-- A derivation consumes certificates for explicitly named node dependencies. -/
structure DerivedNode where
  node : CertNode
  dependencies : List CertNode
  derive : (∀ d, d ∈ dependencies → ProofCertificate d) → node.statement

/-- FRONTIER=[] is insufficient: certification additionally requires the
PROVED status witness and certificates for every declared dependency. -/
def certifyDerived (d : DerivedNode)
    (hstatus : d.node.status = .proved)
    (hdeps : ∀ dep, dep ∈ d.dependencies → ProofCertificate dep) :
    ProofCertificate d.node :=
  ProofCertificate.mk d.node hstatus (d.derive hdeps)

def kernelTrueNode : CertNode where
  id := "KERNEL_TRUE"
  statement := True
  deps := []
  status := .proved

example : ProofCertificate kernelTrueNode :=
  ProofCertificate.mk kernelTrueNode rfl True.intro

def kernelConditionalNode : CertNode :=
  { kernelTrueNode with id := "KERNEL_CONDITIONAL", status := .provedConditional }
def kernelRefutedNode : CertNode :=
  { kernelTrueNode with id := "KERNEL_REFUTED", status := .refuted }
def kernelDefinitionNode : CertNode :=
  { kernelTrueNode with id := "KERNEL_DEFINITION", status := .definitionInterface }
def kernelNumericalNode : CertNode :=
  { kernelTrueNode with id := "KERNEL_NUMERICAL", status := .numericalEvidence }
def kernelOpenNode : CertNode :=
  { kernelTrueNode with id := "KERNEL_OPEN", status := .openBridge }

example : ¬ Nonempty (ProofCertificate kernelConditionalNode) := by
  apply no_promotion
  decide
example : ¬ Nonempty (ProofCertificate kernelRefutedNode) := by
  apply no_promotion
  decide
example : ¬ Nonempty (ProofCertificate kernelDefinitionNode) := by
  apply no_promotion
  decide
example : ¬ Nonempty (ProofCertificate kernelNumericalNode) := by
  apply no_promotion
  decide
example : ¬ Nonempty (ProofCertificate kernelOpenNode) := by
  exact no_open kernelOpenNode rfl

end MCore
