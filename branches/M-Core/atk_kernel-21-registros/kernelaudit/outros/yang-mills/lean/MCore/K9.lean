import MCore.K8
import MCore.K9.Classical

namespace MCore

/-- K9 records that a classical layer has been typed. This certificate concerns
    only the structural interface, not existence of a 4D quantum Yang--Mills
    theory and not the Clay mass-gap conclusion. -/
structure K9ClassicalInterface where
  data : K9.ClassicalGaugeData

/-- The K8 classical obligation is the obligation refined by K9. -/
theorem k9_refines_classical_label :
    k8_target.classical = .classicalGaugeTheory :=
  k8_classical_label

/-- Quantum construction remains outside the K9 classical layer. -/
theorem k9_quantum_still_labelled_open :
    k8_target.quantum = .quantumConstruction :=
  k8_quantum_label

/-- The actual certified target remains OPEN_BRIDGE. -/
theorem k9_target_still_open :
    k6_dependency.target.status = .openBridge :=
  k8_target_still_open

/-- No classical interface may promote the open Yang--Mills target. -/
theorem k9_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k8_no_promotion

end MCore
