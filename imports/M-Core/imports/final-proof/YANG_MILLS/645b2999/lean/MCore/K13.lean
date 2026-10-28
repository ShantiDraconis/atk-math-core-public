import MCore.K12

namespace MCore

/-- Typed physical-state/Hamiltonian interface. K13 does not assert existence. -/
structure K13PhysicalInterface where
  State : Type
  Hamiltonian : State → State
  vacuum : State

/-- The Hilbert-space obligation is identified but not discharged. -/
theorem k13_hilbert_scope : k8_target.hilbert = .physicalHilbertSpace := rfl

/-- A Hamiltonian interface alone proves no positive spectral gap. -/
theorem k13_gap_still_separate : k8_target.gap = .positiveMassGap := k12_gap_still_separate

theorem k13_target_still_open : k6_dependency.target.status = .openBridge := k12_target_still_open

theorem k13_no_promotion : ¬ Nonempty (ProofCertificate k6_dependency.target) := k12_no_promotion

end MCore
