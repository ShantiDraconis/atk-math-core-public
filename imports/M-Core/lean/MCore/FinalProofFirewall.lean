import MCore.FinalProofRegistry

namespace MCore.FinalProof

def FinalProofReady : Prop := provedCount = 7

theorem finalProof_not_ready : ¬ FinalProofReady := by
  simp [FinalProofReady, provedCount_eq_zero]

structure ExternalCertificateEligibility where
  allSevenProved : FinalProofReady

def FINAL_PROOF_DISPLAY : String := s!"{provedCount}/7"
def OPEN_MATH_DISPLAY : String := s!"{openMathCount}/7"

/-- Administrative consistency: all seven current slots are still material
OPEN_MATH, hence no final external certificate is eligible. -/
theorem final_registry_fail_closed :
    openMathCount = 7 ∧ provedCount = 0 := by
  exact ⟨openMathCount_eq_seven, provedCount_eq_zero⟩

#print axioms MCore.FinalProof.registry_length_eq_seven
#print axioms MCore.FinalProof.provedCount_eq_zero
#print axioms MCore.FinalProof.openMathCount_eq_seven
#print axioms MCore.FinalProof.finalProof_not_ready
#print axioms MCore.FinalProof.final_registry_fail_closed
#print axioms MCore.FinalFail.Universal.terminalInhabitants_iff_allSeven
#print axioms MCore.FinalFail.Universal.universal_aggregation_is_fail_closed

end MCore.FinalProof
