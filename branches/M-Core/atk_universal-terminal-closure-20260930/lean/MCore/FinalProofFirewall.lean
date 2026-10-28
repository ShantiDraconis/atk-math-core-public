import MCore.FinalProofRegistry

namespace MCore.FinalProof

def FinalProofReady : Prop := provedCount = 7

theorem finalProof_not_ready : ¬ FinalProofReady := by
  simp [FinalProofReady, provedCount_eq_zero]

structure ExternalCertificateEligibility where
  allSevenProved : FinalProofReady

def FINAL_PROOF_DISPLAY : String := s!"{provedCount}/7"

#print axioms MCore.FinalProof.provedCount_eq_zero
#print axioms MCore.FinalProof.finalProof_not_ready

end MCore.FinalProof
