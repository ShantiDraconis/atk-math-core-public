import MCore.BealSpecification

namespace MCore.BackwardAudit

structure CommonPrimeWitnessContract where
  witness : ∀ d : BealData, CommonPrime d.a d.b d.c

theorem witness_contract_closes_beal
    (W : CommonPrimeWitnessContract) : BealConjecture :=
  W.witness

def bealWithoutOracleClosed : Bool := false

theorem beal_without_oracle_still_open :
    bealWithoutOracleClosed = false := by rfl

#print axioms MCore.BackwardAudit.witness_contract_closes_beal
#print axioms MCore.BackwardAudit.beal_without_oracle_still_open

end MCore.BackwardAudit
