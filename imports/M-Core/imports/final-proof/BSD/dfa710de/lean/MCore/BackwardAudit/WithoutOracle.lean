import MCore.K13

namespace MCore.BackwardAudit

structure RankPartWitnessContract where
  witness : ∀ d : BSDArithmeticAnalyticData, BSDRankPart d

theorem rank_witness_contract_closes
    (W : RankPartWitnessContract) :
    ∀ d : BSDArithmeticAnalyticData, BSDOpenCore d :=
  fun d => W.witness d

def bsdRankPartWithoutOracleClosed : Bool := false

theorem bsd_rank_part_without_oracle_still_open :
    bsdRankPartWithoutOracleClosed = false := by rfl

#print axioms MCore.BackwardAudit.rank_witness_contract_closes
#print axioms MCore.BackwardAudit.bsd_rank_part_without_oracle_still_open

end MCore.BackwardAudit
