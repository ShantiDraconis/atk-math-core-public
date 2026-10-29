import MCore.ResolutionPredicate

namespace MCore.ExactGap

def status : String :=
  "8/8 pinned including Poincare positive control; seven unsolved prize endpoints remain OPEN_MATH"

def sourceOfTruth : String :=
  "Canonical audit/ATK_HARD_CHAIN_INDEX.md + per-repository terminal producer indexes"

def openPrizeEndpoints : Nat := 7

theorem openPrizeEndpoints_eq_seven : openPrizeEndpoints = 7 := by decide

end MCore.ExactGap
