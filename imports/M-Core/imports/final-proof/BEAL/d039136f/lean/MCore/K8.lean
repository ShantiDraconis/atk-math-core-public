import MCore.K7

namespace MCore

/-- Exact negation of the Beal endpoint for one admissible datum. -/
def NoCommonPrime (d : BealData) : Prop :=
  ¬ CommonPrime d.a d.b d.c

/-- A datum satisfying `NoCommonPrime` is precisely a counterexample candidate. -/
theorem noCommonPrime_is_counterexample (d : BealData) :
    NoCommonPrime d ↔ BealCounterexample d := by
  rfl

/-- A Beal proof constructively excludes every counterexample. -/
theorem beal_excludes_all_counterexamples (h : BealConjecture) :
    ∀ d : BealData, ¬ BealCounterexample d := by
  intro d hd
  exact hd (h d)

/-- A single no-common-prime datum constructively refutes Beal. -/
theorem noCommonPrime_refutes_beal (d : BealData) (h : NoCommonPrime d) :
    ¬ BealConjecture := by
  intro hBeal
  exact h (hBeal d)

/-- Exact constructive closing obligation: provide the common-prime witness for every admissible datum. -/
theorem closeBeal_from_commonPrime_witnesses
    (h : ∀ d : BealData, CommonPrime d.a d.b d.c) : BealConjecture :=
  h

end MCore
