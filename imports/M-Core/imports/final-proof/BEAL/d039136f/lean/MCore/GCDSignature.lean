import MCore.BealSpecification

namespace MCore

theorem commonPrime_to_commonDivisor {a b c : Nat} (h : CommonPrime a b c) :
    ∃ d : Nat, CommonDivisor d a b c := by
  rcases h with ⟨p, hp, hpa, hpb, hpc⟩
  exact ⟨p, hp.1, hpa, hpb, hpc⟩

/-- Exact implication needed by the endpoint: a common-prime witness supplies a nontrivial common divisor. -/
theorem beal_commonPrime_implies_commonDivisor (d : BealData)
    (h : CommonPrime d.a d.b d.c) : ∃ q : Nat, CommonDivisor q d.a d.b d.c :=
  commonPrime_to_commonDivisor h

end MCore
