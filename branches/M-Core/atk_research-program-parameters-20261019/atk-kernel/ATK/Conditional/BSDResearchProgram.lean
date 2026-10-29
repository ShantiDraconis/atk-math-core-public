import ATK.Conditional.BSD

/-!
# Research-structure decomposition of `RankOpen` (O6)

This module adds **no new mathematical content**. It decomposes the rank-equality obligation,
for analytic rank `≥ 2`, into the two directions a real proof needs: the already-classical
"at least" direction and the genuinely open "at most" direction. Nothing here is inhabited.

* **Lower bound (case-by-case classical technique).** Exhibiting `rank(E) ≥ analyticRank(E)`
  independent points of infinite order — via Heegner points of higher conductor, explicit
  descent, or numerical construction — is a case-by-case classical technique, not a uniform
  theorem.
* **Upper bound (open).** The matching upper bound `rank(E) ≤ analyticRank(E)` is exactly what
  Kolyvagin's Euler-system method (1988–89) supplies *only* when `analyticRank(E) ≤ 1`
  (bounding the Selmer group / showing `Ш(E)[p^∞]` is finite for enough primes `p`). No
  analogous general method is known once the analytic rank reaches `2`: this is precisely where
  Gross–Zagier–Kolyvagin stops, and it is the open mathematics, not a gap in this formalization.
-/

namespace ATK.Conditional.BSD

universe u

/-- The two-direction shape of a real `RankOpen` producer, for one curve `E`. -/
structure BSDHigherRankProgram (M : BSDModel.{u}) (E : M.Curve) where
  /-- Classical direction: an explicit construction giving the lower bound. -/
  lowerBound : M.analyticRank E ≤ M.rank E
  /-- Open direction: the matching Selmer/Euler-system upper bound. -/
  upperBound : M.rank E ≤ M.analyticRank E

/-- The decomposition still supplies exactly the rank equality this curve needs. -/
theorem BSDHigherRankProgram.toEquality {M : BSDModel.{u}} {E : M.Curve}
    (P : BSDHigherRankProgram M E) : M.rank E = M.analyticRank E := by
  have h1 := P.lowerBound
  have h2 := P.upperBound
  omega

/-- A full producer, supplying the program for every curve of analytic rank `≥ 2`. -/
theorem rankOpen_of_researchPrograms {M : BSDModel.{u}}
    (P : ∀ E, 2 ≤ M.analyticRank E → BSDHigherRankProgram M E) : RankOpen M :=
  fun E hE => (P E hE).toEquality

end ATK.Conditional.BSD

#print axioms ATK.Conditional.BSD.BSDHigherRankProgram.toEquality
#print axioms ATK.Conditional.BSD.rankOpen_of_researchPrograms
