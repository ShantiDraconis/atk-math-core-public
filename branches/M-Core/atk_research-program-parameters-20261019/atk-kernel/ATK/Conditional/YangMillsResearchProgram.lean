import ATK.Conditional.YangMills

/-!
# Research-structure decomposition of `ConstructiveYM4D` (O8)

This module adds **no new mathematical content**. It decomposes the single existential in
`ConstructiveYM4D M` (`∃ μ, OSAxioms G μ ∧ ∃ m > 0, ClusterRate μ m`) into the two named steps a
real constructive-QFT research program actually has, following the Osterwalder–Seiler /
Osterwalder–Schrader lattice program, and proves the decomposition still implies the original
obligation. Nothing here is inhabited.

* **Step 1 — the regulated (lattice) construction.** For *any* compact group `G` and *any* fixed
  cutoff `a` and volume `L`, Osterwalder & Seiler ("Gauge Theories as a Problem of Constructive
  Quantum Field Theory and Statistical Mechanics", 1978) construct a reflection-positive
  Euclidean measure from the Haar measure on `G` via the Wilson plaquette action, with a strictly
  positive transfer-matrix gap at each fixed `(a, L)`. This step is classical.
* **Step 2 — the continuum limit.** A measure (and a cluster rate) that survives `a → 0`,
  `L → ∞` with the rate staying bounded *away from* `0`. This is the genuinely open step, and it
  is exactly the Clay problem, not a technicality: `m-core-yang-mills`'s own exactly solvable
  abelian toy model (`ATK.YMToy.massa_tende_zero`, ported from that repository's
  `A1/PositiveControl.lean`) proves that its lattice gap `m(β) → 0` as the weak-coupling/continuum
  limit is taken — pointwise control at every fixed lattice does not, by itself, give a surviving
  continuum gap. Nothing in Step 1 forces Step 2.
-/

namespace ATK.Conditional.YangMills

universe u v w

/-- The two-step shape of a real `ConstructiveYM4D` producer, for one fixed compact group `G`. -/
structure YM4DResearchProgram (M : YMModel.{u, v, w}) (G : M.Group) where
  /-- Step 1 (classical): the regulated measure at every cutoff `a` and volume `L`. -/
  regulated : ℝ → ℕ → M.Euclidean
  /-- Step 1 (classical): it satisfies the OS axioms at every `(a, L)`. -/
  regulated_OS : ∀ a L, M.OSAxioms G (regulated a L)
  /-- Step 1 (classical): its lattice-level cluster rate, positive at every fixed `(a, L)`. -/
  latticeRate : ℝ → ℕ → ℝ
  latticeRate_pos : ∀ a L, 0 < latticeRate a L
  latticeRate_holds : ∀ a L, M.ClusterRate (regulated a L) (latticeRate a L)
  /-- Step 2 (open): a continuum-limit measure, still satisfying the OS axioms. -/
  continuum : M.Euclidean
  continuum_OS : M.OSAxioms G continuum
  /-- Step 2 (open): its cluster rate, strictly positive — the actual mass gap. -/
  continuumRate : ℝ
  continuumRate_pos : 0 < continuumRate
  continuumRate_holds : M.ClusterRate continuum continuumRate

/-- The decomposition still supplies exactly `ConstructiveYM4D`'s witness for this `G`. -/
theorem YM4DResearchProgram.toWitness {M : YMModel.{u, v, w}} {G : M.Group}
    (P : YM4DResearchProgram M G) :
    ∃ μ, M.OSAxioms G μ ∧ ∃ m : ℝ, 0 < m ∧ M.ClusterRate μ m :=
  ⟨P.continuum, P.continuum_OS, P.continuumRate, P.continuumRate_pos, P.continuumRate_holds⟩

/-- A full producer, supplying Step 2 for every compact simple group. -/
theorem constructiveYM4D_of_researchPrograms {M : YMModel.{u, v, w}}
    (P : ∀ G, M.CompactSimple G → YM4DResearchProgram M G) : ConstructiveYM4D M :=
  fun G hG => (P G hG).toWitness

end ATK.Conditional.YangMills

#print axioms ATK.Conditional.YangMills.YM4DResearchProgram.toWitness
#print axioms ATK.Conditional.YangMills.constructiveYM4D_of_researchPrograms
