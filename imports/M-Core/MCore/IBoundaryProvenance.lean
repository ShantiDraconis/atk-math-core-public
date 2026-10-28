import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Real

/-!
# I-Boundary Provenance

A no-axiom/no-sorry kernel for the boundary ideas:
* singularity forms remain distinct;
* boundary equivalence is not equality;
* positive and negative approaches retain orientation;
* both approaches converge to the same boundary;
* terminal projection loses provenance, giving an explicit non-zero residue.

This file does NOT redefine ordinary real division.  In particular, `0/0`
and `1/0` remain outside ordinary field division semantics.  The constructors
below are tagged boundary states.
-/

namespace MCore.IBoundary

inductive SingularityKind where
  | zeroOverZero
  | oneOverZero
  | zeroOverInfinity
  | oneOverInfinity
  deriving DecidableEq, Repr

inductive Orientation where
  | negative
  | balanced
  | positive
  deriving DecidableEq, Repr

/-- A boundary number keeps its real projection and the provenance that a
plain terminal real value would erase. -/
structure INumber where
  realPart : ℝ
  infinitesimalPart : ℝ
  kind : SingularityKind
  orientation : Orientation
  deriving DecidableEq, Repr

/-- Terminal observable projection. -/
def terminalProjection (x : INumber) : ℝ := x.realPart

/-- Two states are boundary-equivalent when their terminal real projections
coincide. This deliberately does not identify the states themselves. -/
def BoundaryEquivalent (x y : INumber) : Prop :=
  terminalProjection x = terminalProjection y

instance : Setoid INumber where
  r := BoundaryEquivalent
  iseqv := by
    constructor
    · intro x; rfl
    · intro x y h; exact h.symm
    · intro x y z hxy hyz; exact hxy.trans hyz

def I00 : INumber :=
  ⟨0, 0, .zeroOverZero, .balanced⟩

def I10 : INumber :=
  ⟨0, 0, .oneOverZero, .balanced⟩

def I0Inf : INumber :=
  ⟨0, 0, .zeroOverInfinity, .balanced⟩

def I1Inf : INumber :=
  ⟨0, 0, .oneOverInfinity, .balanced⟩

theorem singularity_kinds_pairwise_distinct :
    SingularityKind.zeroOverZero ≠ SingularityKind.oneOverZero ∧
    SingularityKind.zeroOverZero ≠ SingularityKind.zeroOverInfinity ∧
    SingularityKind.zeroOverZero ≠ SingularityKind.oneOverInfinity ∧
    SingularityKind.oneOverZero ≠ SingularityKind.zeroOverInfinity ∧
    SingularityKind.oneOverZero ≠ SingularityKind.oneOverInfinity ∧
    SingularityKind.zeroOverInfinity ≠ SingularityKind.oneOverInfinity := by
  decide

theorem canonical_states_pairwise_distinct :
    I00 ≠ I10 ∧ I00 ≠ I0Inf ∧ I00 ≠ I1Inf ∧
    I10 ≠ I0Inf ∧ I10 ≠ I1Inf ∧ I0Inf ≠ I1Inf := by
  decide

theorem canonical_states_boundary_equivalent :
    BoundaryEquivalent I00 I10 ∧
    BoundaryEquivalent I00 I0Inf ∧
    BoundaryEquivalent I00 I1Inf := by
  exact ⟨rfl, rfl, rfl⟩

/-- Negative approach to the zero/zero boundary. -/
def approachNeg (ε : ℝ) : INumber :=
  ⟨-ε, ε, .zeroOverZero, .negative⟩

/-- Positive approach to the same zero/zero boundary. -/
def approachPos (ε : ℝ) : INumber :=
  ⟨ε, ε, .zeroOverZero, .positive⟩

theorem approach_orientation_distinct (ε : ℝ) :
    (approachNeg ε).orientation ≠ (approachPos ε).orientation := by
  decide

theorem approach_states_distinct (ε : ℝ) :
    approachNeg ε ≠ approachPos ε := by
  intro h
  have ho := congrArg INumber.orientation h
  exact approach_orientation_distinct ε ho

theorem negative_terminal_limit :
    Tendsto (fun ε : ℝ => terminalProjection (approachNeg ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa [terminalProjection, approachNeg] using
    (tendsto_neg_atTop_iff.comp tendsto_id)

theorem positive_terminal_limit :
    Tendsto (fun ε : ℝ => terminalProjection (approachPos ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa [terminalProjection, approachPos] using
    (tendsto_id : Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))

/-- A simpler epsilon formulation of the two-sided convergence, independent
of topology-library lemma naming. -/
theorem two_sided_terminal_distance (ε : ℝ) (hε : 0 ≤ ε) :
    |terminalProjection (approachNeg ε) - terminalProjection (approachPos ε)| =
      2 * ε := by
  simp [terminalProjection, approachNeg, approachPos, abs_of_nonneg hε]

/-- Provenance code: different singularity natures receive different exact
codes.  This is a concrete information channel, not an axiom. -/
def kindCode : SingularityKind → ℤ
  | .zeroOverZero => 0
  | .oneOverZero => 1
  | .zeroOverInfinity => 2
  | .oneOverInfinity => 3

def orientationCode : Orientation → ℤ
  | .negative => -1
  | .balanced => 0
  | .positive => 1

/-- Information retained by the full state but erased by terminalProjection. -/
def provenanceCode (x : INumber) : ℤ × ℤ :=
  (kindCode x.kind, orientationCode x.orientation)

theorem same_terminal_different_nature :
    terminalProjection I00 = terminalProjection I10 ∧
    provenanceCode I00 ≠ provenanceCode I10 := by
  constructor
  · rfl
  · decide

theorem same_boundary_different_orientation (ε : ℝ) :
    provenanceCode (approachNeg ε) ≠ provenanceCode (approachPos ε) := by
  decide

/-- Terminal collapse forgets all provenance. -/
def collapse (x : INumber) : INumber :=
  ⟨x.realPart, 0, .zeroOverZero, .balanced⟩

theorem collapse_preserves_terminal (x : INumber) :
    terminalProjection (collapse x) = terminalProjection x := by
  rfl

/-- Residue is exact provenance loss. -/
def ProvenanceResidue (x : INumber) : Prop :=
  provenanceCode x ≠ provenanceCode (collapse x)

theorem negative_approach_has_residue (ε : ℝ) :
    ProvenanceResidue (approachNeg ε) := by
  decide

theorem positive_approach_has_residue (ε : ℝ) :
    ProvenanceResidue (approachPos ε) := by
  decide

/-- A binary terminal representation cannot reconstruct every full I-state:
I00 and I10 have the same terminal observation but are distinct states. -/
theorem terminal_projection_not_injective :
    ¬ Function.Injective terminalProjection := by
  intro h
  have hs : I00 = I10 := h rfl
  exact canonical_states_pairwise_distinct.1 hs

/-- Exact boundary information-loss theorem used by the future BSD composition.
It says only that this architecture's terminal real projection is incomplete;
it makes no claim that BSD itself is true or false. -/
theorem StructuralBoundaryInformationLoss :
    (∃ x y : INumber,
      x ≠ y ∧
      BoundaryEquivalent x y ∧
      provenanceCode x ≠ provenanceCode y) ∧
    ¬ Function.Injective terminalProjection := by
  constructor
  · refine ⟨I00, I10, ?_, ?_, ?_⟩
    · exact canonical_states_pairwise_distinct.1
    · rfl
    · exact same_terminal_different_nature.2
  · exact terminal_projection_not_injective

end MCore.IBoundary
