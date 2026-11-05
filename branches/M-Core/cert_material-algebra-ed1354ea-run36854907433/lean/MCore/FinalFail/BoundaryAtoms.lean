import MCore.FinalFail.SevenLocalNuclei

namespace MCore.FinalFail

/-!
# Unconditional boundary atoms

Each active open problem receives a freely generated boundary atom.  These atoms
are unconditional formal objects of M-Core: they require no proof of the
corresponding external conjectural statement.

They are intentionally NOT identified definitionally with RH counterexamples,
Navier--Stokes stabilizers, Hodge cycles, SAT lower bounds, BSD identities,
Beal common-prime witnesses, or Yang--Mills realizations.  Such an
identification is a separate semantic interpretation and therefore cannot be
smuggled in by the datatype.
-/

/-- A freely generated formal inhabitant for each of the seven active boundary
slots.  This is the precise sense in which the boundary objects are now
unconditionally inhabited inside the formal hypothesis world. -/
inductive BoundaryAtom : ProblemId → Type
  | beal : BoundaryAtom .beal
  | navierStokes : BoundaryAtom .navierStokes
  | hodge : BoundaryAtom .hodge
  | pVsNP : BoundaryAtom .pVsNP
  | bsd : BoundaryAtom .bsd
  | riemann : BoundaryAtom .riemann
  | yangMills : BoundaryAtom .yangMills
  deriving Repr

/-- Every problem has a canonical boundary atom with no mathematical premise. -/
def boundaryAtom : (p : ProblemId) → BoundaryAtom p
  | .beal => .beal
  | .navierStokes => .navierStokes
  | .hodge => .hodge
  | .pVsNP => .pVsNP
  | .bsd => .bsd
  | .riemann => .riemann
  | .yangMills => .yangMills

theorem boundaryAtom_nonempty (p : ProblemId) :
    Nonempty (BoundaryAtom p) :=
  ⟨boundaryAtom p⟩

/-- Inventory of the seven unconditional formal inhabitants. -/
def unconditionalBoundaryInventory : List (Sigma BoundaryAtom) := [
  ⟨.riemann, .riemann⟩,
  ⟨.beal, .beal⟩,
  ⟨.navierStokes, .navierStokes⟩,
  ⟨.hodge, .hodge⟩,
  ⟨.pVsNP, .pVsNP⟩,
  ⟨.bsd, .bsd⟩,
  ⟨.yangMills, .yangMills⟩
]

def unconditionalFormalInhabitantCount : Nat :=
  unconditionalBoundaryInventory.length

theorem unconditionalFormalInhabitantCount_eq_seven :
    unconditionalFormalInhabitantCount = 7 := by
  decide

universe u

/-- Semantic interpretation is the explicit bridge from a free boundary atom to
a concrete target type.  Constructing this bridge is where the genuine
mathematical content must live. -/
structure BoundaryInterpretation
    (p : ProblemId) (Target : Sort u) where
  realize : BoundaryAtom p → Target

def realizeBoundary
    {p : ProblemId} {Target : Sort u}
    (I : BoundaryInterpretation p Target) : Target :=
  I.realize (boundaryAtom p)

theorem interpretedBoundary_nonempty
    {p : ProblemId} {Target : Sort u}
    (I : BoundaryInterpretation p Target) :
    Nonempty Target :=
  ⟨realizeBoundary I⟩


/-- Semantic firewall: because every BoundaryAtom is already inhabited, producing
an interpretation is exactly as strong (at the level of inhabitance) as
producing the classical target itself.  The formal atom therefore cannot make
the external mathematics easier by itself. -/
theorem nonempty_boundaryInterpretation_iff_nonempty_target
    {p : ProblemId} {Target : Sort u} :
    Nonempty (BoundaryInterpretation p Target) ↔ Nonempty Target := by
  constructor
  · rintro ⟨I⟩
    exact ⟨I.realize (boundaryAtom p)⟩
  · rintro ⟨t⟩
    exact ⟨{ realize := fun _ => t }⟩

end MCore.FinalFail
