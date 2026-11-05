import MCore.FinalFail.ClosedCenterHard

namespace MCore.FinalFail

/-- A resolved center stores admissible branches and one distinguished identity branch.
The identity branch is not required to be the only admissible branch. -/
structure ResolvedCenter where
  Branch : Type
  identity : Branch
  admissible : Branch → Prop
  identity_admissible : admissible identity

/-- The center is determined when every two admissible branches coincide. -/
def CenterDetermined (R : ResolvedCenter) : Prop :=
  ∀ a b : R.Branch, R.admissible a → R.admissible b → a = b

/-- Fundamental indeterminacy is structural branching, not a numeric value for 0/0. -/
def FundamentalIndeterminacy (R : ResolvedCenter) : Prop :=
  ∃ a b : R.Branch, R.admissible a ∧ R.admissible b ∧ a ≠ b

/-- Alias used by the brain layer: I_fail is a structural invariant. -/
def IFail (R : ResolvedCenter) : Prop :=
  FundamentalIndeterminacy R

theorem fundamental_indeterminacy_not_determined
    {R : ResolvedCenter}
    (h : FundamentalIndeterminacy R) :
    ¬ CenterDetermined R := by
  intro hdet
  rcases h with ⟨a, b, ha, hb, hab⟩
  exact hab (hdet a b ha hb)

theorem determined_not_fundamentally_indeterminate
    {R : ResolvedCenter}
    (h : CenterDetermined R) :
    ¬ FundamentalIndeterminacy R := by
  intro hfail
  exact fundamental_indeterminacy_not_determined hfail h

/-- Coordinate change between branch spaces, with explicit inverse and
admissibility preservation. This avoids treating a coordinate choice as
mathematical content. -/
structure CenterCoordinateEquiv (A B : ResolvedCenter) where
  toFun : A.Branch → B.Branch
  invFun : B.Branch → A.Branch
  leftInv : ∀ a : A.Branch, invFun (toFun a) = a
  rightInv : ∀ b : B.Branch, toFun (invFun b) = b
  admissible_iff :
    ∀ a : A.Branch, A.admissible a ↔ B.admissible (toFun a)

theorem fundamental_indeterminacy_forward_invariant
    {A B : ResolvedCenter}
    (E : CenterCoordinateEquiv A B)
    (hA : FundamentalIndeterminacy A) :
    FundamentalIndeterminacy B := by
  rcases hA with ⟨a, b, ha, hb, hab⟩
  refine ⟨E.toFun a, E.toFun b, ?_, ?_, ?_⟩
  · exact (E.admissible_iff a).mp ha
  · exact (E.admissible_iff b).mp hb
  · intro hEq
    apply hab
    calc
      a = E.invFun (E.toFun a) := (E.leftInv a).symm
      _ = E.invFun (E.toFun b) := by rw [hEq]
      _ = b := E.leftInv b

/-- Three distinguished semantic reference directions, explicitly non-exhaustive. -/
inductive ReferenceDirection where
  | extinction
  | identity
  | escape
  | other
  deriving DecidableEq, Repr

theorem reference_triad_is_not_exhaustive :
    ∃ d : ReferenceDirection,
      d ≠ .extinction ∧ d ≠ .identity ∧ d ≠ .escape := by
  exact ⟨.other, by decide, by decide, by decide⟩

#print axioms MCore.FinalFail.fundamental_indeterminacy_not_determined
#print axioms MCore.FinalFail.fundamental_indeterminacy_forward_invariant
#print axioms MCore.FinalFail.reference_triad_is_not_exhaustive

end MCore.FinalFail
