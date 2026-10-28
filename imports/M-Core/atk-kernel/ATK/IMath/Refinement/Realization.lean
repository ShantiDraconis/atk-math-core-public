import Mathlib.Data.Set.Basic

namespace IMath

universe u

/-- A realization is the set of values still compatible with current information. -/
abbrev Realization (α : Type u) := Set α

/--
A refines B when every realization compatible with A is also compatible
with B. Thus A carries at least as much information as B.
-/
def refines {α : Type u} (A B : Realization α) : Prop :=
  A ⊆ B

theorem refines_refl {α : Type u} (A : Realization α) :
    refines A A :=
  Set.Subset.rfl

theorem refines_trans {α : Type u} {A B C : Realization α}
    (hAB : refines A B) (hBC : refines B C) :
    refines A C :=
  Set.Subset.trans hAB hBC

theorem refines_antisymm {α : Type u} {A B : Realization α}
    (hAB : refines A B) (hBA : refines B A) :
    A = B :=
  Set.Subset.antisymm hAB hBA

end IMath
