import Mathlib

namespace MCore.MaterialMath

/-- Three primitive states of the ATK tri-state phase object. -/
inductive Phase3 where
  | seed
  | passage
  | manifest
  deriving DecidableEq, Repr

namespace Phase3

/-- The fundamental 120-degree phase advance, represented combinatorially. -/
def rotate : Phase3 → Phase3
  | .seed => .passage
  | .passage => .manifest
  | .manifest => .seed

/-- Two phase advances. -/
def rotate2 (p : Phase3) : Phase3 := rotate (rotate p)

/-- Three phase advances return to the initial state. -/
theorem rotate_three (p : Phase3) :
    rotate (rotate (rotate p)) = p := by
  cases p <;> rfl

/-- A single phase advance has no fixed point. -/
theorem rotate_ne_self (p : Phase3) :
    rotate p ≠ p := by
  cases p <;> decide

/-- Two phase advances also have no fixed point. -/
theorem rotate2_ne_self (p : Phase3) :
    rotate2 p ≠ p := by
  cases p <;> decide

/-- Rotation is injective. -/
theorem rotate_injective : Function.Injective rotate := by
  intro p q h
  cases p <;> cases q <;> simp [rotate] at h ⊢

/-- Rotation is surjective. -/
theorem rotate_surjective : Function.Surjective rotate := by
  intro p
  cases p with
  | seed => exact ⟨.manifest, rfl⟩
  | passage => exact ⟨.seed, rfl⟩
  | manifest => exact ⟨.passage, rfl⟩

/-- Rotation is a bijection. -/
theorem rotate_bijective : Function.Bijective rotate :=
  ⟨rotate_injective, rotate_surjective⟩

/-- Undirected adjacency on the 3-cycle. -/
def Adjacent (p q : Phase3) : Prop :=
  q = rotate p ∨ p = rotate q

theorem adjacent_symmetric {p q : Phase3} :
    Adjacent p q → Adjacent q p := by
  intro h
  rcases h with h | h
  · right
    exact h
  · left
    exact h

theorem not_adjacent_self (p : Phase3) :
    ¬ Adjacent p p := by
  intro h
  rcases h with h | h
  · exact rotate_ne_self p h.symm
  · exact rotate_ne_self p h.symm

/-- On the 3-cycle every distinct state is adjacent. -/
theorem adjacent_of_ne {p q : Phase3} (h : p ≠ q) :
    Adjacent p q := by
  cases p <;> cases q <;> simp_all [Adjacent, rotate]

/-- A finite cyclic distance: zero on the diagonal, one otherwise. -/
def cyclicDistance (p q : Phase3) : Nat :=
  if p = q then 0 else 1

theorem cyclicDistance_self (p : Phase3) :
    cyclicDistance p p = 0 := by
  simp [cyclicDistance]

theorem cyclicDistance_eq_one {p q : Phase3} (h : p ≠ q) :
    cyclicDistance p q = 1 := by
  simp [cyclicDistance, h]

theorem cyclicDistance_symmetric (p q : Phase3) :
    cyclicDistance p q = cyclicDistance q p := by
  by_cases h : p = q
  · subst q
    simp [cyclicDistance]
  · have h' : q ≠ p := by
      intro hp
      exact h hp.symm
    simp [cyclicDistance, h, h']

end Phase3

end MCore.MaterialMath
