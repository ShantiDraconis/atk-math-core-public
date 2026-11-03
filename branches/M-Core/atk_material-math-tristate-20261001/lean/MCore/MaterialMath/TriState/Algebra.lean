import MCore.MaterialMath.TriState.Core

namespace MCore.MaterialMath

open Phase3

/-- A tri-number over a coefficient type α is a value carried by each phase. -/
abbrev TriNumber (α : Type*) := Phase3 → α

namespace TriNumber

/-- Rotate the phase coordinates of a tri-number. -/
def rotate {α : Type*} (x : TriNumber α) : TriNumber α :=
  fun p => x (Phase3.rotate p)

/-- Two phase rotations. -/
def rotate2 {α : Type*} (x : TriNumber α) : TriNumber α :=
  rotate (rotate x)

/-- Three rotations are identity. -/
theorem rotate_three {α : Type*} (x : TriNumber α) :
    rotate (rotate (rotate x)) = x := by
  funext p
  cases p <;> rfl

/-- Coordinate sum. -/
def phaseSum {α : Type*} [Add α] (x : TriNumber α) : α :=
  x .seed + x .passage + x .manifest

theorem phaseSum_rotate
    {α : Type*} [AddCommMonoid α]
    (x : TriNumber α) :
    phaseSum (rotate x) = phaseSum x := by
  simp [phaseSum, rotate, Phase3.rotate, add_assoc, add_comm, add_left_comm]

/-- Quadratic phase energy. -/
def quadraticEnergy
    {α : Type*} [CommRing α]
    (x : TriNumber α) : α :=
  x .seed ^ 2 + x .passage ^ 2 + x .manifest ^ 2

theorem quadraticEnergy_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    quadraticEnergy (rotate x) = quadraticEnergy x := by
  simp [quadraticEnergy, rotate, Phase3.rotate, add_assoc, add_comm, add_left_comm]

/-- Cubic three-phase interaction invariant. -/
def cubicInteraction
    {α : Type*} [CommRing α]
    (x : TriNumber α) : α :=
  x .seed * x .passage * x .manifest

theorem cubicInteraction_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    cubicInteraction (rotate x) = cubicInteraction x := by
  simp [cubicInteraction, rotate, Phase3.rotate, mul_assoc, mul_comm, mul_left_comm]

/-- Discrete 3-cycle Laplacian. -/
def laplacian
    {α : Type*} [CommRing α]
    (x : TriNumber α) : TriNumber α :=
  fun p =>
    x (Phase3.rotate p) +
    x (Phase3.rotate2 p) -
    (2 : α) * x p

/-- The discrete Laplacian has zero total phase sum. -/
theorem phaseSum_laplacian_zero
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    phaseSum (laplacian x) = 0 := by
  simp [phaseSum, laplacian, Phase3.rotate, Phase3.rotate2]
  ring

/-- The Laplacian commutes with cyclic rotation. -/
theorem laplacian_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    laplacian (rotate x) = rotate (laplacian x) := by
  funext p
  cases p <;> simp [laplacian, rotate, Phase3.rotate, Phase3.rotate2]

/-- A balanced tri-number has vanishing total phase sum. -/
def Balanced
    {α : Type*} [AddMonoid α]
    (x : TriNumber α) : Prop :=
  phaseSum x = 0

theorem balanced_rotate
    {α : Type*} [AddCommMonoid α]
    {x : TriNumber α}
    (h : Balanced x) :
    Balanced (rotate x) := by
  simpa [Balanced, phaseSum_rotate] using h

/-- A coherent tri-number has all three phase values equal. -/
def Coherent {α : Type*} (x : TriNumber α) : Prop :=
  x .seed = x .passage ∧ x .passage = x .manifest

theorem coherent_rotate
    {α : Type*}
    {x : TriNumber α}
    (h : Coherent x) :
    Coherent (rotate x) := by
  rcases h with ⟨h₁, h₂⟩
  constructor
  · simpa [rotate, Phase3.rotate] using h₂
  · simp [rotate, Phase3.rotate, h₁, h₂]

/-- A nondegenerate tri-number has pairwise-distinct phase values. -/
def Nondegenerate {α : Type*} (x : TriNumber α) : Prop :=
  x .seed ≠ x .passage ∧
  x .passage ≠ x .manifest ∧
  x .manifest ≠ x .seed

theorem nondegenerate_rotate
    {α : Type*}
    {x : TriNumber α}
    (h : Nondegenerate x) :
    Nondegenerate (rotate x) := by
  rcases h with ⟨hSP, hPM, hMS⟩
  exact ⟨
    by simpa [rotate, Phase3.rotate] using hPM,
    by simpa [rotate, Phase3.rotate] using hMS,
    by simpa [rotate, Phase3.rotate] using hSP
  ⟩

/-- Formal tri-stable constant.

This is intentionally NOT definitionally identified with 0/0.
It is a primitive three-state algebraic datum.
-/
def I3 : TriNumber Int
  | .seed => 1
  | .passage => 0
  | .manifest => -1

theorem I3_balanced : Balanced I3 := by
  norm_num [Balanced, phaseSum, I3]

theorem I3_nondegenerate : Nondegenerate I3 := by
  norm_num [Nondegenerate, I3]

theorem I3_rotation_period_three :
    rotate (rotate (rotate I3)) = I3 :=
  rotate_three I3

end TriNumber

end MCore.MaterialMath
