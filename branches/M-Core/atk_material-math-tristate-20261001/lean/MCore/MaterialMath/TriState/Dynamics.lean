import MCore.MaterialMath.TriState.Algebra

namespace MCore.MaterialMath

open Phase3
open TriNumber

namespace TriDynamics

/-- Harmonic tri-numbers are annihilated by the discrete 3-cycle Laplacian. -/
def Harmonic
    {α : Type*} [CommRing α]
    (x : TriNumber α) : Prop :=
  laplacian x = 0

/-- Every coherent tri-number is harmonic. -/
theorem coherent_implies_harmonic
    {α : Type*} [CommRing α]
    {x : TriNumber α}
    (h : TriNumber.Coherent x) :
    Harmonic x := by
  rcases h with ⟨hSP, hPM⟩
  funext p
  cases p <;> simp [Harmonic, laplacian, Phase3.rotate, Phase3.rotate2, hSP, hPM]
  <;> ring

/-- Over an ordered field, the only harmonic tri-numbers are coherent.
Thus the kernel of the cyclic Laplacian is exactly the diagonal subspace. -/
theorem harmonic_implies_coherent
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {x : TriNumber α}
    (h : Harmonic x) :
    TriNumber.Coherent x := by
  have hs := congrFun h Phase3.seed
  have hp := congrFun h Phase3.passage
  simp [Harmonic, laplacian, Phase3.rotate, Phase3.rotate2] at hs hp
  constructor <;> linarith

theorem harmonic_iff_coherent
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {x : TriNumber α} :
    Harmonic x ↔ TriNumber.Coherent x := by
  constructor
  · exact harmonic_implies_coherent
  · exact coherent_implies_harmonic

/-- The Laplacian defect itself is always balanced. -/
theorem laplacian_is_balanced
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    TriNumber.Balanced (TriNumber.laplacian x) := by
  exact phaseSum_laplacian_zero x

/-- A scalar observable is rotation-conserved when one phase advance leaves it unchanged. -/
def RotationConserved
    {α β : Type*}
    (F : TriNumber α → β) : Prop :=
  ∀ x, F (TriNumber.rotate x) = F x

theorem phaseSum_conserved
    {α : Type*} [AddCommMonoid α] :
    RotationConserved (@phaseSum α _) :=
  phaseSum_rotate

theorem quadraticEnergy_conserved
    {α : Type*} [CommRing α] :
    RotationConserved (@quadraticEnergy α _) :=
  quadraticEnergy_rotate

theorem cubicInteraction_conserved
    {α : Type*} [CommRing α] :
    RotationConserved (@cubicInteraction α _) :=
  cubicInteraction_rotate

/-- Rotation orbit of a tri-number, written explicitly to avoid quotient machinery. -/
def orbit3 {α : Type*} (x : TriNumber α) :
    TriNumber α × TriNumber α × TriNumber α :=
  (x, TriNumber.rotate x, TriNumber.rotate2 x)

/-- The orbit closes after exactly three applications at the operator level. -/
theorem orbit_closure
    {α : Type*} (x : TriNumber α) :
    TriNumber.rotate (TriNumber.rotate2 x) = x := by
  simpa [TriNumber.rotate2] using TriNumber.rotate_three x

/-- The formal I3 state is harmonic only if its three values collapse,
which they do not. -/
theorem I3_not_harmonic :
    ¬ Harmonic I3 := by
  intro h
  have hs := congrFun h Phase3.seed
  norm_num [Harmonic, laplacian, I3, Phase3.rotate, Phase3.rotate2] at hs

/-- Rotation preserves the distinction of the three I3 phase values. -/
theorem I3_orbit_nondegenerate :
    TriNumber.Nondegenerate I3 ∧
    TriNumber.Nondegenerate (TriNumber.rotate I3) ∧
    TriNumber.Nondegenerate (TriNumber.rotate2 I3) := by
  exact ⟨
    I3_nondegenerate,
    nondegenerate_rotate I3_nondegenerate,
    nondegenerate_rotate (nondegenerate_rotate I3_nondegenerate)
  ⟩

end TriDynamics

end MCore.MaterialMath
