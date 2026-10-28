import MCore.Core
import Mathlib

namespace MCore

/-- Degree-one amplitude homogeneity on a real vector space. -/
def AmplitudeHomogeneous {U : Type*} [AddCommGroup U] [Module ℝ U]
    (I : U → ℝ) : Prop :=
  ∀ (A : ℝ) (u : U), I (A • u) = A * I u

/-- A1: one positive witness rules out every universal fixed upper gap on an
amplitude-unbounded class. This is the precise theorem behind the heuristic
`sup_A I(Au)=∞`; no extended-real supremum machinery is needed. -/
theorem amplitude_unbounded
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (I : U → ℝ) (hhom : AmplitudeHomogeneous I)
    {u : U} (hu : 0 < I u) :
    ∀ B : ℝ, ∃ A : ℝ, B < I (A • u) := by
  intro B
  let A : ℝ := (|B| + 1) / I u
  refine ⟨A, ?_⟩
  rw [hhom]
  dsimp [A]
  field_simp
  linarith [le_abs_self B]

/-- Corollary: no fixed `δ>0` can give `I ≤ 1-δ` for all amplitudes. -/
theorem no_fixed_delta_gap
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (I : U → ℝ) (hhom : AmplitudeHomogeneous I)
    {u : U} (hu : 0 < I u) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, I (A • u) ≤ 1 - δ := by
  rintro ⟨δ, hδ, hgap⟩
  obtain ⟨A, hA⟩ := amplitude_unbounded I hhom hu (1 - δ)
  exact (not_lt_of_ge (hgap A)) hA

end MCore
