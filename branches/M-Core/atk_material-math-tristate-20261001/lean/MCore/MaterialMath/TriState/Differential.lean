import MCore.MaterialMath.TriState.Algebra

namespace MCore.MaterialMath

open Phase3
open TriNumber

namespace TriDifferential

/-- Forward discrete derivative along the cyclic orientation. -/
def forward
    {α : Type*} [AddGroup α]
    (x : TriNumber α) : TriNumber α :=
  fun p => x (Phase3.rotate p) - x p

/-- Backward discrete derivative along the cyclic orientation. -/
def backward
    {α : Type*} [AddGroup α]
    (x : TriNumber α) : TriNumber α :=
  fun p => x (Phase3.rotate2 p) - x p

/-- The graph Laplacian is the sum of forward and backward derivatives. -/
theorem laplacian_eq_forward_add_backward
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    laplacian x =
      fun p => forward x p + backward x p := by
  funext p
  simp [laplacian, forward, backward]
  ring

/-- Forward derivative has zero total phase sum. -/
theorem phaseSum_forward_zero
    {α : Type*} [AddCommGroup α]
    (x : TriNumber α) :
    phaseSum (forward x) = 0 := by
  simp [phaseSum, forward, Phase3.rotate]
  abel

/-- Backward derivative has zero total phase sum. -/
theorem phaseSum_backward_zero
    {α : Type*} [AddCommGroup α]
    (x : TriNumber α) :
    phaseSum (backward x) = 0 := by
  simp [phaseSum, backward, Phase3.rotate, Phase3.rotate2]
  abel

/-- Forward differentiation commutes with cyclic rotation. -/
theorem forward_rotate
    {α : Type*} [AddGroup α]
    (x : TriNumber α) :
    forward (TriNumber.rotate x) = TriNumber.rotate (forward x) := by
  funext p
  cases p <;>
    simp [forward, TriNumber.rotate, Phase3.rotate]

/-- Backward differentiation commutes with cyclic rotation. -/
theorem backward_rotate
    {α : Type*} [AddGroup α]
    (x : TriNumber α) :
    backward (TriNumber.rotate x) = TriNumber.rotate (backward x) := by
  funext p
  cases p <;>
    simp [backward, TriNumber.rotate, Phase3.rotate, Phase3.rotate2]

/-- Coherent states have zero forward derivative. -/
theorem forward_eq_zero_of_coherent
    {α : Type*} [AddGroup α]
    {x : TriNumber α}
    (h : TriNumber.Coherent x) :
    forward x = 0 := by
  rcases h with ⟨hSP, hPM⟩
  funext p
  cases p <;>
    simp [forward, Phase3.rotate, hSP, hPM]

/-- Zero forward derivative forces coherence. -/
theorem coherent_of_forward_eq_zero
    {α : Type*} [AddGroup α]
    {x : TriNumber α}
    (h : forward x = 0) :
    TriNumber.Coherent x := by
  have hs := congrFun h Phase3.seed
  have hp := congrFun h Phase3.passage
  simp [forward, Phase3.rotate] at hs hp
  exact ⟨hs, hp⟩

theorem forward_eq_zero_iff_coherent
    {α : Type*} [AddGroup α]
    {x : TriNumber α} :
    forward x = 0 ↔ TriNumber.Coherent x := by
  constructor
  · exact coherent_of_forward_eq_zero
  · exact forward_eq_zero_of_coherent

end TriDifferential

end MCore.MaterialMath
