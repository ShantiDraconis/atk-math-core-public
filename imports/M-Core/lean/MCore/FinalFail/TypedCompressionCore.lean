import Mathlib.Data.Set.Basic

/-!
# Typed Projection/Fiber Core for FINAL_FAIL

Axiom-free structural core recovered from the useful portion of the historical
LRE vocabulary.  This file deliberately does not import any LRE axiom.

`Set`, set-builder notation, `Set.Nonempty` and `Function.Injective` come from
Mathlib; the file did not compile without this import.
-/

namespace MCore.FinalFail

universe u v

/-- A bare compression/projection map. No injectivity, surjectivity or topology
is assumed. -/
structure Compression (X : Type u) (Y : Type v) where
  map : X → Y

namespace Compression

variable {X : Type u} {Y : Type v}

/-- The fiber over y is the exact preimage of y. -/
def fiber (C : Compression X Y) (y : Y) : Set X :=
  {x | C.map x = y}

/-- Compression kernel-equivalence: two inputs are observationally equal
exactly when compression gives the same output. -/
def KernelEq (C : Compression X Y) (x₁ x₂ : X) : Prop :=
  C.map x₁ = C.map x₂

theorem kernelEq_refl (C : Compression X Y) (x : X) : C.KernelEq x x := rfl

theorem kernelEq_symm (C : Compression X Y) {x₁ x₂ : X}
    (h : C.KernelEq x₁ x₂) : C.KernelEq x₂ x₁ := h.symm

theorem kernelEq_trans (C : Compression X Y) {x₁ x₂ x₃ : X}
    (h12 : C.KernelEq x₁ x₂) (h23 : C.KernelEq x₂ x₃) :
    C.KernelEq x₁ x₃ := h12.trans h23

theorem mem_fiber_self (C : Compression X Y) (x : X) :
    x ∈ C.fiber (C.map x) := rfl

theorem same_fiber_iff_kernelEq (C : Compression X Y) (x₁ x₂ : X) :
    x₂ ∈ C.fiber (C.map x₁) ↔ C.KernelEq x₂ x₁ := Iff.rfl

/-- A section is a right inverse of compression: C ∘ R = id. -/
structure Section (C : Compression X Y) where
  map : Y → X
  rightInverse : ∀ y, C.map (map y) = y

/-- A retraction law in the opposite direction: R ∘ C = id.  Kept distinct
from Section on purpose. -/
def LeftInverseLaw (C : Compression X Y) (R : Y → X) : Prop :=
  ∀ x, R (C.map x) = x

theorem section_fiber_nonempty (C : Compression X Y) (R : C.Section) (y : Y) :
    (C.fiber y).Nonempty := by
  exact ⟨R.map y, R.rightInverse y⟩

/-- If one reconstruction map is both a section and a left inverse, compression
is injective. This is the exact firewall against pretending a lossy compression
has a bilateral inverse. -/
theorem bilateral_inverse_implies_injective
    (C : Compression X Y) (R : C.Section)
    (hleft : C.LeftInverseLaw R.map) :
    Function.Injective C.map := by
  intro x₁ x₂ h
  calc
    x₁ = R.map (C.map x₁) := (hleft x₁).symm
    _ = R.map (C.map x₂) := congrArg R.map h
    _ = x₂ := hleft x₂

/-- Conversely, a witnessed collision rules out any bilateral reconstruction. -/
theorem collision_blocks_bilateral_inverse
    (C : Compression X Y)
    {x₁ x₂ : X} (hne : x₁ ≠ x₂) (hcollision : C.KernelEq x₁ x₂)
    (R : C.Section) :
    ¬ C.LeftInverseLaw R.map := by
  intro hleft
  exact hne (C.bilateral_inverse_implies_injective R hleft hcollision)

end Compression

end MCore.FinalFail
