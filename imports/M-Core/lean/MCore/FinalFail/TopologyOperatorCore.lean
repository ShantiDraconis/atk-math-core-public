namespace MCore.FinalFail

structure Triad (F I M : Type) where
  C_minus : F → M
  C_plus : I → M
  R_minus : M → Option F
  R_plus : M → Option I

namespace Triad

variable {F I M : Type} (T : Triad F I M)

def defect (m : M) : Prop :=
  (∀ f, T.R_minus m = some f → T.C_minus f ≠ m) ∨
  (∀ i, T.R_plus m = some i → T.C_plus i ≠ m)

def isRetractionMinusOn (S : M → Prop) : Prop :=
  ∀ m, S m → ∃ f, T.R_minus m = some f ∧ T.C_minus f = m

def isRetractionPlusOn (S : M → Prop) : Prop :=
  ∀ m, S m → ∃ i, T.R_plus m = some i ∧ T.C_plus i = m

def fiberMinus (m : M) : F → Prop := fun f => T.C_minus f = m
def fiberPlus (m : M) : I → Prop := fun i => T.C_plus i = m

def iterateCR (m : M) : Option M :=
  match T.R_minus m with
  | some f => some (T.C_minus f)
  | none =>
      match T.R_plus m with
      | some i => some (T.C_plus i)
      | none => none

def isFixedPoint (m : M) : Prop := T.iterateCR m = some m

theorem minus_retraction_implies_fixed
    {S : M → Prop} (h : T.isRetractionMinusOn S) {m : M} (hm : S m) :
    T.isFixedPoint m := by
  rcases h m hm with ⟨f, hR, hC⟩
  simp [isFixedPoint, iterateCR, hR, hC]

end Triad

structure AbstractNucleus (M : Type) where
  carrier : M → Prop
  closed : Prop

def preimageMinus {F I M : Type} (T : Triad F I M) (N : AbstractNucleus M) : F → Prop :=
  fun f => N.carrier (T.C_minus f)

def preimagePlus {F I M : Type} (T : Triad F I M) (N : AbstractNucleus M) : I → Prop :=
  fun i => N.carrier (T.C_plus i)

structure RealImaginaryCore (M : Type) where
  RealPart : Type
  ImagPart : Type
  Re : M → RealPart
  Im : M → ImagPart
  jointlyFaithful : ∀ x y, Re x = Re y → Im x = Im y → x = y

theorem real_imaginary_ext {M : Type} (C : RealImaginaryCore M)
    {x y : M} (hRe : C.Re x = C.Re y) (hIm : C.Im x = C.Im y) :
    x = y := C.jointlyFaithful x y hRe hIm

end MCore.FinalFail
