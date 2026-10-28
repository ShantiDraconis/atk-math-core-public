/-
Copyright (c) 2026 Tiago Paschoalatto Fagliari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiago Paschoalatto Fagliari
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Basic

/-!
# Rational Hodge structures and Hodge classes

A pure rational Hodge structure of weight `n` on a `ℚ`-vector space `V` is a decomposition
`ℂ ⊗[ℚ] V = ⨁ H^{p, n - p}` such that complex conjugation exchanges `H^{p, q}` and `H^{q, p}`.
A Hodge class in a structure of weight `2 p` is a rational vector whose image lies in `H^{p, p}`.

## Main definitions

* `HodgeStructure V n`, `HodgeStructure.IsHodgeClass`, `HodgeStructure.hodgeClasses`.
* `HodgeStructure.pure p`: the structure of type `(p, p)`; `HodgeStructure.tate`: `ℚ(-1)`.

## Main results

* `HodgeStructure.hodgeClasses` is a `ℚ`-subspace.
* Every vector of `HodgeStructure.pure p` is a Hodge class; in `ℚ(-1)`, `H^{2,0} = 0`.
-/

open TensorProduct

/-- Complex conjugation, as a `ℚ`-linear map. -/
noncomputable def Complex.conjRat : ℂ →ₗ[ℚ] ℂ := (Complex.conjAe.toLinearMap).restrictScalars ℚ

namespace HodgeStructure

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on `ℂ ⊗[ℚ] V`. -/
noncomputable def conj : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V := TensorProduct.map Complex.conjRat LinearMap.id

@[simp] theorem conj_tmul (z : ℂ) (v : V) : conj V (z ⊗ₜ v) = (starRingEnd ℂ z) ⊗ₜ v := rfl

theorem conj_conj (x : ℂ ⊗[ℚ] V) : conj V (conj V x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conj_surjective : Function.Surjective (conj V) := fun x => ⟨conj V x, conj_conj V x⟩

end HodgeStructure

/-- A pure rational Hodge structure of weight `n`. -/
structure HodgeStructure (V : Type*) [AddCommGroup V] [Module ℚ V] (n : ℤ) where
  /-- `H p` is `H^{p, n - p}`. -/
  H : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  isInternal : DirectSum.IsInternal H
  conj_image : ∀ p, HodgeStructure.conj V '' (H p : Set (ℂ ⊗[ℚ] V)) = H (n - p)

namespace HodgeStructure

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A Hodge class: a rational vector whose image lies in `H^{p, p}`. -/
def IsHodgeClass {p : ℤ} (h : HodgeStructure V (2 * p)) (v : V) : Prop := (1 : ℂ) ⊗ₜ[ℚ] v ∈ h.H p

/-- The `ℚ`-subspace of Hodge classes. -/
def hodgeClasses {p : ℤ} (h : HodgeStructure V (2 * p)) : Submodule ℚ V where
  carrier := {v | h.IsHodgeClass v}
  zero_mem' := by simp [IsHodgeClass]
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, IsHodgeClass, tmul_add] at *
    exact add_mem ha hb
  smul_mem' := fun q v hv => by
    simp only [Set.mem_ofPred_eq, IsHodgeClass] at *
    have : (1 : ℂ) ⊗ₜ[ℚ] (q • v) = (q : ℂ) • ((1 : ℂ) ⊗ₜ[ℚ] v) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Rat.smul_one_eq_cast, smul_eq_mul,
        mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hv

/-- The pure structure of type `(p, p)`. -/
noncomputable def pure (p₀ : ℤ) : HodgeStructure V (2 * p₀) where
  H p := if p = p₀ then ⊤ else ⊥
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro i
      by_cases hi : i = p₀
      · subst hi
        have : (⨆ (j : ℤ) (_ : j ≠ i), (if j = i then ⊤ else ⊥ : Submodule ℂ (ℂ ⊗[ℚ] V))) = ⊥ := by
          simp only [iSup_eq_bot]
          intro j hj
          simp [hj]
        rw [this]
        exact disjoint_bot_right
      · simp only [hi, ite_false]
        exact disjoint_bot_left
    · refine eq_top_iff.mpr (le_iSup_of_le p₀ ?_)
      simp
  conj_image := fun p => by
    by_cases hp : p = p₀
    · subst hp
      simp only [show 2 * p - p = p by ring, ite_true, Submodule.top_coe, Set.image_univ,
        (conj_surjective V).range_eq]
    · have hq : ¬ (2 * p₀ - p = p₀) := fun h => hp (by omega)
      simp only [hp, hq, ite_false, Submodule.bot_coe, Set.image_singleton, map_zero]

theorem isHodgeClass_pure (p₀ : ℤ) (v : V) : (pure (V := V) p₀).IsHodgeClass v := by
  simp [IsHodgeClass, pure]

/-- The Tate structure `ℚ(-1)`: weight `2`, type `(1, 1)`. -/
noncomputable def tate : HodgeStructure ℚ (2 * 1) := pure 1

theorem tate_isHodgeClass_one : tate.IsHodgeClass (1 : ℚ) := isHodgeClass_pure 1 1

theorem tate_hodgeClasses : tate.hodgeClasses = ⊤ :=
  eq_top_iff.mpr fun v _ => isHodgeClass_pure 1 v

theorem tate_H_two : tate.H 2 = ⊥ := by simp [tate, pure]

end HodgeStructure
