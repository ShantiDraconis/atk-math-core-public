/-
Copyright (c) 2026 Tiago Paschoalatto Fagliari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiago Paschoalatto Fagliari
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Hermitian structures and local Kähler metrics

A Hermitian structure on a complex normed space `E` is a real inner product `g` invariant under
the complex structure `J = I • ·`. Its fundamental form `ω(v, w) = g(J v, w)` is alternating and
`J`-invariant. A local Kähler metric on a set `U ⊆ E` is a smooth family of Hermitian structures
whose fundamental form is closed. This is the local model of a Kähler manifold; the global notion
needs differential forms on manifolds, which Mathlib does not have yet.

## Main definitions

* `HermitianStructure E`
* `HermitianStructure.fundamentalForm`, `HermitianStructure.fundamentalTwoForm`
* `LocalKahlerMetric U`

## Main results

* `HermitianStructure.fundamentalForm_antisymm`, `HermitianStructure.fundamentalForm_self`,
  `HermitianStructure.fundamentalForm_smul_I`.
* `HermitianStructure.standard`: the standard structure on `ℂ`, with `ω(1, I) = 1`.
* `LocalKahlerMetric.standard`: the flat metric on `ℂ` is Kähler.
-/

open Complex
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplication by `I`, as a continuous `ℝ`-linear map. -/
noncomputable def complexStructure : E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ I

@[simp] theorem complexStructure_apply (v : E) : (complexStructure : E →L[ℝ] E) v = I • v := rfl

variable (E) in
/-- A Hermitian structure: a real inner product invariant under multiplication by `I`. -/
structure HermitianStructure where
  /-- The real inner product. -/
  g : E →L[ℝ] E →L[ℝ] ℝ
  symm : ∀ v w, g v w = g w v
  pos : ∀ v, v ≠ 0 → 0 < g v v
  smul_I : ∀ v w, g (I • v) (I • w) = g v w

namespace HermitianStructure

variable (h : HermitianStructure E)

/-- The fundamental form `ω(v, w) = g(I • v, w)`. -/
noncomputable def fundamentalForm : E →L[ℝ] E →L[ℝ] ℝ := h.g.comp complexStructure

theorem fundamentalForm_apply (v w : E) : h.fundamentalForm v w = h.g (I • v) w := rfl

theorem fundamentalForm_antisymm (v w : E) : h.fundamentalForm v w = - h.fundamentalForm w v := by
  rw [fundamentalForm_apply, fundamentalForm_apply, ← h.smul_I (I • v) w, smul_smul, I_mul_I,
    neg_one_smul, map_neg, neg_apply, h.symm v]

theorem fundamentalForm_self (v : E) : h.fundamentalForm v v = 0 := by
  have := h.fundamentalForm_antisymm v v
  linarith

theorem fundamentalForm_smul_I (v w : E) :
    h.fundamentalForm (I • v) (I • w) = h.fundamentalForm v w := by
  rw [fundamentalForm_apply, fundamentalForm_apply, h.smul_I]

/-- The fundamental form as a continuous alternating 2-form (the alternatization of `ω`, that is
`2 ω`). -/
noncomputable def fundamentalTwoForm : E [⋀^Fin 2]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
      : (E →L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)).comp h.fundamentalForm)

/-- The standard Hermitian structure on `ℂ`: `g(v, w) = re (conj v * w)`. -/
noncomputable def standard : HermitianStructure ℂ where
  g := (innerSL ℝ (E := ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  symm v w := real_inner_comm w v
  pos v hv := real_inner_self_pos.mpr hv
  smul_I v w := by
    change ⟪I • v, I • w⟫_ℝ = ⟪v, w⟫_ℝ
    simp only [smul_eq_mul, Complex.inner, map_mul, conj_I]
    ring_nf
    simp

theorem standard_fundamentalForm_one_I : standard.fundamentalForm 1 I = 1 := by
  change ⟪I • (1 : ℂ), I⟫_ℝ = 1
  simp

end HermitianStructure

/-- A local Kähler metric on `U`: a smooth family of Hermitian structures with closed fundamental
form. -/
structure LocalKahlerMetric (U : Set E) where
  /-- The metric at each point. -/
  metric : E → HermitianStructure E
  contDiffOn : ContDiffOn ℝ ⊤ (fun x => (metric x).fundamentalTwoForm) U
  closed : ∀ x ∈ U, extDerivWithin (fun x => (metric x).fundamentalTwoForm) U x = 0

/-- The flat metric on `ℂ` is Kähler. -/
noncomputable def LocalKahlerMetric.standard : LocalKahlerMetric (Set.univ : Set ℂ) where
  metric := fun _ => HermitianStructure.standard
  contDiffOn := contDiffOn_const
  closed := fun x _ => by
    simp only [extDerivWithin, fderivWithin_const_apply]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero]
