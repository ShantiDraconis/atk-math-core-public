/-
Copyright (c) 2026 Tiago Paschoalatto Fagliari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiago Paschoalatto Fagliari
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Birch and Swinnerton-Dyer conjecture (rank part)

We state the rank part of the Birch and Swinnerton-Dyer conjecture for a Weierstrass curve over
`ℚ`, using `WeierstrassCurve.LSeries` and the group of rational points `E.toAffine.Point`.

## Main definitions

* `WeierstrassCurve.LFunctionContinued E`: an entire function agreeing with `E.LSeries` on the
  half-plane `3 / 2 < re s`.
* `WeierstrassCurve.LFunctionContinued.analyticRank`: the order of vanishing at `s = 1`.
* `WeierstrassCurve.mordellWeilRank E`: the rank of `E(ℚ)` as an element of `ℕ∞`.
* `WeierstrassCurve.BSDConjecture E`: a continuation exists and its order of vanishing at `s = 1`
  is the Mordell–Weil rank.

## Main results

* `WeierstrassCurve.LFunctionContinued.instSubsingleton`: the continuation is unique.
* `WeierstrassCurve.LFunctionContinued.L_one_eq_zero_iff`: `L(E, 1) = 0` iff the analytic rank
  is positive.
* `WeierstrassCurve.bsdConjecture_iff_of_mordellWeilRank_eq_zero`: for a curve of rank `0`, the
  conjecture says exactly that the continuation exists and does not vanish at `s = 1`.

## Implementation notes

The half-plane is `3 / 2 < re s` rather than `1 < re s`: `LSeries` is defined with `tsum`, which
is `0` outside absolute summability, and the L-series of an elliptic curve is absolutely summable
exactly on `3 / 2 < re s` (by the Hasse bound). With `1 < re s` the structure would force `L s = 0`
on the strip `1 < re s ≤ 3 / 2` and would be empty for genuine elliptic curves.
-/

open Complex

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ)

/-- An analytic continuation of the L-series of `E`: an entire function agreeing with
`E.LSeries` on the half-plane of absolute convergence `3 / 2 < re s`. -/
structure LFunctionContinued where
  /-- The continued function. -/
  L : ℂ → ℂ
  differentiable : Differentiable ℂ L
  eq_LSeries : ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

namespace LFunctionContinued

variable {E}

theorem ext_L {L₁ L₂ : E.LFunctionContinued} (h : L₁.L = L₂.L) : L₁ = L₂ := by
  cases L₁; cases L₂; simp only at h; subst h; rfl

theorem L_eq (L₁ L₂ : E.LFunctionContinued) : L₁.L = L₂.L := by
  have h₁ : AnalyticOnNhd ℂ L₁.L Set.univ := fun z _ => L₁.differentiable.analyticAt z
  have h₂ : AnalyticOnNhd ℂ L₂.L Set.univ := fun z _ => L₂.differentiable.analyticAt z
  refine h₁.eq_of_eventuallyEq h₂ (z₀ := 2) ?_
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  filter_upwards [hopen.mem_nhds hmem] with s hs
  rw [L₁.eq_LSeries s hs, L₂.eq_LSeries s hs]

/-- The analytic continuation is unique. -/
instance instSubsingleton : Subsingleton E.LFunctionContinued :=
  ⟨fun L₁ L₂ => ext_L (L_eq L₁ L₂)⟩

/-- The analytic rank: the order of vanishing at `s = 1`. -/
noncomputable def analyticRank (L : E.LFunctionContinued) : ℕ∞ := analyticOrderAt L.L 1

theorem L_one_eq_zero_iff (L : E.LFunctionContinued) : L.L 1 = 0 ↔ 0 < L.analyticRank := by
  have ha : AnalyticAt ℂ L.L 1 := L.differentiable.analyticAt 1
  rw [analyticRank, pos_iff_ne_zero, Ne, analyticOrderAt_eq_zero]
  constructor
  · intro h0 hc
    rcases hc with hc | hc
    · exact hc ha
    · exact hc h0
  · intro hn
    by_contra h0
    exact hn (Or.inr h0)

end LFunctionContinued

/-- The Mordell–Weil rank of `E(ℚ)`, as an element of `ℕ∞`. -/
noncomputable def mordellWeilRank : ℕ∞ := Cardinal.toENat (Module.rank ℤ E.toAffine.Point)

/-- **The Birch and Swinnerton-Dyer conjecture** (rank part) for `E`. -/
def BSDConjecture : Prop :=
  ∃ L : E.LFunctionContinued, L.analyticRank = E.mordellWeilRank

theorem bsdConjecture_iff_forall :
    E.BSDConjecture ↔ Nonempty E.LFunctionContinued ∧
      ∀ L : E.LFunctionContinued, L.analyticRank = E.mordellWeilRank := by
  constructor
  · rintro ⟨L, h⟩
    exact ⟨⟨L⟩, fun L' => by rw [Subsingleton.elim L' L]; exact h⟩
  · rintro ⟨⟨L⟩, h⟩
    exact ⟨L, h L⟩

theorem bsdConjecture_iff_of_mordellWeilRank_eq_zero (h : E.mordellWeilRank = 0) :
    E.BSDConjecture ↔ ∃ L : E.LFunctionContinued, L.L 1 ≠ 0 := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, fun h0 => ?_⟩
    have := (L.L_one_eq_zero_iff).mp h0
    rw [hL, h] at this
    exact lt_irrefl _ this
  · rintro ⟨L, hL⟩
    refine ⟨L, ?_⟩
    rw [h]
    by_contra hne
    exact hL ((L.L_one_eq_zero_iff).mpr (pos_iff_ne_zero.mpr hne))

/-- Example: the curve `y² = x³ − x` (discriminant `64`) is elliptic. -/
example : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩

end WeierstrassCurve
