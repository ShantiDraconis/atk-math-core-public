import MCore.FinalFail.Semantic.BSD
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.Analysis.Analytic.Order
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace MCore.FinalFail.Semantic

/-!
# BSD concrete rank producer — Mathlib v4.34 probe

This branch is isolated from the v4.19 main kernel.  It tests the first Mathlib
release containing all of the APIs needed to bind the BSD rank side to the same
genuine elliptic curve over Q.
-/

structure EllipticCurveQ where
  curve : WeierstrassCurve ℚ
  elliptic : IsUnit curve.Δ

instance (E : EllipticCurveQ) : E.curve.IsElliptic where
  isUnit := E.elliptic

noncomputable def EllipticCurveQ.LSeries (E : EllipticCurveQ) (s : ℂ) : ℂ :=
  E.curve.LSeries s

def bsdPositiveControlCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

theorem bsdPositiveControlCurve_delta :
    bsdPositiveControlCurve.Δ = (64 : ℚ) := by
  norm_num [bsdPositiveControlCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

def bsdPositiveControl : EllipticCurveQ where
  curve := bsdPositiveControlCurve
  elliptic := by
    rw [bsdPositiveControlCurve_delta]
    norm_num

theorem ellipticCurveQ_nonempty : Nonempty EllipticCurveQ :=
  ⟨bsdPositiveControl⟩

abbrev EllipticCurveQ.Points (E : EllipticCurveQ) : Type :=
  E.curve.toAffine.Point

def MordellWeilFiniteGeneration (E : EllipticCurveQ) : Prop :=
  AddGroup.FG E.Points

/-- Exact 2-descent residue: finite index of 2E(Q) inside E(Q). -/
def MWTwoDescentFinite (E : EllipticCurveQ) : Prop :=
  (nsmulAddMonoidHom (α := E.Points) 2).range.FiniteIndex

/-- All height-theoretic premises of Mordell--Weil descent except the finite
2-descent quotient are discharged by Mathlib's elliptic-height library. -/
theorem mordellWeilFiniteGeneration_of_twoDescent
    (E : EllipticCurveQ) (h₂ : MWTwoDescentFinite E) :
    MordellWeilFiniteGeneration E := by
  obtain ⟨C, hC⟩ :=
    WeierstrassCurve.Affine.approx_parallelogram_law E.curve.toAffine
  apply AddCommGroup.fg_of_descent'
      (h := fun P : E.Points => P.naiveHeight) (C := C) h₂
  · intro P
    exact Height.logHeight_nonneg P.xRep
  · exact hC

/-- The classical free Z-rank of the actual rational-point group. -/
noncomputable def EllipticCurveQ.mordellWeilRank (E : EllipticCurveQ) : Nat :=
  Module.finrank ℤ E.Points

/-- The torsion order is already canonical from the same rational-point group. -/
noncomputable def EllipticCurveQ.torsionOrder (E : EllipticCurveQ) : Nat := by
  letI : Finite (AddCommGroup.torsion E.Points) :=
    WeierstrassCurve.Affine.finite_torsion
  exact Nat.card (AddCommGroup.torsion E.Points)

/-- Rank-side BSD producer for one genuine elliptic curve.

The continuation cannot be chosen independently of E: it must agree with the
Mathlib Hasse--Weil L-series of the same curve on a right half-plane.
-/
structure BSDRankProducerFor (E : EllipticCurveQ) where
  twoDescentFinite : MWTwoDescentFinite E
  continuation : ℂ → ℂ
  analytic : ∀ z : ℂ, AnalyticAt ℂ continuation z
  agreesOnRightHalfPlane :
    ∀ s : ℂ, 2 < s.re → continuation s = E.LSeries s
  rankEquality :
    analyticOrderAt continuation (1 : ℂ) =
      (E.mordellWeilRank : ℕ∞)

def BSDRankProducer : Prop :=
  ∀ E : EllipticCurveQ, Nonempty (BSDRankProducerFor E)

theorem BSDRankProducerFor.finiteGeneration
    {E : EllipticCurveQ} (P : BSDRankProducerFor E) :
    MordellWeilFiniteGeneration E :=
  mordellWeilFiniteGeneration_of_twoDescent E P.twoDescentFinite

/-- Counter-audit: two arbitrary natural numbers remain a toy interface even
on a genuine curve and therefore are not used by BSDRankProducer. -/
structure BSDNaiveRankPair (E : EllipticCurveQ) where
  analyticOrderAtOne : Nat
  mordellWeilRank : Nat

def trivialBSDNaiveRankPair (E : EllipticCurveQ) : BSDNaiveRankPair E where
  analyticOrderAtOne := 0
  mordellWeilRank := 0

theorem naiveRankPair_is_trivially_inhabited (E : EllipticCurveQ) :
    Nonempty (BSDNaiveRankPair E) :=
  ⟨trivialBSDNaiveRankPair E⟩

end MCore.FinalFail.Semantic
