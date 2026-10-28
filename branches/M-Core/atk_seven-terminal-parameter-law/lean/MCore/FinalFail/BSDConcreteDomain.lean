import MCore.FinalFail.Semantic.BSD
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Analytic.Order

namespace MCore.FinalFail.Semantic

/-!
# BSD concrete source domain at the pinned Mathlib v4.19.0 boundary

What is kernel-available at the repository's pinned dependency:
* genuine nonsingular Weierstrass curves over Q;
* analytic vanishing-order infrastructure (`analyticOrderAt`).

What is NOT available in Mathlib v4.19.0:
* the later `EllipticCurve.LFunction` module;
* the later elliptic-curve rational-point group API;
* the later elliptic-height/descent module;
* the later abstract descent theorem used to reduce Mordell--Weil finite
  generation to finiteness of E(Q)/2E(Q).

Therefore this module closes only the genuine geometric source binding.  It
does not fabricate replacements for the missing arithmetic/analytic APIs.
-/

/-- A genuine elliptic curve over Q represented by a nonsingular Weierstrass
equation. -/
structure EllipticCurveQ where
  curve : WeierstrassCurve ℚ
  elliptic : IsUnit curve.Δ

instance (E : EllipticCurveQ) : E.curve.IsElliptic where
  isUnit := E.elliptic

/-- Positive control: y^2 = x^3 - x. -/
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

/-- Administrative source-version boundary.  These booleans are audit data,
not mathematical hypotheses and not producers. -/
structure BSDPinnedApiBoundary where
  genuineCurveDomain : Bool
  analyticOrderAvailable : Bool
  ellipticLSeriesAvailable : Bool
  rationalPointGroupAvailable : Bool
  ellipticDescentAvailable : Bool
  deriving DecidableEq, Repr

def bsdPinnedApiBoundary : BSDPinnedApiBoundary := {
  genuineCurveDomain := true
  analyticOrderAvailable := true
  ellipticLSeriesAvailable := false
  rationalPointGroupAvailable := false
  ellipticDescentAvailable := false
}

theorem bsd_pinned_has_genuine_domain :
    bsdPinnedApiBoundary.genuineCurveDomain = true := rfl

theorem bsd_pinned_missing_lseries :
    bsdPinnedApiBoundary.ellipticLSeriesAvailable = false := rfl

theorem bsd_pinned_missing_point_group :
    bsdPinnedApiBoundary.rationalPointGroupAvailable = false := rfl

theorem bsd_pinned_missing_descent :
    bsdPinnedApiBoundary.ellipticDescentAvailable = false := rfl

end MCore.FinalFail.Semantic
