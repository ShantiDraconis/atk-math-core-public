import MCore.FinalFail.MaterialField
import MCore.FinalFail.MaterialGeometry

namespace MCore.FinalFail.MaterialPolynomial

open MCore.FinalFail.MaterialAlgebra
open MCore.FinalFail.MaterialDerived

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState
abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector

/-!
# Polynomial and affine dynamics over the three-state material algebra

All results here are internal consequences of the explicit three-element field
table already kernel-checked in MaterialField.

They do not assert that any external mathematical conjecture has been solved,
and they do not identify ordinary indeterminate expressions such as 0/0 with
TriState values.
-/

namespace TriState

/-- Subtraction in the explicit additive group. -/
def sub (x y : TState) : TState := x + (-y)

@[simp] theorem sub_self (x : TState) :
    sub x x = 0 := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x

/-- Additive right cancellation in the explicit three-element group. -/
theorem add_right_cancel
    (a b c : TState) (h : a + c = b + c) :
    a = b := by
  have h' := congrArg (fun t : TState => t + (-c)) h
  have ha : (a + c) + (-c) = a := by
    rw [
      MCore.FinalFail.MaterialAlgebra.TriState.add_assoc,
      MCore.FinalFail.MaterialAlgebra.TriState.add_neg,
      MCore.FinalFail.MaterialAlgebra.TriState.add_seed
    ]
  have hb : (b + c) + (-c) = b := by
    rw [
      MCore.FinalFail.MaterialAlgebra.TriState.add_assoc,
      MCore.FinalFail.MaterialAlgebra.TriState.add_neg,
      MCore.FinalFail.MaterialAlgebra.TriState.add_seed
    ]
  calc
    a = (a + c) + (-c) := ha.symm
    _ = (b + c) + (-c) := h'
    _ = b := hb

/-- Additive left cancellation. -/
theorem add_left_cancel
    (a b c : TState) (h : c + a = c + b) :
    a = b := by
  rw [MCore.FinalFail.MaterialAlgebra.TriState.add_comm c a,
      MCore.FinalFail.MaterialAlgebra.TriState.add_comm c b] at h
  exact add_right_cancel a b c h

/-- Square. -/
def sq (x : TState) : TState := x * x

/-- Kronecker/Lagrange basis at 0. -/
def basis0 (x : TState) : TState :=
  1 + (-(sq x))

/-- Kronecker/Lagrange basis at 1. -/
def basis1 (x : TState) : TState :=
  (.manifest : TState) * x * (x + 1)

/-- Kronecker/Lagrange basis at 2 (= -1). -/
def basis2 (x : TState) : TState :=
  (.manifest : TState) * x * (x + .manifest)

@[simp] theorem basis0_seed : basis0 .seed = 1 := by rfl
@[simp] theorem basis0_transit : basis0 .transit = 0 := by rfl
@[simp] theorem basis0_manifest : basis0 .manifest = 0 := by rfl

@[simp] theorem basis1_seed : basis1 .seed = 0 := by rfl
@[simp] theorem basis1_transit : basis1 .transit = 1 := by rfl
@[simp] theorem basis1_manifest : basis1 .manifest = 0 := by rfl

@[simp] theorem basis2_seed : basis2 .seed = 0 := by rfl
@[simp] theorem basis2_transit : basis2 .transit = 0 := by rfl
@[simp] theorem basis2_manifest : basis2 .manifest = 1 := by rfl

/-- Lagrange partition of unity on the three-element carrier. -/
theorem basis_partition (x : TState) :
    basis0 x + basis1 x + basis2 x = 1 := by
  cases x <;> rfl

/-- Pairwise orthogonality of the three point idempotents. -/
theorem basis01_orthogonal (x : TState) :
    basis0 x * basis1 x = 0 := by
  cases x <;> rfl

theorem basis02_orthogonal (x : TState) :
    basis0 x * basis2 x = 0 := by
  cases x <;> rfl

theorem basis12_orthogonal (x : TState) :
    basis1 x * basis2 x = 0 := by
  cases x <;> rfl

/-- Point idempotence. -/
theorem basis0_idem (x : TState) :
    basis0 x * basis0 x = basis0 x := by
  cases x <;> rfl

theorem basis1_idem (x : TState) :
    basis1 x * basis1 x = basis1 x := by
  cases x <;> rfl

theorem basis2_idem (x : TState) :
    basis2 x * basis2 x = basis2 x := by
  cases x <;> rfl

/-- Lagrange interpolant for an arbitrary unary operator. -/
def interpolate (f : TState → TState) (x : TState) : TState :=
  f .seed * basis0 x +
  f .transit * basis1 x +
  f .manifest * basis2 x

/-- Every unary operator on the three-element carrier is represented by the
explicit degree-at-most-two Lagrange formula. -/
theorem interpolate_exact (f : TState → TState) :
    ∀ x, interpolate f x = f x := by
  intro x
  cases x with
  | seed =>
      simp only [
        interpolate,
        basis0_seed, basis1_seed, basis2_seed,
        MCore.FinalFail.MaterialAlgebra.TriState.mul_one,
        MCore.FinalFail.MaterialAlgebra.TriState.mul_zero
      ]
      cases h : f .seed <;> rfl
  | transit =>
      simp only [
        interpolate,
        basis0_transit, basis1_transit, basis2_transit,
        MCore.FinalFail.MaterialAlgebra.TriState.mul_zero,
        MCore.FinalFail.MaterialAlgebra.TriState.mul_one
      ]
      cases h : f .transit <;> rfl
  | manifest =>
      simp only [
        interpolate,
        basis0_manifest, basis1_manifest, basis2_manifest,
        MCore.FinalFail.MaterialAlgebra.TriState.mul_zero,
        MCore.FinalFail.MaterialAlgebra.TriState.mul_one
      ]
      cases h : f .manifest <;> rfl

/-- Functional extensional form: every endomorphism is its quadratic
interpolant. -/
theorem every_unary_operator_is_quadratic
    (f : TState → TState) :
    interpolate f = f := by
  funext x
  exact interpolate_exact f x

/-- An affine operator x ↦ a*x+b. -/
def affine (a b x : TState) : TState :=
  a * x + b

@[simp] theorem affine_zero_scale (b x : TState) :
    affine 0 b x = b := by
  cases b <;> cases x <;> rfl

@[simp] theorem affine_one_scale (b x : TState) :
    affine 1 b x = x + b := by
  cases b <;> cases x <;> rfl

/-- Composition law for affine operators. -/
theorem affine_comp
    (a b c d x : TState) :
    affine a b (affine c d x) =
      affine (a * c) (a * d + b) x := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> rfl

/-- Translation by 1 is exactly the certified three-cycle rotation. -/
theorem affine_one_one_eq_rotate (x : TState) :
    affine 1 1 x = x.rotate := by
  cases x <;> rfl

/-- Translation by 2 is the inverse/two-step rotation. -/
theorem affine_one_manifest_eq_rotate_twice (x : TState) :
    affine 1 .manifest x = x.rotate.rotate := by
  cases x <;> rfl

/-- Every nonzero affine slope yields an injective operator. -/
theorem affine_injective
    (a b : TState) (ha : a ≠ 0) :
    Function.Injective (affine a b) := by
  intro x y h
  have hm : a * x = a * y := by
    exact add_right_cancel (a * x) (a * y) b h
  exact MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero ha hm

/-- Every nonzero affine slope yields a surjective operator. -/
theorem affine_surjective
    (a b : TState) (ha : a ≠ 0) :
    Function.Surjective (affine a b) := by
  intro y
  refine ⟨a * (y + (-b)), ?_⟩
  cases a with
  | seed =>
      exact False.elim (ha rfl)
  | transit =>
      cases b <;> cases y <;> rfl
  | manifest =>
      cases b <;> cases y <;> rfl

theorem affine_bijective
    (a b : TState) (ha : a ≠ 0) :
    Function.Bijective (affine a b) :=
  ⟨affine_injective a b ha, affine_surjective a b ha⟩

/-- Frobenius fixes every point, hence is the identity endomorphism. -/
def frobenius (x : TState) : TState := (x * x) * x

theorem frobenius_eq_id :
    frobenius = id := by
  funext x
  exact MCore.FinalFail.MaterialField.TriState.frobenius_identity x

end TriState

namespace SevenLaneVector

/-- Componentwise affine action with a shared scalar and shift. -/
def affine
    (a : TState) (b x : LaneVector) : LaneVector where
  riemann := TriState.affine a b.riemann x.riemann
  beal := TriState.affine a b.beal x.beal
  pvsnp := TriState.affine a b.pvsnp x.pvsnp
  navierStokes := TriState.affine a b.navierStokes x.navierStokes
  hodge := TriState.affine a b.hodge x.hodge
  bsd := TriState.affine a b.bsd x.bsd
  yangMills := TriState.affine a b.yangMills x.yangMills

/-- Shared nonzero affine slope preserves equality of seven-lane states. -/
theorem affine_injective
    (a : TState) (b : LaneVector) (ha : a ≠ 0) :
    Function.Injective (affine a b) := by
  intro x y h
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · apply TriState.affine_injective a b.riemann ha
    exact congrArg (fun z : LaneVector => z.riemann) h
  · apply TriState.affine_injective a b.beal ha
    exact congrArg (fun z : LaneVector => z.beal) h
  · apply TriState.affine_injective a b.pvsnp ha
    exact congrArg (fun z : LaneVector => z.pvsnp) h
  · apply TriState.affine_injective a b.navierStokes ha
    exact congrArg (fun z : LaneVector => z.navierStokes) h
  · apply TriState.affine_injective a b.hodge ha
    exact congrArg (fun z : LaneVector => z.hodge) h
  · apply TriState.affine_injective a b.bsd ha
    exact congrArg (fun z : LaneVector => z.bsd) h
  · apply TriState.affine_injective a b.yangMills ha
    exact congrArg (fun z : LaneVector => z.yangMills) h

/-- Hamming geometry is invariant under a common nondegenerate affine change
of coordinates. -/
theorem hamming_affine
    (a : TState) (b x y : LaneVector) (ha : a ≠ 0) :
    MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming
        (affine a b x) (affine a b y) =
      MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming x y := by
  unfold MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming affine
  have hR :
      TriState.affine a b.riemann x.riemann =
          TriState.affine a b.riemann y.riemann ↔
        x.riemann = y.riemann := by
    constructor
    · intro h
      apply TriState.affine_injective a b.riemann ha
      exact h
    · intro h
      exact congrArg (TriState.affine a b.riemann) h
  have hB :
      TriState.affine a b.beal x.beal =
          TriState.affine a b.beal y.beal ↔
        x.beal = y.beal := by
    constructor
    · intro h
      apply TriState.affine_injective a b.beal ha
      exact h
    · intro h
      exact congrArg (TriState.affine a b.beal) h
  have hP :
      TriState.affine a b.pvsnp x.pvsnp =
          TriState.affine a b.pvsnp y.pvsnp ↔
        x.pvsnp = y.pvsnp := by
    constructor
    · intro h
      apply TriState.affine_injective a b.pvsnp ha
      exact h
    · intro h
      exact congrArg (TriState.affine a b.pvsnp) h
  have hN :
      TriState.affine a b.navierStokes x.navierStokes =
          TriState.affine a b.navierStokes y.navierStokes ↔
        x.navierStokes = y.navierStokes := by
    constructor
    · intro h
      apply TriState.affine_injective a b.navierStokes ha
      exact h
    · intro h
      exact congrArg (TriState.affine a b.navierStokes) h
  have hH :
      TriState.affine a b.hodge x.hodge =
          TriState.affine a b.hodge y.hodge ↔
        x.hodge = y.hodge := by
    constructor
    · intro h
      apply TriState.affine_injective a b.hodge ha
      exact h
    · intro h
      exact congrArg (TriState.affine a b.hodge) h
  have hD :
      TriState.affine a b.bsd x.bsd =
          TriState.affine a b.bsd y.bsd ↔
        x.bsd = y.bsd := by
    constructor
    · intro h
      apply TriState.affine_injective a b.bsd ha
      exact h
    · intro h
      exact congrArg (TriState.affine a b.bsd) h
  have hY :
      TriState.affine a b.yangMills x.yangMills =
          TriState.affine a b.yangMills y.yangMills ↔
        x.yangMills = y.yangMills := by
    constructor
    · intro h
      apply TriState.affine_injective a b.yangMills ha
      exact h
    · intro h
      exact congrArg (TriState.affine a b.yangMills) h
  simp [hR, hB, hP, hN, hH, hD, hY]

end SevenLaneVector

#print axioms MCore.FinalFail.MaterialPolynomial.TriState.every_unary_operator_is_quadratic
#print axioms MCore.FinalFail.MaterialPolynomial.TriState.add_right_cancel
#print axioms MCore.FinalFail.MaterialPolynomial.TriState.affine_comp
#print axioms MCore.FinalFail.MaterialPolynomial.TriState.affine_bijective
#print axioms MCore.FinalFail.MaterialPolynomial.TriState.frobenius_eq_id
#print axioms MCore.FinalFail.MaterialPolynomial.SevenLaneVector.affine_injective
#print axioms MCore.FinalFail.MaterialPolynomial.SevenLaneVector.hamming_affine

end MCore.FinalFail.MaterialPolynomial
