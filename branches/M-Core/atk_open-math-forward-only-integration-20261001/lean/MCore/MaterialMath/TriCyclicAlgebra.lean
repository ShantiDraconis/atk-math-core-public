import Mathlib

namespace MCore.MaterialMath

/-- The three cyclic phases used by the material algebra. -/
inductive TriPhase where
  | manifest
  | crossing
  | seed
  deriving DecidableEq, Repr

/-- A three-component number/state.  The names encode the cyclic phases
Manifest -> Crossing -> Seed -> Manifest. -/
structure TriNumber (α : Type*) where
  manifest : α
  crossing : α
  seed : α
  deriving Repr

namespace TriNumber

variable {α : Type*}

/-- Extensionality principle for tri-numbers. -/
@[ext] theorem ext {x y : TriNumber α}
    (hManifest : x.manifest = y.manifest)
    (hCrossing : x.crossing = y.crossing)
    (hSeed : x.seed = y.seed) :
    x = y := by
  cases x
  cases y
  simp_all


/-- Cyclic phase rotation of order three. -/
def rotate (x : TriNumber α) : TriNumber α where
  manifest := x.seed
  crossing := x.manifest
  seed := x.crossing

theorem rotate_three (x : TriNumber α) :
    rotate (rotate (rotate x)) = x := by
  cases x
  rfl

/-- Componentwise addition. -/
def add [Add α] (x y : TriNumber α) : TriNumber α where
  manifest := x.manifest + y.manifest
  crossing := x.crossing + y.crossing
  seed := x.seed + y.seed

/-- Componentwise negation. -/
def neg [Neg α] (x : TriNumber α) : TriNumber α where
  manifest := -x.manifest
  crossing := -x.crossing
  seed := -x.seed

/-- Scalar action on all three phases. -/
def smul [SMul R α] (r : R) (x : TriNumber α) : TriNumber α where
  manifest := r • x.manifest
  crossing := r • x.crossing
  seed := r • x.seed

/-- Cyclic convolution product.  Algebraically this is the coefficient rule
for the group algebra of the cyclic group C3. -/
def cyclicMul [Add α] [Mul α] (x y : TriNumber α) : TriNumber α where
  manifest :=
    x.manifest * y.manifest +
    x.crossing * y.seed +
    x.seed * y.crossing
  crossing :=
    x.manifest * y.crossing +
    x.crossing * y.manifest +
    x.seed * y.seed
  seed :=
    x.manifest * y.seed +
    x.crossing * y.crossing +
    x.seed * y.manifest

/-- Multiplicative identity for cyclic convolution. -/
def cyclicOne [Zero α] [One α] : TriNumber α where
  manifest := 1
  crossing := 0
  seed := 0

theorem cyclicMul_one [CommSemiring α] (x : TriNumber α) :
    cyclicMul x cyclicOne = x := by
  cases x
  simp [cyclicMul, cyclicOne]

theorem one_cyclicMul [CommSemiring α] (x : TriNumber α) :
    cyclicMul cyclicOne x = x := by
  cases x
  simp [cyclicMul, cyclicOne]

theorem cyclicMul_comm [CommSemiring α] (x y : TriNumber α) :
    cyclicMul x y = cyclicMul y x := by
  apply TriNumber.ext <;> simp [cyclicMul] <;> ring

theorem cyclicMul_assoc [CommSemiring α] (x y z : TriNumber α) :
    cyclicMul (cyclicMul x y) z = cyclicMul x (cyclicMul y z) := by
  apply TriNumber.ext <;> simp [cyclicMul] <;> ring

theorem cyclicMul_add_left [CommSemiring α] (x y z : TriNumber α) :
    cyclicMul (add x y) z = add (cyclicMul x z) (cyclicMul y z) := by
  apply TriNumber.ext <;> simp [cyclicMul, add] <;> ring

theorem rotate_cyclicMul [CommSemiring α] (x y : TriNumber α) :
    rotate (cyclicMul x y) = cyclicMul (rotate x) y := by
  apply TriNumber.ext <;> simp [rotate, cyclicMul] <;> ring

/-- Total symmetric content. -/
def total [Add α] (x : TriNumber α) : α :=
  x.manifest + x.crossing + x.seed

theorem total_rotate [AddCommSemigroup α] (x : TriNumber α) :
    total (rotate x) = total x := by
  cases x
  simp [total, rotate, add_assoc, add_comm, add_left_comm]

/-- Traction: directed contrast between Manifest and Seed. -/
def traction [Sub α] (x : TriNumber α) : α :=
  x.manifest - x.seed

/-- Repulsion: the Crossing phase measured against the two endpoints. -/
def repulsion [Ring α] (x : TriNumber α) : α :=
  2 * x.crossing - x.manifest - x.seed

/-- Alternating cyclic two-form.  This is the oriented phase-coupling
quantity and is used as the algebraic notion of torsion. -/
def torsion [Ring α] (x y : TriNumber α) : α :=
  (x.manifest * y.crossing +
   x.crossing * y.seed +
   x.seed * y.manifest) -
  (x.crossing * y.manifest +
   x.seed * y.crossing +
   x.manifest * y.seed)

theorem torsion_self [CommRing α] (x : TriNumber α) :
    torsion x x = 0 := by
  simp [torsion]
  ring

theorem torsion_skew [CommRing α] (x y : TriNumber α) :
    torsion x y = - torsion y x := by
  simp [torsion]
  ring

theorem torsion_rotate_both [CommRing α] (x y : TriNumber α) :
    torsion (rotate x) (rotate y) = torsion x y := by
  cases x
  cases y
  simp [torsion, rotate]
  ring

/-- Quadratic phase-spread invariant. -/
def spread [CommRing α] (x : TriNumber α) : α :=
  (x.manifest - x.crossing)^2 +
  (x.crossing - x.seed)^2 +
  (x.seed - x.manifest)^2

theorem spread_rotate [CommRing α] (x : TriNumber α) :
    spread (rotate x) = spread x := by
  cases x
  simp [spread, rotate]
  ring

/-- All phases coincide. -/
def Balanced (x : TriNumber α) : Prop :=
  x.manifest = x.crossing ∧ x.crossing = x.seed

theorem balanced_rotate_iff (x : TriNumber α) :
    Balanced (rotate x) ↔ Balanced x := by
  cases x
  simp [Balanced, rotate]
  aesop

/-- The symmetric total vanishes. -/
def ZeroSum [Add α] [Zero α] (x : TriNumber α) : Prop :=
  total x = 0

theorem zeroSum_rotate_iff [AddCommMonoid α] (x : TriNumber α) :
    ZeroSum (rotate x) ↔ ZeroSum x := by
  simp [ZeroSum, total_rotate]

/-- A distinguished one-phase basis state. -/
def manifestBasis [Zero α] [One α] : TriNumber α :=
  cyclicOne

/-- The other phase basis states are rotations of Manifest. -/
def crossingBasis [Zero α] [One α] : TriNumber α :=
  rotate manifestBasis

def seedBasis [Zero α] [One α] : TriNumber α :=
  rotate crossingBasis

theorem basis_cycle [Zero α] [One α] :
    rotate seedBasis = (manifestBasis : TriNumber α) := by
  simp [seedBasis, crossingBasis, manifestBasis, rotate, cyclicOne]

/-- Product topology inherited from α³. -/
def toProduct (x : TriNumber α) : α × α × α :=
  (x.manifest, x.crossing, x.seed)

instance [TopologicalSpace α] : TopologicalSpace (TriNumber α) :=
  TopologicalSpace.induced toProduct inferInstance

end TriNumber

/-- A formal ratio.  It deliberately does not identify division-by-zero forms
with ordinary field elements. -/
structure FormalRatio (α : Type*) where
  numerator : α
  denominator : α
  deriving Repr

namespace FormalRatio

variable {α : Type*}

def evaluable [Zero α] (r : FormalRatio α) : Prop :=
  r.denominator ≠ 0

def zeroOverZero [Zero α] : FormalRatio α where
  numerator := 0
  denominator := 0

/-- Formal I = 0/0.  This is an indeterminate form, not field division. -/
abbrev I [Zero α] : FormalRatio α :=
  zeroOverZero

theorem zeroOverZero_not_evaluable [Zero α] :
    ¬ evaluable (zeroOverZero : FormalRatio α) := by
  simp [evaluable, zeroOverZero]

end FormalRatio

/-- Classification of the material numerical forms introduced by this kernel. -/
inductive MaterialNumberClass where
  | scalar
  | triStable
  | balancedTriStable
  | zeroSumTriStable
  | formalSingularRatio
  deriving DecidableEq, Repr

end MCore.MaterialMath
