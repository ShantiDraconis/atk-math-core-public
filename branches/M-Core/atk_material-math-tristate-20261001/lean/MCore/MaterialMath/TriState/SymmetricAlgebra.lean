import MCore.MaterialMath.TriState.Algebra

namespace MCore.MaterialMath

open Phase3
open TriNumber

namespace TriSymmetric

/-- First elementary symmetric invariant. -/
def e1 {α : Type*} [CommRing α] (x : TriNumber α) : α :=
  x .seed + x .passage + x .manifest

/-- Second elementary symmetric invariant. -/
def e2 {α : Type*} [CommRing α] (x : TriNumber α) : α :=
  x .seed * x .passage +
  x .passage * x .manifest +
  x .manifest * x .seed

/-- Third elementary symmetric invariant. -/
def e3 {α : Type*} [CommRing α] (x : TriNumber α) : α :=
  x .seed * x .passage * x .manifest

theorem e1_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    e1 (TriNumber.rotate x) = e1 x := by
  simp [e1, TriNumber.rotate, Phase3.rotate, add_assoc, add_comm, add_left_comm]

theorem e2_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    e2 (TriNumber.rotate x) = e2 x := by
  simp [e2, TriNumber.rotate, Phase3.rotate]
  ring

theorem e3_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    e3 (TriNumber.rotate x) = e3 x := by
  simp [e3, TriNumber.rotate, Phase3.rotate]
  ring

/-- Characteristic cubic associated with a tri-number. -/
def characteristic
    {α : Type*} [CommRing α]
    (x : TriNumber α) (t : α) : α :=
  t^3 - e1 x * t^2 + e2 x * t - e3 x

/-- The characteristic cubic is invariant under phase rotation. -/
theorem characteristic_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) (t : α) :
    characteristic (TriNumber.rotate x) t = characteristic x t := by
  simp [characteristic, e1_rotate, e2_rotate, e3_rotate]

/-- Every phase coordinate is a root of the characteristic cubic. -/
theorem characteristic_seed_zero
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    characteristic x (x .seed) = 0 := by
  simp [characteristic, e1, e2, e3]
  ring

theorem characteristic_passage_zero
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    characteristic x (x .passage) = 0 := by
  simp [characteristic, e1, e2, e3]
  ring

theorem characteristic_manifest_zero
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    characteristic x (x .manifest) = 0 := by
  simp [characteristic, e1, e2, e3]
  ring

/-- Rotation-invariant algebraic fingerprint. -/
structure Fingerprint (α : Type*) [CommRing α] where
  s1 : α
  s2 : α
  s3 : α

def fingerprint
    {α : Type*} [CommRing α]
    (x : TriNumber α) : Fingerprint α :=
  ⟨e1 x, e2 x, e3 x⟩

theorem fingerprint_rotate
    {α : Type*} [CommRing α]
    (x : TriNumber α) :
    fingerprint (TriNumber.rotate x) = fingerprint x := by
  apply Fingerprint.ext <;>
  simp [fingerprint, e1_rotate, e2_rotate, e3_rotate]


/-- Exact elementary invariants of the distinguished tri-state constant I3. -/
theorem I3_e1 : e1 I3 = 0 := by
  norm_num [e1, I3]

theorem I3_e2 : e2 I3 = -1 := by
  norm_num [e2, I3]

theorem I3_e3 : e3 I3 = 0 := by
  norm_num [e3, I3]

/-- The characteristic cubic of I3 is t^3 - t. -/
theorem I3_characteristic (t : Int) :
    characteristic I3 t = t^3 - t := by
  simp [characteristic, I3_e1, I3_e2, I3_e3]
  ring

/-- Factorized form of the I3 cubic. -/
theorem I3_characteristic_factorized (t : Int) :
    characteristic I3 t = t * (t - 1) * (t + 1) := by
  rw [I3_characteristic]
  ring

end TriSymmetric

end MCore.MaterialMath
