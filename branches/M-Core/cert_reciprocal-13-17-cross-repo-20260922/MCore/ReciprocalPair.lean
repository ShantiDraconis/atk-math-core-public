namespace MCore

/-- Exact fraction syntax. No floating point and no cryptographic claim. -/
structure ExactFraction where
  num : Nat
  den : Nat
  deriving DecidableEq, Repr

namespace ExactFraction

/-- Exact multiplication before normalization. -/
def mul (a b : ExactFraction) : ExactFraction :=
  ⟨a.num * b.num, a.den * b.den⟩

/-- Exact addition before normalization. -/
def add (a b : ExactFraction) : ExactFraction :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

/-- Exact quotient transformation a/b for fraction representatives. -/
def div (a b : ExactFraction) : ExactFraction :=
  ⟨a.num * b.den, a.den * b.num⟩

/-- A raw fraction represents one when numerator and denominator coincide. -/
def representsOne (a : ExactFraction) : Prop := a.num = a.den

end ExactFraction

/-- Endpoint representatives requested by the model: 13/1 and 17/1. -/
def endpoint13 : ExactFraction := ⟨13, 1⟩
def endpoint17 : ExactFraction := ⟨17, 1⟩

/-- The exact forward projection (13/1)/(17/1). -/
def forward13_17 : ExactFraction := ExactFraction.div endpoint13 endpoint17

/-- The exact reverse projection (17/1)/(13/1). -/
def reverse17_13 : ExactFraction := ExactFraction.div endpoint17 endpoint13

/-- Orientation-independent exact sum of the two reciprocal directions. -/
def symmetric13_17 : ExactFraction := ExactFraction.add forward13_17 reverse17_13

/-- Exact product of the two reciprocal directions. -/
def closure13_17 : ExactFraction := ExactFraction.mul forward13_17 reverse17_13

theorem endpoint_projection_forward :
    forward13_17 = ⟨13, 17⟩ := by
  rfl

theorem endpoint_projection_reverse :
    reverse17_13 = ⟨17, 13⟩ := by
  rfl

/-- (13/17)(17/13) has equal numerator and denominator: exact closure at 1. -/
theorem reciprocal_closure_represents_one :
    ExactFraction.representsOne closure13_17 := by
  rfl

theorem reciprocal_closure_exact :
    closure13_17 = ⟨221, 221⟩ := by
  rfl

/-- 13/17 + 17/13 = 458/221 exactly, before any decimal approximation. -/
theorem symmetric_invariant_exact :
    symmetric13_17 = ⟨458, 221⟩ := by
  rfl

/-- Swapping the two endpoints swaps the two orientations exactly. -/
theorem orientation_pair_exact :
    (forward13_17, reverse17_13) = (⟨13, 17⟩, ⟨17, 13⟩) := by
  rfl

/--
The formal relation is a quotient transformation, not the false arithmetic
claim 13 = 17. The public invariant 458/221 is not a password, key, or entropy.
-/
structure ReciprocalPublicInvariant where
  forward : ExactFraction
  reverse : ExactFraction
  symmetric : ExactFraction
  closure : ExactFraction
  deriving DecidableEq, Repr

def reciprocalPublicInvariant13_17 : ReciprocalPublicInvariant where
  forward := forward13_17
  reverse := reverse17_13
  symmetric := symmetric13_17
  closure := closure13_17

theorem reciprocalPublicInvariant13_17_exact :
    reciprocalPublicInvariant13_17 =
      ⟨⟨13, 17⟩, ⟨17, 13⟩, ⟨458, 221⟩, ⟨221, 221⟩⟩ := by
  rfl

end MCore
