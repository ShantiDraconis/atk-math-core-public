namespace MCore.MaterialMath

/--
Two-sided material resolution of a proposition P.

The positive and negative producers are concrete data types.  Classical
excluded middle for P cannot manufacture inhabitants of either producer type.
-/
structure TwoSidedMaterialResolution
    (P : Prop)
    (PositiveProducer NegativeProducer : Type) where
  positiveCloses : PositiveProducer → P
  negativeCloses : NegativeProducer → ¬ P

namespace TwoSidedMaterialResolution

variable {P : Prop}
variable {PositiveProducer NegativeProducer : Type}

/-- Positive material evidence closes the proposition. -/
theorem close_positive
    (R : TwoSidedMaterialResolution P PositiveProducer NegativeProducer)
    (h : Nonempty PositiveProducer) :
    P := by
  rcases h with ⟨p⟩
  exact R.positiveCloses p

/-- Negative material evidence closes the negation. -/
theorem close_negative
    (R : TwoSidedMaterialResolution P PositiveProducer NegativeProducer)
    (h : Nonempty NegativeProducer) :
    ¬ P := by
  rcases h with ⟨n⟩
  exact R.negativeCloses n

/--
A genuine material resolution certificate accepts either orientation, but
requires an inhabitant of one producer type.
-/
def MateriallyResolved
    (R : TwoSidedMaterialResolution P PositiveProducer NegativeProducer) : Prop :=
  Nonempty PositiveProducer ∨ Nonempty NegativeProducer

/-- Any material resolution produces one of the two mathematical outcomes. -/
theorem materiallyResolved_elim
    (R : TwoSidedMaterialResolution P PositiveProducer NegativeProducer)
    (h : R.MateriallyResolved) :
    P ∨ ¬ P := by
  rcases h with hp | hn
  · exact Or.inl (R.close_positive hp)
  · exact Or.inr (R.close_negative hn)

/--
If both material producers are inhabited, the adapters are inconsistent:
the kernel derives False.  "Both" is therefore an audit-failure state, not a
third truth value for P.
-/
theorem both_material_routes_contradict
    (R : TwoSidedMaterialResolution P PositiveProducer NegativeProducer)
    (hp : Nonempty PositiveProducer)
    (hn : Nonempty NegativeProducer) :
    False := by
  exact (R.close_negative hn) (R.close_positive hp)

/--
Fail-closed principle: the resolution interface itself does not contain an
inhabitant of either producer.
-/
structure MaterialResolutionCertificate
    (R : TwoSidedMaterialResolution P PositiveProducer NegativeProducer) where
  resolved : R.MateriallyResolved

end TwoSidedMaterialResolution

end MCore.MaterialMath
