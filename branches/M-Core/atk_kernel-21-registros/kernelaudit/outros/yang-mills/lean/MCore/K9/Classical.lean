namespace MCore.K9

/-- Minimal algebraic interface for the classical Yang--Mills layer.
    K9 deliberately avoids pretending that differential geometry or
    quantization has already been constructed. -/
structure ClassicalGaugeData where
  GaugeGroup : Type
  BaseSpace : Type
  Connection : Type
  Curvature : Connection → Type

/-- A typed gauge action. Its laws are data to be certified separately. -/
structure GaugeAction (D : ClassicalGaugeData) where
  GaugeTransformation : Type
  act : GaugeTransformation → D.Connection → D.Connection

/-- Covariant derivative interface on curvature-valued objects. -/
structure CovariantDerivative (D : ClassicalGaugeData) where
  derivative : (A : D.Connection) → D.Curvature A → Type

/-- Bianchi is represented as an explicit proposition supplied by a concrete
    geometric realization; it is not postulated globally as an axiom. -/
def BianchiProperty (D : ClassicalGaugeData) (CD : CovariantDerivative D)
    (A : D.Connection) (F : D.Curvature A) : Prop :=
  Nonempty (CD.derivative A F)

end MCore.K9
