import MCore.YangMills.A1.RegulatedConstruction

namespace MCore.YangMills.A1

open MeasureTheory

/-- Typed gauge invariance of every regulated measure. This replaces the
opaque proposition at the certification boundary. -/
structure MeasureInvariance (C : RegulatedYM4Construction) : Prop where
  measurableGauge :
    ∀ a L g, @Measurable (C.fiber a L).State (C.fiber a L).State
      (C.fiber a L).measurable (C.fiber a L).measurable (C.GaugeAction a L g)
  map_eq :
    ∀ a L g,
      @Measure.map (C.fiber a L).State (C.fiber a L).State
        (C.fiber a L).measurable (C.fiber a L).measurable
        (C.GaugeAction a L g) (C.fiber a L).measure =
        (C.fiber a L).measure

/-- Typed gauge invariance of every regulated observable. -/
structure ObservableInvariance (C : RegulatedYM4Construction) : Prop where
  invariant :
    ∀ a L (O : C.Signature.Observable) (g : C.Signature.GaugeGroup)
      (x : (C.fiber a L).State),
      C.observable a L O (C.GaugeAction a L g x) =
        C.observable a L O x

/-- Reflection positivity is kept as an explicit sesquilinear test rather than
an opaque proposition. The concrete reflection map and test algebra remain
scientific data of the regulated construction. -/
structure ReflectionPositivityData (C : RegulatedYM4Construction) where
  Test : Type
  reflect : Test → Test
  pairing : Test → Test → ℂ
  hermitianReflection : ∀ f, pairing (reflect f) f = star (pairing f (reflect f))
  nonnegative : ∀ f, 0 ≤ (pairing (reflect f) f).re

/-- Minimal typed transfer-operator contract at A1. The Hilbert realization is
data, while positivity/self-adjointness/contraction are explicit laws. -/
structure PositiveTransferData (C : RegulatedYM4Construction) where
  State : Type
  [instNormedAddCommGroup : NormedAddCommGroup State]
  [instInnerProductSpace : InnerProductSpace ℂ State]
  transfer : State →L[ℂ] State
  positive : ∀ x, 0 ≤ (inner x (transfer x) : ℂ).re
  symmetric : ∀ x y, (inner (transfer x) y : ℂ) = inner x (transfer y)
  contraction : ∀ x, ‖transfer x‖ ≤ ‖x‖

attribute [instance] PositiveTransferData.instNormedAddCommGroup
attribute [instance] PositiveTransferData.instInnerProductSpace

/-- The hardened A1 endpoint. None of the four scientific laws can be closed by
supplying a bare Prop. -/
structure A1ScientificWitness (C : RegulatedYM4Construction) where
  measureInvariance : MeasureInvariance C
  observableInvariance : ObservableInvariance C
  reflectionPositivity : ReflectionPositivityData C
  positiveTransfer : PositiveTransferData C
  uniformity : UniformRegulatorControl C

def A1ScientificOpenBridge (C : RegulatedYM4Construction) : Prop :=
  Nonempty (A1ScientificWitness C)

theorem a1_witness_supplies_uniformity {C : RegulatedYM4Construction}
    (W : A1ScientificWitness C) : A1UniformityBridge C :=
  ⟨W.uniformity⟩

end MCore.YangMills.A1
