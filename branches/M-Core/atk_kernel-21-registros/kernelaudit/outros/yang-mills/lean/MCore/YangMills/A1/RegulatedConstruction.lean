import Mathlib
import MCore.K24

namespace MCore.YangMills.A1

open Filter Topology

inductive ImportStatus
  | adapted
  | analogyOnly
  | openBridge
deriving DecidableEq, Repr

structure ModelSignature where
  Dimension : Type
  GaugeGroup : Type
  Regulator : Type
  Volume : Type
  Coupling : Type
  Action : Type
  Observable : Type

structure RegulatedMeasureFiber where
  State : Type
  measurable : MeasurableSpace State
  measure : @MeasureTheory.Measure State measurable

structure RegulatedYM4Construction where
  Signature : ModelSignature
  fiber : Signature.Regulator → Signature.Volume → RegulatedMeasureFiber
  admissible : Signature.Regulator → Signature.Volume → Prop
  GaugeAction :
    ∀ a L, Signature.GaugeGroup → (fiber a L).State → (fiber a L).State
  ObservableValue : Type
  observable :
    ∀ a L, Signature.Observable → (fiber a L).State → ObservableValue
  gaugeInvariantMeasure : Prop
  gaugeInvariantObservables : Prop
  reflectionPositive : Prop
  positiveTransferOperator : Prop

/-- A1 uses explicit real coordinates for the limiting directions. The maps
keep the construction's regulator/volume types distinct from their numerical
scales. -/
structure A1LimitCoordinates (C : RegulatedYM4Construction) where
  cutoffValue : C.Signature.Regulator → ℝ
  volumeValue : C.Signature.Volume → ℝ

/-- Hardened A1 uniformity: the scientific content is no longer three opaque
Props. Both one-variable limits and the joint cutoff/volume limit are explicit.
The joint limit is the compatibility requirement that prevents stitching
unrelated theorems from different regulated models. -/
structure UniformRegulatorControl (C : RegulatedYM4Construction) where
  coordinates : A1LimitCoordinates C
  estimate : C.Signature.Regulator → C.Signature.Volume → ℝ
  nonnegative : ∀ a L, 0 ≤ estimate a L
  cutoffLimit :
    ∀ L, Tendsto (fun a => estimate a L)
      (comap coordinates.cutoffValue (nhdsWithin 0 (Set.Ioi 0))) (nhds 0)
  volumeLimit :
    ∀ a, Tendsto (fun L => estimate a L)
      (comap coordinates.volumeValue atTop) (nhds 0)
  jointLimit :
    Tendsto (fun p : C.Signature.Regulator × C.Signature.Volume =>
      estimate p.1 p.2)
      ((comap coordinates.cutoffValue (nhdsWithin 0 (Set.Ioi 0))) ×ˢ
       (comap coordinates.volumeValue atTop))
      (nhds 0)

/-- Possessing pointwise regulated constructions does not manufacture this
witness. -/
def A1UniformityBridge (C : RegulatedYM4Construction) : Prop :=
  Nonempty (UniformRegulatorControl C)

structure SignatureAdapter (A B : ModelSignature) where
  dimensionCompatible : Prop
  gaugeGroupCompatible : Prop
  regulatorCompatible : Prop
  volumeCompatible : Prop
  couplingCompatible : Prop
  actionCompatible : Prop
  observableCompatible : Prop

def SignatureAdapter.Valid {A B : ModelSignature}
    (T : SignatureAdapter A B) : Prop :=
  T.dimensionCompatible ∧
  T.gaugeGroupCompatible ∧
  T.regulatorCompatible ∧
  T.volumeCompatible ∧
  T.couplingCompatible ∧
  T.actionCompatible ∧
  T.observableCompatible

theorem adapter_requires_all_coordinates
    {A B : ModelSignature} (T : SignatureAdapter A B)
    (h : T.Valid) :
    T.dimensionCompatible ∧ T.gaugeGroupCompatible ∧
    T.regulatorCompatible ∧ T.volumeCompatible ∧
    T.couplingCompatible ∧ T.actionCompatible ∧
    T.observableCompatible := h

def PointwiseToUniformBridge (C : RegulatedYM4Construction) : Prop :=
  (∀ a L, C.admissible a L → Nonempty (C.fiber a L).State) →
  A1UniformityBridge C

structure A1Certificate where
  construction : RegulatedYM4Construction
  uniformity : UniformRegulatorControl construction

structure LegacyK24Adapter
    (C : RegulatedYM4Construction)
    (R : K24RegulatorFamily)
    (P : K24RegulatedMeasureProblem R) where
  cutoffMap : C.Signature.Regulator → R.Cutoff
  volumeMap : C.Signature.Volume → R.Volume
  existence : P.existsOnAdmissible
  gaugeSector : P.gaugeInvariantSector
  reflection : P.reflectionPositiveOnAdmissible
  cutoffTight : P.cutoffTightness
  volumeTight : P.volumeTightness

def UniformityPromotionWouldRequire
    (C : RegulatedYM4Construction) : Prop :=
  PointwiseToUniformBridge C

end MCore.YangMills.A1
