import MCore.MaterialMath.InternalTerminalProducers
import MCore.MaterialMath.TriState.HeatFlow
import MCore.MaterialMath.TriState.SymmetricAlgebra
import MCore.MaterialMath.TriState.OperationalAlgebra
import MCore.MaterialMath.TriState.MetricTopology

namespace MCore.MaterialMath

open Phase3
open TriNumber
open TriDynamics
open TriArithmetic
open TriSpectral
open TriSymmetric
open TriAlgebra
open TriHeat

/-- A completely closed mathematical root for the new tri-state theory.

No field is an open conjecture, no field is an alias for a Millennium-problem
endpoint, and no field requires an external mathematical hypothesis.
-/
structure UnconditionalMaterialRoot where
  phasePeriodThree :
    ∀ p : Phase3,
      Phase3.rotate (Phase3.rotate (Phase3.rotate p)) = p
  oneStepNoFixedPoint :
    ¬ HasFixedPoint Phase3.rotate
  distinctPhaseGap :
    ∀ {p q : Phase3}, p ≠ q →
      Phase3.cyclicDistance p q = 1
  ultrametric :
    ∀ p q r : Phase3,
      Phase3.cyclicDistance p r ≤
        max (Phase3.cyclicDistance p q) (Phase3.cyclicDistance q r)
  laplacianBalanced :
    ∀ x : TriNumber ℝ,
      TriNumber.Balanced (TriNumber.laplacian x)
  harmonicCoherent :
    ∀ x : TriNumber ℝ,
      TriDynamics.Harmonic x ↔ TriNumber.Coherent x
  centeredEigenmode :
    ∀ x : TriNumber ℝ,
      TriNumber.laplacian (TriArithmetic.center x) =
        fun p => (-3 : ℝ) * TriArithmetic.center x p
  characteristicInvariant :
    ∀ (x : TriNumber ℤ) (t : ℤ),
      TriSymmetric.characteristic (TriNumber.rotate x) t = TriSymmetric.characteristic x t
  I3Balanced : TriNumber.Balanced I3
  I3Nondegenerate : TriNumber.Nondegenerate I3
  I3OrbitDistinct :
    I3 ≠ J3 ∧ J3 ≠ K3 ∧ K3 ≠ I3
  I3HeatClosedForm :
    ∀ n p,
      iterate n (fun q => (I3 q : ℝ)) p =
        (1 / 2 : ℝ) ^ n * (I3 p : ℝ)
  internalProducers : InternalProducerSuite

/-- Real-valued embedding of I3. -/
def I3Real : TriNumber ℝ :=
  fun p => (I3 p : ℝ)

theorem I3Real_balanced :
    TriNumber.Balanced I3Real := by
  norm_num [I3Real, TriNumber.Balanced, TriNumber.phaseSum, I3]

theorem I3Real_heat_closed_form :
    ∀ n p,
      iterate n I3Real p =
        (1 / 2 : ℝ) ^ n * I3Real p :=
  iterate_closed_form I3Real_balanced

/-- Every coordinate of the distinguished I3 state vanishes under the
unconditional dissipative evolution. -/
theorem I3Real_heat_vanishes (p : Phase3) :
    VanishesAtInfinity (fun n => iterate n I3Real p) :=
  iterate_coordinate_vanishes I3Real_balanced p

/-- Closed inhabitant of the entire new material theory. -/
def unconditionalMaterialRoot : UnconditionalMaterialRoot where
  phasePeriodThree := Phase3.rotate_three
  oneStepNoFixedPoint := rotate_has_no_fixedPoint
  distinctPhaseGap := fun h => Phase3.cyclicDistance_eq_one h
  ultrametric := Phase3.cyclicDistance_ultrametric
  laplacianBalanced := fun x => TriDynamics.laplacian_is_balanced x
  harmonicCoherent := fun x => TriDynamics.harmonic_iff_coherent
  centeredEigenmode := fun x => TriSpectral.laplacian_center x
  characteristicInvariant := fun x t => TriSymmetric.characteristic_rotate x t
  I3Balanced := I3_balanced
  I3Nondegenerate := I3_nondegenerate
  I3OrbitDistinct := orbit_three_distinct
  I3HeatClosedForm := by
    intro n p
    simpa [I3Real] using I3Real_heat_closed_form n p
  internalProducers := internalProducerSuite

theorem unconditionalMaterialRoot_inhabited :
    Nonempty UnconditionalMaterialRoot :=
  ⟨unconditionalMaterialRoot⟩

end MCore.MaterialMath
