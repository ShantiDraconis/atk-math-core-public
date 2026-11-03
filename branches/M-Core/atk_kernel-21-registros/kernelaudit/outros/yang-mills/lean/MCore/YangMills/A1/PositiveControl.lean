import MCore.YangMills.A1.Hardening

namespace MCore.YangMills.A1

open MeasureTheory Filter

/-!
Test-9 positive control for `A1ScientificWitness`.

This file decomposes the hardened endpoint into its five sub-bridges
(`MeasureInvariance`, `ObservableInvariance`, `ReflectionPositivityData`,
`PositiveTransferData`, `UniformRegulatorControl`) and constructs an explicit
witness for a single-point, trivial-gauge-group model. The point is *only*
to show the type `A1ScientificWitness` is inhabited — the same sanity check
the frontier protocol runs on Poincaré as a closed positive control — so that
a future failure to build a physical witness can be blamed on physics, not on
a vacuous or mistyped definition.

`toyConstruction` is not a Yang-Mills theory: the gauge group has one
element, the state space is a point, and `toyUniformity`'s estimate is the
identically-zero function. None of `positive_cutoff_gap_firewall`,
`finite_volume_gap_firewall`, or
`pointwise_cutoff_volume_positive_not_uniform` are contradicted by it: those
firewalls rule out a uniform bound for a *nontrivial* (nowhere-zero)
cutoff/volume estimate, which is exactly what a physical mass gap witness
would have to supply. `toy_a1_scientific_witness` therefore leaves
`A1ScientificOpenBridge` open for every construction whose estimate is not
degenerate; it only certifies that the boundary itself is well-formed.
-/

instance : MeasurableSpace Unit := ⊤

def toySignature : ModelSignature where
  Dimension := Unit
  GaugeGroup := Unit
  Regulator := ℝ
  Volume := ℕ
  Coupling := Unit
  Action := Unit
  Observable := Unit

noncomputable def toyFiber (_ : ℝ) (_ : ℕ) : RegulatedMeasureFiber where
  State := Unit
  measurable := inferInstance
  measure := Measure.dirac ()

noncomputable def toyConstruction : RegulatedYM4Construction where
  Signature := toySignature
  fiber := toyFiber
  admissible := fun _ _ => True
  GaugeAction := fun _ _ _ x => x
  ObservableValue := Unit
  observable := fun _ _ _ _ => ()
  gaugeInvariantMeasure := True
  gaugeInvariantObservables := True
  reflectionPositive := True
  positiveTransferOperator := True

theorem toy_measure_invariance : MeasureInvariance toyConstruction where
  measurableGauge := fun _ _ _ => measurable_id
  map_eq := fun _ _ _ => by
    show Measure.map (fun x : Unit => x) (Measure.dirac ()) = Measure.dirac ()
    exact Measure.map_dirac measurable_id ()

theorem toy_observable_invariance : ObservableInvariance toyConstruction where
  invariant := fun _ _ _ _ _ => rfl

noncomputable def toyReflectionPositivity : ReflectionPositivityData toyConstruction where
  Test := Unit
  reflect := id
  pairing := fun _ _ => 1
  hermitianReflection := fun _ => by simp
  nonnegative := fun _ => by simp

noncomputable def toyPositiveTransfer : PositiveTransferData toyConstruction where
  State := ℂ
  instNormedAddCommGroup := inferInstance
  instInnerProductSpace := inferInstance
  transfer := 0
  positive := fun _ => by simp
  symmetric := fun _ _ => by simp
  contraction := fun _ => by simp

noncomputable def toyLimitCoordinates : A1LimitCoordinates toyConstruction where
  cutoffValue := id
  volumeValue := fun (L : ℕ) => (L : ℝ)

/-- The degenerate (identically-zero) case explicitly excluded from counting
as a physical mass-gap estimate: it is uniform for the trivial reason that it
carries no gap at all. -/
noncomputable def toyUniformity : UniformRegulatorControl toyConstruction where
  coordinates := toyLimitCoordinates
  estimate := fun _ _ => 0
  nonnegative := fun _ _ => le_refl 0
  cutoffLimit := fun _ => tendsto_const_nhds
  volumeLimit := fun _ => tendsto_const_nhds
  jointLimit := tendsto_const_nhds

theorem toy_a1_scientific_witness : A1ScientificOpenBridge toyConstruction :=
  ⟨{ measureInvariance := toy_measure_invariance
     observableInvariance := toy_observable_invariance
     reflectionPositivity := toyReflectionPositivity
     positiveTransfer := toyPositiveTransfer
     uniformity := toyUniformity }⟩

end MCore.YangMills.A1
