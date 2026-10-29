import MCore.YangMills.A1.Hardening
import MCore.YangMills.A1.UniformityTriviality

namespace MCore.YangMills.A1

/-!
Adversarial audit of the A1 B3/B4 interfaces.

Both `ReflectionPositivityData C` and `PositiveTransferData C` currently use
`C` only as a phantom parameter: none of their laws connect their test/state
spaces or operators to `C.fiber`, `C.observable`, the regulator, or volume.
Therefore each admits a universal trivial inhabitant.

Combined with `UniformityTriviality.lean`, this proves that the current
`A1ScientificOpenBridge C` is equivalent to only B1 + B2.  This is a semantic
RED test for the current interface, not a physical Yang--Mills theorem.
-/

noncomputable def trivialReflectionPositivityForAnyConstruction
    (C : RegulatedYM4Construction) : ReflectionPositivityData C where
  Test := Unit
  reflect := id
  pairing := fun _ _ => 0
  hermitianReflection := fun _ => by simp
  nonnegative := fun _ => by simp

noncomputable def trivialPositiveTransferForAnyConstruction
    (C : RegulatedYM4Construction) : PositiveTransferData C where
  State := ℂ
  instNormedAddCommGroup := inferInstance
  instInnerProductSpace := inferInstance
  transfer := 0
  positive := fun _ => by simp
  symmetric := fun _ _ => by simp
  contraction := fun _ => by simp

theorem reflection_positivity_data_inhabited_for_every_construction
    (C : RegulatedYM4Construction) :
    Nonempty (ReflectionPositivityData C) :=
  ⟨trivialReflectionPositivityForAnyConstruction C⟩

theorem positive_transfer_data_inhabited_for_every_construction
    (C : RegulatedYM4Construction) :
    Nonempty (PositiveTransferData C) :=
  ⟨trivialPositiveTransferForAnyConstruction C⟩

theorem a1_scientific_open_bridge_iff_B1_B2
    (C : RegulatedYM4Construction) :
    A1ScientificOpenBridge C ↔
      (MeasureInvariance C ∧ ObservableInvariance C) := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.measureInvariance, W.observableInvariance⟩
  · rintro ⟨hMeasure, hObservable⟩
    exact ⟨{
      measureInvariance := hMeasure
      observableInvariance := hObservable
      reflectionPositivity := trivialReflectionPositivityForAnyConstruction C
      positiveTransfer := trivialPositiveTransferForAnyConstruction C
      uniformity := trivialUniformRegulatorControl C
    }⟩

end MCore.YangMills.A1
