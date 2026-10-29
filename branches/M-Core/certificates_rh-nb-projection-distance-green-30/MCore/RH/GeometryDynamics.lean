import Mathlib
import MCore.RH.Status

namespace MCore.RH

/-- A stage records a carrier and the dimension assigned by the model.
No embedding claim is hidden in this structure. -/
structure GeometricStage where
  Carrier : Type
  dimension : ℕ

/-- A certified embedding requires an actual injectivity proof. -/
structure CertifiedEmbedding (X Y : GeometricStage) where
  toFun : X.Carrier → Y.Carrier
  injective : Function.Injective toFun

/-- Positive scale, excluding the zero/negative-scale ambiguity. -/
def PositiveScale := {x : ℝ // 0 < x}

/-- Time is kept distinct from scale and from any DBN deformation parameter. -/
structure TimedScaledStage extends GeometricStage where
  Time : Type
  state : Time → Type
  scale : PositiveScale → Carrier → Carrier

/-- Two-parameter evolution with identity and composition laws. -/
structure Evolution (X : TimedScaledStage) where
  evolve : (t₁ t₂ : X.Time) → X.state t₁ → X.state t₂
  identity : ∀ (t : X.Time) (x : X.state t), evolve t t x = x
  composition : ∀ (t₁ t₂ t₃ : X.Time) (x : X.state t₁),
    evolve t₂ t₃ (evolve t₁ t₂ x) = evolve t₁ t₃ x

/-- A deformation parameter is deliberately a different type from physical time. -/
structure DeformationParameter where
  value : ℝ

end MCore.RH
