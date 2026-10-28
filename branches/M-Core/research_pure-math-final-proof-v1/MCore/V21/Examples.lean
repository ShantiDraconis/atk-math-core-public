import MCore.V21.CrossRepo
import MCore.V21.ResidueClassifier

namespace MCore.V21.Examples

theorem logical_two_edge_close
    (Start Middle Final : Prop)
    (hSM : Start → Middle)
    (hMF : Middle → Final) :
    Start → Final :=
  fun hs => hMF (hSM hs)

/-- These two quantifier shapes are deliberately distinct. No conversion
    theorem is provided because that would be a quantifier placebo. -/
def PerInstanceWitness
    (X Witness : Type*) (Good : X → Witness → Prop) : Prop :=
  ∀ x, ∃ w, Good x w

def UniformWitness
    (X Witness : Type*) (Good : X → Witness → Prop) : Prop :=
  ∃ w, ∀ x, Good x w

/-- Generic scaling law. The factor is explicit, so a numerical constant cannot
    silently replace a symbolic scaling rule. -/
def ScalingLaw
    {X : Type*}
    (scale : ℝ → X → X)
    (K : X → ℝ)
    (factor : ℝ → ℝ) : Prop :=
  ∀ (lam : ℝ) (x : X), lam ≠ 0 →
    K (scale lam x) = factor lam * K x

end MCore.V21.Examples
