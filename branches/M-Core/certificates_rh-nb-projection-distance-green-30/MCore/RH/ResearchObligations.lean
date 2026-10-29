import MCore.RH.BridgeInterfaces
import MCore.RH.GeometryDynamics

namespace MCore.RH

/-- Abstract quantitative approximation datum.  It deliberately does not
mention zeta or RH. -/
structure ApproximationDatum where
  error : ℕ → ℝ
  nonnegative : ∀ n, 0 ≤ error n

/-- The analytic content needed from an NB-style route: the approximation
error tends to zero.  Constructing such a datum from M-Core is the open bridge. -/
def ApproximationConverges (d : ApproximationDatum) : Prop :=
  Filter.Tendsto d.error Filter.atTop (nhds 0)

/-- A generic positive quadratic form interface.  Positivity alone is not RH;
an arithmetic identification theorem is separately required. -/
structure PositiveQuadraticForm (V : Type) where
  q : V → ℝ
  nonnegative : ∀ v, 0 ≤ q v

/-- Distinguishes physical time, positive scale, regularization epsilon, and
an independent deformation parameter.  No equality between them is assumed. -/
structure ParameterPoint where
  physicalTime : ℝ
  scale : PositiveScale
  epsilon : PositiveScale
  deformation : DeformationParameter

/-- A proposed multiscale error family.  A useful theorem must bound this
family and then prove a limit; merely defining it proves nothing about RH. -/
structure MultiscaleError where
  value : ℕ → ParameterPoint → ℝ
  nonnegative : ∀ n p, 0 ≤ value n p

/-- Pure logical endpoint for an NB-style route.  The difficult hypotheses
are explicit arguments, so this theorem contains no hidden scientific axiom. -/
theorem rh_of_mcore_nb
    {P NBCriterion RH : Prop}
    (mcore_to_nb : P → NBCriterion)
    (nb_to_rh : NBCriterion → RH)
    (hP : P) : RH :=
  nb_to_rh (mcore_to_nb hP)

/-- Pure logical endpoint for a Li/Weil-style positivity route. -/
theorem rh_of_mcore_positivity
    {P Positivity RH : Prop}
    (mcore_to_pos : P → Positivity)
    (pos_to_rh : Positivity → RH)
    (hP : P) : RH :=
  pos_to_rh (mcore_to_pos hP)

/-- Pure logical endpoint for a DBN-style route.  In an analytic
instantiation, `LambdaNonpositive` must really mean Lambda <= 0. -/
theorem rh_of_mcore_dbn
    {P LambdaNonpositive RH : Prop}
    (mcore_to_lambda_nonpositive : P → LambdaNonpositive)
    (lambda_nonpositive_to_rh : LambdaNonpositive → RH)
    (hP : P) : RH :=
  lambda_nonpositive_to_rh (mcore_to_lambda_nonpositive hP)

end MCore.RH
