import MCore.MaterialMath.TransverseContraction

namespace MCore.MaterialMath

noncomputable section

namespace TriNumber

/--
General transverse profile: the balanced component is fixed and the transverse
component is scaled by an arbitrary real sequence a_n.
-/
def profiledTransverseTrajectory
    (x : TriNumber ℝ)
    (a : Nat → ℝ)
    (n : Nat) : TriNumber ℝ :=
  add
    (balancedProjection x)
    (smul (a n) (fluctuation x))

/-- Exact phase-energy law for an arbitrary transverse profile. -/
theorem phaseEnergy_profiledTransverseTrajectory
    (x : TriNumber ℝ)
    (a : Nat → ℝ)
    (n : Nat) :
    phaseEnergy (profiledTransverseTrajectory x a n) =
      (a n)^2 * phaseEnergy x := by
  unfold phaseEnergy
  rw [spread_add_balanced_left
      (balancedProjection x)
      (smul (a n) (fluctuation x))
      (balancedProjection_is_balanced x)]
  rw [spread_smul]
  rw [spread_fluctuation]

/--
Any scalar transverse profile a_n -> 0 forces phase-energy vanishing.
This includes geometric decay, logarithmic decay such as 1/sqrt(log n), and
other problem-specific asymptotic scales once their convergence is proved.
-/
theorem phaseEnergy_profiledTransverseTrajectory_tendsto_zero
    (x : TriNumber ℝ)
    (a : Nat → ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => phaseEnergy (profiledTransverseTrajectory x a n))
      Filter.atTop (nhds 0) := by
  have hsq :
      Filter.Tendsto
        (fun n => (a n)^2)
        Filter.atTop (nhds (0^2 : ℝ)) :=
    ha.pow 2
  have hmul :
      Filter.Tendsto
        (fun n => (a n)^2 * phaseEnergy x)
        Filter.atTop (nhds ((0^2 : ℝ) * phaseEnergy x)) :=
    hsq.mul_const (phaseEnergy x)
  simpa [phaseEnergy_profiledTransverseTrajectory] using hmul

/--
Every proven vanishing transverse profile therefore yields a genuine F1 law.
-/
def profiledTransverseVanishingLaw
    (x : TriNumber ℝ)
    (a : Nat → ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds 0)) :
    VanishingLaw
      (fun n => phaseEnergy (profiledTransverseTrajectory x a n)) where
  nonneg := fun n => spread_nonneg _
  tendsToZero :=
    phaseEnergy_profiledTransverseTrajectory_tendsto_zero x a ha

#print axioms MCore.MaterialMath.TriNumber.phaseEnergy_profiledTransverseTrajectory
#print axioms MCore.MaterialMath.TriNumber.phaseEnergy_profiledTransverseTrajectory_tendsto_zero

end TriNumber

end

end MCore.MaterialMath
