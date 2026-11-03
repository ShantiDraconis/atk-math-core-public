import MCore.MaterialMath.TriCyclicSpectral
import Mathlib.Analysis.SpecificLimits.Basic

namespace MCore.MaterialMath

noncomputable section

namespace TriNumber

/--
Geometric transverse contraction.  The equilibrium component is frozen while
the zero-sum fluctuation is multiplied by q^n.
-/
def geometricTransverseTrajectory
    (x : TriNumber ℝ) (q : ℝ) (n : Nat) : TriNumber ℝ :=
  add
    (balancedProjection x)
    (smul (q ^ n) (fluctuation x))

/-- The geometric trajectory preserves the equilibrium mean exactly. -/
theorem geometricTransverseTrajectory_balancedProjection
    (x : TriNumber ℝ) (q : ℝ) (n : Nat) :
    balancedProjection (geometricTransverseTrajectory x q n) =
      balancedProjection x := by
  apply TriNumber.ext <;>
    simp [geometricTransverseTrajectory, balancedProjection, fluctuation, mean,
      total, add, smul]
  all_goals ring

/-- Exact scaling law for spread under scalar multiplication. -/
theorem spread_smul
    (a : ℝ) (x : TriNumber ℝ) :
    spread (smul a x) = a^2 * spread x := by
  rcases x with ⟨m,c,s⟩
  simp [spread, smul]
  ring

/-- Adding a balanced state does not change phase spread. -/
theorem spread_add_balanced_left
    (b t : TriNumber ℝ)
    (hb : Balanced b) :
    spread (add b t) = spread t := by
  rcases b with ⟨bm,bc,bs⟩
  rcases t with ⟨tm,tc,ts⟩
  rcases hb with ⟨h1,h2⟩
  change bm = bc at h1
  change bc = bs at h2
  subst bc
  subst bs
  simp [spread, add]
  ring

/--
Exact energy law for geometric transverse contraction:
E_n = q^(2n) E_0.
-/
theorem phaseEnergy_geometricTransverseTrajectory
    (x : TriNumber ℝ) (q : ℝ) (n : Nat) :
    phaseEnergy (geometricTransverseTrajectory x q n) =
      (q^2)^n * phaseEnergy x := by
  unfold phaseEnergy
  rw [spread_add_balanced_left
      (balancedProjection x)
      (smul (q ^ n) (fluctuation x))
      (balancedProjection_is_balanced x)]
  rw [spread_smul]
  rw [spread_fluctuation]
  ring

/--
For every contraction factor 0 <= q < 1, the transverse phase energy converges
geometrically to zero.
-/
theorem phaseEnergy_geometricTransverseTrajectory_tendsto_zero
    (x : TriNumber ℝ)
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    Filter.Tendsto
      (fun n => phaseEnergy (geometricTransverseTrajectory x q n))
      Filter.atTop (nhds 0) := by
  have hq2_nonneg : 0 ≤ q^2 := sq_nonneg q
  have hq2_lt_one : q^2 < 1 := by
    nlinarith
  have hp :
      Filter.Tendsto
        (fun n : Nat => (q^2)^n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq2_nonneg hq2_lt_one
  have hm :
      Filter.Tendsto
        (fun n : Nat => (q^2)^n * phaseEnergy x)
        Filter.atTop (nhds (0 * phaseEnergy x)) :=
    hp.mul_const (phaseEnergy x)
  simpa [phaseEnergy_geometricTransverseTrajectory] using hm

/-- Every strict geometric transverse contraction therefore supplies a genuine
F1 vanishing law. -/
def geometricTransverseVanishingLaw
    (x : TriNumber ℝ)
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    VanishingLaw
      (fun n => phaseEnergy (geometricTransverseTrajectory x q n)) where
  nonneg := fun n => spread_nonneg _
  tendsToZero :=
    phaseEnergy_geometricTransverseTrajectory_tendsto_zero x q hq0 hq1

/--
The same kernel also contains a genuine F2 coercive gap on normalized
transverse states, so the tri-cyclic core simultaneously supports
vanishing (F1) and positive-gap (F2) mechanisms without identifying them.
-/
theorem triCyclic_F1_F2_kernel :
    (∃ x : TriNumber ℝ, ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      Nonempty
        (VanishingLaw
          (fun n => phaseEnergy (geometricTransverseTrajectory x q n)))) ∧
    Nonempty
      (GapLaw
        (TriNumber ℝ)
        (fun x => ZeroSum x ∧ euclideanSquare x = 1)
        phaseLaplacianEnergy) := by
  refine ⟨?_, ⟨normalizedTransverseGapLaw⟩⟩
  let x : TriNumber ℝ := { manifest := 1, crossing := 0, seed := -1 }
  refine ⟨x, (1/2 : ℝ), by norm_num, by norm_num, ?_⟩
  exact ⟨geometricTransverseVanishingLaw x (1/2 : ℝ) (by norm_num) (by norm_num)⟩

#print axioms MCore.MaterialMath.TriNumber.phaseEnergy_geometricTransverseTrajectory
#print axioms MCore.MaterialMath.TriNumber.phaseEnergy_geometricTransverseTrajectory_tendsto_zero
#print axioms MCore.MaterialMath.TriNumber.triCyclic_F1_F2_kernel

end TriNumber

end

end MCore.MaterialMath
