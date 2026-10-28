import MCore.SpectralExclusion
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MCore

/-- Regulator-level transfer data, normalized in physical units.
No Yang--Mills witness is asserted here. -/
structure PhysicalTransferGapData where
  cutoff : ℝ
  volume : ℕ
  transferNorm : ℝ
  cutoff_pos : 0 < cutoff
  transferNorm_nonneg : 0 ≤ transferNorm
  transferNorm_le_one : transferNorm ≤ 1

/-- A normalization-safe physical lower bound.  It avoids requiring a
dimensionless one-step gap bounded away from zero as the cutoff tends to zero. -/
def PhysicalMassLowerBound (R : PhysicalTransferGapData) (m0 : ℝ) : Prop :=
  0 < m0 ∧ R.transferNorm ≤ Real.exp (-R.cutoff * m0)

/-- Uniformity over cutoff and volume is part of the scientific input. -/
def UniformPhysicalMassLowerBound
    (R : ℝ → ℕ → PhysicalTransferGapData) (m0 a0 : ℝ) : Prop :=
  0 < m0 ∧ 0 < a0 ∧
    ∀ (a : ℝ) (L : ℕ), 0 < a → a < a0 →
      (R a L).cutoff = a ∧ PhysicalMassLowerBound (R a L) m0

/-- The one-step physical bound propagates mechanically to every integer
separation.  This is the exact algebra needed for d = n*a. -/
theorem physical_mass_bound_iterates
    (q a m0 : ℝ) (n : ℕ)
    (hq : 0 ≤ q)
    (hstep : q ≤ Real.exp (-a * m0)) :
    q ^ n ≤ Real.exp (-((n : ℝ) * a) * m0) := by
  have hpow : q ^ n ≤ (Real.exp (-a * m0)) ^ n :=
    pow_le_pow_left₀ hq hstep n
  calc
    q ^ n ≤ (Real.exp (-a * m0)) ^ n := hpow
    _ = Real.exp ((n : ℝ) * (-a * m0)) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (-((n : ℝ) * a) * m0) := by
      congr 1
      ring

/-- F4: positivity at every finite volume does not imply a positive
volume-uniform lower bound. -/
theorem finite_volume_gap_not_uniform :
    ∃ gamma : ℕ → ℝ,
      (∀ L, 0 < gamma L) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ L, c ≤ gamma L :=
  pointwise_pos_not_uniform

/-- F5: positivity for every cutoff does not control the physical ratio
gamma(a)/a.  The explicit family gamma(a)=a^2 has gamma(a)>0 for a>0,
while gamma(a)/a=a can be arbitrarily small. -/
theorem positive_cutoff_gap_not_physical_uniform :
    ∃ gamma : ℝ → ℝ,
      (∀ a : ℝ, 0 < a → 0 < gamma a) ∧
      ¬ ∃ m0 : ℝ, 0 < m0 ∧
        ∀ a : ℝ, 0 < a → a < 1 → m0 ≤ gamma a / a := by
  refine ⟨fun a => a ^ 2, ?_, ?_⟩
  · intro a ha
    positivity
  · rintro ⟨m0, hm0, hbound⟩
    let a : ℝ := min (1 / 2) (m0 / 2)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have ha1 : a < 1 := by
      dsimp [a]
      exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have ham : a < m0 := by
      dsimp [a]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hm0)
    have h := hbound a ha ha1
    have hsimp : a ^ 2 / a = a := by
      rw [pow_two]
      exact mul_div_cancel_left₀ a (ne_of_gt ha)
    rw [hsimp] at h
    exact (not_lt_of_ge h) ham

/-- Scientific firewall: a Poincare/Dirichlet estimate becomes relevant to the
transfer Hamiltonian only after a proved comparison theorem.  This definition
records that missing implication rather than assuming the two gaps coincide. -/
def DirichletToTransferBridge
    (DirichletEstimate : Prop)
    (TransferPhysicalGap : Prop) : Prop :=
  DirichletEstimate → TransferPhysicalGap

end MCore
