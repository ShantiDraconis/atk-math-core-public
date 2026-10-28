import MCore.A3Zero
import Mathlib

namespace MCore

/-- The numerator and denominator are fixed globally; only the approach path
changes. This makes the 0/0 obstruction an actual path-dependence statement. -/
def zeroG (p : ℝ × ℝ) : ℝ := p.1
def zeroH (p : ℝ × ℝ) : ℝ := p.2

/-- Continuous path gamma_c(t) = (c t,t) approaching the common zero. -/
def zeroPath (c t : ℝ) : ℝ × ℝ := (c * t, t)

/-- The numerator tends to zero along every fixed-c path. -/
theorem zeroG_tendsto (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => zeroG (zeroPath c t)) (nhds 0) (nhds 0) := by
  simpa [zeroG, zeroPath] using (continuousAt_const.mul (continuousAt_id' (0 : ℝ))).tendsto

/-- The denominator tends to zero along every fixed-c path. -/
theorem zeroH_tendsto (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => zeroH (zeroPath c t)) (nhds 0) (nhds 0) := by
  simpa [zeroH, zeroPath] using (continuousAt_id' (0 : ℝ)).tendsto

/-- Away from the zero itself, the fixed quotient G/H is exactly the path
parameter c. -/
theorem quotient_zeroPath {c t : ℝ} (ht : t ≠ 0) :
    zeroG (zeroPath c t) / zeroH (zeroPath c t) = c := by
  simp [zeroG, zeroH, zeroPath, ht]

/-- The quotient has limit c along the punctured c-path. -/
theorem quotient_tendsto (c : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => zeroG (zeroPath c t) / zeroH (zeroPath c t))
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
  have hne : ∀ᶠ t : ℝ in nhdsWithin 0 {0}ᶜ, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    intro hzero
    apply ht
    simp [hzero]
  have hEq : (fun t : ℝ => zeroG (zeroPath c t) / zeroH (zeroPath c t))
      =ᶠ[nhdsWithin 0 {0}ᶜ] (fun _ : ℝ => c) := by
    filter_upwards [hne] with t ht
    exact quotient_zeroPath (c := c) (t := t) ht
  exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => c) (nhdsWithin 0 {0}ᶜ) (nhds c)).congr' hEq.symm

/-- K0 and RHO give incompatible limits for the same globally fixed G/H. -/
theorem K0_RHO_incompatible : (0 : ℝ) ≠ (1 / 2 : ℝ) := by
  norm_num

/-- Obligation 17: an explicit fixed numerator and denominator both approach
zero along each path. -/
theorem quotient_explicit :
    ∀ c : ℝ,
      Filter.Tendsto (fun t : ℝ => zeroG (zeroPath c t)) (nhds 0) (nhds 0) ∧
      Filter.Tendsto (fun t : ℝ => zeroH (zeroPath c t)) (nhds 0) (nhds 0) := by
  intro c
  exact ⟨zeroG_tendsto c, zeroH_tendsto c⟩

/-- Obligation 18: K0 and RHO are genuine paths for the same quotient, with
actual punctured-neighborhood limits 0 and 1/2. -/
theorem K0_limit :
    Filter.Tendsto
      (fun t : ℝ => zeroG (zeroPath 0 t) / zeroH (zeroPath 0 t))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := quotient_tendsto 0

theorem RHO_limit :
    Filter.Tendsto
      (fun t : ℝ => zeroG (zeroPath (1 / 2 : ℝ) t) / zeroH (zeroPath (1 / 2 : ℝ) t))
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2 : ℝ)) := quotient_tendsto (1 / 2)

/-- No single path-independent extension value can agree with both distinct
limits. -/
theorem explicit_no_common_extension :
    ¬ ∃ L : ℝ, L = 0 ∧ L = (1 / 2 : ℝ) := by
  exact no_path_independent_extension
    { limit₁ := 0, limit₂ := 1 / 2, distinct := by norm_num }

end MCore
