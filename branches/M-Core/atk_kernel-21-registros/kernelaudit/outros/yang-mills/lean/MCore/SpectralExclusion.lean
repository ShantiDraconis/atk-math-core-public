import MCore.SpectralConcreteAdapter
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MCore

structure PositiveSpectralLaplaceData where
  laplace : ℝ → ℝ
  massBelow : ℝ → ℝ
  lowerBound : ∀ t r : ℝ, 0 ≤ t → 0 ≤ r →
    Real.exp (-t * r) * massBelow r ≤ laplace t

structure ExponentialDecayData (L : ℝ → ℝ) where
  C : ℝ
  m : ℝ
  C_nonneg : 0 ≤ C
  m_pos : 0 < m
  upperBound : ∀ t : ℝ, 0 ≤ t → L t ≤ C * Real.exp (-m * t)

/-- G1: exponential escape with an explicit witness.  No assumption `C ≥ q` is used. -/
theorem exponential_growth_escape
    (q : ℝ) (hq : 0 < q) (C : ℝ) (hC : 0 ≤ C)
    (m r : ℝ) (hmr : 0 < m - r) :
    ∃ t : ℝ, 0 ≤ t ∧ C < q * Real.exp ((m - r) * t) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · subst C
    exact ⟨0, le_rfl, by simpa using hq⟩
  · let a : ℝ := m - r
    let x : ℝ := C / q
    have ha : 0 < a := hmr
    have hx : 0 < x := div_pos hCpos hq
    let t : ℝ := max 0 (Real.log x / a) + 1
    have ht : 0 ≤ t := by
      dsimp [t]
      have hmax : 0 ≤ max 0 (Real.log x / a) := le_max_left _ _
      linarith
    have hdiv : Real.log x / a ≤ max 0 (Real.log x / a) := le_max_right _ _
    have hlog_le : Real.log x ≤ a * max 0 (Real.log x / a) := by
      simpa [mul_comm] using (div_le_iff₀ ha).mp hdiv
    have hlog_lt : Real.log x < a * t := by
      dsimp [t]
      nlinarith
    have hxexp : x < Real.exp (a * t) := by
      rw [← Real.exp_log hx]
      exact Real.exp_lt_exp.mpr hlog_lt
    have hmul : q * x < q * Real.exp (a * t) :=
      mul_lt_mul_of_pos_left hxexp hq
    have hqx : q * x = C := by
      dsimp [x]
      field_simp [ne_of_gt hq]
    refine ⟨t, ht, ?_⟩
    simpa [a, hqx] using hmul

/-- F3: pointwise positive rates need not have a positive uniform lower bound. -/
theorem pointwise_pos_not_uniform :
    ∃ m : ℕ → ℝ, (∀ n, 0 < m n) ∧ ¬ ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ m n := by
  refine ⟨fun n => 1 / (n + 1 : ℝ), ?_, ?_⟩
  · intro n
    positivity
  · rintro ⟨c, hc, hc_le⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / c)
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    have hn_base : 1 < (n : ℝ) * c := by
      have h := (div_lt_iff₀ hc).mp hn
      simpa [mul_comm] using h
    have hn_step : (n : ℝ) * c < (n + 1 : ℝ) * c := by
      have hnlt : (n : ℝ) < n + 1 := by norm_num
      exact mul_lt_mul_of_pos_right hnlt hc
    have hprod : 1 < (n + 1 : ℝ) * c := lt_trans hn_base hn_step
    have hlt : 1 / (n + 1 : ℝ) < c := by
      rw [div_lt_iff₀ hnpos]
      simpa [mul_comm] using hprod
    exact (not_lt_of_ge (hc_le n)) hlt

theorem positive_mass_below_rate_contradiction
    (q C m r t : ℝ)
    (hq : 0 < q) (hC : 0 ≤ C) (hgap : r < m) (ht : 0 ≤ t)
    (hlower : Real.exp (-t * r) * q ≤ C * Real.exp (-m * t))
    (hlarge : C < q * Real.exp ((m - r) * t)) : False := by
  have hem : 0 < Real.exp (m * t) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hlower (le_of_lt hem)
  have hid1 : Real.exp (-t * r) * Real.exp (m * t) =
      Real.exp ((m - r) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid2 : Real.exp (-m * t) * Real.exp (m * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hnorm : q * Real.exp ((m - r) * t) ≤ C := by
    calc
      q * Real.exp ((m - r) * t)
          = q * (Real.exp (-t * r) * Real.exp (m * t)) := by rw [hid1]
      _ = (Real.exp (-t * r) * q) * Real.exp (m * t) := by ring
      _ ≤ (C * Real.exp (-m * t)) * Real.exp (m * t) := hmul
      _ = C := by rw [mul_assoc, hid2, mul_one]
  exact (not_lt_of_ge hnorm) hlarge

theorem spectral_exclusion_at_subrate
    (S : PositiveSpectralLaplaceData)
    (D : ExponentialDecayData S.laplace)
    (r : ℝ) (hr0 : 0 ≤ r) (hrm : r < D.m) :
    S.massBelow r ≤ 0 := by
  by_contra h
  have hq : 0 < S.massBelow r := lt_of_not_ge h
  obtain ⟨t, ht, hlarge⟩ := exponential_growth_escape
    (S.massBelow r) hq D.C D.C_nonneg D.m r (sub_pos.mpr hrm)
  have hlower := S.lowerBound t r ht hr0
  have hupper := D.upperBound t ht
  have hchain : Real.exp (-t * r) * S.massBelow r ≤
      D.C * Real.exp (-D.m * t) := le_trans hlower hupper
  exact positive_mass_below_rate_contradiction
    (S.massBelow r) D.C D.m r t hq D.C_nonneg hrm ht hchain hlarge

/-- The growth witness is now discharged internally; the remaining S1 realization
contains only the positive spectral lower-bound law and exponential decay. -/
structure SpectralExclusionRealization where
  spectral : PositiveSpectralLaplaceData
  decay : ExponentialDecayData spectral.laplace

theorem realized_exclusion
    (R : SpectralExclusionRealization)
    (mass_nonneg : ∀ r : ℝ, 0 ≤ r → 0 ≤ R.spectral.massBelow r)
    (r : ℝ) (hr0 : 0 ≤ r) (hrm : r < R.decay.m) :
    R.spectral.massBelow r = 0 := by
  apply le_antisymm
  · exact spectral_exclusion_at_subrate R.spectral R.decay r hr0 hrm
  · exact mass_nonneg r hr0

end MCore
