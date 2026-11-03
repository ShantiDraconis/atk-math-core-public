import MCore.MaterialMath.TriState.Spectral
import MCore.MaterialMath.Contraction

namespace MCore.MaterialMath

open TriNumber
open TriArithmetic
open TriSpectral

namespace TriHeat

/-- Fixed explicit dissipative step on real tri-numbers. -/
def halfStep (x : TriNumber ℝ) : TriNumber ℝ :=
  fun p => x p + (1 / 6 : ℝ) * TriNumber.laplacian x p

/-- On the balanced sector, the explicit step is exactly multiplication by 1/2. -/
theorem halfStep_eq_half_of_balanced
    {x : TriNumber ℝ}
    (h : TriNumber.Balanced x) :
    halfStep x = fun p => (1 / 2 : ℝ) * x p := by
  have hspec := laplacian_eq_neg_three_of_balanced (α := ℝ) h
  funext p
  have hp := congrFun hspec p
  rw [halfStep, hp]
  ring

/-- The balanced sector is invariant under the dissipative step. -/
theorem halfStep_balanced
    {x : TriNumber ℝ}
    (h : TriNumber.Balanced x) :
    TriNumber.Balanced (halfStep x) := by
  rw [halfStep_eq_half_of_balanced h]
  unfold TriNumber.Balanced TriNumber.phaseSum
  have hs : x .seed + x .passage + x .manifest = 0 := h
  simp
  linarith

/-- Iterated dissipative evolution. -/
def iterate : Nat → TriNumber ℝ → TriNumber ℝ
  | 0, x => x
  | n + 1, x => halfStep (iterate n x)

/-- Balanced data remain balanced for all iterations. -/
theorem iterate_balanced
    {x : TriNumber ℝ}
    (h : TriNumber.Balanced x) :
    ∀ n, TriNumber.Balanced (iterate n x) := by
  intro n
  induction n with
  | zero =>
      simpa [iterate] using h
  | succ n ih =>
      simpa [iterate] using halfStep_balanced ih

/-- Exact closed form: every balanced mode decays by 2^{-n}. -/
theorem iterate_closed_form
    {x : TriNumber ℝ}
    (h : TriNumber.Balanced x) :
    ∀ n p,
      iterate n x p = (1 / 2 : ℝ) ^ n * x p := by
  intro n
  induction n with
  | zero =>
      intro p
      simp [iterate]
  | succ n ih =>
      intro p
      have hb : TriNumber.Balanced (iterate n x) := iterate_balanced h n
      have hs := congrFun (halfStep_eq_half_of_balanced hb) p
      rw [iterate, hs, ih p, pow_succ]
      ring

/-- Each phase coordinate of a balanced mode vanishes at infinity. -/
theorem iterate_coordinate_vanishes
    {x : TriNumber ℝ}
    (h : TriNumber.Balanced x)
    (p : Phase3) :
    VanishesAtInfinity (fun n => iterate n x p) := by
  intro ε hε
  by_cases hx : x p = 0
  · refine ⟨0, ?_⟩
    intro n hn
    rw [iterate_closed_form h n p, hx, mul_zero, abs_zero]
    exact le_of_lt hε
  · have hhalf : |(1 / 2 : ℝ)| < 1 := by norm_num
    have hpow :
        Tendsto (fun n : Nat => |(1 / 2 : ℝ)| ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one hhalf
    have hpos : 0 < ε / |x p| := div_pos hε (abs_pos.mpr hx)
    rcases (Metric.tendsto_atTop.1 hpow) (ε / |x p|) hpos with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hp := hN n hn
    rw [iterate_closed_form h n p, abs_mul, abs_pow]
    have hxnonneg : 0 ≤ |x p| := abs_nonneg _
    have hle : |(1 / 2 : ℝ)| ^ n ≤ ε / |x p| := le_of_lt hp
    calc
      |(1 / 2 : ℝ)| ^ n * |x p|
          ≤ (ε / |x p|) * |x p| :=
            mul_le_mul_of_nonneg_right hle hxnonneg
      _ = ε := by
        field_simp [abs_ne_zero.mpr hx]

end TriHeat

end MCore.MaterialMath
