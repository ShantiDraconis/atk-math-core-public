import Mathlib

/-!
# ATK-RH — Euler bound audit

This file separates exact algebra from unverified numerical inputs.
The rational numbers below are decimal REPORTS from an earlier calculation,
NOT kernel-certified values of Nyman–Beurling integrals.
No RH theorem is asserted.

Status: SOURCE_ONLY; Lean/lake were not available in this environment.
-/

namespace ATK.RH

/-- Ratio criterion, expressed without division. -/
def violates (E B : ℕ → ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * B n < E n

/-- A violation of at least 100% means E is at least twice nB. -/
def violates100 (E B : ℕ → ℝ) (n : ℕ) : Prop :=
  2 * ((n : ℝ) * B n) ≤ E n

/-- The first violating index, if one exists, is specified by a minimum property. -/
def IsFirstViolation (E B : ℕ → ℝ) (n : ℕ) : Prop :=
  violates E B n ∧ ∀ k < n, ¬ violates E B k

/-- A 100% violation entails an ordinary violation if the bound is positive. -/
theorem violates_of_violates100 (E B : ℕ → ℝ) (n : ℕ)
    (hB : 0 < B n) (hn : 0 < n) (h : violates100 E B n) :
    violates E B n := by
  unfold violates100 at h
  unfold violates
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < (n : ℝ) * B n := mul_pos hnR hB
  linarith

/-- Exact decimal inputs transcribed as rational numbers. -/
def reportedE23 : ℚ := 1557778 / 100000000
def reportedBound23 : ℚ := 822506 / 100000000
def reportedE24 : ℚ := 155508423 / 10000000000
def reportedBound24 : ℚ := 76812306 / 10000000000

/-- The reported N=23 decimals are below the 100% threshold. -/
theorem reported_23_below_double :
    reportedE23 < 2 * reportedBound23 := by
  norm_num [reportedE23, reportedBound23]

/-- The reported N=24 decimals exceed the 100% threshold. -/
theorem reported_24_above_double :
    2 * reportedBound24 < reportedE24 := by
  norm_num [reportedE24, reportedBound24]

/-- This checks only the arithmetic of the two reported decimal inputs. -/
theorem reported_24_exceeds_bound :
    reportedBound24 < reportedE24 := by
  norm_num [reportedE24, reportedBound24]

/-- Algebraic equivalence for the normalized-error condition. -/
theorem normalized_bound_iff (E B : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    E n / (n : ℝ) ≤ B n ↔ E n ≤ (n : ℝ) * B n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact (div_le_iff₀ hnR)


/-! ## Additional numerical reports (not proved equal to genuine E_n).
All `reportedError` entries are rounded observations copied from the conversation.
`reportedRatio` entries are ratio-only reports. They are not integral certificates.
-/

def reportedError : ℕ → Option ℚ
  | n => match n with
    | 1 => some (3835660243 / 12500000000)
    | 2 => some (957477839 / 10000000000)
    | 3 => some (329758471 / 5000000000)
    | 4 => some (363190179 / 10000000000)
    | 5 => some (181040173 / 5000000000)
    | 6 => some (243883679 / 10000000000)
    | 7 => some (242445253 / 10000000000)
    | 8 => some (602377 / 25000000)
    | 9 => some (477051 / 20000000)
    | 10 => some (51249 / 2500000)
    | 11 => some (409963 / 20000000)
    | 12 => some (62107 / 3125000)
    | 13 => some (1853181 / 100000000)
    | 14 => some (1470417187 / 80000000000)
    | 20 => some (1612419 / 100000000)
    | 21 => some (1609083 / 100000000)
    | 22 => some (194727 / 12500000)
    | 23 => some (778889 / 50000000)
    | 24 => some (155508423 / 10000000000)
    | 25 => some (772699 / 50000000)
    | 26 => some (767201 / 50000000)
    | 27 => some (1524421 / 100000000)
    | 28 => some (1473027 / 100000000)
    | 30 => some (291123 / 20000000)
    | _ => none

def reportedRatio : ℕ → Option ℚ
  | n => match n with
    | 15 => some (138827 / 125000)
    | 16 => some (1170947 / 1000000)
    | 17 => some (1286557 / 1000000)
    | 18 => some (1387409 / 1000000)
    | 19 => some (741409 / 500000)
    | 40 => some (9251 / 2500)
    | 50 => some (12857 / 2500)
    | 60 => some (67481 / 10000)
    | 70 => some (4249 / 500)
    | _ => none

/-- Recorded reports do not establish any fact about the L² integrals. -/
theorem reported_E24_is_recorded :
    reportedError 24 = some (155508423 / 10000000000 : ℚ) := by
  norm_num [reportedError]

end ATK.RH