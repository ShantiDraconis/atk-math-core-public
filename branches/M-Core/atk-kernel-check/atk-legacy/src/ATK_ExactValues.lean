import Mathlib

namespace ATKExactValues

-- Verified rational arithmetic targets; no open conjecture is asserted.
example : (2:ℚ) * 2 - 1 = 3 := by norm_num
example : (5:ℚ)/6 - 7/12 = 1/4 := by norm_num
example : ((7:ℚ)/12) / (5/6) = 7/10 := by norm_num
example : 1 - ((7:ℚ)/12) / (5/6) = 3/10 := by norm_num
example : (27:ℚ)/32 * 2 = 27/16 := by norm_num
example : (1:ℚ) - (1/4 + 1/3) = 5/12 := by norm_num
example : (1:ℚ)/2 + 1/3 = 5/6 := by norm_num

-- Formalizes algebraic absorption only; the analytic bounds remain assumptions.
theorem absorption (bulk tail rem nu z y cB cT C : ℝ)
    (hb : bulk ≤ cB * nu * z)
    (ht : tail ≤ cT * nu * z)
    (hr : rem ≤ C * y ^ 2) :
    bulk + tail + rem ≤ (cB + cT) * nu * z + C * y ^ 2 := by
  nlinarith [hb, ht, hr]

end ATKExactValues
