import MCore.MaterialMath.GlobalMaterialTheorem

namespace MCore.MaterialMath

noncomputable section

namespace TriNumber

/-- Euclidean inner product of the transverse fluctuations. -/
def transverseInner (x y : TriNumber ℝ) : ℝ :=
  (fluctuation x).manifest * (fluctuation y).manifest +
  (fluctuation x).crossing * (fluctuation y).crossing +
  (fluctuation x).seed * (fluctuation y).seed

/--
Exact transverse Lagrange identity:
E(x)E(y) = 3 torsion(x,y)^2 + 9 <x_perp,y_perp>^2.

Thus torsion is the oriented area observable of the transverse plane.
-/
theorem spread_product_eq_torsion_plus_transverseInner
    (x y : TriNumber ℝ) :
    spread x * spread y =
      3 * (torsion x y)^2 +
      9 * (transverseInner x y)^2 := by
  rcases x with ⟨xm,xc,xs⟩
  rcases y with ⟨ym,yc,ys⟩
  simp [spread, torsion, transverseInner, fluctuation, mean, total]
  ring

/-- Universal torsion-energy inequality. -/
theorem three_torsion_sq_le_spread_product
    (x y : TriNumber ℝ) :
    3 * (torsion x y)^2 ≤ spread x * spread y := by
  rw [spread_product_eq_torsion_plus_transverseInner]
  nlinarith [sq_nonneg (transverseInner x y)]

/--
Equality in the torsion-energy inequality occurs exactly when the transverse
fluctuations are orthogonal.
-/
theorem three_torsion_sq_eq_spread_product_iff
    (x y : TriNumber ℝ) :
    3 * (torsion x y)^2 = spread x * spread y ↔
      transverseInner x y = 0 := by
  rw [spread_product_eq_torsion_plus_transverseInner]
  constructor
  · intro h
    have hs : (transverseInner x y)^2 = 0 := by nlinarith
    exact sq_eq_zero_iff.mp hs
  · intro h
    rw [h]
    ring

/-- If both states have spread 3, then the squared torsion is at most 3. -/
theorem torsion_sq_le_one_of_spread_three
    (x y : TriNumber ℝ)
    (hx : spread x = 3)
    (hy : spread y = 3) :
    (torsion x y)^2 ≤ 3 := by
  have h := three_torsion_sq_le_spread_product x y
  rw [hx, hy] at h
  nlinarith

#print axioms MCore.MaterialMath.TriNumber.spread_product_eq_torsion_plus_transverseInner
#print axioms MCore.MaterialMath.TriNumber.three_torsion_sq_le_spread_product
#print axioms MCore.MaterialMath.TriNumber.three_torsion_sq_eq_spread_product_iff

end TriNumber

end

end MCore.MaterialMath
