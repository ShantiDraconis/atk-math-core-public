import Mathlib

/-!
# ATK — Poincaré / fluxo de Ricci: identidade na 3-esfera redonda

Para g = a² g_{S³}: R = 6/a² e Vol = 2π² a³, logo ∫ R dV = 12 π² a.
Com a² = a₀² - 4t isto confere V'(t) = -∫ R dV no fluxo de Ricci.

* `round_sphere_scalar_integral` — (6/a²)(2π² a³) = 12 π² a, para a > 0.
-/

namespace ATK.Geometry

theorem round_sphere_scalar_integral {a : ℝ} (ha : 0 < a) :
    (6 / a ^ 2) * (2 * Real.pi ^ 2 * a ^ 3) = 12 * Real.pi ^ 2 * a := by
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 ha.ne')]
  ring

end ATK.Geometry

#print axioms ATK.Geometry.round_sphere_scalar_integral
