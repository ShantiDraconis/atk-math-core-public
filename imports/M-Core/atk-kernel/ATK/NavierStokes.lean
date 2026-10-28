import Mathlib

/-!
# ATK — Navier–Stokes: absorção e comparação de Riccati

Enunciados auxiliares (não a regularidade global 3D):
* `absorption`            — se B ≤ c_B ν z, T ≤ c_T ν z, R ≤ C y², sobra a margem (1 - c_B - c_T) ν z.
* `absorption_margin_pos` — c_B + c_T < 1 ⇒ δ = 1 - c_B - c_T > 0.
* `riccati_comparison`    — y' ≤ 2 C y² e y > 0 em [0,T] ⇒ 1/y(t) ≥ 1/y(0) - 2 C t.
* `riccati_upper_bound`   — enquanto 1 - 2 C y(0) t > 0, y(t) ≤ y(0) / (1 - 2 C y(0) t).

O limite superior pode explodir em tempo finito: isto é uma estimativa local.
-/

namespace ATK.NavierStokes

open Set

theorem absorption {ν z y y' B T R cB cT C : ℝ}
    (hE : y' / 2 + ν * z ≤ B + T + R)
    (hB : B ≤ cB * ν * z) (hT : T ≤ cT * ν * z) (hR : R ≤ C * y ^ 2) :
    y' / 2 + (1 - cB - cT) * ν * z ≤ C * y ^ 2 := by
  linarith

theorem absorption_margin_pos {cB cT : ℝ} (h : cB + cT < 1) : 0 < 1 - cB - cT := by
  linarith

theorem riccati_comparison {y y' : ℝ → ℝ} {C T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t ∈ Icc 0 T, 0 < y t)
    (hderiv : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Icc 0 T, y' t ≤ 2 * C * y t ^ 2) :
    ∀ t ∈ Icc 0 T, (y 0)⁻¹ - 2 * C * t ≤ (y t)⁻¹ := by
  -- g(s) = 1/y(s) + 2 C s tem derivada -y'/y² + 2C ≥ 0
  have hg_deriv : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (y s)⁻¹ + 2 * C * s) (-y' t / y t ^ 2 + 2 * C * 1) t := by
    intro t ht
    exact ((hderiv t).inv (hpos t ht).ne').add ((hasDerivAt_id' (x := t)).const_mul (2 * C))
  have hg : MonotoneOn (fun s => (y s)⁻¹ + 2 * C * s) (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact continuousOn_of_forall_continuousAt fun t ht =>
        (hg_deriv t ht).continuousAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hg_deriv t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
      rw [(hg_deriv t htI).deriv]
      have hy2 : 0 < y t ^ 2 := by have := hpos t htI; positivity
      have h2 : y' t / y t ^ 2 ≤ 2 * C := by
        rw [div_le_iff₀ hy2]
        exact hineq t htI
      have hneg : -y' t / y t ^ 2 = -(y' t / y t ^ 2) := neg_div _ _
      rw [hneg]
      linarith
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, hT⟩
  have hmono := hg h0 ht ht.1
  simp only [mul_zero, add_zero] at hmono
  linarith

theorem riccati_upper_bound {y y' : ℝ → ℝ} {C T t : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ s ∈ Icc 0 T, 0 < y s)
    (hderiv : ∀ s, HasDerivAt y (y' s) s)
    (hineq : ∀ s ∈ Icc 0 T, y' s ≤ 2 * C * y s ^ 2)
    (ht : t ∈ Icc 0 T) (hden : 0 < 1 - 2 * C * y 0 * t) :
    y t ≤ y 0 / (1 - 2 * C * y 0 * t) := by
  have h := riccati_comparison hT hpos hderiv hineq t ht
  have hy0 : 0 < y 0 := hpos 0 ⟨le_refl 0, hT⟩
  have hyt : 0 < y t := hpos t ht
  rw [le_div_iff₀ hden]
  have e1 : y 0 * y t * (y 0)⁻¹ = y t := by
    rw [mul_comm (y 0) (y t), mul_assoc, mul_inv_cancel₀ hy0.ne', mul_one]
  have e2 : y 0 * y t * (y t)⁻¹ = y 0 := by
    rw [mul_assoc, mul_inv_cancel₀ hyt.ne', mul_one]
  have key := mul_le_mul_of_nonneg_left h (mul_pos hy0 hyt).le
  rw [mul_sub, e1, e2] at key
  nlinarith [key]

end ATK.NavierStokes

#print axioms ATK.NavierStokes.absorption
#print axioms ATK.NavierStokes.absorption_margin_pos
#print axioms ATK.NavierStokes.riccati_comparison
#print axioms ATK.NavierStokes.riccati_upper_bound
