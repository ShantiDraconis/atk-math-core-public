import Mathlib

/-!
# ATK — Riemann (rota Nyman–Beurling / Báez-Duarte)

* `residual_tendsto_zero` — 0 ≤ D_N ≤ K / log(N+2) para todo N ⇒ D_N → 0.
  (O antecedente é a obrigação aberta `ConcreteUniformLogDNBound`; ela implica RH.)
* `schur_step_monotone`   — D_{N+1} = D_N - u²/s com s > 0 ⇒ D_{N+1} ≤ D_N.
* `gram_complete_square`  — 1 - 2⟨b,c⟩ + cᵀGc = (1 - bᵀG⁻¹b) + (c - G⁻¹b)ᵀ G (c - G⁻¹b),
                            para G simétrica invertível.
* `gram_residual_le`      — se G é semidefinida positiva, 1 - bᵀG⁻¹b é o mínimo de
                            ‖χ - Σ cⱼφⱼ‖² = 1 - 2⟨b,c⟩ + cᵀGc (cota inferior para todo c).
-/

namespace ATK.Riemann

open Filter Topology Matrix

theorem residual_tendsto_zero {D : ℕ → ℝ} {K : ℝ}
    (h0 : ∀ N, 0 ≤ D N) (hK : ∀ N, D N ≤ K / Real.log ((N : ℝ) + 2)) :
    Tendsto D atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hmaj : Tendsto (fun N : ℕ => K / Real.log ((N : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj h0 hK

theorem schur_step_monotone {DN s u : ℝ} (hs : 0 < s) : DN - u ^ 2 / s ≤ DN := by
  have : 0 ≤ u ^ 2 / s := div_nonneg (sq_nonneg u) hs.le
  linarith

theorem gram_complete_square {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hG : G.IsSymm) (hdet : IsUnit G.det) (b c : n → ℝ) :
    1 - 2 * (b ⬝ᵥ c) + c ⬝ᵥ (G *ᵥ c)
      = (1 - b ⬝ᵥ (G⁻¹ *ᵥ b)) + (c - G⁻¹ *ᵥ b) ⬝ᵥ (G *ᵥ (c - G⁻¹ *ᵥ b)) := by
  have hw : G *ᵥ (G⁻¹ *ᵥ b) = b := by
    rw [mulVec_mulVec, mul_nonsing_inv G hdet, one_mulVec]
  have hwc : (G⁻¹ *ᵥ b) ⬝ᵥ (G *ᵥ c) = b ⬝ᵥ c := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hG.eq, hw]
  have hcw : c ⬝ᵥ (G *ᵥ (G⁻¹ *ᵥ b)) = b ⬝ᵥ c := by
    rw [hw, dotProduct_comm]
  have hww : (G⁻¹ *ᵥ b) ⬝ᵥ (G *ᵥ (G⁻¹ *ᵥ b)) = b ⬝ᵥ (G⁻¹ *ᵥ b) := by
    rw [hw, dotProduct_comm]
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hwc, hcw, hww]
  ring

theorem gram_residual_le {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hPSD : G.PosSemidef) (hG : G.IsSymm) (hdet : IsUnit G.det)
    (b c : n → ℝ) :
    1 - b ⬝ᵥ (G⁻¹ *ᵥ b) ≤ 1 - 2 * (b ⬝ᵥ c) + c ⬝ᵥ (G *ᵥ c) := by
  rw [gram_complete_square G hG hdet b c]
  have h := hPSD.dotProduct_mulVec_nonneg (c - G⁻¹ *ᵥ b)
  have hstar : star (c - G⁻¹ *ᵥ b) = c - G⁻¹ *ᵥ b := by
    ext i
    simp
  rw [hstar] at h
  linarith

end ATK.Riemann

#print axioms ATK.Riemann.residual_tendsto_zero
#print axioms ATK.Riemann.schur_step_monotone
#print axioms ATK.Riemann.gram_complete_square
#print axioms ATK.Riemann.gram_residual_le
