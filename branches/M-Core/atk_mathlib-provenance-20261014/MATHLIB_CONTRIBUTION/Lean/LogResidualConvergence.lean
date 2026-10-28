import Mathlib

/-!
ATK candidate: conditional logarithmic residual convergence.
Original: ShantiDraconis/m-core-riemann/atk-kernel/ATK/Riemann.lean
Source blob SHA: 018b395f949eca88536537428244f4c2d369e06b
The uniform logarithmic bound is an explicit assumption; no RH proof.
Kernel validation pending.
-/

namespace ATK.MathlibCandidates

open Filter Topology

theorem residual_tendsto_zero {D : ℕ → ℝ} {K : ℝ}
    (h0 : ∀ N, 0 ≤ D N)
    (hK : ∀ N, D N ≤ K / Real.log ((N : ℝ) + 2)) :
    Tendsto D atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hmaj : Tendsto (fun N : ℕ => K / Real.log ((N : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj h0 hK

end ATK.MathlibCandidates

#print axioms ATK.MathlibCandidates.residual_tendsto_zero
