import MCore.RH.NB.Projection

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

noncomputable def dN (rho : D.GeneratorFamily) (N : ℕ) : ℝ :=
  ‖D.chi - (D.P rho N D.chi : D.H)‖

noncomputable def DN (rho : D.GeneratorFamily) (N : ℕ) : ℝ :=
  (D.dN rho N) ^ 2

theorem dN_nonneg (rho : D.GeneratorFamily) (N : ℕ) :
    0 ≤ D.dN rho N := by
  exact norm_nonneg _

theorem DN_nonneg (rho : D.GeneratorFamily) (N : ℕ) :
    0 ≤ D.DN rho N := by
  exact sq_nonneg _

end NBHilbertData
end MCore.RH.NB
