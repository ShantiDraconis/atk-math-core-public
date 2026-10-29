import MCore.RH.NB.ZeroLimitFrontier

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

structure VanishingUpperBound (rho : D.GeneratorFamily) where
  eps : ℕ → ℝ
  eps_nonneg : ∀ N, 0 ≤ eps N
  dn_le : ∀ N, D.DN rho N ≤ eps N
  eps_tendsto_zero : Filter.Tendsto eps Filter.atTop (nhds 0)

theorem DNToZero_of_vanishingUpperBound
    (rho : D.GeneratorFamily)
    (h : VanishingUpperBound D rho) :
    D.DNToZero rho := by
  have hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun N => D.DN_nonneg rho N))
    (Filter.Eventually.of_forall h.dn_le)
    h.eps_tendsto_zero

theorem DNLimit_eq_zero_of_vanishingUpperBound
    (rho : D.GeneratorFamily)
    (h : VanishingUpperBound D rho) :
    D.DNLimit rho = 0 :=
  (D.DNToZero_iff_DNLimit_eq_zero rho).mp
    (D.DNToZero_of_vanishingUpperBound rho h)

def terminalProducerStatus : String :=
  "OPEN_MATH: construct VanishingUpperBound for the concrete generator family"

#print axioms DNToZero_of_vanishingUpperBound
#print axioms DNLimit_eq_zero_of_vanishingUpperBound

end NBHilbertData
end MCore.RH.NB
