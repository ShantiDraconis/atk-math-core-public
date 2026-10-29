import MCore.RH.NB.Antitone
import Mathlib.Topology.Order.MonotoneConvergence

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

theorem DN_bddBelow (rho : D.GeneratorFamily) :
    BddBelow (Set.range (D.DN rho)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact D.DN_nonneg rho N

noncomputable def DNLimit (rho : D.GeneratorFamily) : ℝ :=
  ⨅ N : ℕ, D.DN rho N

theorem tendsto_DN_DNLimit (rho : D.GeneratorFamily) :
    Filter.Tendsto (D.DN rho) Filter.atTop (nhds (D.DNLimit rho)) := by
  unfold DNLimit
  exact tendsto_atTop_ciInf (D.DN_antitone rho) (D.DN_bddBelow rho)

theorem DNLimit_nonneg (rho : D.GeneratorFamily) :
    0 ≤ D.DNLimit rho := by
  unfold DNLimit
  exact le_ciInf (fun N => D.DN_nonneg rho N)

end NBHilbertData
end MCore.RH.NB
