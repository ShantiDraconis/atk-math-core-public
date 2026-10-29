import MCore.RH.NB.FiniteSpan
import Mathlib.Analysis.InnerProductSpace.Projection

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

noncomputable instance hasOrthogonalProjection_V (rho : D.GeneratorFamily) (N : ℕ) :
    (D.V rho N).HasOrthogonalProjection := by
  letI : Module.Finite ℝ (D.V rho N) := D.finiteDimensional_V rho N
  letI : CompleteSpace (D.V rho N) :=
    IsClosed.completeSpace_coe (D.isClosed_V rho N)
  infer_instance

noncomputable def P (rho : D.GeneratorFamily) (N : ℕ) :
    D.H →L[ℝ] (D.V rho N) :=
  (D.V rho N).orthogonalProjection

theorem P_mem (rho : D.GeneratorFamily) (N : ℕ) (x : D.H) :
    ((D.P rho N x : D.V rho N) : D.H) ∈ D.V rho N :=
  Subtype.coe_prop _

theorem residual_inner_eq_zero (rho : D.GeneratorFamily) (N : ℕ) (x : D.H)
    (v : D.H) (hv : v ∈ D.V rho N) :
    @inner ℝ D.H _ (x - (D.P rho N x : D.H)) v = 0 := by
  exact Submodule.orthogonalProjection_inner_eq_zero x v hv

theorem P_minimal (rho : D.GeneratorFamily) (N : ℕ) (x : D.H) :
    ‖x - (D.P rho N x : D.H)‖ = ⨅ v : D.V rho N, ‖x - (v : D.H)‖ := by
  exact Submodule.orthogonalProjection_minimal x

end NBHilbertData
end MCore.RH.NB
