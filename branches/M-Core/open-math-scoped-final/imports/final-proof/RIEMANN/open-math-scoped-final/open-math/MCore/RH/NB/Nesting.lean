import MCore.RH.NB.Distance

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

theorem finiteGenerators_mono (rho : D.GeneratorFamily) {N M : ℕ} (hNM : N ≤ M) :
    D.finiteGenerators rho N ⊆ D.finiteGenerators rho M := by
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact ⟨Fin.castLE hNM n, rfl⟩

theorem V_mono_of_le (rho : D.GeneratorFamily) {N M : ℕ} (hNM : N ≤ M) :
    D.V rho N ≤ D.V rho M := by
  unfold V
  exact Submodule.span_mono (D.finiteGenerators_mono rho hNM)

theorem V_le_succ (rho : D.GeneratorFamily) (N : ℕ) :
    D.V rho N ≤ D.V rho (N + 1) := by
  exact D.V_mono_of_le rho (Nat.le_succ N)

end NBHilbertData
end MCore.RH.NB
