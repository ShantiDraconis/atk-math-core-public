import MCore.RH.NB.Limit

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

/-- The genuine zero-defect convergence proposition. This is a definition, not an assumption. -/
def DNToZero (rho : D.GeneratorFamily) : Prop :=
  Filter.Tendsto (D.DN rho) Filter.atTop (nhds 0)

/-- For the already-certified convergent defect sequence, convergence to zero is
exactly the statement that its canonical limit is zero. -/
theorem DNToZero_iff_DNLimit_eq_zero (rho : D.GeneratorFamily) :
    D.DNToZero rho ↔ D.DNLimit rho = 0 := by
  constructor
  · intro hzero
    exact tendsto_nhds_unique (D.tendsto_DN_DNLimit rho) hzero
  · intro hlim
    unfold DNToZero
    simpa [hlim] using D.tendsto_DN_DNLimit rho

/-- A pointwise zero upper bound forces the zero-limit frontier. This theorem is
pure order logic and does not provide such a bound. -/
theorem DNToZero_of_le_zero (rho : D.GeneratorFamily)
    (hupper : ∀ N : ℕ, D.DN rho N ≤ 0) : D.DNToZero rho := by
  have hzero : D.DN rho = fun _ : ℕ => (0 : ℝ) := by
    funext N
    exact le_antisymm (hupper N) (D.DN_nonneg rho N)
  unfold DNToZero
  rw [hzero]
  exact tendsto_const_nhds

end NBHilbertData
end MCore.RH.NB
