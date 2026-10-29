import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection

namespace MCore.RH.NB

structure NBHilbertData where
  H : Type
  instNormedAddCommGroup : NormedAddCommGroup H
  instInnerProductSpace : InnerProductSpace ℝ H
  instCompleteSpace : CompleteSpace H
  chi : H

attribute [instance] NBHilbertData.instNormedAddCommGroup
attribute [instance] NBHilbertData.instInnerProductSpace
attribute [instance] NBHilbertData.instCompleteSpace

namespace NBHilbertData

variable (D : NBHilbertData)

def GeneratorFamily := ℕ → D.H

def finiteGenerators (rho : D.GeneratorFamily) (N : ℕ) : Set D.H :=
  Set.range (fun n : Fin N => rho n)

def V (rho : D.GeneratorFamily) (N : ℕ) : Submodule ℝ D.H :=
  Submodule.span ℝ (D.finiteGenerators rho N)

theorem generator_mem_V (rho : D.GeneratorFamily) (N : ℕ) (n : Fin N) :
    rho n ∈ D.V rho N := by
  apply Submodule.subset_span
  exact ⟨n, rfl⟩

theorem finite_finiteGenerators (rho : D.GeneratorFamily) (N : ℕ) :
    (D.finiteGenerators rho N).Finite := by
  exact Set.finite_range _

end NBHilbertData
end MCore.RH.NB
