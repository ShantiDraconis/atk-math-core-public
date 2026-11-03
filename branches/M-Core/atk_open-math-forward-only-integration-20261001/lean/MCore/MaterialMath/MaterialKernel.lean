import MCore.MaterialMath.TriCyclicAlgebra
import MCore.MaterialMath.TriCyclicCalculus
import MCore.MaterialMath.TriCyclicDecomposition
import MCore.MaterialMath.TriCyclicGeometry
import MCore.MaterialMath.TriCyclicTopology
import MCore.MaterialMath.OperatorLaws
import MCore.MaterialMath.TriCyclicSpectral

/-!
# MCore Material Mathematics Kernel

Single import root for the tri-cyclic material mathematics layer.

This module certifies only the internal mathematics and the typed interfaces
toward the seven terminal producers. It does not inhabit any open-problem
terminal target by itself.
-/

namespace MCore.MaterialMath

/-- Version marker for the first complete tri-cyclic material kernel. -/
def materialKernelVersion : Nat := 1

theorem materialKernelVersion_eq_one :
    materialKernelVersion = 1 := by
  rfl

end MCore.MaterialMath
