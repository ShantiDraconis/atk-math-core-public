import Mathlib

/-!
# ATK — Hodge: realização linear com matriz invertível

Se M é a matriz (racional) que expressa classes de ciclos já dados numa base, e M é invertível,
então todo vetor-alvo α é combinação racional única dessas classes: c = M⁻¹ α.

* `linear_realization` — ∃ c, M c = α.
* `realization_unique` — M c = α ⇒ c = M⁻¹ α.

Isto é álgebra linear sobre ℚ: pressupõe que os ciclos já existem. A conjectura de Hodge é
justamente a existência deles; nada aqui a prova.
-/

namespace ATK.Hodge

open Matrix

theorem linear_realization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (hM : IsUnit M.det) (α : ι → ℚ) :
    ∃ c : ι → ℚ, M *ᵥ c = α :=
  ⟨M⁻¹ *ᵥ α, by rw [mulVec_mulVec, mul_nonsing_inv M hM, one_mulVec]⟩

theorem realization_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (hM : IsUnit M.det) (α c : ι → ℚ) (h : M *ᵥ c = α) :
    c = M⁻¹ *ᵥ α := by
  rw [← h, mulVec_mulVec, nonsing_inv_mul M hM, one_mulVec]

end ATK.Hodge

#print axioms ATK.Hodge.linear_realization
#print axioms ATK.Hodge.realization_unique
