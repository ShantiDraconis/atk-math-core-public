import Mathlib

/-!
# ATK — Yang–Mills: núcleo algébrico da monotonicidade da massa efetiva

Para C(t) = Σ aₙ e^{-Eₙ t}, a massa efetiva m(t) = -C'(t)/C(t) satisfaz
m'(t) = -(C·C'' - C'²)/C².  Com pesos wₙ = aₙ e^{-Eₙ t} ≥ 0:
C = Σ w, -C' = Σ w E, C'' = Σ w E².

* `weighted_cauchy_schwarz`  — (Σ w E)² ≤ (Σ w)(Σ w E²) para w ≥ 0.
* `effective_mass_slope_nonpos` — -((Σ w)(Σ w E²) - (Σ w E)²)/(Σ w)² ≤ 0.

Isto NÃO constrói a teoria quântica 4D nem prova gap de massa.
-/

namespace ATK.YangMills

theorem weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (w E : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * E i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * E i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i _
    exact le_of_eq (by ring)

theorem effective_mass_slope_nonpos {ι : Type*} (s : Finset ι) (w E : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    -((∑ i ∈ s, w i) * (∑ i ∈ s, w i * E i ^ 2) - (∑ i ∈ s, w i * E i) ^ 2)
      / (∑ i ∈ s, w i) ^ 2 ≤ 0 := by
  have h := weighted_cauchy_schwarz s w E hw
  have hX : 0 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * E i ^ 2) - (∑ i ∈ s, w i * E i) ^ 2 := by
    linarith
  rw [neg_div]
  exact neg_nonpos.mpr (div_nonneg hX (sq_nonneg _))

end ATK.YangMills

#print axioms ATK.YangMills.weighted_cauchy_schwarz
#print axioms ATK.YangMills.effective_mass_slope_nonpos
