import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.Count

/-!
# O laplaciano do ciclo `Cₙ`: matriz, autovetores e espectro com multiplicidades

`ParametrosModelo.espectro_ciclo` calcula só cinco valores `2 − 2cos(kπ/5)`, e
`ParametrosModelo.autovetor_ciclo` é uma recorrência em `ℤ`. Aqui o laplaciano do ciclo com
`n = m + 1` vértices é a matriz finita `lap R m : Matrix (Fin n) (Fin n) R`,
`L = 2I − P − P⁻¹` (vizinhos `j ± 1` módulo `n`), e o espectro é provado inteiro:

* `autovetor`: para todo `y` com `yⁿ = 1`, o vetor `j ↦ yʲ` é autovetor de `L` com autovalor
  `2 − y − y⁻¹`; `modo_zero`: o vetor constante tem autovalor 0;
* `lap_diagonaliza`: a matriz de Vandermonde dos modos `ζᵏ` (`ζ = e^{2πi/n}`) é invertível e
  `L = V⁻¹ D V`, `D` diagonal;
* `charpoly_lap`, `espectro_lap`: o polinômio característico é `∏ₖ (X − λₖ)` e o multiconjunto
  das raízes (o espectro com multiplicidades) é `{λₖ : k = 0, …, n − 1}`,
  `λₖ = 2 − 2cos(2πk/n)`; `autovalor_simetria`: `λₙ₋ₖ = λₖ`;
* para `C₁₀`: `lap_C10_entradas` (as 100 entradas), `espectro_C10` (o multiconjunto explícito das
  10 raízes) e `multiplicidade_C10` (0 e 4 simples; `(3 ∓ √5)/2`, `(5 ∓ √5)/2` duplos).

Modelo finito exato (`EXACT_MODEL`); não é a teoria de Yang–Mills.
-/

namespace ATK.LaplacianoCiclo

open Matrix Polynomial Complex Finset
open scoped Real

/-- Laplaciano do ciclo com `m + 1` vértices: `L i j = 2[i = j] − [j = i + 1] − [i = j + 1]`,
somas módulo `m + 1`. -/
def lap (R : Type*) [Ring R] (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j =>
    (if i = j then 2 else 0) - (if j = i + 1 then 1 else 0) - (if i = j + 1 then 1 else 0)

/-- `L` é simétrica. -/
theorem lap_simetrica (R : Type*) [Ring R] (m : ℕ) : (lap R m)ᵀ = lap R m := by
  ext i j
  have h : (j = i) ↔ (i = j) := eq_comm
  simp only [transpose_apply, lap, of_apply, h]
  rw [sub_right_comm]

/-- As 100 entradas de `L` para `C₁₀`: 2 na diagonal, −1 entre vizinhos do ciclo (inclusive
`0 ~ 9`), 0 no resto. -/
theorem lap_C10_entradas :
    lap ℤ 9 = Matrix.of fun i j : Fin 10 =>
      if i = j then 2 else if j = i + 1 ∨ i = j + 1 then -1 else 0 := by
  decide +kernel

/-- Ação de `L` num vetor: `(L u) i = 2 u i − u (i + 1) − u (i − 1)`. -/
theorem lap_mulVec {R : Type*} [CommRing R] (m : ℕ) (u : Fin (m + 1) → R) (i : Fin (m + 1)) :
    (lap R m *ᵥ u) i = 2 * u i - u (i + 1) - u (i - 1) := by
  have h : ∀ j : Fin (m + 1), (i = j + 1) ↔ (j = i - 1) := fun j => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [mulVec, dotProduct, lap, of_apply, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, h, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma pow_val_add {ζ : ℂ} {m : ℕ} (hζ : ζ ^ (m + 1) = 1) (a b : Fin (m + 1)) :
    ζ ^ ((a + b : Fin (m + 1)) : ℕ) = ζ ^ (a : ℕ) * ζ ^ (b : ℕ) := by
  rw [Fin.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

lemma pow_val_one {ζ : ℂ} {m : ℕ} (hζ : ζ ^ (m + 1) = 1) :
    ζ ^ ((1 : Fin (m + 1)) : ℕ) = ζ := by
  rw [Fin.val_one', ← pow_eq_pow_mod _ hζ, pow_one]

lemma pow_val_sub_one {ζ : ℂ} {m : ℕ} (hζ : ζ ^ (m + 1) = 1) (i : Fin (m + 1)) :
    ζ ^ ((i - 1 : Fin (m + 1)) : ℕ) * ζ = ζ ^ (i : ℕ) := by
  conv_rhs => rw [← sub_add_cancel i 1]
  rw [pow_val_add hζ, pow_val_one hζ]

/-- Autovetores: se `yᵐ⁺¹ = 1`, então `L (j ↦ yʲ) = (2 − y − y⁻¹) (j ↦ yʲ)`. -/
theorem autovetor (m : ℕ) {y : ℂ} (hy : y ^ (m + 1) = 1) :
    lap ℂ m *ᵥ (fun j : Fin (m + 1) => y ^ (j : ℕ)) =
      (2 - y - y⁻¹) • (fun j : Fin (m + 1) => y ^ (j : ℕ)) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  funext i
  rw [lap_mulVec, Pi.smul_apply, smul_eq_mul, pow_val_add hy, pow_val_one hy]
  have h := pow_val_sub_one hy i
  have h' : y ^ ((i - 1 : Fin (m + 1)) : ℕ) = y ^ (i : ℕ) * y⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hy0, mul_one]
  rw [h']
  ring

/-- O modo zero: o vetor constante está no núcleo de `L` (autovalor 0). -/
theorem modo_zero (m : ℕ) : lap ℂ m *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  funext i
  rw [lap_mulVec]
  simp only [Pi.zero_apply]
  norm_num

/-- A raiz primitiva `ζ = e^{2πi/(m+1)}`. -/
noncomputable def ζ (m : ℕ) : ℂ := exp (2 * π * I / ((m + 1 : ℕ) : ℂ))

theorem primitiva (m : ℕ) : IsPrimitiveRoot (ζ m) (m + 1) :=
  isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)

lemma raiz_pow (m : ℕ) (k : Fin (m + 1)) : (ζ m ^ (k : ℕ)) ^ (m + 1) = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, (primitiva m).pow_eq_one, one_pow]

/-- O `k`-ésimo autovalor `λₖ = 2 − 2cos(2πk/(m+1))`. -/
noncomputable def autovalor (m : ℕ) (k : Fin (m + 1)) : ℝ :=
  2 - 2 * Real.cos (2 * π * ((k : ℕ) : ℝ) / ((m : ℝ) + 1))

/-- O autovalor do modo `ζᵏ` é real: `2 − ζᵏ − ζ⁻ᵏ = 2 − 2cos(2πk/(m+1))`. -/
theorem autovalor_eq (m : ℕ) (k : Fin (m + 1)) :
    2 - ζ m ^ (k : ℕ) - (ζ m ^ (k : ℕ))⁻¹ = (autovalor m k : ℂ) := by
  have hx : ζ m ^ (k : ℕ) = exp (((2 * π * ((k : ℕ) : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ) * I) := by
    rw [ζ, ← exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hx, ← exp_neg, ← neg_mul, sub_sub, ← two_cos, autovalor]
  push_cast
  ring

/-- A matriz dos modos: a linha `k` é o autovetor `j ↦ ζᵏʲ` (Vandermonde em `ζᵏ`). -/
noncomputable def modos (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  vandermonde fun k : Fin (m + 1) => ζ m ^ (k : ℕ)

/-- Os autovalores complexos `2 − ζᵏ − ζ⁻ᵏ`. -/
noncomputable def autovaloresC (m : ℕ) (k : Fin (m + 1)) : ℂ :=
  2 - ζ m ^ (k : ℕ) - (ζ m ^ (k : ℕ))⁻¹

theorem modos_mul_lap (m : ℕ) : modos m * lap ℂ m = diagonal (autovaloresC m) * modos m := by
  ext k i
  rw [diagonal_mul, mul_apply]
  have h := congrFun (autovetor m (raiz_pow m k)) i
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [modos, vandermonde_apply, autovaloresC]
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, ← transpose_apply (lap ℂ m) i j, lap_simetrica]

/-- Os `m + 1` modos são linearmente independentes: `det V ≠ 0` (os `ζᵏ` são distintos). -/
theorem det_modos_ne_zero (m : ℕ) : (modos m).det ≠ 0 := by
  rw [modos, det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext ((primitiva m).pow_inj a.isLt b.isLt hab)

/-- Diagonalização: `L = V⁻¹ D V`. -/
theorem lap_diagonaliza (m : ℕ) :
    lap ℂ m = (modos m)⁻¹ * diagonal (autovaloresC m) * modos m := by
  have hu : IsUnit (modos m).det := isUnit_iff_ne_zero.mpr (det_modos_ne_zero m)
  rw [mul_assoc, ← modos_mul_lap]
  exact (nonsing_inv_mul_cancel_left _ _ hu).symm

/-- O polinômio característico: `χ_L = ∏ₖ (X − λₖ)`. -/
theorem charpoly_lap (m : ℕ) :
    (lap ℂ m).charpoly = ∏ k, (X - C ((autovalor m k : ℝ) : ℂ)) := by
  have hu : IsUnit (modos m) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_modos_ne_zero m))
  have hc := charpoly_units_conj' hu.unit (diagonal (autovaloresC m))
  rw [IsUnit.unit_spec] at hc
  rw [lap_diagonaliza m, hc, charpoly_diagonal]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [autovaloresC, autovalor_eq]

/-- O espectro com multiplicidades: as raízes de `χ_L` são exatamente `λ₀, …, λₘ`. -/
theorem espectro_lap (m : ℕ) :
    (lap ℂ m).charpoly.roots = Finset.univ.val.map fun k => ((autovalor m k : ℝ) : ℂ) := by
  have h := roots_multiset_prod_X_sub_C (Finset.univ.val.map fun k => ((autovalor m k : ℝ) : ℂ))
  rw [Multiset.map_map] at h
  rw [charpoly_lap, Finset.prod_eq_multiset_prod]
  exact h

/-- Simetria das multiplicidades: `λₙ₋ₖ = λₖ`. -/
theorem autovalor_simetria (m k : ℕ) (hk : k ≤ m + 1) :
    2 - 2 * Real.cos (2 * π * ((m + 1 - k : ℕ) : ℝ) / ((m : ℝ) + 1)) =
      2 - 2 * Real.cos (2 * π * (k : ℝ) / ((m : ℝ) + 1)) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.cast_sub hk, Nat.cast_add, Nat.cast_one]
  have h : 2 * π * ((m : ℝ) + 1 - k) / ((m : ℝ) + 1) = 2 * π - 2 * π * k / ((m : ℝ) + 1) := by
    field_simp
  rw [h, Real.cos_two_pi_sub]

/-! ## O ciclo de 10 vértices -/

lemma autovalor_nove (k : Fin 10) : autovalor 9 k = 2 - 2 * Real.cos ((k : ℕ) * π / 5) := by
  unfold autovalor
  rw [show 2 * π * ((k : ℕ) : ℝ) / (((9 : ℕ) : ℝ) + 1) = ((k : ℕ) : ℝ) * π / 5 by push_cast; ring]

/-- Os dez autovalores de `C₁₀` em forma fechada, na ordem `k = 0, …, 9`. -/
theorem valores_C10 :
    List.ofFn (autovalor 9) =
      [0, (3 - √5) / 2, (5 - √5) / 2, (3 + √5) / 2, (5 + √5) / 2, 4,
        (5 + √5) / 2, (3 + √5) / 2, (5 - √5) / 2, (3 - √5) / 2] := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have c1 : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
  have c2 : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul, c1]
    nlinarith [h5]
  have c3 : Real.cos (3 * π / 5) = -((√5 - 1) / 4) := by
    rw [show 3 * π / 5 = π - 2 * π / 5 by ring, Real.cos_pi_sub, c2]
  have c4 : Real.cos (4 * π / 5) = -((1 + √5) / 4) := by
    rw [show 4 * π / 5 = π - π / 5 by ring, Real.cos_pi_sub, c1]
  have c5 : Real.cos (5 * π / 5) = -1 := by
    rw [show 5 * π / 5 = π by ring, Real.cos_pi]
  have c6 : Real.cos (6 * π / 5) = -((1 + √5) / 4) := by
    rw [show 6 * π / 5 = π / 5 + π by ring, Real.cos_add_pi, c1]
  have c7 : Real.cos (7 * π / 5) = -((√5 - 1) / 4) := by
    rw [show 7 * π / 5 = 2 * π / 5 + π by ring, Real.cos_add_pi, c2]
  have c8 : Real.cos (8 * π / 5) = (√5 - 1) / 4 := by
    rw [show 8 * π / 5 = 3 * π / 5 + π by ring, Real.cos_add_pi, c3, neg_neg]
  have c9 : Real.cos (9 * π / 5) = (1 + √5) / 4 := by
    rw [show 9 * π / 5 = 4 * π / 5 + π by ring, Real.cos_add_pi, c4, neg_neg]
  simp only [List.ofFn_succ, List.ofFn_zero, autovalor_nove, Fin.val_succ, Fin.val_zero,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, zero_div,
    Real.cos_zero]
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **Espectro de `C₁₀` com multiplicidades**: o multiconjunto das raízes de `χ_L` é
`{0, (3−√5)/2, (5−√5)/2, (3+√5)/2, (5+√5)/2, 4, (5+√5)/2, (3+√5)/2, (5−√5)/2, (3−√5)/2}`. -/
theorem espectro_C10 :
    (lap ℂ 9).charpoly.roots =
      ↑(List.map Complex.ofReal
        [0, (3 - √5) / 2, (5 - √5) / 2, (3 + √5) / 2, (5 + √5) / 2, 4,
          (5 + √5) / 2, (3 + √5) / 2, (5 - √5) / 2, (3 - √5) / 2]) := by
  rw [espectro_lap, Fin.univ_val_map, ← valores_C10, List.map_ofFn]
  rfl

/-- Os seis autovalores distintos de `C₁₀`, em ordem crescente. -/
noncomputable def valor : Fin 6 → ℝ :=
  ![0, (3 - √5) / 2, (5 - √5) / 2, (3 + √5) / 2, (5 + √5) / 2, 4]

theorem valor_estrito : StrictMono valor := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < √5 := by positivity
  have hs3 : √5 < 3 := by nlinarith
  have hs1 : 1 < √5 := by nlinarith
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · show (0 : ℝ) < (3 - √5) / 2
    linarith
  · show (3 - √5) / 2 < (5 - √5) / 2
    linarith
  · show (5 - √5) / 2 < (3 + √5) / 2
    linarith
  · show (3 + √5) / 2 < (5 + √5) / 2
    linarith
  · show (5 + √5) / 2 < (4 : ℝ)
    linarith

lemma valores_C10_indices :
    List.ofFn (autovalor 9) = List.map valor [0, 1, 2, 3, 4, 5, 4, 3, 2, 1] := by
  rw [valores_C10]
  rfl

/-- **Multiplicidades em `C₁₀`**: 0 e 4 são raízes simples de `χ_L`; `(3 − √5)/2`,
`(5 − √5)/2`, `(3 + √5)/2` e `(5 + √5)/2` são raízes duplas. -/
theorem multiplicidade_C10 (a : Fin 6) :
    (lap ℂ 9).charpoly.rootMultiplicity (valor a : ℂ) = if a = 0 ∨ a = 5 then 1 else 2 := by
  classical
  have hinj : Function.Injective (Complex.ofReal ∘ valor) :=
    Complex.ofReal_injective.comp valor_estrito.injective
  rw [← count_roots, espectro_C10, ← valores_C10, valores_C10_indices, List.map_map,
    Multiset.coe_count]
  refine (List.count_map_of_injective _ (Complex.ofReal ∘ valor) hinj a).trans ?_
  revert a
  decide

/-- Os autovalores são reais e o gap espectral de `C₁₀` é `(3 − √5)/2 > 0`. -/
theorem gap_C10 : 0 < (3 - √5) / 2 ∧ (3 - √5) / 2 = valor 1 := by
  refine ⟨?_, rfl⟩
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < √5 := by positivity
  nlinarith

end ATK.LaplacianoCiclo

#print axioms ATK.LaplacianoCiclo.lap_simetrica
#print axioms ATK.LaplacianoCiclo.lap_C10_entradas
#print axioms ATK.LaplacianoCiclo.lap_mulVec
#print axioms ATK.LaplacianoCiclo.pow_val_add
#print axioms ATK.LaplacianoCiclo.pow_val_one
#print axioms ATK.LaplacianoCiclo.pow_val_sub_one
#print axioms ATK.LaplacianoCiclo.autovetor
#print axioms ATK.LaplacianoCiclo.modo_zero
#print axioms ATK.LaplacianoCiclo.primitiva
#print axioms ATK.LaplacianoCiclo.raiz_pow
#print axioms ATK.LaplacianoCiclo.autovalor_eq
#print axioms ATK.LaplacianoCiclo.modos_mul_lap
#print axioms ATK.LaplacianoCiclo.det_modos_ne_zero
#print axioms ATK.LaplacianoCiclo.lap_diagonaliza
#print axioms ATK.LaplacianoCiclo.charpoly_lap
#print axioms ATK.LaplacianoCiclo.espectro_lap
#print axioms ATK.LaplacianoCiclo.autovalor_simetria
#print axioms ATK.LaplacianoCiclo.autovalor_nove
#print axioms ATK.LaplacianoCiclo.valores_C10
#print axioms ATK.LaplacianoCiclo.espectro_C10
#print axioms ATK.LaplacianoCiclo.valor_estrito
#print axioms ATK.LaplacianoCiclo.valores_C10_indices
#print axioms ATK.LaplacianoCiclo.multiplicidade_C10
#print axioms ATK.LaplacianoCiclo.gap_C10
