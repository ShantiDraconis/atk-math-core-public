import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Module

/-!
# ATK — Álgebra triádica: operadores de ordem 3, pontos fixos e cadeias simétricas

O ciclo de três estados (manifesto → travessia → semente → manifesto) como **operador `T` com
`T³ = 1`**, em qualquer `ℂ`-álgebra (operadores, matrizes, …):

* `ω = (−1 + i√3)/2`: `ω² + ω + 1 = 0`, `ω³ = 1`.
* Projetores `P₀ = (1 + T + T²)/3`, `P₁ = (1 + ω²T + ωT²)/3`, `P₂ = (1 + ωT + ω²T²)/3`:
  **`decomposicao`**: `P₀ + P₁ + P₂ = 1`; `T P_j = ωʲ P_j` (`autovetor_*`); `P_j² = P_j` e
  `P_i P_j = 0` (`i ≠ j`); e todo `X = P₀X + P₁X + P₂X` com cada parte autovetor de `T`.
* **`orbita_um_ou_tres`**: para `σ³ = id`, toda órbita tem tamanho `1` ou `3`.
* **`pontos_fixos_mod_tres`**: `|X| ≡ |Fix σ| (mod 3)` para `σ³ = id` num conjunto finito.
* **`markov_circulante`**: uma matriz 3×3 que comuta com o ciclo `R` é circulante;
  **`markov_uniforme_estacionaria`**: se, além disso, é estocástica, a distribuição uniforme
  `(1/3, 1/3, 1/3)` é estacionária.

São resultados clássicos, agora certificados; o que a teoria triádica acrescentar terá de ser lei
nova **sobre** estes objetos (ver `MODELOS_TERMINAIS.md`).
-/

namespace ATK.Triadico

open Complex

/-- Raiz cúbica primitiva da unidade `ω = (−1 + i√3)/2`. -/
noncomputable def ω : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem omega_quad : ω ^ 2 + ω + 1 = 0 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [ω, pow_two] <;> nlinarith

theorem omega_cubo : ω ^ 3 = 1 := by
  have h := omega_quad
  have : ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := by ring
  rw [h, mul_zero, sub_eq_zero] at this
  exact this

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  have := omega_quad
  rw [h] at this
  norm_num at this

section Algebra
set_option linter.unusedSectionVars false

variable {A : Type*} [Ring A] [Algebra ℂ A] (T : A)

/-- Projetor na componente invariante. -/
noncomputable def P₀ : A := (1 / 3 : ℂ) • (1 + T + T ^ 2)
/-- Projetor na componente `ω`. -/
noncomputable def P₁ : A := (1 / 3 : ℂ) • (1 + ω ^ 2 • T + ω • T ^ 2)
/-- Projetor na componente `ω²`. -/
noncomputable def P₂ : A := (1 / 3 : ℂ) • (1 + ω • T + ω ^ 2 • T ^ 2)

variable {T}

theorem T_mul_T2 (hT : T ^ 3 = 1) : T * T ^ 2 = 1 := by rw [← pow_succ', hT]

/-- `(1 + bT + cT²) X = (1 + bμ + cμ²) X` quando `T X = μ X`. -/
theorem aplica {X : A} {μ b c : ℂ} (hX : T * X = μ • X) :
    (1 + b • T + c • T ^ 2) * X = (1 + b * μ + c * μ ^ 2) • X := by
  have h2 : T ^ 2 * X = μ ^ 2 • X := by
    rw [pow_two, mul_assoc, hX, mul_smul_comm, hX, smul_smul, pow_two]
  rw [add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, hX, h2, smul_smul, smul_smul]
  module

/-- **Soma dos projetores**: `P₀ + P₁ + P₂ = 1`. -/
theorem decomposicao : P₀ T + P₁ T + P₂ T = 1 := by
  have h := omega_quad
  unfold P₀ P₁ P₂
  have e : (1 / 3 : ℂ) • (1 + T + T ^ 2) + (1 / 3 : ℂ) • (1 + ω ^ 2 • T + ω • T ^ 2) +
      (1 / 3 : ℂ) • (1 + ω • T + ω ^ 2 • T ^ 2) =
      (1 : A) + ((1 + ω + ω ^ 2) / 3) • T + ((1 + ω + ω ^ 2) / 3) • T ^ 2 := by module
  rw [e, show (1 + ω + ω ^ 2) / 3 = 0 by linear_combination h / 3, zero_smul, zero_smul,
    add_zero, add_zero]

theorem autovetor_0 (hT : T ^ 3 = 1) : T * P₀ T = P₀ T := by
  unfold P₀
  rw [mul_smul_comm, mul_add, mul_add, mul_one, ← pow_two, T_mul_T2 hT]
  module

theorem autovetor_1 (hT : T ^ 3 = 1) : T * P₁ T = ω • P₁ T := by
  have h3 := omega_cubo
  unfold P₁
  rw [mul_smul_comm, mul_add, mul_add, mul_one, mul_smul_comm, mul_smul_comm, ← pow_two,
    T_mul_T2 hT]
  have e : ω • (1 / 3 : ℂ) • (1 + ω ^ 2 • T + ω • T ^ 2) =
      (1 / 3 : ℂ) • (ω • (1 : A) + ω ^ 3 • T + ω ^ 2 • T ^ 2) := by module
  rw [e, h3, one_smul]
  module

theorem autovetor_2 (hT : T ^ 3 = 1) : T * P₂ T = ω ^ 2 • P₂ T := by
  have h3 := omega_cubo
  unfold P₂
  rw [mul_smul_comm, mul_add, mul_add, mul_one, mul_smul_comm, mul_smul_comm, ← pow_two,
    T_mul_T2 hT]
  have e : ω ^ 2 • (1 / 3 : ℂ) • (1 + ω • T + ω ^ 2 • T ^ 2) =
      (1 / 3 : ℂ) • (ω ^ 2 • (1 : A) + ω ^ 3 • T + (ω ^ 3 * ω) • T ^ 2) := by module
  rw [e, h3, one_smul, one_mul]
  module

/-- Produto `P_i X` com `T X = μ X`: o escalar `(1 + bμ + cμ²)/3`. -/
theorem proj_mul {X : A} {μ b c : ℂ} (hX : T * X = μ • X) :
    (1 / 3 : ℂ) • (1 + b • T + c • T ^ 2) * X = ((1 + b * μ + c * μ ^ 2) / 3) • X := by
  rw [smul_mul_assoc, aplica hX, smul_smul]; congr 1; ring

theorem idem_0 (hT : T ^ 3 = 1) : P₀ T * P₀ T = P₀ T := by
  have h := proj_mul (b := 1) (c := 1) (autovetor_0 hT |>.trans (one_smul ℂ _).symm)
  simp only [one_smul] at h
  unfold P₀ at h ⊢
  rw [h]; norm_num

theorem idem_1 (hT : T ^ 3 = 1) : P₁ T * P₁ T = P₁ T := by
  have h3 := omega_cubo
  have h := proj_mul (b := ω ^ 2) (c := ω) (autovetor_1 hT)
  unfold P₁ at h ⊢
  rw [h, show (1 + ω ^ 2 * ω + ω * ω ^ 2) / 3 = 1 by linear_combination (2 / 3 : ℂ) * h3, one_smul]

theorem idem_2 (hT : T ^ 3 = 1) : P₂ T * P₂ T = P₂ T := by
  have h3 := omega_cubo
  have h := proj_mul (b := ω) (c := ω ^ 2) (autovetor_2 hT)
  unfold P₂ at h ⊢
  rw [h, show (1 + ω * ω ^ 2 + ω ^ 2 * (ω ^ 2) ^ 2) / 3 = 1 by
    linear_combination (1 / 3 + (ω ^ 3 + 1) / 3 : ℂ) * h3, one_smul]

theorem orto_01 (hT : T ^ 3 = 1) : P₀ T * P₁ T = 0 := by
  have hq := omega_quad
  have h := proj_mul (b := 1) (c := 1) (autovetor_1 hT)
  simp only [one_smul] at h
  unfold P₀ P₁ at *
  rw [h, show (1 + 1 * ω + 1 * ω ^ 2) / 3 = 0 by linear_combination hq / 3, zero_smul]

theorem orto_02 (hT : T ^ 3 = 1) : P₀ T * P₂ T = 0 := by
  have hq := omega_quad
  have h3 := omega_cubo
  have h := proj_mul (b := 1) (c := 1) (autovetor_2 hT)
  simp only [one_smul] at h
  unfold P₀ P₂ at *
  rw [h, show (1 + 1 * ω ^ 2 + 1 * (ω ^ 2) ^ 2) / 3 = 0 by
    linear_combination (1 / 3 : ℂ) * hq + (ω / 3) * h3, zero_smul]

theorem orto_12 (hT : T ^ 3 = 1) : P₁ T * P₂ T = 0 := by
  have hq := omega_quad
  have h3 := omega_cubo
  have h := proj_mul (b := ω ^ 2) (c := ω) (autovetor_2 hT)
  unfold P₁ P₂ at *
  rw [h, show (1 + ω ^ 2 * ω ^ 2 + ω * (ω ^ 2) ^ 2) / 3 = 0 by
    linear_combination (1 / 3 : ℂ) * hq + ((ω + ω ^ 2) / 3) * h3, zero_smul]

theorem orto_10 (hT : T ^ 3 = 1) : P₁ T * P₀ T = 0 := by
  have hq := omega_quad
  have h := proj_mul (b := ω ^ 2) (c := ω) ((autovetor_0 hT).trans (one_smul ℂ _).symm)
  unfold P₁ P₀ at *
  rw [h, show (1 + ω ^ 2 * 1 + ω * 1 ^ 2) / 3 = 0 by linear_combination hq / 3, zero_smul]

theorem orto_20 (hT : T ^ 3 = 1) : P₂ T * P₀ T = 0 := by
  have hq := omega_quad
  have h := proj_mul (b := ω) (c := ω ^ 2) ((autovetor_0 hT).trans (one_smul ℂ _).symm)
  unfold P₂ P₀ at *
  rw [h, show (1 + ω * 1 + ω ^ 2 * 1 ^ 2) / 3 = 0 by linear_combination hq / 3, zero_smul]

theorem orto_21 (hT : T ^ 3 = 1) : P₂ T * P₁ T = 0 := by
  have hq := omega_quad
  have h3 := omega_cubo
  have h := proj_mul (b := ω) (c := ω ^ 2) (autovetor_1 hT)
  unfold P₂ P₁ at *
  rw [h, show (1 + ω * ω + ω ^ 2 * ω ^ 2) / 3 = 0 by
    linear_combination (1 / 3 : ℂ) * hq + (ω / 3) * h3, zero_smul]

/-- **Decomposição espectral triádica**: todo `X` é a soma de três componentes, cada uma
autovetor de `T` com autovalor `1`, `ω`, `ω²`. -/
theorem decomposicao_espectral (hT : T ^ 3 = 1) (X : A) :
    X = P₀ T * X + P₁ T * X + P₂ T * X ∧
      T * (P₀ T * X) = P₀ T * X ∧ T * (P₁ T * X) = ω • (P₁ T * X) ∧
        T * (P₂ T * X) = ω ^ 2 • (P₂ T * X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← add_mul, ← add_mul, decomposicao, one_mul]
  · rw [← mul_assoc, autovetor_0 hT]
  · rw [← mul_assoc, autovetor_1 hT, smul_mul_assoc]
  · rw [← mul_assoc, autovetor_2 hT, smul_mul_assoc]

end Algebra

/-! ## Órbitas e pontos fixos de um ciclo de ordem 3 -/

/-- **Toda órbita de `σ` com `σ³ = id` tem tamanho 1 ou 3.** -/
theorem orbita_um_ou_tres {α : Type*} (σ : α → α) (h : σ^[3] = id) (x : α) :
    Function.minimalPeriod σ x = 1 ∨ Function.minimalPeriod σ x = 3 := by
  have hper : Function.IsPeriodicPt σ 3 x := by
    show σ^[3] x = x; rw [h]; rfl
  have hd := hper.minimalPeriod_dvd
  exact (Nat.dvd_prime Nat.prime_three).1 hd

set_option backward.isDefEq.respectTransparency false in
open Function in
/-- **Teorema de pontos fixos triádicos**: `|X| ≡ |Fix σ| (mod 3)` para `σ³ = id`. -/
theorem pontos_fixos_mod_tres {α : Type*} [Fintype α] [DecidableEq α] (f : Function.End α)
    (hf : f ^ 3 = 1) : Fintype.card α ≡ Fintype.card f.fixedPoints [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (by simpa using hf)

/-! ## Cadeias de Markov com simetria triádica -/

/-- O ciclo `R` dos três estados (matriz de permutação). -/
def R : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem R_cubo : R ^ 3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [R, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Comutar com o ciclo ⇒ circulante**: `P_{i+1, j+1} = P_{i j}`. -/
theorem markov_circulante (P : Matrix (Fin 3) (Fin 3) ℝ) (h : P * R = R * P) :
    P 1 1 = P 0 0 ∧ P 2 2 = P 0 0 ∧ P 1 2 = P 0 1 ∧ P 2 0 = P 0 1 ∧
      P 1 0 = P 0 2 ∧ P 2 1 = P 0 2 := by
  have e : ∀ i j, (P * R) i j = (R * P) i j := fun i j => by rw [h]
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e10 := e 1 0; have e11 := e 1 1; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e22 := e 2 2
  simp [R, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Distribuição uniforme estacionária**: uma matriz estocástica que comuta com o ciclo deixa
`(1/3, 1/3, 1/3)` invariante. -/
theorem markov_uniforme_estacionaria (P : Matrix (Fin 3) (Fin 3) ℝ) (h : P * R = R * P)
    (hlin : ∀ i, ∑ j, P i j = 1) (j : Fin 3) : ∑ i, (1 / 3 : ℝ) * P i j = 1 / 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := markov_circulante P h
  have r0 := hlin 0
  simp only [Fin.sum_univ_three] at r0 ⊢
  fin_cases j <;> simp <;> linarith

end ATK.Triadico

#print axioms ATK.Triadico.omega_quad
#print axioms ATK.Triadico.omega_cubo
#print axioms ATK.Triadico.omega_ne_one
#print axioms ATK.Triadico.T_mul_T2
#print axioms ATK.Triadico.aplica
#print axioms ATK.Triadico.decomposicao
#print axioms ATK.Triadico.autovetor_0
#print axioms ATK.Triadico.autovetor_1
#print axioms ATK.Triadico.autovetor_2
#print axioms ATK.Triadico.proj_mul
#print axioms ATK.Triadico.idem_0
#print axioms ATK.Triadico.idem_1
#print axioms ATK.Triadico.idem_2
#print axioms ATK.Triadico.orto_01
#print axioms ATK.Triadico.orto_02
#print axioms ATK.Triadico.orto_12
#print axioms ATK.Triadico.orto_10
#print axioms ATK.Triadico.orto_20
#print axioms ATK.Triadico.orto_21
#print axioms ATK.Triadico.decomposicao_espectral
#print axioms ATK.Triadico.orbita_um_ou_tres
#print axioms ATK.Triadico.pontos_fixos_mod_tres
#print axioms ATK.Triadico.R_cubo
#print axioms ATK.Triadico.markov_circulante
#print axioms ATK.Triadico.markov_uniforme_estacionaria
