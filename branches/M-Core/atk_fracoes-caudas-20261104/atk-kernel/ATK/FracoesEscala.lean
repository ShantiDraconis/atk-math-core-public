import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ATK — A fração de escala: Navier–Stokes e Yang–Mills (rodada 103)

**Lei de escala** (`escala`): para `f : ℝ^d → F`, `k > 0`,
`∫ ‖k^a f(k x)‖^q dx = k^{a q − d} ∫ ‖f‖^q dx`. O expoente `a q − d` decide se a norma `L^q` vê ou não a
mudança de escala; a fração crítica é `q = d/a`.

* **Navier–Stokes** (`u_k(x, t) = k u(k x, k² t)`, `a = 1`): em `d = 3`, `L³` é crítica (`ns_L3_critico`)
  e a energia `L²` ganha `k^{−1}` (`ns_energia_3d`): a única quantidade controlada (energia) é
  **supercrítica** — a lacuna é `½` na escala de Sobolev (`Ḣ^{1/2}` é crítico, `L² = Ḣ⁰`). Em `d = 2` a
  energia é crítica (`ns_energia_2d`) e a regularidade global é teorema (Ladyzhenskaya). A condição de
  Prodi–Serrin `2/p + 3/q = 1` é a invariância de `L^p_t L^q_x` (`serrin_invariante`).
* **Yang–Mills** (`F_k(x) = k² F(k x)`, `a = 2`): em `d = 4` a energia `∫|F|²` é crítica
  (`ym_energia_4d`). A teoria clássica não tem escala de massa; o *gap* de massa do problema do milênio
  é quântico (transmutação dimensional, `β₀ = 11N/3`), fora desta lei.

Classificação: **ferramenta** (lei de mudança de variáveis) e **reformulação** (o que cada problema tem
de crítico). Nenhum dos dois problemas avança com isso: é o mapa de onde está a dificuldade.
-/

open MeasureTheory Module

namespace ATK.Fracoes.Escala

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Lei de escala** em `ℝ^d`. -/
theorem escala (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) {k : ℝ} (hk : 0 < k) (a q : ℝ) :
    ∫ x, ‖k ^ a • f (k • x)‖ ^ q ∂μ = k ^ (a * q - finrank ℝ E) * ∫ x, ‖f x‖ ^ q ∂μ := by
  have hka : 0 < k ^ a := Real.rpow_pos_of_pos hk a
  have e1 : ∀ x, ‖k ^ a • f (k • x)‖ ^ q = k ^ (a * q) * ‖f (k • x)‖ ^ q := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg hka.le, Real.mul_rpow hka.le (norm_nonneg _),
      ← Real.rpow_mul hk.le]
  simp_rw [e1]
  rw [integral_const_mul, Measure.integral_comp_smul μ (fun y => ‖f y‖ ^ q) k, smul_eq_mul, ← mul_assoc]
  congr 1
  have hkd : 0 < k ^ finrank ℝ E := pow_pos hk _
  rw [abs_of_pos (inv_pos.mpr hkd), Real.rpow_sub hk, Real.rpow_natCast, div_eq_mul_inv]

/-- A fração crítica: o expoente `a q − d` se anula exatamente em `q = d/a`. -/
theorem critico_iff {a q d : ℝ} (ha : a ≠ 0) : a * q - d = 0 ↔ q = d / a := by
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- **NS, `d = 3`**: `‖k u(k·)‖_{L³} = ‖u‖_{L³}`. -/
theorem ns_L3_critico (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {k : ℝ} (hk : 0 < k) :
    ∫ x, ‖k ^ (1 : ℝ) • u (k • x)‖ ^ (3 : ℝ) = ∫ x, ‖u x‖ ^ (3 : ℝ) := by
  rw [escala volume u hk, finrank_euclideanSpace_fin]
  norm_num

/-- **NS, `d = 3`**: a energia ganha `k^{−1}` — supercrítica. -/
theorem ns_energia_3d (u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {k : ℝ} (hk : 0 < k) :
    ∫ x, ‖k ^ (1 : ℝ) • u (k • x)‖ ^ (2 : ℝ) = k ^ (-1 : ℝ) * ∫ x, ‖u x‖ ^ (2 : ℝ) := by
  rw [escala volume u hk, finrank_euclideanSpace_fin]
  norm_num

/-- **NS, `d = 2`**: a energia é crítica. -/
theorem ns_energia_2d (u : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) {k : ℝ} (hk : 0 < k) :
    ∫ x, ‖k ^ (1 : ℝ) • u (k • x)‖ ^ (2 : ℝ) = ∫ x, ‖u x‖ ^ (2 : ℝ) := by
  rw [escala volume u hk, finrank_euclideanSpace_fin]
  norm_num

/-- **YM, `d = 4`**: `∫ |k² F(k·)|² = ∫ |F|²` — a energia de Yang–Mills é crítica. -/
theorem ym_energia_4d {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Fc : EuclideanSpace ℝ (Fin 4) → G) {k : ℝ} (hk : 0 < k) :
    ∫ x, ‖k ^ (2 : ℝ) • Fc (k • x)‖ ^ (2 : ℝ) = ∫ x, ‖Fc x‖ ^ (2 : ℝ) := by
  rw [escala volume Fc hk, finrank_euclideanSpace_fin]
  norm_num

/-- **Prodi–Serrin**: o peso de `‖u_k‖_{L^p_t L^q_x}` sob `u_k = k u(k x, k² t)` em `d = 3` é
`k^{1 − 2/p − 3/q}`; é invariante exatamente quando `2/p + 3/q = 1`. -/
theorem serrin_invariante {p q : ℝ} : 1 - 2 / p - 3 / q = 0 ↔ 2 / p + 3 / q = 1 := by
  constructor <;> intro h <;> linarith

/-- A lacuna de criticalidade (índice de Sobolev crítico menos o da energia): NS `d = 3` tem `½`,
NS `d = 2` e YM `d = 4` têm `0`. -/
theorem lacunas : ((3 : ℚ) / 2 - 1) - 0 = 1 / 2 ∧ ((2 : ℚ) / 2 - 1) - 0 = 0 ∧
    ((4 : ℚ) / 2 - 1) - 1 = 0 := by
  norm_num

end ATK.Fracoes.Escala

#print axioms ATK.Fracoes.Escala.escala
#print axioms ATK.Fracoes.Escala.critico_iff
#print axioms ATK.Fracoes.Escala.ns_L3_critico
#print axioms ATK.Fracoes.Escala.ns_energia_3d
#print axioms ATK.Fracoes.Escala.ns_energia_2d
#print axioms ATK.Fracoes.Escala.ym_energia_4d
#print axioms ATK.Fracoes.Escala.serrin_invariante
#print axioms ATK.Fracoes.Escala.lacunas
