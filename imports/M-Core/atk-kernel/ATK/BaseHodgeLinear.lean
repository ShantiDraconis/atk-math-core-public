/-
ATK.Base (H1) — Álgebra linear de Hodge (peso 1).

Primeira camada da base para Hodge.  Uma estrutura de Hodge de peso 1 é dada por um espaço
complexo `W` (a complexificação `H¹(X, ℝ) ⊗ ℂ`) com um operador `J` de quadrado `−1`
(a estrutura complexa induzida) e uma conjugação `σ` (semilinear, involutiva) que comuta com `J`.
Para toros complexos e, via teoria de Hodge, para variedades de Kähler compactas, `H¹` tem esta
forma.  Aqui:

* **`decomposicao_hodge`**: `W = H^{1,0} ⊕ H^{0,1}` com `H^{1,0} = ker(J − i)` e
  `H^{0,1} = ker(J + i)`;
* **`conj_H10`**, **`conj_H01`**: `σ` troca `H^{1,0}` e `H^{0,1}` (simetria de Hodge);
* **`simetria_hodge`**: `h^{1,0} = h^{0,1}`;
* **`dim_par`**: `dim W = 2 h^{1,0}` — a sombra linear do fato de que o primeiro número de Betti
  de uma variedade de Kähler compacta é par.

A teoria de Hodge propriamente dita (formas harmônicas, `H^k = ⊕ H^{p,q}` em Kähler) e o teorema
(1,1) de Lefschetz continuam fora do alcance da Mathlib atual (camadas H2–H3).
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module

open Complex ComplexConjugate

namespace ATK.BaseHodgeLinear

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Operador de estrutura complexa: `J² = −1`. -/
structure EstruturaComplexa (W : Type*) [AddCommGroup W] [Module ℂ W] where
  J : W →ₗ[ℂ] W
  J_sq : ∀ w, J (J w) = -w

variable (E : EstruturaComplexa W)

/-- `H^{1,0} = ker(J − i)`. -/
def H10 : Submodule ℂ W := LinearMap.ker (E.J - I • LinearMap.id)

/-- `H^{0,1} = ker(J + i)`. -/
def H01 : Submodule ℂ W := LinearMap.ker (E.J + I • LinearMap.id)

theorem mem_H10 {w : W} : w ∈ H10 E ↔ E.J w = I • w := by
  simp [H10, sub_eq_zero]

theorem mem_H01 {w : W} : w ∈ H01 E ↔ E.J w = -(I • w) := by
  simp [H01, add_eq_zero_iff_eq_neg]

theorem disjoint_H : Disjoint (H10 E) (H01 E) := by
  rw [Submodule.disjoint_def]
  intro w h1 h2
  rw [mem_H10] at h1
  rw [mem_H01] at h2
  have h : I • w = -(I • w) := h1.symm.trans h2
  have h' : (2 * I) • w = 0 := by
    rw [mul_smul, two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h').resolve_left (mul_ne_zero two_ne_zero I_ne_zero)

theorem I_smul_I_smul (v : W) : I • I • v = -v := by
  rw [smul_smul, I_mul_I, neg_one_smul]

theorem codisjoint_H : Codisjoint (H10 E) (H01 E) := by
  rw [codisjoint_iff, eq_top_iff]
  intro w _
  rw [Submodule.mem_sup]
  refine ⟨(1 / 2 : ℂ) • (w - I • E.J w), ?_, (1 / 2 : ℂ) • (w + I • E.J w), ?_, ?_⟩
  · rw [mem_H10, map_smul, map_sub, map_smul, E.J_sq, smul_comm I (1 / 2 : ℂ),
      smul_sub I w (I • E.J w), I_smul_I_smul]
    module
  · rw [mem_H01, map_smul, map_add, map_smul, E.J_sq, smul_comm I (1 / 2 : ℂ),
      smul_add I w (I • E.J w), I_smul_I_smul]
    module
  · rw [← smul_add, sub_add_add_cancel, ← two_smul ℂ w, smul_smul]
    norm_num

/-- **Decomposição de Hodge (peso 1)**: `W = H^{1,0} ⊕ H^{0,1}`. -/
theorem decomposicao_hodge : IsCompl (H10 E) (H01 E) :=
  ⟨disjoint_H E, codisjoint_H E⟩

/-! ### Simetria de Hodge -/

variable (σ : W →ₛₗ[starRingEnd ℂ] W)

/-- `σ` leva `H^{1,0}` em `H^{0,1}`. -/
theorem conj_H10 (hσ : ∀ w, σ (E.J w) = E.J (σ w)) {w : W} (hw : w ∈ H10 E) :
    σ w ∈ H01 E := by
  rw [mem_H10] at hw
  rw [mem_H01, ← hσ, hw, LinearMap.map_smulₛₗ, starRingEnd_apply, star_def, conj_I, neg_smul]

/-- `σ` leva `H^{0,1}` em `H^{1,0}`. -/
theorem conj_H01 (hσ : ∀ w, σ (E.J w) = E.J (σ w)) {w : W} (hw : w ∈ H01 E) :
    σ w ∈ H10 E := by
  rw [mem_H01] at hw
  rw [mem_H10, ← hσ, hw, map_neg, LinearMap.map_smulₛₗ, starRingEnd_apply, star_def, conj_I,
    neg_smul, neg_neg]

/-- A conjugação restrita, como equivalência aditiva `H^{1,0} ≃ H^{0,1}`. -/
def conjEquiv (hσ : ∀ w, σ (E.J w) = E.J (σ w)) (hinv : ∀ w, σ (σ w) = w) :
    H10 E ≃+ H01 E where
  toFun w := ⟨σ w.1, conj_H10 E σ hσ w.2⟩
  invFun w := ⟨σ w.1, conj_H01 E σ hσ w.2⟩
  left_inv w := Subtype.ext (hinv w.1)
  right_inv w := Subtype.ext (hinv w.1)
  map_add' a b := Subtype.ext (map_add σ a.1 b.1)

/-- **Simetria de Hodge**: `h^{1,0} = h^{0,1}`. -/
theorem simetria_hodge (hσ : ∀ w, σ (E.J w) = E.J (σ w)) (hinv : ∀ w, σ (σ w) = w) :
    Module.finrank ℂ (H10 E) = Module.finrank ℂ (H01 E) := by
  have h := rank_eq_of_equiv_equiv (starRingEnd ℂ) (conjEquiv E σ hσ hinv)
    (Function.Involutive.bijective fun z => Complex.conj_conj z)
    fun c w => Subtype.ext (LinearMap.map_smulₛₗ σ c (w : W))
  unfold Module.finrank
  rw [h]

/-- **`dim W = 2 h^{1,0}`**: o "primeiro número de Betti" é par. -/
theorem dim_par [FiniteDimensional ℂ W] (hσ : ∀ w, σ (E.J w) = E.J (σ w))
    (hinv : ∀ w, σ (σ w) = w) :
    Module.finrank ℂ W = 2 * Module.finrank ℂ (H10 E) := by
  rw [← Submodule.finrank_add_eq_of_isCompl (decomposicao_hodge E), ← simetria_hodge E σ hσ hinv]
  ring

end ATK.BaseHodgeLinear

#print axioms ATK.BaseHodgeLinear.mem_H10
#print axioms ATK.BaseHodgeLinear.mem_H01
#print axioms ATK.BaseHodgeLinear.disjoint_H
#print axioms ATK.BaseHodgeLinear.I_smul_I_smul
#print axioms ATK.BaseHodgeLinear.codisjoint_H
#print axioms ATK.BaseHodgeLinear.decomposicao_hodge
#print axioms ATK.BaseHodgeLinear.conj_H10
#print axioms ATK.BaseHodgeLinear.conj_H01
#print axioms ATK.BaseHodgeLinear.simetria_hodge
#print axioms ATK.BaseHodgeLinear.dim_par
