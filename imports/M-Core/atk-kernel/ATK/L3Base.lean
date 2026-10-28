import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# ATK — L3, base: estruturas de Hodge e estruturas de Kähler

Rascunho no estilo da Mathlib para a ligação L3 (Hodge), nos dois PRs sugeridos:

* **PR 1 — Kähler** (modelo local): `Hermitiana E` é um produto interno real num espaço complexo
  invariante por `J = i •`, com forma fundamental `ω(v, w) = g(Jv, w)` (antissimétrica, alternada,
  `J`-invariante). `KahlerLocal U` é uma métrica hermitiana suave num aberto `U` cuja forma
  fundamental é fechada (`extDerivWithin … = 0`, com a derivada exterior da Mathlib em espaços
  normados). É o modelo de uma carta de uma variedade de Kähler; a versão em variedades depende de
  formas diferenciais em variedades, que a Mathlib ainda não tem.
* **PR 2 — classes de Hodge**: `HodgeStructure V n` é uma estrutura de Hodge racional pura de peso
  `n` (`V_ℂ = ⨁ H^{p, n−p}`, com `conj H^{p,q} = H^{q,p}`); `IsHodgeClass` (vetor racional em
  `H^{p,p}`, peso `2p`) e `hodgeClasses`, um subespaço racional.

**Testes de sanidade**: a métrica plana de `ℂ` é de Kähler (`planaKahler`) e `ω(1, i) = 1`
(`plana_ω`); a estrutura de Tate `ℚ(−1)` tem `1` como classe de Hodge e `H^{2,0} = 0`.

Para a conjectura de Hodge falta, na Mathlib, a cohomologia singular `H^{2p}(X, ℚ)` de uma
variedade projetiva complexa lisa com sua decomposição de Hodge e a aplicação classe de ciclo. Nada
aqui prova a conjectura de Hodge. **CLOSED_MATH continua false.**
-/

open TensorProduct

namespace ATK.L3Base

/-! ## Estruturas de Hodge racionais e classes de Hodge -/

section hodge

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- A conjugação complexa, como mapa `ℚ`-linear. -/
noncomputable def conjQ : ℂ →ₗ[ℚ] ℂ := (Complex.conjAe.toLinearMap).restrictScalars ℚ

@[simp] theorem conjQ_apply (z : ℂ) : conjQ z = (starRingEnd ℂ) z := rfl

/-- A conjugação em `V_ℂ = ℂ ⊗[ℚ] V` (no primeiro fator). -/
noncomputable def conjV : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V := TensorProduct.map conjQ LinearMap.id

@[simp] theorem conjV_tmul (z : ℂ) (v : V) : conjV V (z ⊗ₜ v) = (starRingEnd ℂ z) ⊗ₜ v := rfl

/-- A conjugação é uma involução. -/
theorem conjV_conjV (x : ℂ ⊗[ℚ] V) : conjV V (conjV V x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conjV_surjective : Function.Surjective (conjV V) :=
  fun x => ⟨conjV V x, conjV_conjV V x⟩

/-- **Estrutura de Hodge racional pura de peso `n`**: `V_ℂ = ⨁_p H^{p, n−p}` e a conjugação
troca `H^{p, n−p}` com `H^{n−p, p}`. -/
structure HodgeStructure (n : ℤ) where
  /-- `H p` é o espaço `H^{p, n−p}`. -/
  H : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Decomposição em soma direta. -/
  isInternal : DirectSum.IsInternal H
  /-- Simetria de Hodge: `conj H^{p,q} = H^{q,p}`. -/
  conj_eq : ∀ p, conjV V '' (H p : Set (ℂ ⊗[ℚ] V)) = H (n - p)

variable {V}

/-- **Classe de Hodge**: em peso `2p`, um vetor racional cuja imagem em `V_ℂ` está em `H^{p,p}`. -/
def IsHodgeClass {p : ℤ} (h : HodgeStructure V (2 * p)) (v : V) : Prop :=
  (1 : ℂ) ⊗ₜ[ℚ] v ∈ h.H p

/-- As classes de Hodge formam um subespaço racional. -/
def hodgeClasses {p : ℤ} (h : HodgeStructure V (2 * p)) : Submodule ℚ V where
  carrier := {v | IsHodgeClass h v}
  zero_mem' := by simp [IsHodgeClass]
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, IsHodgeClass, tmul_add] at *
    exact add_mem ha hb
  smul_mem' := fun q v hv => by
    simp only [Set.mem_ofPred_eq, IsHodgeClass] at *
    have : (1 : ℂ) ⊗ₜ[ℚ] (q • v) = (q : ℂ) • ((1 : ℂ) ⊗ₜ[ℚ] v) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Rat.smul_one_eq_cast, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hv

/-- Estrutura pura de tipo `(p₀, p₀)`: `V_ℂ = H^{p₀, p₀}`. -/
noncomputable def puraTipo (p₀ : ℤ) : HodgeStructure V (2 * p₀) where
  H p := if p = p₀ then ⊤ else ⊥
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro i
      by_cases hi : i = p₀
      · subst hi
        have : (⨆ (j : ℤ) (_ : j ≠ i), (if j = i then ⊤ else ⊥ : Submodule ℂ (ℂ ⊗[ℚ] V))) = ⊥ := by
          simp only [iSup_eq_bot]
          intro j hj
          simp [hj]
        rw [this]
        exact disjoint_bot_right
      · simp only [hi, ite_false]
        exact disjoint_bot_left
    · refine eq_top_iff.mpr (le_iSup_of_le p₀ ?_)
      simp
  conj_eq := fun p => by
    by_cases hp : p = p₀
    · subst hp
      simp only [show 2 * p - p = p by ring, ite_true, Submodule.top_coe, Set.image_univ,
        (conjV_surjective V).range_eq]
    · have hq : ¬ (2 * p₀ - p = p₀) := fun h => hp (by omega)
      simp only [hp, hq, ite_false, Submodule.bot_coe, Set.image_singleton, map_zero]

/-- Em `puraTipo p₀`, todo vetor racional é uma classe de Hodge. -/
theorem isHodgeClass_puraTipo (p₀ : ℤ) (v : V) : IsHodgeClass (puraTipo (V := V) p₀) v := by
  simp [IsHodgeClass, puraTipo]

end hodge

/-! ### Teste de sanidade: a estrutura de Tate `ℚ(−1)` -/

/-- A estrutura de Tate `ℚ(−1)`: `ℚ` com peso 2 e tipo `(1, 1)` (a de `H²` da reta projetiva). -/
noncomputable def tate : HodgeStructure ℚ (2 * 1) := puraTipo 1

/-- **Teste**: `1 ∈ ℚ(−1)` é uma classe de Hodge (a classe de um ponto em `H²(ℙ¹)`). -/
theorem tate_classe : IsHodgeClass tate (1 : ℚ) := isHodgeClass_puraTipo 1 1

/-- **Teste**: as classes de Hodge de `ℚ(−1)` são todo `ℚ`. -/
theorem tate_classes : hodgeClasses tate = ⊤ :=
  eq_top_iff.mpr fun v _ => isHodgeClass_puraTipo 1 v

/-- **Teste**: na decomposição de `ℚ(−1)`, `H^{2,0} = 0`. -/
theorem tate_H20 : tate.H 2 = ⊥ := by simp [tate, puraTipo]

/-! ## Estruturas de Kähler (modelo local) -/

section kahler

open Complex
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplicação por `i`, como mapa `ℝ`-linear contínuo (a estrutura complexa `J`). -/
noncomputable def Jm : E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ I

@[simp] theorem Jm_apply (v : E) : (Jm : E →L[ℝ] E) v = I • v := rfl

variable (E) in
/-- **Estrutura hermitiana** (linear) num espaço complexo: um produto interno real `g`
invariante pela estrutura complexa `J = i •`. -/
structure Hermitiana where
  /-- O produto interno real. -/
  g : E →L[ℝ] E →L[ℝ] ℝ
  symm : ∀ v w, g v w = g w v
  pos : ∀ v, v ≠ 0 → 0 < g v v
  J_inv : ∀ v w, g (I • v) (I • w) = g v w

namespace Hermitiana

variable (h : Hermitiana E)

/-- A **forma fundamental** `ω(v, w) = g(J v, w)`. -/
noncomputable def ω : E →L[ℝ] E →L[ℝ] ℝ := h.g.comp Jm

theorem ω_apply (v w : E) : h.ω v w = h.g (I • v) w := rfl

/-- `ω` é antissimétrica. -/
theorem ω_antisymm (v w : E) : h.ω v w = - h.ω w v := by
  rw [ω_apply, ω_apply, ← h.J_inv (I • v) w, smul_smul, I_mul_I, neg_one_smul, map_neg,
    neg_apply, h.symm v]

/-- `ω` é alternada. -/
theorem ω_self (v : E) : h.ω v v = 0 := by
  have := h.ω_antisymm v v
  linarith

/-- `ω` é `J`-invariante. -/
theorem ω_J (v w : E) : h.ω (I • v) (I • w) = h.ω v w := by
  rw [ω_apply, ω_apply, h.J_inv]

/-- A forma fundamental como 2-forma alternada contínua (normalização: a alternância de `ω`,
isto é `2ω`). -/
noncomputable def forma : E [⋀^Fin 2]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
      : (E →L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)).comp h.ω)

end Hermitiana

/-- **Métrica de Kähler local** num aberto `U` de um espaço complexo (o modelo de uma carta de uma
variedade de Kähler): uma métrica hermitiana em cada ponto, suave, com forma fundamental fechada. -/
structure KahlerLocal (U : Set E) where
  /-- A métrica em cada ponto. -/
  h : E → Hermitiana E
  /-- Suavidade da forma fundamental. -/
  suave : ContDiffOn ℝ ⊤ (fun x => (h x).forma) U
  /-- `dω = 0`. -/
  fechada : ∀ x ∈ U, extDerivWithin (fun x => (h x).forma) U x = 0

/-! ### Teste de sanidade: a métrica plana de `ℂ` -/

/-- A métrica plana de `ℂ`: `g(v, w) = Re (conj v · w)`. -/
noncomputable def plana : Hermitiana ℂ where
  g := (innerSL ℝ (E := ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  symm v w := real_inner_comm w v
  pos v hv := real_inner_self_pos.mpr hv
  J_inv v w := by
    change ⟪I • v, I • w⟫_ℝ = ⟪v, w⟫_ℝ
    simp only [smul_eq_mul, Complex.inner, map_mul, conj_I]
    ring_nf
    simp

/-- **Teste**: `ω(1, i) = 1` (a forma de área usual). -/
theorem plana_ω : plana.ω 1 I = 1 := by
  change ⟪I • (1 : ℂ), I⟫_ℝ = 1
  simp

/-- **Teste**: a métrica plana constante é de Kähler em todo `ℂ`. -/
noncomputable def planaKahler : KahlerLocal (Set.univ : Set ℂ) where
  h := fun _ => plana
  suave := contDiffOn_const
  fechada := fun x _ => by
    simp only [extDerivWithin, fderivWithin_const_apply]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero]

end kahler

end ATK.L3Base

#print axioms ATK.L3Base.conjV_conjV
#print axioms ATK.L3Base.conjV_surjective
#print axioms ATK.L3Base.isHodgeClass_puraTipo
#print axioms ATK.L3Base.tate_classe
#print axioms ATK.L3Base.tate_classes
#print axioms ATK.L3Base.tate_H20
#print axioms ATK.L3Base.Hermitiana.ω_apply
#print axioms ATK.L3Base.Hermitiana.ω_antisymm
#print axioms ATK.L3Base.Hermitiana.ω_self
#print axioms ATK.L3Base.Hermitiana.ω_J
#print axioms ATK.L3Base.plana_ω
