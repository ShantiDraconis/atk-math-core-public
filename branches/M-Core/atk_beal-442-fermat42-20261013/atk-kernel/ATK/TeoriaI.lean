import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ATK — Teoria I: o que a álgebra permite (e proíbe) para `0/0`

**Fenômeno.** `0/0` não tem valor: como forma de limite, ele pode dar qualquer número real.

**O que este arquivo prova (sem axiomas novos):**

* `valoresZeroSobreZero_eq_univ`: o conjunto dos valores possíveis da forma `0/0`
  (limites de `f/g` com `f, g → 0`) é **todo** `ℝ`. É o modelo concreto de "indeterminada".
* `absorvente_eq_zero`: em qualquer estrutura com `0 · x = 0` (todo anel), um elemento absorvente
  (`x · e = e` para todo `x`) **é** o próprio `0`. Logo não existe um `⊥ = 0/0` absorvente e
  distinto de `0` dentro de um anel (`sem_absorvente_nao_nulo`).
* `falhaAbsorcao_falsa_em_R`: a condição `¬ ∃ e, ∀ x, x * e = e` é **falsa** em `ℝ` (`e = 0`);
  uma estrutura que a exija de `ℝ` não tem habitante.
* `zero_sem_inverso`, `divisao_total_colapsa`: num anel não trivial `0` não tem inverso, e uma
  divisão total com `(x/0)·0 = x` força o anel a ser trivial.
* `convencao_mathlib`: a convenção da Mathlib (`0⁻¹ = 0`, logo `0/0 = 0`) é consistente — ela
  abandona `(x/y)·y = x` em `y = 0`, não a distributividade.

**Literatura.** Teorias totais para `0/0` já existem e abrem mão de leis de anel de forma
controlada: rodas (*wheels*, Carlström 2004: `0·x = 0` deixa de valer em geral) e *common
meadows* (Bergstra–Ponse: um elemento `⊥` absorvente para `+` e `·`). Uma "Teoria I" nova precisa
dizer qual lei de anel abandona e comparar-se com essas duas; os teoremas acima mostram que
alguma lei **tem** de ser abandonada.
-/

open Filter Topology

namespace ATK.TeoriaI

/-! ## No-go algébricos -/

/-- Em qualquer `MulZeroClass` (todo anel), um elemento absorvente é `0`. -/
theorem absorvente_eq_zero {R : Type*} [MulZeroClass R] {e : R} (h : ∀ x, x * e = e) : e = 0 := by
  have h0 := h 0
  rw [zero_mul] at h0
  exact h0.symm

/-- Não existe `⊥` absorvente e distinto de `0` num anel. -/
theorem sem_absorvente_nao_nulo {R : Type*} [MulZeroClass R] :
    ¬ ∃ e : R, e ≠ 0 ∧ ∀ x, x * e = e := by
  rintro ⟨e, he, h⟩
  exact he (absorvente_eq_zero h)

/-- A condição `¬ ∃ e, ∀ x, x * e = e` é falsa em `ℝ`: `e = 0` é absorvente. -/
theorem falhaAbsorcao_falsa_em_R : ∃ e : ℝ, ∀ x : ℝ, x * e = e :=
  ⟨0, fun x => mul_zero x⟩

/-- Num anel não trivial, `0` não tem inverso. -/
theorem zero_sem_inverso {R : Type*} [MulZeroOneClass R] [Nontrivial R] (z : R) : 0 * z ≠ 1 := by
  rw [zero_mul]
  exact zero_ne_one

/-- Uma divisão total com `(x / 0) · 0 = x` força todo elemento a ser `0`. -/
theorem divisao_total_colapsa {R : Type*} [MulZeroClass R] (div : R → R → R)
    (h : ∀ x, div x 0 * 0 = x) (x : R) : x = 0 := by
  have hx := h x
  rw [mul_zero] at hx
  exact hx.symm

/-- A convenção da Mathlib: `0 / 0 = 0` em `ℝ`. -/
theorem convencao_mathlib : (0 : ℝ) / 0 = 0 := div_zero 0

/-! ## Modelo concreto: os valores da forma `0/0` -/

/-- Valores possíveis de `0/0`: limites de `f/g` quando `f, g → 0` (em `t → 0`, `t ≠ 0`). -/
def valoresZeroSobreZero : Set ℝ :=
  {L | ∃ f g : ℝ → ℝ, Tendsto f (𝓝[≠] 0) (𝓝 0) ∧ Tendsto g (𝓝[≠] 0) (𝓝 0) ∧
    Tendsto (fun t => f t / g t) (𝓝[≠] 0) (𝓝 L)}

/-- **`0/0` pode valer qualquer real**: o conjunto de valores é `ℝ` inteiro. -/
theorem valoresZeroSobreZero_eq_univ : valoresZeroSobreZero = Set.univ := by
  ext L
  simp only [valoresZeroSobreZero, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  refine ⟨fun t => L * t, fun t => t, ?_, ?_, ?_⟩
  · have hc : Tendsto (fun t : ℝ => L * t) (𝓝 0) (𝓝 (L * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  · exact (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (mul_div_cancel_right₀ L ht).symm

/-- Consequência: nenhum valor único representa `0/0` como limite. -/
theorem zeroSobreZero_nao_unico : ∀ L : ℝ, ∃ L' : ℝ, L' ≠ L ∧ L' ∈ valoresZeroSobreZero := by
  intro L
  refine ⟨L + 1, by linarith, ?_⟩
  rw [valoresZeroSobreZero_eq_univ]
  trivial

end ATK.TeoriaI

#print axioms ATK.TeoriaI.absorvente_eq_zero
#print axioms ATK.TeoriaI.sem_absorvente_nao_nulo
#print axioms ATK.TeoriaI.falhaAbsorcao_falsa_em_R
#print axioms ATK.TeoriaI.zero_sem_inverso
#print axioms ATK.TeoriaI.divisao_total_colapsa
#print axioms ATK.TeoriaI.convencao_mathlib
#print axioms ATK.TeoriaI.valoresZeroSobreZero_eq_univ
#print axioms ATK.TeoriaI.zeroSobreZero_nao_unico
