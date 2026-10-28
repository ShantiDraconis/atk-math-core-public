import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-!
# ATK — Cálculo de hipóteses: derivação, redução, corte, componentes e base minimal

Formaliza as regras de contabilidade usadas no `HYPOTHESIS_MAP` e em `ATK.BridgeReduction`:
uma família de hipóteses `P : ι → Prop`, um conjunto finito de índices `H` e um alvo `T`.

* `Derives P H T` — as hipóteses de `H` juntas implicam `T`;
* `derives_mono` (monotonia), `derives_cut` (corte), `derives_reduce` e `reduction_invariant`
  (trocar hipóteses por outras que as implicam / equivalentes);
* `reach_imp`, `scc_iff` — num grafo de implicações **provadas**, alcançabilidade mútua dá
  equivalência (componente fortemente conexa = uma hipótese só);
* `exists_minimal_basis` — todo conjunto que deriva `T` contém uma base minimal por inclusão.

**Ressalva semântica, provada aqui** (`derives_empty_iff`, `minimal_basis_eq_empty_of_true`):
dentro do Lean, "`H` deriva `T`" é a *proposição* `(∀ i ∈ H, P i) → T`. Se `T` é verdadeiro, o
conjunto vazio já deriva `T`, e a única base minimal é `∅`. Logo nenhuma minimização feita
*dentro* do kernel separa "conjecturas irredutíveis" de "hipóteses redundantes": isso é uma
questão de **provabilidade** (metamatemática), não de verdade. O que o kernel certifica de fato
são as **arestas** — implicações já provadas, como `ATK.BridgeReduction.pontes_iff_restantes`.
Matemática elementar; nenhuma obrigação O1–O8 muda. **CLOSED_MATH continua false.**
-/

namespace ATK.HypothesisCalculus

variable {ι : Type*} (P : ι → Prop)

/-- As hipóteses indexadas por `H` juntas implicam `T`. -/
def Derives (H : Finset ι) (T : Prop) : Prop :=
  (∀ i ∈ H, P i) → T

/-- Sem hipóteses, derivar `T` é o mesmo que `T`. -/
theorem derives_empty_iff {T : Prop} : Derives P ∅ T ↔ T :=
  ⟨fun h => h (by simp), fun h _ => h⟩

/-- **Monotonia**: acrescentar hipóteses preserva derivações. -/
theorem derives_mono {H H' : Finset ι} (hsub : H ⊆ H') {T : Prop} (h : Derives P H T) :
    Derives P H' T :=
  fun hH' => h fun i hi => hH' i (hsub hi)

/-- **Corte**: se `H` deriva `P j` e `insert j H` deriva `T`, então `H` deriva `T`. -/
theorem derives_cut [DecidableEq ι] {H : Finset ι} {j : ι} {T : Prop}
    (hj : Derives P H (P j)) (hT : Derives P (insert j H) T) : Derives P H T := by
  intro hH
  apply hT
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact hj hH
  · exact hH i hi

/-- **Redução**: se cada hipótese de `H` é implicada pelas de `H'`, toda derivação a partir de
`H` vira derivação a partir de `H'`. -/
theorem derives_reduce {κ : Type*} (Q : κ → Prop) {H : Finset ι} {H' : Finset κ} {T : Prop}
    (hred : ∀ i ∈ H, (∀ k ∈ H', Q k) → P i) (h : Derives P H T) : Derives Q H' T :=
  fun hH' => h fun i hi => hred i hi hH'

/-- **Invariância de redução**: famílias que se implicam mutuamente derivam os mesmos alvos. -/
theorem reduction_invariant {κ : Type*} (Q : κ → Prop) {H : Finset ι} {H' : Finset κ} {T : Prop}
    (hred : ∀ i ∈ H, (∀ k ∈ H', Q k) → P i) (hred' : ∀ k ∈ H', (∀ i ∈ H, P i) → Q k) :
    Derives P H T ↔ Derives Q H' T :=
  ⟨derives_reduce P Q hred, derives_reduce Q P hred'⟩

/-- Num grafo cujas arestas são implicações provadas, alcançar dá implicação. -/
theorem reach_imp {R : ι → ι → Prop} (hR : ∀ i j, R i j → P i → P j) {i j : ι}
    (h : Relation.ReflTransGen R i j) : P i → P j := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hi => hR _ _ hbc (ih hi)

/-- **Componente fortemente conexa**: alcançabilidade mútua dá equivalência. -/
theorem scc_iff {R : ι → ι → Prop} (hR : ∀ i j, R i j → P i → P j) {i j : ι}
    (h₁ : Relation.ReflTransGen R i j) (h₂ : Relation.ReflTransGen R j i) : P i ↔ P j :=
  ⟨reach_imp P hR h₁, reach_imp P hR h₂⟩

/-- **Base minimal**: todo `H` que deriva `T` contém `H' ⊆ H` que deriva `T` e do qual nenhuma
hipótese pode ser retirada. -/
theorem exists_minimal_basis [DecidableEq ι] :
    ∀ (H : Finset ι) {T : Prop}, Derives P H T →
      ∃ H' ⊆ H, Derives P H' T ∧ ∀ j ∈ H', ¬ Derives P (H'.erase j) T := by
  intro H
  induction H using Finset.strongInduction with
  | _ H ih =>
    intro T h
    by_cases hmin : ∀ j ∈ H, ¬ Derives P (H.erase j) T
    · exact ⟨H, subset_refl _, h, hmin⟩
    · push Not at hmin
      obtain ⟨j, hj, hder⟩ := hmin
      obtain ⟨H', hsub, hH', hmin'⟩ := ih (H.erase j) (Finset.erase_ssubset hj) hder
      exact ⟨H', hsub.trans (Finset.erase_subset _ _), hH', hmin'⟩

/-- **Ressalva**: se o alvo é verdadeiro, a única base minimal é `∅`. A minimalidade dentro do
kernel mede verdade, não provabilidade. -/
theorem minimal_basis_eq_empty_of_true [DecidableEq ι] {T : Prop} (hT : T) {H' : Finset ι}
    (hmin : ∀ j ∈ H', ¬ Derives P (H'.erase j) T) : H' = ∅ := by
  by_contra hne
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact hmin j hj fun _ => hT

end ATK.HypothesisCalculus

#print axioms ATK.HypothesisCalculus.derives_empty_iff
#print axioms ATK.HypothesisCalculus.derives_mono
#print axioms ATK.HypothesisCalculus.derives_cut
#print axioms ATK.HypothesisCalculus.derives_reduce
#print axioms ATK.HypothesisCalculus.reduction_invariant
#print axioms ATK.HypothesisCalculus.reach_imp
#print axioms ATK.HypothesisCalculus.scc_iff
#print axioms ATK.HypothesisCalculus.exists_minimal_basis
#print axioms ATK.HypothesisCalculus.minimal_basis_eq_empty_of_true
