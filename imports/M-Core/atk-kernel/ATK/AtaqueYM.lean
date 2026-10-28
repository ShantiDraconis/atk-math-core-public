/-
ATK — Programa de ataque, frente Yang–Mills: a interface entre a positividade por reflexão
abstrata (Y3) e a ação de Wilson refletida (Y3').

* `FormaRefletida μ S`: a ação `S` em `Ω = X × X` se escreve como
  `−S(a, b) = B(a) + B(b) + Σᵢ cᵢ Cᵢ(a) Cᵢ(b)` com `cᵢ ≥ 0` e funções limitadas mensuráveis;
* **`rp_de_forma`**: `FormaRefletida ⇒` positividade por reflexão de `e^{−S}`
  (`⟨Θ(F)·F⟩ ≥ 0` para toda `F` limitada mensurável) — consequência de
  `ATK.BasePositividadeReflexao`;
* **`forma_soma`**: a forma refletida é estável por soma de ações (plaquetas de cada metade e
  plaquetas que cruzam o plano podem ser tratadas separadamente);
* **`forma_metade`**: ações que só dependem de uma metade de cada lado (`B(a) + B(b)`) têm a
  forma, com cruzamento vazio.

O alvo Y3' é provar `FormaRefletida` para a ação de Wilson numa rede com reflexão por um plano
(com fixação de calibre nos elos que cruzam); Y4 (gap em acoplamento forte) vem depois.
-/
import ATK.BasePositividadeReflexao

open MeasureTheory

namespace ATK.AtaqueYM

open ATK.BasePositividadeReflexao

variable {X : Type*} [MeasurableSpace X]

/-- `−S(a, b) = B(a) + B(b) + Σᵢ cᵢ Cᵢ(a) Cᵢ(b)` com `cᵢ ≥ 0`, tudo limitado e mensurável. -/
def FormaRefletida (S : X × X → ℝ) : Prop :=
  ∃ (n : ℕ) (B : X → ℝ) (C : Fin n → X → ℝ) (c : Fin n → ℝ),
    (∀ i, 0 ≤ c i) ∧ Measurable B ∧ (∀ i, Measurable (C i)) ∧
    (∃ MB, ∀ a, |B a| ≤ MB) ∧ (∃ MC, ∀ i a, |C i a| ≤ MC) ∧
    ∀ z, -S z = B z.1 + B z.2 + ∑ i, c i * C i z.1 * C i z.2

/-- **Forma refletida ⇒ positividade por reflexão.** -/
theorem rp_de_forma (μ : Measure X) [IsFiniteMeasure μ] {S : X × X → ℝ}
    (hS : FormaRefletida S) {F : X → ℝ} (hF : Measurable F) {MF : ℝ} (hFb : ∀ a, |F a| ≤ MF) :
    0 ≤ ∫ z, F z.1 * F z.2 * Real.exp (-S z) ∂(μ.prod μ) := by
  obtain ⟨n, B, C, c, hc, hB, hC, ⟨MB, hBb⟩, ⟨MC, hCb⟩, hS⟩ := hS
  simp_rw [hS]
  exact positividade_reflexao_coef μ hc hF hB hC hFb hBb hCb

/-- Ações só de metades têm a forma refletida (cruzamento vazio). -/
theorem forma_metade {B : X → ℝ} (hB : Measurable B) {MB : ℝ} (hBb : ∀ a, |B a| ≤ MB) :
    FormaRefletida fun z : X × X => -(B z.1 + B z.2) := by
  refine ⟨0, B, Fin.elim0, Fin.elim0, fun i => i.elim0, hB, fun i => i.elim0, ⟨MB, hBb⟩,
    ⟨0, fun i => i.elim0⟩, fun z => ?_⟩
  simp

/-- **Estabilidade por soma**: as partes de uma ação podem ser decompostas separadamente. -/
theorem forma_soma {S T : X × X → ℝ} (hS : FormaRefletida S) (hT : FormaRefletida T) :
    FormaRefletida fun z => S z + T z := by
  obtain ⟨n, B, C, c, hc, hB, hC, ⟨MB, hBb⟩, ⟨MC, hCb⟩, hS⟩ := hS
  obtain ⟨m, B', C', c', hc', hB', hC', ⟨MB', hBb'⟩, ⟨MC', hCb'⟩, hT⟩ := hT
  refine ⟨n + m, fun a => B a + B' a, Fin.append C C', Fin.append c c', ?_, hB.add hB', ?_,
    ⟨MB + MB', fun a => (abs_add_le _ _).trans (add_le_add (hBb a) (hBb' a))⟩,
    ⟨max MC MC', ?_⟩, fun z => ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hc j
    · simpa using hc' j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hC j
    · simpa using hC' j
  · intro i a
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using (hCb j a).trans (le_max_left _ _)
    · simpa using (hCb' j a).trans (le_max_right _ _)
  · rw [neg_add, hS z, hT z, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

end ATK.AtaqueYM

#print axioms ATK.AtaqueYM.rp_de_forma
#print axioms ATK.AtaqueYM.forma_metade
#print axioms ATK.AtaqueYM.forma_soma
