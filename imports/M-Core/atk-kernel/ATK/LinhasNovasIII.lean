import ATK.LinhasNovasII
import Mathlib.Data.Int.SuccPred

/-!
# Linhas novas III: vereditos afiados

* **Cauda**: `ℤ[1/10]` é denso, enumerável e **não fechado** (`conjunto_not_closed`): `1/3` está
  no fecho e fora do conjunto (`um_terco_no_fecho`).
* **Truncamento**: com alfabeto finito, `∃ k, trunc L k = L ⟺ L` finita (`trunc_eq_self_iff`). O
  truncamento colapsa exatamente as linguagens finitas; saber qual `k` basta é saber `L`.
* **Ordem**: `ℕ` sem topo, `ℕ∞` com topo; "existe maior abaixo de cada ponto não mínimo" ⟺
  `PredOrder` (`maior_abaixo_iff_predOrder`), que unifica `int_maior_negativo` e
  `sem_maior_negativo`: `ℤ` tem predecessor, `ℝ` não tem (`real_sem_pred`).
* **Involução**: **refutação** de "toda involução estritamente decrescente de `ℝ` é `x ↦ a − x`":
  `quebrada` (`−2x` à esquerda de 0, `−x/2` à direita) é contraexemplo
  (`strictAnti_involutive_nao_afim`). O centro único existe (`quebrada_fixo`), mas não é reflexão.
* **Morfismos de involuções**: `Hom` comuta com `σ` e leva fixos em fixos; o colapso `∞ = 0` é um
  morfismo `invProj → invReal` não injetivo (`colapsoHom`, `colapso_nao_injetivo`).
-/

open ATK.LinhasNovas Filter Topology

namespace ATK.LinhasNovas

namespace Cauda

/-- **Não é fechado**: denso e fechado daria `ℝ` inteiro, mas `1/3` fica de fora. -/
theorem conjunto_not_closed : ¬ IsClosed conjunto := fun h => by
  have : (1 / 3 : ℝ) ∈ closure conjunto := conjunto_dense.closure_eq ▸ Set.mem_univ _
  rw [h.closure_eq] at this
  exact um_terco_cauda_infinita this

/-- `1/3` está no fecho sem estar no conjunto. -/
theorem um_terco_no_fecho : (1 / 3 : ℝ) ∈ closure conjunto ∧ (1 / 3 : ℝ) ∉ conjunto :=
  ⟨conjunto_dense.closure_eq ▸ Set.mem_univ _, um_terco_cauda_infinita⟩

end Cauda

namespace Truncamento

/-- **O truncamento colapsa exatamente as linguagens finitas** (alfabeto finito). -/
theorem trunc_eq_self_iff {α : Type*} [Finite α] (L : Set (List α)) :
    (∃ k, trunc L k = L) ↔ L.Finite := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact (List.finite_length_le α k).subset fun _ hw => hw.2
  · intro hL
    obtain ⟨k, hk⟩ := (hL.image List.length).exists_le
    exact ⟨k, Set.ext fun w => ⟨fun h => h.1, fun h => ⟨h, hk _ ⟨w, h, rfl⟩⟩⟩⟩

end Truncamento

namespace Ordem

/-- **`ℕ` não tem topo; `ℕ∞` tem.** -/
theorem nat_sem_topo : ¬ BddAbove (Set.univ : Set ℕ) := fun ⟨N, h⟩ => by
  have := h (Set.mem_univ (N + 1)); omega

theorem enat_com_topo : BddAbove (Set.univ : Set ℕ∞) := ⟨⊤, fun _ _ => le_top⟩

/-- **Maior abaixo de cada ponto ⟺ ordem com predecessor.** -/
theorem maior_abaixo_iff_predOrder {α : Type*} [LinearOrder α] :
    (∀ a : α, ¬ IsMin a → ∃ r < a, ∀ x < a, x ≤ r) ↔ Nonempty (PredOrder α) := by
  classical
  constructor
  · intro h
    refine ⟨{ pred := fun a => if ha : IsMin a then a else Classical.choose (h a ha),
              pred_le := ?_, min_of_le_pred := ?_, le_pred_of_lt := ?_ }⟩
    · intro a
      by_cases ha : IsMin a
      · simp [ha]
      · simp only [ha, dite_false]; exact (Classical.choose_spec (h a ha)).1.le
    · intro a hle
      by_contra ha
      simp only [ha, dite_false] at hle
      exact absurd (Classical.choose_spec (h a ha)).1 (not_lt.mpr hle)
    · intro a b hab
      have hb : ¬ IsMin b := fun hb => absurd (hb hab.le) (not_le.mpr hab)
      simp only [hb, dite_false]
      exact (Classical.choose_spec (h b hb)).2 a hab
  · rintro ⟨_⟩ a ha
    exact ⟨Order.pred a, Order.pred_lt_of_not_isMin ha, fun x hx => Order.le_pred_of_lt hx⟩

/-- `ℤ` tem predecessor; `ℝ` não tem nenhum. -/
theorem int_pred : Nonempty (PredOrder ℤ) := ⟨inferInstance⟩

theorem real_sem_pred : ¬ Nonempty (PredOrder ℝ) := by
  rw [← maior_abaixo_iff_predOrder]
  intro h
  obtain ⟨r, hr, hmax⟩ := h 0 (not_isMin 0)
  have := hmax ((r + 0) / 2) (by linarith)
  linarith

end Ordem

namespace Involucao

/-- `x ↦ −2x` à esquerda de `0`, `x ↦ −x/2` à direita. -/
noncomputable def quebrada (x : ℝ) : ℝ := if x ≤ 0 then -2 * x else -x / 2

theorem quebrada_involutive : Function.Involutive quebrada := by
  intro x
  unfold quebrada
  split_ifs with h1 h2 h2 <;> linarith

theorem quebrada_strictAnti : StrictAnti quebrada := by
  intro x y hxy
  unfold quebrada
  split_ifs <;> linarith

/-- **Refutação**: há involução estritamente decrescente de `ℝ` que **não** é `x ↦ a − x`. A
linha da constante ½ não pode ser fortalecida para "toda simetria decrescente de `ℝ` é uma
reflexão". -/
theorem strictAnti_involutive_nao_afim :
    ∃ f : ℝ → ℝ, StrictAnti f ∧ Function.Involutive f ∧ ∀ a : ℝ, f ≠ fun x => a - x := by
  refine ⟨quebrada, quebrada_strictAnti, quebrada_involutive, fun a h => ?_⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hm := congrFun h (-1)
  simp only [quebrada] at h0 h1 hm
  norm_num at h0 h1 hm
  linarith

/-- O único fixo de `quebrada` é `0`: o centro existe, mas a simetria não é reflexão. -/
theorem quebrada_fixo (x : ℝ) : quebrada x = x ↔ x = 0 := by
  unfold quebrada
  split_ifs <;> constructor <;> intro h <;> linarith

end Involucao

namespace InvolucaoComFixos

/-- Morfismo de involuções: comuta com `σ`. -/
structure Hom {α β : Type*} (A : InvolucaoComFixos α) (B : InvolucaoComFixos β) where
  toFun : α → β
  comm : ∀ x, toFun (A.σ x) = B.σ (toFun x)

/-- Morfismos levam fixos em fixos. -/
theorem Hom.mapsTo_fixos {α β : Type*} {A : InvolucaoComFixos α} {B : InvolucaoComFixos β}
    (f : Hom A B) : Set.MapsTo f.toFun A.fixos B.fixos := fun x hx => by
  rw [B.mem_fixos, ← f.comm, (A.mem_fixos x).mp hx]

/-- A inversão de `ℝ` (convenção `0⁻¹ = 0`). -/
noncomputable def invReal : InvolucaoComFixos ℝ := deInvolutiva (fun x => x⁻¹) inv_involutive

/-- **O colapso `∞ = 0` é um morfismo** da inversão projetiva para a de `ℝ`, não uma igualdade. -/
noncomputable def colapsoHom : Hom invProj invReal :=
  ⟨Colapso.colapso, Colapso.colapso_inv⟩

/-- O colapso não é injetivo (cola `∞` e `0`), então não é isomorfismo. -/
theorem colapso_nao_injetivo : ¬ Function.Injective colapsoHom.toFun := fun h =>
  absurd (h (a₁ := infinito) (a₂ := some 0) rfl) (by simp [infinito])

end InvolucaoComFixos

end ATK.LinhasNovas
#print axioms ATK.LinhasNovas.Cauda.conjunto_not_closed
#print axioms ATK.LinhasNovas.Cauda.um_terco_no_fecho
#print axioms ATK.LinhasNovas.Truncamento.trunc_eq_self_iff
#print axioms ATK.LinhasNovas.Ordem.nat_sem_topo
#print axioms ATK.LinhasNovas.Ordem.enat_com_topo
#print axioms ATK.LinhasNovas.Ordem.maior_abaixo_iff_predOrder
#print axioms ATK.LinhasNovas.Ordem.int_pred
#print axioms ATK.LinhasNovas.Ordem.real_sem_pred
#print axioms ATK.LinhasNovas.Involucao.quebrada_involutive
#print axioms ATK.LinhasNovas.Involucao.quebrada_strictAnti
#print axioms ATK.LinhasNovas.Involucao.strictAnti_involutive_nao_afim
#print axioms ATK.LinhasNovas.Involucao.quebrada_fixo
#print axioms ATK.LinhasNovas.InvolucaoComFixos.Hom.mapsTo_fixos
#print axioms ATK.LinhasNovas.InvolucaoComFixos.colapso_nao_injetivo
