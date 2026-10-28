import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Rank
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# ATK — O posto livre de um grupo abeliano f.g. é o posto sobre `ℤ`

A Mathlib define `AddCommGroup.freeRank A` como o número **mínimo de geradores** de `A ⧸ torsion A`
(`AddGroup.rank`), e o posto de Mordell–Weil costuma ser escrito como `Module.finrank ℤ A` ou
`Module.rank ℤ A`. A Mathlib (v4.34.1 e o `master` de 14/10/2026) não tem o lema que liga os dois.
Provado aqui:

* `rank_eq_finrank`: sem torção, número mínimo de geradores = `finrank ℤ`;
* `rank_eq_of_surjective`: um epimorfismo cujo núcleo é de torção preserva `Module.rank ℤ`;
* `freeRank_eq_finrank`: **`AddCommGroup.freeRank A = Module.finrank ℤ A`** para `A` f.g.

É usado para comparar o enunciado de BSD do ATK (posto `Module.rank ℤ`) com o do formal-conjectures
(posto `AddCommGroup.freeRank`). Candidato a PR na Mathlib (`Mathlib/GroupTheory/Torsion.lean`).
-/

open Module

namespace ATK.PostoLivre

universe u

/-- Num grupo abeliano f.g. sem torção, o número mínimo de geradores é o posto sobre `ℤ`. -/
theorem rank_eq_finrank (M : Type*) [AddCommGroup M] [IsAddTorsionFree M] [AddGroup.FG M] :
    AddGroup.rank M = finrank ℤ M := by
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr ‹_›
  apply le_antisymm
  · classical
    let b := Module.finBasis ℤ M
    have hspan : Submodule.span ℤ (Set.range b) = ⊤ := b.span_eq
    have hcl : AddSubgroup.closure ((Finset.univ.image b : Finset M) : Set M) = ⊤ := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Submodule.span_int_eq_addSubgroupClosure,
        hspan, Submodule.top_toAddSubgroup]
    calc AddGroup.rank M ≤ (Finset.univ.image b).card := AddGroup.rank_le hcl
      _ ≤ (Finset.univ : Finset (Fin (finrank ℤ M))).card := Finset.card_image_le
      _ = finrank ℤ M := by simp
  · obtain ⟨S, hcard, hS⟩ := AddGroup.rank_spec M
    have hspan : Submodule.span ℤ (Set.range ((↑) : S → M)) = ⊤ := by
      rw [Subtype.range_coe_subtype, Finset.setOfPred_mem]
      apply Submodule.toAddSubgroup_injective
      rw [Submodule.span_int_eq_addSubgroupClosure, hS, Submodule.top_toAddSubgroup]
    calc finrank ℤ M ≤ Fintype.card S := finrank_le_of_span_eq_top hspan
      _ = AddGroup.rank M := by rw [Fintype.card_coe, hcard]

/-- Um epimorfismo com núcleo de torção preserva o posto sobre `ℤ`. -/
theorem rank_eq_of_surjective {A B : Type u} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f) (hker : ∀ x, f x = 0 → ∃ n : ℤ, n ≠ 0 ∧ n • x = 0) :
    Module.rank ℤ A = Module.rank ℤ B := by
  rw [LinearMap.rank_eq_of_surjective (f := f.toIntLinearMap) hf]
  have h0 : Module.rank ℤ (LinearMap.ker f.toIntLinearMap) = 0 := by
    rw [rank_eq_zero_iff]
    rintro ⟨x, hx⟩
    obtain ⟨n, hn, hnx⟩ := hker x hx
    exact ⟨n, hn, Subtype.ext hnx⟩
  rw [h0, add_zero]

/-- **O posto livre (`AddCommGroup.freeRank`) é o posto sobre `ℤ`.** -/
theorem freeRank_eq_finrank (A : Type u) [AddCommGroup A] [AddGroup.FG A] :
    AddCommGroup.freeRank A = finrank ℤ A := by
  rw [AddCommGroup.freeRank_def, rank_eq_finrank]
  have h := rank_eq_of_surjective (QuotientAddGroup.mk' (AddCommGroup.torsion A))
    (QuotientAddGroup.mk'_surjective _) fun x hx => by
      have hx' : x ∈ AddCommGroup.torsion A := (QuotientAddGroup.eq_zero_iff x).mp hx
      obtain ⟨n, hn, hnx⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).mp hx'
      exact ⟨n, by exact_mod_cast hn.ne', by rw [natCast_zsmul]; exact hnx⟩
  exact (congrArg Cardinal.toNat h).symm

end ATK.PostoLivre

#print axioms ATK.PostoLivre.rank_eq_finrank
#print axioms ATK.PostoLivre.rank_eq_of_surjective
#print axioms ATK.PostoLivre.freeRank_eq_finrank
