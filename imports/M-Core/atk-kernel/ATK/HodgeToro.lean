import ATK.L3Base
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# ATK — Ligação L3: a estrutura de Hodge de `H¹` de um toro complexo

Um exemplo geométrico de `ATK.L3Base.HodgeStructure`: para `τ` com `Im τ ≠ 0`, o toro complexo
(curva elíptica) `E_τ = ℂ / (ℤ + τℤ)` tem `H¹(E_τ, ℚ) = Hom(ℤ + τℤ, ℚ) ≅ ℚ²` (base dual a `1, τ`),
e a forma holomorfa `dz` é, em `H¹(E_τ, ℂ) = ℂ ⊗ ℚ²`, o vetor `dz = e₁ + τ e₂`
(`dz(1) = 1`, `dz(τ) = τ`). A decomposição de Hodge de peso 1 é

  `H^{1,0} = ℂ·dz`,  `H^{0,1} = ℂ·dz̄ = ℂ·(e₁ + τ̄ e₂)`.

Provado aqui:
* `conjV_smul`: a conjugação de `V_ℂ` é antilinear;
* `disjunto` / `gera`: `dz` e `dz̄` são linearmente independentes e geram `V_ℂ` (`τ − τ̄ ≠ 0`);
* `toro τ hτ : HodgeStructure (Fin 2 → ℚ) 1` — uma estrutura de Hodge racional pura de peso 1
  (decomposição em soma direta e simetria de Hodge `conj H^{1,0} = H^{0,1}`);
* teste: `finrank_H10`: `h^{1,0} = 1` (o gênero da curva).

A construção é feita à mão a partir do reticulado; derivar `H¹` da cohomologia singular do toro e
`dz` da teoria de de Rham exige cohomologia de variedades, ausente da Mathlib. A ligação L3 continua
`NAO_EXISTE_NA_MATHLIB`.
-/

open TensorProduct ATK.L3Base

namespace ATK.HodgeToro

/-! ## A conjugação é antilinear -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem conjV_smul (z : ℂ) (x : ℂ ⊗[ℚ] V) :
    conjV V (z • x) = (starRingEnd ℂ z) • conjV V x := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => rw [TensorProduct.smul_tmul', conjV_tmul, conjV_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem image_span (u : ℂ ⊗[ℚ] V) :
    conjV V '' (Submodule.span ℂ {u} : Set (ℂ ⊗[ℚ] V)) = Submodule.span ℂ {conjV V u} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact Submodule.mem_span_singleton.mpr ⟨starRingEnd ℂ a, (conjV_smul a u).symm⟩
  · intro hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨starRingEnd ℂ a • u, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u), ?_⟩
    rw [conjV_smul, Complex.conj_conj]

/-! ## O toro `ℂ / (ℤ + τℤ)` -/

/-- A base `1 ⊗ eᵢ` de `ℂ ⊗[ℚ] ℚ²`. -/
noncomputable abbrev B : Module.Basis (Fin 2) ℂ (ℂ ⊗[ℚ] (Fin 2 → ℚ)) :=
  Algebra.TensorProduct.basis ℂ (Pi.basisFun ℚ (Fin 2))

/-- `dz = e₁ + τ e₂`. -/
noncomputable def dz (τ : ℂ) : ℂ ⊗[ℚ] (Fin 2 → ℚ) := B 0 + τ • B 1

theorem conjV_B (i : Fin 2) : conjV (Fin 2 → ℚ) (B i) = B i := by
  simp [B, Algebra.TensorProduct.basis_apply]

theorem conjV_dz (τ : ℂ) : conjV (Fin 2 → ℚ) (dz τ) = dz (starRingEnd ℂ τ) := by
  rw [dz, dz, map_add, conjV_smul, conjV_B, conjV_B]

theorem sub_conj_ne {τ : ℂ} (hτ : τ.im ≠ 0) : τ - starRingEnd ℂ τ ≠ 0 := by
  rw [Complex.sub_conj]
  exact mul_ne_zero (by exact_mod_cast mul_ne_zero two_ne_zero hτ) Complex.I_ne_zero

theorem repr_dz (τ : ℂ) : B.repr (dz τ) 0 = 1 ∧ B.repr (dz τ) 1 = τ := by
  simp [dz]

theorem dz_ne_zero (τ : ℂ) : dz τ ≠ 0 := by
  intro h
  have := (repr_dz τ).1
  rw [h] at this
  simp at this

/-- `ℂ·dz ∩ ℂ·dz̄ = 0`. -/
theorem disjunto {τ : ℂ} (hτ : τ.im ≠ 0) :
    Disjoint (Submodule.span ℂ {dz τ}) (Submodule.span ℂ {dz (starRingEnd ℂ τ)}) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx'
  have h0 := congrArg (fun y => B.repr y 0) ht
  have h1 := congrArg (fun y => B.repr y 1) ht
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, (repr_dz _).1, (repr_dz _).2] at h0 h1
  have hst : t = s := by simpa using h0
  subst hst
  have : t * (τ - starRingEnd ℂ τ) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp this with h | h
  · rw [h, zero_smul]
  · exact absurd h (sub_conj_ne hτ)

/-- `dz` e `dz̄` geram `V_ℂ`. -/
theorem gera {τ : ℂ} (hτ : τ.im ≠ 0) :
    Submodule.span ℂ {dz τ} ⊔ Submodule.span ℂ {dz (starRingEnd ℂ τ)} = ⊤ := by
  have hB1 : B 1 = (τ - starRingEnd ℂ τ)⁻¹ • (dz τ - dz (starRingEnd ℂ τ)) := by
    rw [dz, dz, add_sub_add_left_eq_sub, ← sub_smul, smul_smul,
      inv_mul_cancel₀ (sub_conj_ne hτ), one_smul]
  have hmem1 : B 1 ∈ Submodule.span ℂ {dz τ} ⊔ Submodule.span ℂ {dz (starRingEnd ℂ τ)} := by
    rw [hB1]
    exact Submodule.smul_mem _ _ (sub_mem
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  have hmem0 : B 0 ∈ Submodule.span ℂ {dz τ} ⊔ Submodule.span ℂ {dz (starRingEnd ℂ τ)} := by
    have : B 0 = dz τ - τ • B 1 := by rw [dz, add_sub_cancel_right]
    rw [this]
    exact sub_mem (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
      (Submodule.smul_mem _ _ hmem1)
  refine eq_top_iff.mpr ?_
  rw [← B.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hmem0
  · exact hmem1

/-- Os espaços `H^{p, 1−p}`: `H^{1,0} = ℂ·dz`, `H^{0,1} = ℂ·dz̄`, os demais nulos. -/
noncomputable def Hτ (τ : ℂ) (p : ℤ) : Submodule ℂ (ℂ ⊗[ℚ] (Fin 2 → ℚ)) :=
  if p = 1 then Submodule.span ℂ {dz τ}
  else if p = 0 then Submodule.span ℂ {dz (starRingEnd ℂ τ)} else ⊥

/-- **A estrutura de Hodge de peso 1 de `H¹(ℂ / (ℤ + τℤ), ℚ)`.** -/
noncomputable def toro (τ : ℂ) (hτ : τ.im ≠ 0) : HodgeStructure (Fin 2 → ℚ) 1 where
  H := Hτ τ
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro i
      by_cases h1 : i = 1
      · subst h1
        refine (disjunto hτ).mono_right (iSup₂_le fun j hj => ?_)
        simp only [Hτ, hj, ite_false]
        split_ifs <;> simp
      by_cases h0 : i = 0
      · subst h0
        refine (disjunto hτ).symm.mono_right (iSup₂_le fun j hj => ?_)
        simp only [Hτ, hj, ite_false]
        split_ifs <;> simp
      · simp only [Hτ, h1, h0, ite_false]
        exact disjoint_bot_left
    · refine eq_top_iff.mpr ((gera hτ).ge.trans (sup_le ?_ ?_))
      · exact le_iSup_of_le 1 (by simp [Hτ])
      · exact le_iSup_of_le 0 (by simp [Hτ])
  conj_eq := fun p => by
    by_cases h1 : p = 1
    · subst h1
      simp only [Hτ, ite_true, show (1 : ℤ) - 1 = 0 by norm_num, show (0 : ℤ) ≠ 1 by norm_num,
        ite_false, image_span, conjV_dz]
    by_cases h0 : p = 0
    · subst h0
      simp only [Hτ, show (0 : ℤ) ≠ 1 by norm_num, ite_false, ite_true, sub_zero, image_span,
        conjV_dz, Complex.conj_conj]
    · have h1' : (1 : ℤ) - p ≠ 1 := by omega
      have h0' : (1 : ℤ) - p ≠ 0 := by omega
      simp only [Hτ, h1, h0, h1', h0', ite_false, Submodule.bot_coe, Set.image_singleton, map_zero]

/-- **Teste**: `h^{1,0} = dim H^{1,0} = 1` (o gênero da curva elíptica). -/
theorem finrank_H10 (τ : ℂ) (hτ : τ.im ≠ 0) : Module.finrank ℂ ((toro τ hτ).H 1) = 1 := by
  simp only [toro, Hτ]
  exact finrank_span_singleton (dz_ne_zero τ)

/-- **Teste**: o toro quadrado `τ = i`. -/
noncomputable def toroQuadrado : HodgeStructure (Fin 2 → ℚ) 1 := toro Complex.I (by simp)

end ATK.HodgeToro

#print axioms ATK.HodgeToro.conjV_smul
#print axioms ATK.HodgeToro.image_span
#print axioms ATK.HodgeToro.conjV_B
#print axioms ATK.HodgeToro.conjV_dz
#print axioms ATK.HodgeToro.sub_conj_ne
#print axioms ATK.HodgeToro.repr_dz
#print axioms ATK.HodgeToro.dz_ne_zero
#print axioms ATK.HodgeToro.disjunto
#print axioms ATK.HodgeToro.gera
#print axioms ATK.HodgeToro.finrank_H10
