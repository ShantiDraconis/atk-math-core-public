import ATK.ZeroClasses.Symmetry

/-!
# ATK-ZERO-CLASSES — leis: conjuntos, existência, simetria e o grupo dos operadores

* **existência** `Existe F C :⟺ ∃ z ∈ C, F z = 0` — uma *prova* de `Existe F C` é o "ProvenExists"; um
  *postulado* de existência é uma hipótese, e é **inconsistente** assim que a classe é refutada
  (`postulado_refutado`). Exemplo: `z² + 1` tem zero imaginário puro e nenhum zero real
  (`exemplo_quadrado`), logo postular um zero real de `z² + 1` é contraditório;
* **leis de conjuntos** (`lei_intersecao`, `lei_uniao`, `lei_complemento`, `lei_classificacao`);
  **leis de existência**: monotonia, união, união enumerável, interseção (só `⇒`; a recíproca é falsa:
  `existe_inter_nao_reciproca`);
* **lei da simetria**: `T` preserva zeros ⇒ `T(Z) ⊆ Z`; involutiva ⇒ `T(Z) = Z` (`lei_simetria_eq`);
  existência transportada (`existe_transporte`);
* **operadores completos**: `conj`, `refl c`, `tor c` e `id` formam o **grupo de Klein** (`klein`);
  tabela da ação sobre as classes: `conj` preserva **todas** as classes (`conj_classes`); `refl c` troca
  `x < c` com `x > c`, preserva a reta, os reais puros e, para `c ∈ ℚ`, a racionalidade da parte real
  (`refl_classes`); `tor c` idem, preservando a parte imaginária (`tor_classes`).
-/

open Complex ComplexConjugate Set

namespace ATK.ZeroClasses

variable {F f : ℂ → ℂ} {c : ℝ}

/-! ## Existência -/

/-- Existe um zero de `F` na classe `C`. -/
def Existe (F : ℂ → ℂ) (C : Set ℂ) : Prop := ∃ z ∈ C, F z = 0

theorem existe_iff {C : Set ℂ} : Existe F C ↔ (Z F ∩ C).Nonempty :=
  ⟨fun ⟨z, hz, h0⟩ => ⟨z, h0, hz⟩, fun ⟨z, h0, hz⟩ => ⟨z, hz, h0⟩⟩

/-- **Um postulado de existência numa classe refutada é inconsistente.** -/
theorem postulado_refutado {C : Set ℂ} (h : ∀ z ∈ C, F z ≠ 0) : ¬ Existe F C :=
  fun ⟨z, hz, h0⟩ => h z hz h0

/-- `z² + 1`: zero imaginário puro, nenhum zero real. -/
theorem exemplo_quadrado :
    Existe (fun z => z ^ 2 + 1) {z | z.re = 0 ∧ z.im ≠ 0} ∧
      ¬ Existe (fun z => z ^ 2 + 1) {z | z.im = 0} := by
  refine ⟨⟨I, ⟨by simp, by simp⟩, by simp⟩, postulado_refutado ?_⟩
  intro z hz h0
  have hre := congrArg Complex.re h0
  simp only [mem_ofPred_eq] at hz
  simp [sq, hz] at hre
  nlinarith [sq_nonneg z.re]

theorem existe_mono {C D : Set ℂ} (h : C ⊆ D) : Existe F C → Existe F D :=
  fun ⟨z, hz, h0⟩ => ⟨z, h hz, h0⟩

theorem existe_uniao {C D : Set ℂ} : Existe F (C ∪ D) ↔ Existe F C ∨ Existe F D := by
  constructor
  · rintro ⟨z, hz | hz, h0⟩
    · exact Or.inl ⟨z, hz, h0⟩
    · exact Or.inr ⟨z, hz, h0⟩
  · rintro (h | h)
    · exact existe_mono subset_union_left h
    · exact existe_mono subset_union_right h

theorem existe_iUnion {ι : Type*} {C : ι → Set ℂ} : Existe F (⋃ i, C i) ↔ ∃ i, Existe F (C i) := by
  constructor
  · rintro ⟨z, hz, h0⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact ⟨i, z, hi, h0⟩
  · rintro ⟨i, z, hz, h0⟩
    exact ⟨z, mem_iUnion.mpr ⟨i, hz⟩, h0⟩

theorem existe_inter {C D : Set ℂ} : Existe F (C ∩ D) → Existe F C ∧ Existe F D :=
  fun h => ⟨existe_mono inter_subset_left h, existe_mono inter_subset_right h⟩

/-- A recíproca é falsa: `z² + 1` tem zero em `{i}` e em `{−i}`, mas não em `{i} ∩ {−i} = ∅`. -/
theorem existe_inter_nao_reciproca :
    ∃ (F : ℂ → ℂ) (C D : Set ℂ), Existe F C ∧ Existe F D ∧ ¬ Existe F (C ∩ D) := by
  refine ⟨fun z => z ^ 2 + 1, {I}, {-I}, ⟨I, rfl, by simp⟩, ⟨-I, rfl, by simp⟩, ?_⟩
  rintro ⟨z, ⟨h1, h2⟩, _⟩
  rw [mem_singleton_iff] at h1 h2
  rw [h1] at h2
  have := congrArg Complex.im h2
  simp at this
  linarith

/-! ## Leis de conjuntos -/

theorem lei_intersecao (A B : Set ℂ) : Z f ∩ (A ∩ B) = (Z f ∩ A) ∩ B := (inter_assoc _ _ _).symm

theorem lei_uniao (A B : Set ℂ) : Z f ∩ (A ∪ B) = (Z f ∩ A) ∪ (Z f ∩ B) := inter_union_distrib_left _ _ _

theorem lei_complemento (A : Set ℂ) :
    Z f = (Z f ∩ A) ∪ (Z f ∩ Aᶜ) ∧ Disjoint (Z f ∩ A) (Z f ∩ Aᶜ) :=
  ⟨(inter_union_compl _ _).symm,
    Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2⟩

theorem lei_classificacao (z : ℂ) (C : Set ℂ) : z ∈ C ∨ z ∉ C := em _

/-! ## Lei da simetria -/

theorem lei_simetria {T : ℂ → ℂ} (hT : ∀ z, f z = 0 → f (T z) = 0) : T '' Z f ⊆ Z f := by
  rintro _ ⟨z, hz, rfl⟩
  exact hT z hz

theorem lei_simetria_eq {T : ℂ → ℂ} (hT : ∀ z, f z = 0 → f (T z) = 0) (hinv : Function.Involutive T) :
    T '' Z f = Z f := by
  refine (lei_simetria hT).antisymm fun z hz => ⟨T z, hT z hz, hinv z⟩

theorem existe_transporte {T : ℂ → ℂ} (hT : ∀ z, f z = 0 → f (T z) = 0) {C D : Set ℂ}
    (hCD : T '' C ⊆ D) : Existe f C → Existe f D :=
  fun ⟨z, hz, h0⟩ => ⟨T z, hCD ⟨z, hz, rfl⟩, hT z h0⟩

/-! ## O grupo dos operadores -/

/-- **Grupo de Klein** `{id, conj, refl c, tor c}`: cada elemento é involutivo e o produto de dois
distintos é o terceiro. -/
theorem klein (c : ℝ) :
    ((conj : ℂ → ℂ) ∘ conj = id) ∧ (refl c ∘ refl c = id) ∧ (tor c ∘ tor c = id) ∧
      ((conj : ℂ → ℂ) ∘ refl c = tor c) ∧ (refl c ∘ (conj : ℂ → ℂ) = tor c) ∧
      ((conj : ℂ → ℂ) ∘ tor c = refl c) ∧ (tor c ∘ (conj : ℂ → ℂ) = refl c) ∧
      (refl c ∘ tor c = conj) ∧ (tor c ∘ refl c = conj) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext z <;> apply Complex.ext <;> simp

theorem isZero_conj_iff (hf : ConjEquiv f) (z : ℂ) : IsZero f (conj z) ↔ IsZero f z := by
  unfold IsZero
  rw [hf, map_eq_zero]

theorem ratIm_neg (x : ℝ) : (∃ q : ℚ, -x = q) ↔ ∃ q : ℚ, x = q :=
  ⟨fun ⟨q, hq⟩ => ⟨-q, by push_cast; linarith⟩, fun ⟨q, hq⟩ => ⟨-q, by push_cast; linarith⟩⟩

/-- **`conj` preserva todas as classes.** -/
theorem conj_classes (hf : ConjEquiv f) (z : ℂ) :
    (OnLine f c (conj z) ↔ OnLine f c z) ∧ (OffLine f c (conj z) ↔ OffLine f c z) ∧
      (LeftOf f c (conj z) ↔ LeftOf f c z) ∧ (RightOf f c (conj z) ↔ RightOf f c z) ∧
      (PureReal f (conj z) ↔ PureReal f z) ∧ (PureImaginary f (conj z) ↔ PureImaginary f z) ∧
      (Mixed f (conj z) ↔ Mixed f z) ∧ (RatRe f (conj z) ↔ RatRe f z) ∧
      (IrrRe f (conj z) ↔ IrrRe f z) ∧ (RatIm f (conj z) ↔ RatIm f z) ∧
      (IrrIm f (conj z) ↔ IrrIm f z) := by
  have h0 := isZero_conj_iff hf z
  simp only [OnLine, OffLine, LeftOf, RightOf, PureReal, PureImaginary, Mixed, RatRe, IrrRe, RatIm,
    IrrIm, h0, conj_re, conj_im, neg_eq_zero, ne_eq, irrational_neg_iff, ratIm_neg]
  tauto

theorem isZero_refl_iff (hr : ReflZeros f c) (z : ℂ) : IsZero f (refl c z) ↔ IsZero f z :=
  ⟨fun h => by have := zero_refl hr h; rwa [refl_refl] at this, zero_refl hr⟩

theorem ratRe_refl (q : ℚ) (x : ℝ) : (∃ p : ℚ, 2 * (q : ℝ) - x = p) ↔ ∃ p : ℚ, x = p :=
  ⟨fun ⟨p, hp⟩ => ⟨2 * q - p, by push_cast; linarith⟩, fun ⟨p, hp⟩ => ⟨2 * q - p, by push_cast; linarith⟩⟩

/-- **Ação de `refl c`**: preserva a reta e a sua complementar, troca os lados, preserva os reais puros
e a racionalidade da parte imaginária. -/
theorem refl_classes (hr : ReflZeros f c) (z : ℂ) :
    (OnLine f c (refl c z) ↔ OnLine f c z) ∧ (OffLine f c (refl c z) ↔ OffLine f c z) ∧
      (LeftOf f c (refl c z) ↔ RightOf f c z) ∧ (RightOf f c (refl c z) ↔ LeftOf f c z) ∧
      (PureReal f (refl c z) ↔ PureReal f z) ∧ (RatIm f (refl c z) ↔ RatIm f z) ∧
      (IrrIm f (refl c z) ↔ IrrIm f z) := by
  have h0 := isZero_refl_iff hr z
  simp only [OnLine, OffLine, LeftOf, RightOf, PureReal, RatIm, IrrIm, h0, refl_re, refl_im,
    neg_eq_zero, irrational_neg_iff, ratIm_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | trivial
    | exact Iff.rfl
    | (constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩)
    | (constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, fun h => h2 (by linarith)⟩)

/-- Para `c ∈ ℚ`, `refl c` preserva a racionalidade da parte real. -/
theorem refl_ratRe (hr : ReflZeros f (q : ℚ)) (z : ℂ) :
    (RatRe f (refl q z) ↔ RatRe f z) ∧ (IrrRe f (refl q z) ↔ IrrRe f z) := by
  have h0 := isZero_refl_iff hr z
  have hirr : Irrational (2 * (q : ℝ) - z.re) ↔ Irrational z.re := by
    rw [← not_iff_not, not_irrational_iff, not_irrational_iff, ratRe_refl]
  simp only [RatRe, IrrRe, h0, refl_re, ratRe_refl, hirr]
  try exact ⟨trivial, trivial⟩

/-- **Ação de `tor c`**: preserva a reta (pontualmente), troca os lados, preserva a parte imaginária. -/
theorem tor_classes (hc : ConjEquiv f) (hr : ReflZeros f c) (z : ℂ) :
    (OnLine f c (tor c z) ↔ OnLine f c z) ∧ (LeftOf f c (tor c z) ↔ RightOf f c z) ∧
      (PureReal f (tor c z) ↔ PureReal f z) ∧ (RatIm f (tor c z) ↔ RatIm f z) ∧
      (IrrIm f (tor c z) ↔ IrrIm f z) := by
  have h0 : IsZero f (tor c z) ↔ IsZero f z := by
    constructor
    · intro h; have := zero_tor hc hr h; rwa [tor_tor] at this
    · exact zero_tor hc hr
  simp only [OnLine, LeftOf, RightOf, PureReal, RatIm, IrrIm, h0, tor_re, tor_im]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | trivial
    | exact Iff.rfl
    | (constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩)

end ATK.ZeroClasses

#print axioms ATK.ZeroClasses.existe_iff
#print axioms ATK.ZeroClasses.postulado_refutado
#print axioms ATK.ZeroClasses.exemplo_quadrado
#print axioms ATK.ZeroClasses.existe_mono
#print axioms ATK.ZeroClasses.existe_uniao
#print axioms ATK.ZeroClasses.existe_iUnion
#print axioms ATK.ZeroClasses.existe_inter
#print axioms ATK.ZeroClasses.existe_inter_nao_reciproca
#print axioms ATK.ZeroClasses.lei_intersecao
#print axioms ATK.ZeroClasses.lei_uniao
#print axioms ATK.ZeroClasses.lei_complemento
#print axioms ATK.ZeroClasses.lei_classificacao
#print axioms ATK.ZeroClasses.lei_simetria
#print axioms ATK.ZeroClasses.lei_simetria_eq
#print axioms ATK.ZeroClasses.existe_transporte
#print axioms ATK.ZeroClasses.klein
#print axioms ATK.ZeroClasses.isZero_conj_iff
#print axioms ATK.ZeroClasses.ratIm_neg
#print axioms ATK.ZeroClasses.conj_classes
#print axioms ATK.ZeroClasses.isZero_refl_iff
#print axioms ATK.ZeroClasses.ratRe_refl
#print axioms ATK.ZeroClasses.refl_classes
#print axioms ATK.ZeroClasses.refl_ratRe
#print axioms ATK.ZeroClasses.tor_classes
