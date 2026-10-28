import Mathlib

/-!
# ATK-ZERO-CLASSES — camada genérica: classes, partições, aritmética e informação incompleta

Para uma função **arbitrária** `f : ℂ → ℂ` (nenhuma continuidade, nenhuma holomorfia) e um parâmetro
livre `c : ℝ`, com `Z(f) = {z : f z = 0}` e `z = x + iy`:

* **posição** (`LeftOf`, `OnLine`, `RightOf`, `OffLine`): `Z(f) = Z_{x<c} ⊔ Z_{x=c} ⊔ Z_{x>c}`
  (`particao_posicao`, `posicao_exclusiva`), `Z_{x≠c} = Z_{x<c} ⊔ Z_{x>c}` (`offLine_iff`);
* **natureza** (`PureReal`, `PureImaginary`, `Mixed`): `Z(f) = Z_real ⊔ Z*_imag ⊔ Z_misto`
  (`zero_nature`, `particao_natureza`), com a origem só na classe real (`origem_real`);
* **aritmética** (`RatRe`, `IrrRe`, `RatIm`, `IrrIm`): `Z_ℚ ∩ Z_{ℝ∖ℚ} = ∅`, `Z_ℚ ∪ Z_{ℝ∖ℚ} = Z(f)`, para a
  parte real e para a parte imaginária (`particao_re`, `particao_im`);
* **matriz de compatibilidade**: imaginário puro ⇒ parte real racional (`imag_ratRe`); real puro ⇒ parte
  imaginária racional (`real_ratIm`); para `c ∈ ℚ`, parte real irracional ⇒ fora da reta (`irr_offLine`);
  para `c ∉ ℚ`, na reta ⇒ parte real irracional (`onLine_irr`). As células compatíveis são **todas
  realizáveis** por uma mesma função (`realiza_celulas`), e compatibilidade **não** implica existência
  (`compat_nao_existencia`: `f ≡ 1` não tem zeros);
* **informação incompleta** (`Indeterminado K`): um zero fora do conjunto certificado `K`. A classe é
  antimonótona em `K`, vazia para `K = univ`, e **não intrínseca**: todo zero é indeterminado para `K = ∅`
  e determinado para `K = {z}` (`indeterminado_nao_intrinseco`).

Tudo aqui é lógica e álgebra elementar; nada usa propriedades de `ζ`.
-/

open Complex Set

namespace ATK.ZeroClasses

variable (f : ℂ → ℂ) (c : ℝ)

/-- `Z(f)`. -/
def Z : Set ℂ := {z | f z = 0}

/-- `z` é zero de `f`. -/
def IsZero (z : ℂ) : Prop := f z = 0

/-! ## 1. Posição relativa à reta `x = c` -/

def OnLine (z : ℂ) : Prop := IsZero f z ∧ z.re = c
def OffLine (z : ℂ) : Prop := IsZero f z ∧ z.re ≠ c
def LeftOf (z : ℂ) : Prop := IsZero f z ∧ z.re < c
def RightOf (z : ℂ) : Prop := IsZero f z ∧ c < z.re

/-! ## 2. Natureza -/

def PureReal (z : ℂ) : Prop := IsZero f z ∧ z.im = 0
def PureImaginary (z : ℂ) : Prop := IsZero f z ∧ z.re = 0 ∧ z.im ≠ 0
def Mixed (z : ℂ) : Prop := IsZero f z ∧ z.re ≠ 0 ∧ z.im ≠ 0

/-! ## 3. Aritmética -/

def RatRe (z : ℂ) : Prop := IsZero f z ∧ ∃ q : ℚ, z.re = q
def IrrRe (z : ℂ) : Prop := IsZero f z ∧ Irrational z.re
def RatIm (z : ℂ) : Prop := IsZero f z ∧ ∃ q : ℚ, z.im = q
def IrrIm (z : ℂ) : Prop := IsZero f z ∧ Irrational z.im

/-! ## 4. Informação incompleta -/

/-- Zero cuja localização **não** está no conjunto certificado `K`: informação, não espécie. -/
def Indeterminado (K : Set ℂ) (z : ℂ) : Prop := IsZero f z ∧ z ∉ K

variable {f c}

/-! ## Partição por posição -/

/-- **Na reta ou fora da reta.** -/
theorem zero_on_or_off {z : ℂ} (hz : IsZero f z) : OnLine f c z ∨ OffLine f c z := by
  by_cases h : z.re = c
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr ⟨hz, h⟩

theorem not_on_and_off (z : ℂ) : ¬ (OnLine f c z ∧ OffLine f c z) :=
  fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => h2 h1

theorem offLine_iff (z : ℂ) : OffLine f c z ↔ LeftOf f c z ∨ RightOf f c z := by
  constructor
  · rintro ⟨hz, h⟩
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
    · exact ⟨hz, h.ne⟩
    · exact ⟨hz, h.ne'⟩

/-- **Tricotomia** `x < c`, `x = c`, `x > c`. -/
theorem tricotomia {z : ℂ} (hz : IsZero f z) : LeftOf f c z ∨ OnLine f c z ∨ RightOf f c z := by
  rcases lt_trichotomy z.re c with h | h | h
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr (Or.inl ⟨hz, h⟩)
  · exact Or.inr (Or.inr ⟨hz, h⟩)

theorem posicao_exclusiva (z : ℂ) :
    ¬ (LeftOf f c z ∧ OnLine f c z) ∧ ¬ (LeftOf f c z ∧ RightOf f c z) ∧
      ¬ (OnLine f c z ∧ RightOf f c z) := by
  refine ⟨fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ?_, fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ?_, fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ?_⟩
    <;> linarith

/-- **`Z(f) = Z_{x<c} ⊔ Z_{x=c} ⊔ Z_{x>c}`.** -/
theorem particao_posicao :
    Z f = {z | LeftOf f c z} ∪ {z | OnLine f c z} ∪ {z | RightOf f c z} ∧
      Disjoint {z | LeftOf f c z} {z | OnLine f c z} ∧
      Disjoint {z | LeftOf f c z} {z | RightOf f c z} ∧
      Disjoint {z | OnLine f c z} {z | RightOf f c z} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Z, mem_ofPred_eq, mem_union]
    constructor
    · intro hz
      rcases tricotomia (c := c) (show IsZero f z from hz) with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1
      · exact h.1
  · exact Set.disjoint_left.mpr fun z h1 h2 => (posicao_exclusiva z).1 ⟨h1, h2⟩
  · exact Set.disjoint_left.mpr fun z h1 h2 => (posicao_exclusiva z).2.1 ⟨h1, h2⟩
  · exact Set.disjoint_left.mpr fun z h1 h2 => (posicao_exclusiva z).2.2 ⟨h1, h2⟩

/-! ## Partição por natureza -/

/-- **Real puro, imaginário puro ou misto.** -/
theorem zero_nature {z : ℂ} (hz : IsZero f z) : PureReal f z ∨ PureImaginary f z ∨ Mixed f z := by
  by_cases him : z.im = 0
  · exact Or.inl ⟨hz, him⟩
  · by_cases hre : z.re = 0
    · exact Or.inr (Or.inl ⟨hz, hre, him⟩)
    · exact Or.inr (Or.inr ⟨hz, hre, him⟩)

theorem natureza_exclusiva (z : ℂ) :
    ¬ (PureReal f z ∧ PureImaginary f z) ∧ ¬ (PureReal f z ∧ Mixed f z) ∧
      ¬ (PureImaginary f z ∧ Mixed f z) :=
  ⟨fun ⟨⟨_, h1⟩, ⟨_, _, h2⟩⟩ => h2 h1, fun ⟨⟨_, h1⟩, ⟨_, _, h2⟩⟩ => h2 h1,
    fun ⟨⟨_, h1, _⟩, ⟨_, h2, _⟩⟩ => h2 h1⟩

/-- **`Z(f) = Z_real ⊔ Z*_imag ⊔ Z_misto`.** -/
theorem particao_natureza :
    Z f = {z | PureReal f z} ∪ {z | PureImaginary f z} ∪ {z | Mixed f z} ∧
      Disjoint {z | PureReal f z} {z | PureImaginary f z} ∧
      Disjoint {z | PureReal f z} {z | Mixed f z} ∧
      Disjoint {z | PureImaginary f z} {z | Mixed f z} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Z, mem_ofPred_eq, mem_union]
    constructor
    · intro hz
      rcases zero_nature (show IsZero f z from hz) with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1
      · exact h.1
  · exact Set.disjoint_left.mpr fun z h1 h2 => (natureza_exclusiva z).1 ⟨h1, h2⟩
  · exact Set.disjoint_left.mpr fun z h1 h2 => (natureza_exclusiva z).2.1 ⟨h1, h2⟩
  · exact Set.disjoint_left.mpr fun z h1 h2 => (natureza_exclusiva z).2.2 ⟨h1, h2⟩

/-- A origem, se for zero, só está na classe real. -/
theorem origem_real (h : IsZero f 0) : PureReal f 0 ∧ ¬ PureImaginary f 0 ∧ ¬ Mixed f 0 :=
  ⟨⟨h, rfl⟩, fun ⟨_, _, h2⟩ => h2 rfl, fun ⟨_, _, h2⟩ => h2 rfl⟩

/-! ## Partição aritmética -/

theorem not_irrational_iff (x : ℝ) : ¬ Irrational x ↔ ∃ q : ℚ, x = q := by
  unfold Irrational
  simp only [not_not, mem_range]
  exact ⟨fun ⟨q, hq⟩ => ⟨q, hq.symm⟩, fun ⟨q, hq⟩ => ⟨q, hq.symm⟩⟩

theorem ratRe_or_irrRe {z : ℂ} (hz : IsZero f z) : RatRe f z ∨ IrrRe f z := by
  by_cases h : Irrational z.re
  · exact Or.inr ⟨hz, h⟩
  · exact Or.inl ⟨hz, (not_irrational_iff _).mp h⟩

theorem ratRe_irrRe_exclusivo (z : ℂ) : ¬ (RatRe f z ∧ IrrRe f z) :=
  fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => (not_irrational_iff _).mpr h1 h2

theorem ratIm_or_irrIm {z : ℂ} (hz : IsZero f z) : RatIm f z ∨ IrrIm f z := by
  by_cases h : Irrational z.im
  · exact Or.inr ⟨hz, h⟩
  · exact Or.inl ⟨hz, (not_irrational_iff _).mp h⟩

theorem ratIm_irrIm_exclusivo (z : ℂ) : ¬ (RatIm f z ∧ IrrIm f z) :=
  fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => (not_irrational_iff _).mpr h1 h2

/-- **`Z_ℚ ∩ Z_{ℝ∖ℚ} = ∅` e `Z_ℚ ∪ Z_{ℝ∖ℚ} = Z(f)`** (parte real). -/
theorem particao_re :
    {z | RatRe f z} ∩ {z | IrrRe f z} = ∅ ∧ {z | RatRe f z} ∪ {z | IrrRe f z} = Z f := by
  refine ⟨?_, ?_⟩
  · ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact ratRe_irrRe_exclusivo z
  · ext z
    simp only [mem_union, mem_ofPred_eq, Z]
    exact ⟨fun h => h.elim (·.1) (·.1), fun h => ratRe_or_irrRe (show IsZero f z from h)⟩

/-- O mesmo para a parte imaginária. -/
theorem particao_im :
    {z | RatIm f z} ∩ {z | IrrIm f z} = ∅ ∧ {z | RatIm f z} ∪ {z | IrrIm f z} = Z f := by
  refine ⟨?_, ?_⟩
  · ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact ratIm_irrIm_exclusivo z
  · ext z
    simp only [mem_union, mem_ofPred_eq, Z]
    exact ⟨fun h => h.elim (·.1) (·.1), fun h => ratIm_or_irrIm (show IsZero f z from h)⟩

/-! ## Matriz de compatibilidade -/

/-- Imaginário puro ⇒ parte real racional (`= 0`). -/
theorem imag_ratRe {z : ℂ} (h : PureImaginary f z) : RatRe f z := ⟨h.1, 0, by simp [h.2.1]⟩

/-- Logo imaginário puro e parte real irracional são incompatíveis. -/
theorem imag_not_irrRe {z : ℂ} (h : PureImaginary f z) : ¬ IrrRe f z :=
  fun h' => ratRe_irrRe_exclusivo z ⟨imag_ratRe h, h'⟩

/-- Real puro ⇒ parte imaginária racional (`= 0`). -/
theorem real_ratIm {z : ℂ} (h : PureReal f z) : RatIm f z := ⟨h.1, 0, by simp [h.2]⟩

/-- Para `c ∈ ℚ`: parte real irracional ⇒ fora da reta `x = c`. -/
theorem irr_offLine (q : ℚ) {z : ℂ} (h : IrrRe f z) : OffLine f q z :=
  ⟨h.1, fun he => h.2 ⟨q, he.symm⟩⟩

/-- Para `c ∈ ℚ`: na reta `x = c` ⇒ parte real racional. -/
theorem onLine_ratRe (q : ℚ) {z : ℂ} (h : OnLine f q z) : RatRe f z := ⟨h.1, q, h.2⟩

/-- Para `c ∉ ℚ`: na reta `x = c` ⇒ parte real irracional. -/
theorem onLine_irr (hc : Irrational c) {z : ℂ} (h : OnLine f c z) : IrrRe f z :=
  ⟨h.1, h.2 ▸ hc⟩

/-- **Compatibilidade não é existência**: `f ≡ 1` não tem zero em classe nenhuma. -/
theorem compat_nao_existencia (z : ℂ) : ¬ IsZero (fun _ => (1 : ℂ)) z := one_ne_zero

/-- A função que realiza as cinco células compatíveis da matriz. -/
noncomputable def fCelulas (z : ℂ) : ℂ :=
  z * (z - I) * (z - (1 + I)) * (z - (Real.sqrt 2 : ℂ)) * (z - ((Real.sqrt 2 : ℂ) + I))

/-- **Todas as células compatíveis são realizáveis** por uma única função: real∩ℚ (`0`), imaginário
(`i`), misto∩ℚ (`1 + i`), real∩(ℝ∖ℚ) (`√2`), misto∩(ℝ∖ℚ) (`√2 + i`). -/
theorem realiza_celulas :
    (PureReal fCelulas 0 ∧ RatRe fCelulas 0) ∧ PureImaginary fCelulas I ∧
      (Mixed fCelulas (1 + I) ∧ RatRe fCelulas (1 + I)) ∧
      (PureReal fCelulas (Real.sqrt 2) ∧ IrrRe fCelulas (Real.sqrt 2)) ∧
      (Mixed fCelulas ((Real.sqrt 2 : ℂ) + I) ∧ IrrRe fCelulas ((Real.sqrt 2 : ℂ) + I)) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  refine ⟨⟨⟨by simp [IsZero, fCelulas], by simp⟩, by simp [IsZero, fCelulas], 0, by simp⟩,
    ⟨by simp [IsZero, fCelulas], by simp, by simp⟩,
    ⟨⟨by simp [IsZero, fCelulas], by simp, by simp⟩, by simp [IsZero, fCelulas], 1, by simp⟩,
    ⟨⟨by simp [IsZero, fCelulas], by simp⟩, by simp [IsZero, fCelulas], by simpa using irrational_sqrt_two⟩,
    ⟨⟨by simp [IsZero, fCelulas], by simp [hs], by simp⟩, by simp [IsZero, fCelulas],
      by simpa using irrational_sqrt_two⟩⟩

/-! ## A classe da informação incompleta -/

theorem indeterminado_anti {K K' : Set ℂ} (h : K ⊆ K') {z : ℂ} (hz : Indeterminado f K' z) :
    Indeterminado f K z := ⟨hz.1, fun hk => hz.2 (h hk)⟩

theorem indeterminado_univ (z : ℂ) : ¬ Indeterminado f univ z := fun h => h.2 trivial

/-- **Não intrínseca**: o mesmo zero é indeterminado para `K = ∅` e determinado para `K = {z}`. -/
theorem indeterminado_nao_intrinseco {z : ℂ} (hz : IsZero f z) :
    Indeterminado f ∅ z ∧ ¬ Indeterminado f {z} z :=
  ⟨⟨hz, Set.notMem_empty z⟩, fun h => h.2 rfl⟩

/-- Os zeros determinados e os indeterminados particionam `Z(f)`, para cada `K`. -/
theorem particao_informacao (K : Set ℂ) :
    Z f = (Z f ∩ K) ∪ {z | Indeterminado f K z} ∧ Disjoint (Z f ∩ K) {z | Indeterminado f K z} := by
  refine ⟨?_, Set.disjoint_left.mpr fun z h1 h2 => h2.2 h1.2⟩
  ext z
  simp only [mem_union, mem_inter_iff, mem_ofPred_eq, Indeterminado, IsZero, Z]
  tauto

end ATK.ZeroClasses

#print axioms ATK.ZeroClasses.zero_on_or_off
#print axioms ATK.ZeroClasses.not_on_and_off
#print axioms ATK.ZeroClasses.offLine_iff
#print axioms ATK.ZeroClasses.tricotomia
#print axioms ATK.ZeroClasses.posicao_exclusiva
#print axioms ATK.ZeroClasses.particao_posicao
#print axioms ATK.ZeroClasses.zero_nature
#print axioms ATK.ZeroClasses.natureza_exclusiva
#print axioms ATK.ZeroClasses.particao_natureza
#print axioms ATK.ZeroClasses.origem_real
#print axioms ATK.ZeroClasses.not_irrational_iff
#print axioms ATK.ZeroClasses.ratRe_or_irrRe
#print axioms ATK.ZeroClasses.ratRe_irrRe_exclusivo
#print axioms ATK.ZeroClasses.ratIm_or_irrIm
#print axioms ATK.ZeroClasses.ratIm_irrIm_exclusivo
#print axioms ATK.ZeroClasses.particao_re
#print axioms ATK.ZeroClasses.particao_im
#print axioms ATK.ZeroClasses.imag_ratRe
#print axioms ATK.ZeroClasses.imag_not_irrRe
#print axioms ATK.ZeroClasses.real_ratIm
#print axioms ATK.ZeroClasses.irr_offLine
#print axioms ATK.ZeroClasses.onLine_ratRe
#print axioms ATK.ZeroClasses.onLine_irr
#print axioms ATK.ZeroClasses.compat_nao_existencia
#print axioms ATK.ZeroClasses.realiza_celulas
#print axioms ATK.ZeroClasses.indeterminado_anti
#print axioms ATK.ZeroClasses.indeterminado_univ
#print axioms ATK.ZeroClasses.indeterminado_nao_intrinseco
#print axioms ATK.ZeroClasses.particao_informacao
