import ATK.L3Base
import ATK.Conditional.Hodge
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# A conjectura de Hodge sobre os objetos da Mathlib

Enunciado (Deligne, descrição oficial do Clay):

> Seja `X` uma variedade algébrica projetiva não singular sobre `ℂ`. Toda classe de Hodge em
> `H^{2p}(X, ℚ)` é uma combinação linear racional de classes `cl(Z)` de ciclos algébricos.

O que é **real** aqui (objetos da Mathlib):

* `VariedadeProjetivaLisa`: um esquema `X` com morfismo estrutural `X ⟶ Spec ℂ` **liso de dimensão
  relativa `n`** (`SmoothOfRelativeDimension`) que admite uma **imersão fechada** num espaço
  projetivo `ℙᴺ_ℂ = Proj ℂ[x₀, …, x_N]` (`Proj` da Mathlib com a graduação por grau total).
* `CiclosCodim X p`: ciclos algébricos da Mathlib (`AlgebraicCycle X ℚ`) suportados em pontos de
  codimensão `p` (`dim 𝒪_{X,x} = p`).
* `H2p`: `H^{2p}(T, ℚ) := Hom_ℚ(H_{2p}(T; ℚ), ℚ)`, com a **homologia singular** da Mathlib
  (`singularHomologyFunctor` em `ModuleCat ℚ`); sobre um corpo, é a cohomologia singular.
* `IsHodgeClass`: classe racional em `H^{p,p}` de uma estrutura de Hodge pura de peso `2p`
  (`ATK.L3Base.HodgeStructure`).

O que **falta na Mathlib v4.34.1** e entra como dado explícito (`ConstrucoesHodge`):

1. a **analitificação** `X ↦ X(ℂ)` com a topologia clássica;
2. a **decomposição de Hodge** de `H^{2p}(X(ℂ), ℂ)` (teoria de Hodge em variedades de Kähler);
3. a **classe de ciclo** `cl : Z^p(X) → H^{2p}(X(ℂ), ℚ)`.

`HodgeOficial C` é o enunciado relativo a essas três construções. O kernel mostra que ele **só é o
enunciado real quando `C` é a construção genuína**: com `cl = 0` ele vira "toda classe de Hodge é
zero" (`hodge_cl_zero_iff`). E `HodgeOficial C` é exatamente `HodgeConjecture` no modelo
`modelo C` (`hodgeOficial_iff_modelo`), a interface usada pelo resto do kernel.
-/

open AlgebraicGeometry CategoryTheory

namespace ATK.HodgeOficial

/-! ## Variedades projetivas lisas sobre `ℂ` -/

/-- O espaço projetivo `ℙᴺ_ℂ = Proj ℂ[x₀, …, x_N]`. -/
noncomputable def espacoProjetivo (N : ℕ) : Scheme :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := ℂ)
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)

/-- Uma variedade projetiva não singular sobre `ℂ`, de dimensão `n`. -/
structure VariedadeProjetivaLisa where
  /-- O esquema. -/
  X : Scheme
  /-- O morfismo estrutural. -/
  estrutura : X ⟶ Spec (CommRingCat.of ℂ)
  /-- A dimensão. -/
  n : ℕ
  /-- Não singular: liso de dimensão relativa `n` sobre `ℂ`. -/
  lisa : SmoothOfRelativeDimension n estrutura
  /-- Projetiva: imersão fechada num `ℙᴺ_ℂ`. -/
  projetiva : ∃ (N : ℕ) (i : X ⟶ espacoProjetivo N), IsClosedImmersion i

/-- Ciclos algébricos com coeficientes racionais suportados em codimensão `p`. -/
def CiclosCodim (X : Scheme) (p : ℕ) : Set (AlgebraicCycle X ℚ) :=
  {z | ∀ x, z x ≠ 0 → ringKrullDim (X.presheaf.stalk x) = p}

/-- O ciclo nulo tem toda codimensão. -/
theorem zero_mem_ciclosCodim (X : Scheme) (p : ℕ) : (0 : AlgebraicCycle X ℚ) ∈ CiclosCodim X p :=
  fun _ h => absurd rfl h

/-! ## Cohomologia racional singular -/

/-- `H_k(T; ℚ)`, homologia singular da Mathlib com coeficientes em `ℚ`. -/
noncomputable def Hsing (T : TopCat.{0}) (k : ℕ) : ModuleCat.{0} ℚ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj (ModuleCat.of ℚ ℚ)).obj T

/-- `H^{2p}(T, ℚ) = Hom_ℚ(H_{2p}(T; ℚ), ℚ)` (sobre um corpo, a cohomologia singular). -/
abbrev H2p (T : TopCat.{0}) (p : ℕ) : Type := Module.Dual ℚ (Hsing T (2 * p))

/-! ## As construções ausentes da Mathlib -/

/-- As três construções que a Mathlib v4.34.1 ainda não tem. O enunciado só é o real quando estas
são as genuínas: analitificação, decomposição de Hodge (teoria de Kähler) e classe de ciclo. -/
structure ConstrucoesHodge where
  /-- `X ↦ X(ℂ)` com a topologia clássica. -/
  an : VariedadeProjetivaLisa → TopCat.{0}
  /-- A estrutura de Hodge pura de peso `2p` em `H^{2p}(X(ℂ), ℚ)`. -/
  hodge : ∀ V p, ATK.L3Base.HodgeStructure (H2p (an V) p) (2 * (p : ℤ))
  /-- A classe de ciclo `cl : Z^p(X) → H^{2p}(X(ℂ), ℚ)`. -/
  cl : ∀ V p, AlgebraicCycle V.X ℚ → H2p (an V) p

/-- **A conjectura de Hodge** relativa às construções `C`: toda classe de Hodge racional em
`H^{2p}(X(ℂ), ℚ)` é a classe de um ciclo algébrico racional de codimensão `p`. -/
def HodgeOficial (C : ConstrucoesHodge) : Prop :=
  ∀ (V : VariedadeProjetivaLisa) (p : ℕ) (α : H2p (C.an V) p),
    ATK.L3Base.IsHodgeClass (C.hodge V p) α →
      ∃ z ∈ CiclosCodim V.X p, C.cl V p z = α

/-! ## Ligação com a interface do kernel -/

/-- O modelo `HodgeModel` determinado pelas construções. -/
noncomputable def modelo (C : ConstrucoesHodge) : ATK.Conditional.Hodge.HodgeModel.{1, 0} where
  Variety := VariedadeProjetivaLisa
  SmoothProjective _ := True
  dim V := V.n
  Class V p := H2p (C.an V) p
  IsHodge {V} {p} α := ATK.L3Base.IsHodgeClass (C.hodge V p) α
  IsAlgebraic {V} {p} α := ∃ z ∈ CiclosCodim V.X p, C.cl V p z = α

/-- `HodgeOficial C` é exatamente `HodgeConjecture (modelo C)`. -/
theorem hodgeOficial_iff_modelo (C : ConstrucoesHodge) :
    HodgeOficial C ↔ ATK.Conditional.Hodge.HodgeConjecture (modelo C) :=
  ⟨fun h V _ p α hα => h V p α hα, fun h V p α hα => h V trivial p α hα⟩

/-! ## Firewall: o enunciado depende das construções -/

/-- Com uma classe de ciclo nula, o enunciado vira "toda classe de Hodge é zero": sem as
construções genuínas, `HodgeOficial` não é a conjectura de Hodge. -/
theorem hodge_cl_zero_iff (C : ConstrucoesHodge) (h0 : ∀ V p z, C.cl V p z = 0) :
    HodgeOficial C ↔ ∀ V p (α : H2p (C.an V) p), ATK.L3Base.IsHodgeClass (C.hodge V p) α →
      α = 0 := by
  constructor
  · intro h V p α hα
    obtain ⟨z, _, hz⟩ := h V p α hα
    rw [← hz, h0]
  · intro h V p α hα
    exact ⟨0, zero_mem_ciclosCodim _ _, by rw [h0, h V p α hα]⟩

/-! ## Construções coerentes: o que já se sabe sobre a classe de ciclo -/

/-- Construções que satisfazem os teoremas conhecidos: a classe de ciclo é aditiva e a classe de um
ciclo de codimensão `p` é sempre uma classe de Hodge (a direção fácil, provada por Hodge). -/
structure Coerente (C : ConstrucoesHodge) : Prop where
  cl_add : ∀ (V : VariedadeProjetivaLisa) (p : ℕ) (z₁ z₂ : AlgebraicCycle V.X ℚ), C.cl V p (z₁ + z₂) = C.cl V p z₁ + C.cl V p z₂
  cl_hodge : ∀ (V : VariedadeProjetivaLisa) (p : ℕ), ∀ z ∈ CiclosCodim V.X p, ATK.L3Base.IsHodgeClass (C.hodge V p) (C.cl V p z)

/-- Para construções coerentes, a conjectura de Hodge diz exatamente: **as classes de Hodge são as
classes de ciclo**. -/
theorem hodge_iff_imagem {C : ConstrucoesHodge} (hC : Coerente C) :
    HodgeOficial C ↔ ∀ V p, {α : H2p (C.an V) p | ATK.L3Base.IsHodgeClass (C.hodge V p) α} =
      C.cl V p '' CiclosCodim V.X p := by
  constructor
  · intro h V p
    ext α
    constructor
    · intro hα
      obtain ⟨z, hz, rfl⟩ := h V p α hα
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hC.cl_hodge V p z hz
  · intro h V p α hα
    have : α ∈ C.cl V p '' CiclosCodim V.X p := h V p ▸ hα
    obtain ⟨z, hz, rfl⟩ := this
    exact ⟨z, hz, rfl⟩

/-- A coerência **não** fixa a construção: `cl = 0` é coerente (`0` é classe de Hodge), e então o
enunciado vira "toda classe de Hodge é 0". As construções genuínas continuam necessárias. -/
theorem zero_coerente (C : ConstrucoesHodge) (h0 : ∀ V p z, C.cl V p z = 0) : Coerente C where
  cl_add V p z₁ z₂ := by rw [h0, h0, h0, add_zero]
  cl_hodge V p z _ := by
    rw [h0]
    exact (ATK.L3Base.hodgeClasses (C.hodge V p)).zero_mem

end ATK.HodgeOficial

#print axioms ATK.HodgeOficial.zero_mem_ciclosCodim
#print axioms ATK.HodgeOficial.hodgeOficial_iff_modelo
#print axioms ATK.HodgeOficial.hodge_cl_zero_iff
#print axioms ATK.HodgeOficial.hodge_iff_imagem
#print axioms ATK.HodgeOficial.zero_coerente
