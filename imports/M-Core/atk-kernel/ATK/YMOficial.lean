import ATK.L5Base
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# Yang–Mills: o enunciado do Clay, formalizado até onde o texto é matemático

Texto oficial (Jaffe–Witten, *Quantum Yang–Mills Theory*, Clay 2000):

> Prove que para todo grupo de calibre compacto simples `G` existe uma teoria quântica de
> Yang–Mills não trivial em `ℝ⁴` com lacuna de massa `Δ > 0`.

e "teoria quântica de Yang–Mills" quer dizer: satisfaz axiomas pelo menos tão fortes quanto os de
Wightman/Osterwalder–Schrader, e seus operadores de campo locais **correspondem** aos polinômios
locais invariantes de calibre na curvatura `F` e suas derivadas covariantes.

O que este arquivo formaliza, sobre a Mathlib e `ATK.L5Base.Wightman`:

* `CompactaSimples 𝔤`: álgebra de Lie real de dimensão finita, **simples**
  (`LieAlgebra.IsSimple`), de **tipo compacto** (forma de Killing negativa definida). É a álgebra
  de Lie de um grupo de calibre compacto simples; a teoria local só depende de `𝔤`.
* `GapMassa W Δ`: o espectro de energia-momento está em `{0} ∪ {p : p⁰ ≥ 0, p² ≥ Δ²}`, na mesma
  forma distribucional da condição espectral de `Wightman`.
* `NaoTrivial W`: o campo centrado **não** é gaussiano. As funções de Wightman não seguem a fórmula
  de Wick a partir da função de 2 pontos, ou seja, a teoria não é um campo livre generalizado.
* `Invariante` / `trF2`: funções da curvatura invariantes sob a ação adjunta, com o teste de que
  `tr F² = Σ ±K(Fᵢ, Fᵢ)` é invariante (`trF2_invariante`).
* `YMNucleo`: para toda `𝔤` compacta simples existe uma teoria de Wightman em `ℝ⁴`, não trivial,
  com lacuna `Δ > 0`.
* `YMClay Corresponde`: o núcleo **mais** a correspondência com Yang–Mills clássico, recebida como
  predicado explícito.

**Limite honesto**: o texto do Clay não dá critério formal para "corresponde". Qualquer escolha
(OPE com liberdade assintótica, limite de rede com ação de Wilson, …) é uma interpretação. Por isso
`Corresponde` é um parâmetro. `YMNucleo` não usa `𝔤` na teoria (`nucleo_sem_g`), e o kernel
mostra por que cada cláusula é necessária: a teoria trivial satisfaz a lacuna (`trivial_gap`), mas
é gaussiana (`trivial_gaussiana`).
-/

open scoped FourierTransform InnerProductSpace
open MeasureTheory ATK.L5Base

namespace ATK.YMOficial

/-! ## A álgebra de calibre -/

/-- Álgebra de Lie real de dimensão finita, simples e de tipo compacto (Killing negativa definida). -/
def CompactaSimples (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] : Prop :=
  Module.Finite ℝ 𝔤 ∧ LieAlgebra.IsSimple ℝ 𝔤 ∧
    ∀ x : 𝔤, x ≠ 0 → LieModule.traceForm ℝ 𝔤 𝔤 x x < 0

/-- Uma função das 6 componentes da curvatura `F_{μν}` (`μ < ν`) é **invariante de calibre**
se for constante ao longo da ação adjunta infinitesimal `F ↦ F + t ⁅x, F⁆`. -/
def Invariante {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (P : (Fin 6 → 𝔤) → ℝ) : Prop :=
  ∀ (x : 𝔤) (F : Fin 6 → 𝔤), HasDerivAt (fun t : ℝ => P (F + t • fun i => ⁅x, F i⁆)) 0 0

/-- Sinais de Minkowski para `F_{μν}F^{μν}`: componentes elétricas (`0i`) e magnéticas (`ij`). -/
def sinal (i : Fin 6) : ℝ := if i.val < 3 then -1 else 1

/-- `tr F² = Σᵢ ±K(Fᵢ, Fᵢ)`, com `K` a forma de Killing. -/
noncomputable def trF2 {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (F : Fin 6 → 𝔤) : ℝ :=
  ∑ i, sinal i * LieModule.traceForm ℝ 𝔤 𝔤 (F i) (F i)

/-- **Teste**: `tr F²` é invariante de calibre (invariância da forma de Killing). -/
theorem trF2_invariante {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Free ℝ 𝔤]
    [Module.Finite ℝ 𝔤] : Invariante (trF2 (𝔤 := 𝔤)) := by
  intro x F
  set K := LieModule.traceForm ℝ 𝔤 𝔤
  have hK : ∀ i, K (F i) ⁅x, F i⁆ = 0 := fun i => by
    rw [LieModule.traceForm_comm, LieModule.traceForm_apply_lie_apply, lie_self, map_zero]
  have hexp : ∀ t : ℝ, trF2 (F + t • fun i => ⁅x, F i⁆) =
      trF2 F + t ^ 2 * ∑ i, sinal i * K ⁅x, F i⁆ ⁅x, F i⁆ := by
    intro t
    simp only [trF2, Pi.add_apply, Pi.smul_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hK i
    have h2 : K ⁅x, F i⁆ (F i) = 0 := by rw [LieModule.traceForm_comm]; exact h1
    rw [h1, h2]
    ring
  simp_rw [hexp]
  have : HasDerivAt (fun t : ℝ => trF2 F + t ^ 2 * ∑ i, sinal i * K ⁅x, F i⁆ ⁅x, F i⁆)
      (2 * (0 : ℝ) ^ 1 * ∑ i, sinal i * K ⁅x, F i⁆ ⁅x, F i⁆) 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (∑ i, sinal i * K ⁅x, F i⁆ ⁅x, F i⁆)).const_add
      (trF2 F)
    simpa using this
  simpa using this

/-! ## Lacuna de massa -/

section Teoria

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A região espectral com lacuna `Δ`: `{0} ∪ {p : p⁰ ≥ 0, p·p ≥ Δ²}`. -/
def regiaoGap (Δ : ℝ) : Set ET := {0} ∪ {p | 0 ≤ p 0 ∧ Δ ^ 2 ≤ mink p p}

/-- **Lacuna de massa** `Δ`: o espectro de energia-momento está em `regiaoGap Δ` (mesma forma
distribucional da condição espectral de `Wightman`). -/
def GapMassa (W : Wightman H) (Δ : ℝ) : Prop :=
  ∀ ψ χ : H, ∀ g : SchwartzMap ET ℂ, Disjoint (tsupport g) (regiaoGap Δ) →
    ∫ b, ⟪χ, W.U ((2 * Real.pi) • refl b) Lorentz.id ψ⟫_ℂ * (𝓕 g) b = 0

/-! ## Não trivialidade -/

/-- O valor esperado no vácuo `⟨Ω, φ(f) Ω⟩`. -/
noncomputable def vev (W : Wightman H) (f : SchwartzMap ET ℂ) : ℂ := ⟪W.Ω, W.φ f W.Ω⟫_ℂ

/-- O campo centrado `φ(f) − ⟨φ(f)⟩`. -/
noncomputable def campoC (W : Wightman H) (f : SchwartzMap ET ℂ) : H →ₗ[ℂ] H :=
  W.φ f - vev W f • LinearMap.id

/-- Funções de Wightman do campo centrado: `⟨Ω, φc(f₁) ⋯ φc(fₙ) Ω⟩`. -/
noncomputable def wfun (W : Wightman H) (fs : List (SchwartzMap ET ℂ)) : ℂ :=
  ⟪W.Ω, fs.foldr (fun f v => campoC W f v) W.Ω⟫_ℂ

end Teoria

/-- A **fórmula de Wick** (ordenada): soma sobre os emparelhamentos, cada par na ordem original. -/
noncomputable def wick {S : Type*} (w2 : S → S → ℂ) : List S → ℂ
  | [] => 1
  | f :: rest => ∑ i : Fin rest.length, w2 f (rest.get i) * wick w2 (rest.eraseIdx i)
termination_by l => l.length
decreasing_by simp [List.length_eraseIdx]

section Teoria2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A teoria é **gaussiana** (campo livre generalizado): todas as funções de Wightman do campo
centrado seguem a fórmula de Wick a partir da função de 2 pontos. -/
def Gaussiana (W : Wightman H) : Prop :=
  ∀ fs, wfun W fs = wick (fun f g => wfun W [f, g]) fs

/-- **Não trivial**: não gaussiana. -/
def NaoTrivial (W : Wightman H) : Prop := ¬ Gaussiana W

end Teoria2

/-! ## O enunciado -/

/-- **Núcleo formal do problema do Clay**: para toda álgebra de calibre compacta simples existe uma
teoria de Wightman em `ℝ⁴`, não trivial, com lacuna de massa positiva. -/
def YMNucleo : Prop :=
  ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤], CompactaSimples 𝔤 →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (W : Wightman H), NaoTrivial W ∧ ∃ Δ : ℝ, 0 < Δ ∧ GapMassa W Δ

/-- **Enunciado do Clay** com a correspondência a Yang–Mills clássico como predicado explícito
(o texto oficial não a define formalmente). -/
def YMClay (Corresponde : ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], Wightman H → Prop) : Prop :=
  ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤], CompactaSimples 𝔤 →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (W : Wightman H), Corresponde 𝔤 H W ∧ NaoTrivial W ∧ ∃ Δ : ℝ, 0 < Δ ∧ GapMassa W Δ

/-- O enunciado do Clay implica o núcleo, para **qualquer** interpretação de "corresponde". -/
theorem clay_implica_nucleo {C : ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], Wightman H → Prop}
    (h : YMClay C) : YMNucleo := by
  intro 𝔤 _ _ h𝔤
  obtain ⟨H, i1, i2, i3, W, _, hnt, hgap⟩ := h 𝔤 h𝔤
  exact ⟨H, i1, i2, i3, W, hnt, hgap⟩

/-- Com a interpretação vazia (`Corresponde := True`), o enunciado do Clay **é** o núcleo:
sem um critério de correspondência, `𝔤` não entra na teoria. -/
theorem nucleo_sem_g : YMClay (fun _ _ _ _ _ _ _ _ => True) ↔ YMNucleo := by
  constructor
  · exact clay_implica_nucleo
  · intro h 𝔤 _ _ h𝔤
    obtain ⟨H, i1, i2, i3, W, hnt, hgap⟩ := h 𝔤 h𝔤
    exact ⟨H, i1, i2, i3, W, trivial, hnt, hgap⟩

/-! ## Testes: cada cláusula é necessária -/

/-- A teoria trivial tem lacuna de massa para todo `Δ`: o espectro é `{0}`. -/
theorem trivial_gap (Δ : ℝ) : GapMassa ATK.L5Base.trivial Δ := by
  intro ψ χ g hg
  have h0 : g 0 = 0 := by
    by_contra hne
    exact Set.disjoint_left.mp hg (subset_tsupport g hne) (Or.inl rfl)
  change ∫ b, ⟪χ, ψ⟫_ℂ * (𝓕 g) b = 0
  rw [integral_const_mul, integral_fourier, h0, mul_zero]

/-- … mas é gaussiana: a lacuna sozinha não basta, a não trivialidade é necessária. -/
theorem trivial_gaussiana : Gaussiana ATK.L5Base.trivial := by
  intro fs
  have hw : ∀ gs : List (SchwartzMap ET ℂ), gs ≠ [] → wfun ATK.L5Base.trivial gs = 0 := by
    intro gs hgs
    obtain ⟨g, rest, rfl⟩ := List.exists_cons_of_ne_nil hgs
    simp [wfun, campoC, vev, ATK.L5Base.trivial]
  match fs with
  | [] =>
    simp only [wfun, wick, List.foldr_nil, inner_self_eq_norm_sq_to_K,
      ATK.L5Base.trivial.norma_Ω]
    norm_num
  | f :: rest =>
    rw [hw _ (List.cons_ne_nil _ _), wick]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hw _ (List.cons_ne_nil _ _), zero_mul]

theorem trivial_nao_e_nao_trivial : ¬ NaoTrivial ATK.L5Base.trivial :=
  fun h => h trivial_gaussiana

end ATK.YMOficial

#print axioms ATK.YMOficial.trF2_invariante
#print axioms ATK.YMOficial.clay_implica_nucleo
#print axioms ATK.YMOficial.nucleo_sem_g
#print axioms ATK.YMOficial.trivial_gap
#print axioms ATK.YMOficial.trivial_gaussiana
#print axioms ATK.YMOficial.trivial_nao_e_nao_trivial
