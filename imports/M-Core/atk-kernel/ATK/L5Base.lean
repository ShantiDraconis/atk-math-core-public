import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# ATK — L5, base: os axiomas de Wightman

Rascunho no estilo da Mathlib para a ligação L5 (Yang–Mills): a estrutura `Wightman H` de uma
teoria quântica de campos escalar hermitiana em `ℝ⁴` (Streater–Wightman, cap. 3), sobre o que a
Mathlib já tem (espaços de Hilbert, funções de Schwartz, transformada de Fourier):

* espaço-tempo de Minkowski (`mink`, assinatura `(+, −, −, −)`), vetores tipo espaço, cone futuro
  fechado `V̄₊`, transformações de Lorentz próprias ortócronas (`Lorentz`);
* representação unitária fortemente contínua do grupo de Poincaré restrito (topologia de `Lorentz`
  induzida pela norma de operador), vácuo invariante e
  único, domínio denso invariante, campo como distribuição temperada a valores em operadores,
  hermiticidade, covariância, localidade, condição espectral (via `𝓕` da Mathlib, convenção
  `U(a) = e^{i P·a}`), ciclicidade do vácuo.

**Testes de sanidade**: `mink p a = ⟪p, R a⟫` (`mink_eq_inner`), `e₀ ∈ V̄₊`, `e₁` tipo espaço,
`∫ 𝓕 g = g 0`, e a teoria trivial (`H = ℂ`, `φ = 0`) satisfaz os axiomas (`trivial`): os axiomas
são consistentes.

O problema do Clay pede uma teoria **não trivial** de Yang–Mills (grupo de calibre compacto
simples, observáveis locais que correspondem ao Yang–Mills clássico) com lacuna de massa `Δ > 0`;
isso ainda não está expresso aqui (campos de calibre, OS/Wightman para campos vetoriais). Nada aqui
prova a existência de Yang–Mills. **CLOSED_MATH continua false.**
-/

open scoped FourierTransform InnerProductSpace
open MeasureTheory

namespace ATK.L5Base

/-! ## Espaço-tempo de Minkowski -/

/-- O espaço-tempo `ℝ⁴`, coordenadas `(x⁰, x¹, x², x³)` (norma euclidiana só para as funções
de teste). -/
abbrev ET := EuclideanSpace ℝ (Fin 4)

/-- O produto de Minkowski, assinatura `(+, −, −, −)`. -/
def mink (x y : ET) : ℝ := x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- Vetor tipo espaço. -/
def Espacial (x : ET) : Prop := mink x x < 0

/-- Dois conjuntos separados tipo espaço. -/
def SeparadosEspacialmente (A B : Set ET) : Prop := ∀ x ∈ A, ∀ y ∈ B, Espacial (x - y)

/-- O cone futuro fechado `V̄₊`. -/
def coneFuturo : Set ET := {p | 0 ≤ p 0 ∧ 0 ≤ mink p p}

/-- A reflexão espacial `R = diag(1, −1, −1, −1)`: `mink p a = ⟪p, R a⟫`. -/
def refl (a : ET) : ET := WithLp.toLp 2 (fun i => if i = 0 then a 0 else - a i)

/-- Uma transformação de Lorentz própria ortócrona (o grupo de Lorentz restrito `L↑₊`). -/
structure Lorentz where
  /-- A transformação linear. -/
  Λ : ET ≃L[ℝ] ET
  /-- Preserva o produto de Minkowski. -/
  preserva : ∀ x y, mink (Λ x) (Λ y) = mink x y
  /-- Própria: determinante 1. -/
  propria : LinearMap.det (Λ : ET →ₗ[ℝ] ET) = 1
  /-- Ortócrona: preserva o sentido do tempo. -/
  ortocrona : 1 ≤ (Λ (EuclideanSpace.single 0 1)) 0

/-- A identidade. -/
noncomputable def Lorentz.id : Lorentz where
  Λ := ContinuousLinearEquiv.refl ℝ ET
  preserva _ _ := rfl
  propria := by
    rw [show ((ContinuousLinearEquiv.refl ℝ ET : ET ≃L[ℝ] ET) : ET →ₗ[ℝ] ET) = LinearMap.id from rfl,
      LinearMap.det_id]
  ortocrona := by simp

/-- A topologia de `Lorentz`: a induzida pela norma de operador em `ET →L[ℝ] ET`. -/
noncomputable instance : TopologicalSpace Lorentz :=
  TopologicalSpace.induced (fun Λ : Lorentz => (Λ.Λ : ET →L[ℝ] ET)) inferInstance

/-! ## Os axiomas de Wightman -/

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Axiomas de Wightman** para um campo escalar hermitiano em `ℝ⁴` (Streater–Wightman, cap. 3),
com `U(a, Λ) = e^{i P·a}` nos translados. -/
structure Wightman where
  /-- Representação do grupo de Poincaré restrito: `U a Λ` age por `x ↦ Λ x + a`. -/
  U : ET → Lorentz → H →L[ℂ] H
  unitaria : ∀ a Λ, U a Λ ∈ unitary (H →L[ℂ] H)
  identidade : U 0 Lorentz.id = 1
  composicao : ∀ a b (Λ M N : Lorentz), N.Λ = M.Λ.trans Λ.Λ →
    U a Λ ∘L U b M = U (a + Λ.Λ b) N
  /-- Continuidade forte em todo o grupo de Poincaré restrito. -/
  continua : ∀ ψ : H, Continuous fun p : ET × Lorentz => U p.1 p.2 ψ
  /-- O vácuo. -/
  Ω : H
  norma_Ω : ‖Ω‖ = 1
  invariante : ∀ a Λ, U a Λ Ω = Ω
  vacuo_unico : ∀ ψ : H, (∀ a, U a Lorentz.id ψ = ψ) → ∃ c : ℂ, ψ = c • Ω
  /-- O domínio comum, denso, invariante. -/
  D : Submodule ℂ H
  denso : Dense (D : Set H)
  Ω_mem : Ω ∈ D
  U_D : ∀ a Λ, ∀ ψ ∈ D, U a Λ ψ ∈ D
  /-- O campo: distribuição temperada a valores em operadores (definidos em `D`). -/
  φ : SchwartzMap ET ℂ →ₗ[ℂ] H →ₗ[ℂ] H
  φ_D : ∀ f, ∀ ψ ∈ D, φ f ψ ∈ D
  temperado : ∀ ψ ∈ D, ∀ χ ∈ D, Continuous fun f : SchwartzMap ET ℂ => ⟪χ, φ f ψ⟫_ℂ
  /-- Campo hermitiano: `φ(f)* = φ(f̄)` em `D`. -/
  hermitiano : ∀ f f' : SchwartzMap ET ℂ, (∀ x, f' x = (starRingEnd ℂ) (f x)) →
    ∀ ψ ∈ D, ∀ χ ∈ D, ⟪χ, φ f ψ⟫_ℂ = ⟪φ f' χ, ψ⟫_ℂ
  /-- Covariância: `U φ(f) U⁻¹ = φ(f ∘ g⁻¹)`. -/
  covariante : ∀ a (Λ : Lorentz) (f f' : SchwartzMap ET ℂ), (∀ x, f' x = f (Λ.Λ.symm (x - a))) →
    ∀ ψ ∈ D, U a Λ (φ f ψ) = φ f' (U a Λ ψ)
  /-- Localidade (comutatividade microcausal). -/
  localidade : ∀ f g : SchwartzMap ET ℂ, SeparadosEspacialmente (tsupport f) (tsupport g) →
    ∀ ψ ∈ D, φ f (φ g ψ) = φ g (φ f ψ)
  /-- Condição espectral: o espectro de energia-momento está em `V̄₊`. Com `U(a) = e^{i P·a}` e
  `P·a = ⟪P, R a⟫`, isto é: `∫ ⟪χ, U(2π R b) ψ⟫ (𝓕 g)(b) db = ∫ g dμ_{χψ} = 0` sempre que
  `supp g` não toca `V̄₊`. -/
  espectral : ∀ ψ χ : H, ∀ g : SchwartzMap ET ℂ, Disjoint (tsupport g) coneFuturo →
    ∫ b, ⟪χ, U ((2 * Real.pi) • refl b) Lorentz.id ψ⟫_ℂ * (𝓕 g) b = 0
  /-- Cíclico: polinômios no campo aplicados ao vácuo são densos. -/
  ciclico : Dense (Submodule.span ℂ {v : H | ∃ fs : List (SchwartzMap ET ℂ),
    v = fs.foldr (fun f v => φ f v) Ω} : Set H)

/-! ## Testes de sanidade -/

/-- `mink p a = ⟪p, R a⟫`: a reflexão `R` converte o produto de Minkowski no euclidiano. -/
theorem mink_eq_inner (p a : ET) : mink p a = ⟪p, refl a⟫_ℝ := by
  simp [mink, refl, PiLp.inner_apply, Fin.sum_univ_four]
  ring

/-- `e₀ = (1, 0, 0, 0)` está no cone futuro. -/
theorem e0_cone : EuclideanSpace.single (0 : Fin 4) (1 : ℝ) ∈ coneFuturo := by
  simp [coneFuturo, mink]

/-- `e₁ = (0, 1, 0, 0)` é tipo espaço. -/
theorem e1_espacial : Espacial (EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) := by
  simp [Espacial, mink]

/-- A origem está no cone futuro. -/
theorem zero_cone : (0 : ET) ∈ coneFuturo := by simp [coneFuturo, mink]

/-- `∫ 𝓕 g = g 0` (inversão de Fourier na origem). -/
theorem integral_fourier (g : SchwartzMap ET ℂ) : ∫ b, (𝓕 g) b = g 0 := by
  have h : (𝓕⁻ (𝓕 g) : SchwartzMap ET ℂ) 0 = g 0 := by
    rw [FourierPair.fourierInv_fourier_eq (F := SchwartzMap ET ℂ) g]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp

/-- **Teste**: a teoria trivial (`H = ℂ`, `U = 1`, `Ω = 1`, `φ = 0`) satisfaz os axiomas de Wightman.
Os axiomas são consistentes; a teoria trivial não é uma teoria de Yang–Mills (o problema do Clay
pede uma teoria não trivial com grupo de calibre compacto simples e lacuna de massa). -/
noncomputable def trivial : Wightman ℂ where
  U _ _ := 1
  unitaria _ _ := one_mem _
  identidade := rfl
  composicao _ _ _ _ _ _ := ContinuousLinearMap.comp_id _
  continua _ := continuous_const
  Ω := 1
  norma_Ω := by simp
  invariante _ _ := rfl
  vacuo_unico ψ _ := ⟨ψ, by simp⟩
  D := ⊤
  denso := by simp
  Ω_mem := Submodule.mem_top
  U_D _ _ _ _ := Submodule.mem_top
  φ := 0
  φ_D _ _ _ := Submodule.mem_top
  temperado _ _ _ _ := by simp only [LinearMap.zero_apply, inner_zero_right]; exact continuous_const
  hermitiano _ _ _ _ _ _ _ := by simp
  covariante _ _ _ _ _ _ _ := by simp
  localidade _ _ _ _ _ := by simp
  espectral ψ χ g hg := by
    have h0 : g 0 = 0 := by
      by_contra hne
      exact Set.disjoint_left.mp hg (subset_tsupport g hne) zero_cone
    change ∫ b, ⟪χ, ψ⟫_ℂ * (𝓕 g) b = 0
    rw [integral_const_mul, integral_fourier, h0, mul_zero]
  ciclico := by
    have h1 : (1 : ℂ) ∈ Submodule.span ℂ {v : ℂ | ∃ fs : List (SchwartzMap ET ℂ),
        v = fs.foldr (fun f v => (0 : SchwartzMap ET ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) f v) 1} :=
      Submodule.subset_span ⟨[], rfl⟩
    have htop : Submodule.span ℂ {v : ℂ | ∃ fs : List (SchwartzMap ET ℂ),
        v = fs.foldr (fun f v => (0 : SchwartzMap ET ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) f v) 1} = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have := Submodule.smul_mem _ x h1
      simpa using this
    rw [htop]
    simp

end ATK.L5Base

#print axioms ATK.L5Base.mink_eq_inner
#print axioms ATK.L5Base.e0_cone
#print axioms ATK.L5Base.e1_espacial
#print axioms ATK.L5Base.zero_cone
#print axioms ATK.L5Base.integral_fourier
#print axioms ATK.L5Base.trivial
