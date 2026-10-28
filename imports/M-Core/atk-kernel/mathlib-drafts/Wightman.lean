/-
Copyright (c) 2026 Tiago Paschoalatto Fagliari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiago Paschoalatto Fagliari
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped FourierTransform InnerProductSpace
open MeasureTheory

namespace QFT

/-!
# The Wightman axioms

The Wightman axioms for a Hermitian scalar quantum field on `ℝ⁴` (Streater–Wightman, Ch. 3),
built on Hilbert spaces, Schwartz functions and the Fourier transform from Mathlib.

## Main definitions

* `QFT.minkowski`, `QFT.IsSpacelike`, `QFT.closedForwardCone`, `QFT.RestrictedLorentz`.
* `QFT.WightmanQFT H`: unitary representation of the restricted Poincaré group, unique invariant
  vacuum, dense invariant domain, operator-valued tempered field, hermiticity, covariance,
  locality, spectral condition (with `U(a) = e^{i P·a}`), cyclicity of the vacuum.

## Main results

* `QFT.minkowski_eq_inner`: `minkowski p a = ⟪p, R a⟫` with `R = diag(1, -1, -1, -1)`.
* `QFT.trivialTheory`: the trivial theory (`H = ℂ`, zero field) satisfies the axioms.
-/

/-- Spacetime `ℝ⁴` with coordinates `(x⁰, x¹, x², x³)` (the Euclidean norm is only used for
test functions). -/
abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

/-- The Minkowski product, signature `(+, -, -, -)`. -/
def minkowski (x y : Spacetime) : ℝ := x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- A spacelike vector. -/
def IsSpacelike (x : Spacetime) : Prop := minkowski x x < 0

/-- Two spacelike separated sets. -/
def SpacelikeSeparated (A B : Set Spacetime) : Prop := ∀ x ∈ A, ∀ y ∈ B, IsSpacelike (x - y)

/-- The closed forward light cone. -/
def closedForwardCone : Set Spacetime := {p | 0 ≤ p 0 ∧ 0 ≤ minkowski p p}

/-- The spatial reflection `R = diag(1, -1, -1, -1)`, so that `minkowski p a = ⟪p, R a⟫`. -/
def spatialReflection (a : Spacetime) : Spacetime :=
  WithLp.toLp 2 (fun i => if i = 0 then a 0 else - a i)

/-- A proper orthochronous Lorentz transformation. -/
structure RestrictedLorentz where
  /-- The linear map. -/
  Λ : Spacetime ≃L[ℝ] Spacetime
  /-- It preserves the Minkowski product. -/
  map_minkowski : ∀ x y, minkowski (Λ x) (Λ y) = minkowski x y
  /-- Proper: determinant one. -/
  det_eq_one : LinearMap.det (Λ : Spacetime →ₗ[ℝ] Spacetime) = 1
  /-- Orthochronous: it preserves the direction of time. -/
  orthochronous : 1 ≤ (Λ (EuclideanSpace.single 0 1)) 0

/-- The identity. -/
noncomputable def RestrictedLorentz.id : RestrictedLorentz where
  Λ := ContinuousLinearEquiv.refl ℝ Spacetime
  map_minkowski _ _ := rfl
  det_eq_one := by
    rw [show ((ContinuousLinearEquiv.refl ℝ Spacetime : Spacetime ≃L[ℝ] Spacetime) :
        Spacetime →ₗ[ℝ] Spacetime) = LinearMap.id from rfl,
      LinearMap.det_id]
  orthochronous := by simp

/-- The topology on `RestrictedLorentz`, induced by the operator norm on
`Spacetime →L[ℝ] Spacetime`. -/
noncomputable instance : TopologicalSpace RestrictedLorentz :=
  TopologicalSpace.induced (fun Λ : RestrictedLorentz => (Λ.Λ : Spacetime →L[ℝ] Spacetime))
    inferInstance

/-! ## The Wightman axioms -/

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Wightman axioms** for a Hermitian scalar field on `ℝ⁴` (Streater–Wightman, Ch. 3),
with `U(a, Λ) = e^{i P·a}` on translations. -/
structure WightmanQFT where
  /-- Representation of the restricted Poincaré group: `U a Λ` acts by `x ↦ Λ x + a`. -/
  U : Spacetime → RestrictedLorentz → H →L[ℂ] H
  unitary : ∀ a Λ, U a Λ ∈ unitary (H →L[ℂ] H)
  map_one : U 0 RestrictedLorentz.id = 1
  map_mul : ∀ a b (Λ M N : RestrictedLorentz), N.Λ = M.Λ.trans Λ.Λ →
    U a Λ ∘L U b M = U (a + Λ.Λ b) N
  /-- Strong continuity on the whole restricted Poincaré group. -/
  continuous : ∀ ψ : H, Continuous fun p : Spacetime × RestrictedLorentz => U p.1 p.2 ψ
  /-- The vacuum. -/
  Ω : H
  norm_vacuum : ‖Ω‖ = 1
  vacuum_invariant : ∀ a Λ, U a Λ Ω = Ω
  vacuum_unique : ∀ ψ : H, (∀ a, U a RestrictedLorentz.id ψ = ψ) → ∃ c : ℂ, ψ = c • Ω
  /-- The common dense invariant domain. -/
  D : Submodule ℂ H
  dense_domain : Dense (D : Set H)
  vacuum_mem : Ω ∈ D
  domain_invariant : ∀ a Λ, ∀ ψ ∈ D, U a Λ ψ ∈ D
  /-- The field: an operator-valued tempered distribution (operators defined on `D`). -/
  φ : SchwartzMap Spacetime ℂ →ₗ[ℂ] H →ₗ[ℂ] H
  field_domain : ∀ f, ∀ ψ ∈ D, φ f ψ ∈ D
  tempered : ∀ ψ ∈ D, ∀ χ ∈ D, Continuous fun f : SchwartzMap Spacetime ℂ => ⟪χ, φ f ψ⟫_ℂ
  /-- Hermitian field: `φ(f)* = φ(conj f)` on `D`. -/
  hermitian : ∀ f f' : SchwartzMap Spacetime ℂ, (∀ x, f' x = (starRingEnd ℂ) (f x)) →
    ∀ ψ ∈ D, ∀ χ ∈ D, ⟪χ, φ f ψ⟫_ℂ = ⟪φ f' χ, ψ⟫_ℂ
  /-- Covariance: `U φ(f) U⁻¹ = φ(f ∘ g⁻¹)`. -/
  covariant : ∀ a (Λ : RestrictedLorentz) (f f' : SchwartzMap Spacetime ℂ),
    (∀ x, f' x = f (Λ.Λ.symm (x - a))) →
    ∀ ψ ∈ D, U a Λ (φ f ψ) = φ f' (U a Λ ψ)
  /-- Locality (microcausal commutativity). -/
  locality : ∀ f g : SchwartzMap Spacetime ℂ, SpacelikeSeparated (tsupport f) (tsupport g) →
    ∀ ψ ∈ D, φ f (φ g ψ) = φ g (φ f ψ)
  /-- Spectral condition: the energy-momentum spectrum lies in the closed forward cone. With
  `U(a) = e^{i P·a}` and `P·a = ⟪P, R a⟫` this says `∫ ⟪χ, U(2π R b) ψ⟫ (𝓕 g)(b) db = 0` whenever
  the support of `g` misses the cone. -/
  spectral_condition : ∀ ψ χ : H, ∀ g : SchwartzMap Spacetime ℂ,
    Disjoint (tsupport g) closedForwardCone →
    ∫ b, ⟪χ, U ((2 * Real.pi) • spatialReflection b) RestrictedLorentz.id ψ⟫_ℂ * (𝓕 g) b = 0
  /-- Cyclicity: polynomials in the field applied to the vacuum are dense. -/
  cyclic : Dense (Submodule.span ℂ {v : H | ∃ fs : List (SchwartzMap Spacetime ℂ),
    v = fs.foldr (fun f v => φ f v) Ω} : Set H)

/-! ## Sanity checks -/

/-- The reflection `R` turns the Minkowski product into the Euclidean one. -/
theorem minkowski_eq_inner (p a : Spacetime) : minkowski p a = ⟪p, spatialReflection a⟫_ℝ := by
  simp [minkowski, spatialReflection, PiLp.inner_apply, Fin.sum_univ_four]
  ring

/-- `e₀ = (1, 0, 0, 0)` lies in the closed forward cone. -/
theorem e0_mem_closedForwardCone :
    EuclideanSpace.single (0 : Fin 4) (1 : ℝ) ∈ closedForwardCone := by
  simp [closedForwardCone, minkowski]

/-- `e₁ = (0, 1, 0, 0)` is spacelike. -/
theorem e1_isSpacelike : IsSpacelike (EuclideanSpace.single (1 : Fin 4) (1 : ℝ)) := by
  simp [IsSpacelike, minkowski]

/-- The origin lies in the closed forward cone. -/
theorem zero_mem_closedForwardCone : (0 : Spacetime) ∈ closedForwardCone := by
  simp [closedForwardCone, minkowski]

/-- `∫ 𝓕 g = g 0` (Fourier inversion at the origin). -/
theorem integral_fourier_eq (g : SchwartzMap Spacetime ℂ) : ∫ b, (𝓕 g) b = g 0 := by
  have h : (𝓕⁻ (𝓕 g) : SchwartzMap Spacetime ℂ) 0 = g 0 := by
    rw [FourierPair.fourierInv_fourier_eq (F := SchwartzMap Spacetime ℂ) g]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp

/-- The trivial theory (`H = ℂ`, `U = 1`, `Ω = 1`, `φ = 0`) satisfies the Wightman axioms. -/
noncomputable def trivialTheory : WightmanQFT ℂ where
  U _ _ := 1
  unitary _ _ := one_mem _
  map_one := rfl
  map_mul _ _ _ _ _ _ := ContinuousLinearMap.comp_id _
  continuous _ := continuous_const
  Ω := 1
  norm_vacuum := by simp
  vacuum_invariant _ _ := rfl
  vacuum_unique ψ _ := ⟨ψ, by simp⟩
  D := ⊤
  dense_domain := by simp
  vacuum_mem := Submodule.mem_top
  domain_invariant _ _ _ _ := Submodule.mem_top
  φ := 0
  field_domain _ _ _ := Submodule.mem_top
  tempered _ _ _ _ := by simp only [LinearMap.zero_apply, inner_zero_right]; exact continuous_const
  hermitian _ _ _ _ _ _ _ := by simp
  covariant _ _ _ _ _ _ _ := by simp
  locality _ _ _ _ _ := by simp
  spectral_condition ψ χ g hg := by
    have h0 : g 0 = 0 := by
      by_contra hne
      exact Set.disjoint_left.mp hg (subset_tsupport g hne) zero_mem_closedForwardCone
    change ∫ b, ⟪χ, ψ⟫_ℂ * (𝓕 g) b = 0
    rw [integral_const_mul, integral_fourier_eq, h0, mul_zero]
  cyclic := by
    have h1 : (1 : ℂ) ∈ Submodule.span ℂ {v : ℂ | ∃ fs : List (SchwartzMap Spacetime ℂ),
        v = fs.foldr (fun f v => (0 : SchwartzMap Spacetime ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) f v) 1} :=
      Submodule.subset_span ⟨[], rfl⟩
    have htop : Submodule.span ℂ {v : ℂ | ∃ fs : List (SchwartzMap Spacetime ℂ),
        v = fs.foldr (fun f v => (0 : SchwartzMap Spacetime ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) f v) 1} = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have := Submodule.smul_mem _ x h1
      simpa using this
    rw [htop]
    simp

end QFT
