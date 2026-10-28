import Mathlib

/-!
# Navier–Stokes lane — official Clay statements (A) and (C)

Transcription of C. Fefferman, *Existence and smoothness of the Navier–Stokes
equation* (Clay Mathematics Institute official problem description), whole-space
case `n = 3`:

* **(A)** existence and smoothness for every smooth, divergence-free initial
  datum with decay (4), force `f ≡ 0`;
* **(C)** breakdown: for every `ν > 0` there are a datum satisfying (4) and a
  force satisfying (5) for which no smooth, finite-energy solution exists.

Equation numbers follow Fefferman: (1) momentum, (2) incompressibility,
(3) initial condition, (4) datum decay, (5) force decay, (6) smoothness on
`ℝ³ × [0, ∞)`, (7) bounded energy.  The periodic statements (B) and (D) are not
transcribed here.

The lane is dual: prove side `StatementA`, refute side `StatementC`.  Neither is
claimed.  `zero_datum_has_zero_solution` is a sanity check that the solution
notion is well-typed and admits the trivial solution; it says nothing about (A)
or (C).

Notes on fidelity:
* "smooth" is `C^∞`, written `smooth = ((⊤ : ℕ∞) : WithTop ℕ∞)`; in Mathlib
  v4.19 `⊤ : WithTop ℕ∞` denotes *analytic*, which would be a stronger demand;
* the energy bound (7) requires integrability explicitly, so the Bochner
  integral's junk value `0` for non-integrable functions cannot satisfy it.
-/

namespace MCore.FinalFail.Semantic.NavierStokesClay

open MeasureTheory

/-- `ℝ³` with the Euclidean norm. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- `C^∞` smoothness order (not analytic). -/
abbrev smooth : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Coordinate direction `e_j`. -/
noncomputable def e (j : Fin 3) : R3 := EuclideanSpace.single j 1

/-- The closed half-space `ℝ³ × [0, ∞)`. -/
def halfSpace : Set (R3 × ℝ) := Set.univ ×ˢ Set.Ici 0

/-- Spatial partial derivative `∂_{x_j}` of a time-dependent field at time `t`. -/
noncomputable def dx {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : R3 → ℝ → F) (j : Fin 3) (x : R3) (t : ℝ) : F :=
  fderiv ℝ (fun y => v y t) x (e j)

/-- Time derivative `∂_t`, one-sided at `t = 0`. -/
noncomputable def dt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : R3 → ℝ → F) (x : R3) (t : ℝ) : F :=
  derivWithin (fun τ => v x τ) (Set.Ici 0) t

/-- Spatial Laplacian `Δu = ∑_j ∂²u/∂x_j²`. -/
noncomputable def lap (v : R3 → ℝ → R3) (x : R3) (t : ℝ) : R3 :=
  ∑ j, dx (fun y s => dx v j y s) j x t

/-- Convective term `(u · ∇) u = ∑_j u_j ∂u/∂x_j`. -/
noncomputable def conv (u : R3 → ℝ → R3) (x : R3) (t : ℝ) : R3 :=
  ∑ j, (u x t j) • dx u j x t

/-- Pressure gradient `∇p`. -/
noncomputable def gradP (p : R3 → ℝ → ℝ) (x : R3) (t : ℝ) : R3 :=
  ∑ i, (dx p i x t) • e i

/-- Initial datum: smooth, divergence-free, with decay (4)
`|∂^α u°(x)| ≤ C_{αK} (1 + |x|)^{-K}` for every order and every `K`. -/
structure InitialDatum where
  u0 : R3 → R3
  smooth_u0 : ContDiff ℝ smooth u0
  divFree : ∀ x, ∑ i, fderiv ℝ u0 x (e i) i = 0
  decay : ∀ (k : ℕ) (K : ℝ), ∃ C : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ k u0 x‖ ≤ C * (1 + ‖x‖) ^ (-K)

/-- External force: smooth on `ℝ³ × [0, ∞)` with decay (5)
`|∂_x^α ∂_t^m f(x,t)| ≤ C_{αmK} (1 + |x| + t)^{-K}`. -/
structure Force where
  f : R3 → ℝ → R3
  smooth_f : ContDiffOn ℝ smooth (fun q : R3 × ℝ => f q.1 q.2) halfSpace
  decay : ∀ (k : ℕ) (K : ℝ), ∃ C : ℝ, ∀ x t, 0 ≤ t →
    ‖iteratedFDerivWithin ℝ k (fun q : R3 × ℝ => f q.1 q.2) halfSpace (x, t)‖ ≤
      C * (1 + ‖x‖ + t) ^ (-K)

/-- `(p, u)` solves the Navier–Stokes system on `ℝ³ × [0, ∞)` with viscosity `ν`,
force `f` and initial datum `u0`: (1), (2), (3), (6), (7). -/
structure IsSolution (ν : ℝ) (f : R3 → ℝ → R3) (u0 : R3 → R3)
    (u : R3 → ℝ → R3) (p : R3 → ℝ → ℝ) : Prop where
  smooth_u : ContDiffOn ℝ smooth (fun q : R3 × ℝ => u q.1 q.2) halfSpace
  smooth_p : ContDiffOn ℝ smooth (fun q : R3 × ℝ => p q.1 q.2) halfSpace
  momentum : ∀ x t, 0 ≤ t →
    dt u x t + conv u x t = ν • lap u x t - gradP p x t + f x t
  incompressible : ∀ x t, 0 ≤ t → ∑ i, dx u i x t i = 0
  initial : ∀ x, u x 0 = u0 x
  energy : ∃ C : ℝ, ∀ t, 0 ≤ t →
    Integrable (fun x => ‖u x t‖ ^ 2) volume ∧ ∫ x, ‖u x t‖ ^ 2 ≤ C

/-- **Clay (A)**: global existence and smoothness, `f ≡ 0`. Prove side. -/
def StatementA : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ d : InitialDatum,
    ∃ (u : R3 → ℝ → R3) (p : R3 → ℝ → ℝ), IsSolution ν (fun _ _ => 0) d.u0 u p

/-- **Clay (C)**: breakdown on `ℝ³`. Refute side. -/
def StatementC : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ (d : InitialDatum) (F : Force),
    ¬ ∃ (u : R3 → ℝ → R3) (p : R3 → ℝ → ℝ), IsSolution ν F.f d.u0 u p

/-- The zero datum satisfies (4) and incompressibility. -/
noncomputable def zeroDatum : InitialDatum where
  u0 := fun _ => 0
  smooth_u0 := contDiff_const
  divFree := by intro x; simp
  decay := by
    intro k K
    refine ⟨0, fun x => ?_⟩
    simp [iteratedFDeriv_zero_fun]

/-- Sanity check: for every `ν`, the trivial pair `(p, u) = (0, 0)` solves the
system for the zero datum and zero force. -/
theorem zero_datum_has_zero_solution (ν : ℝ) :
    IsSolution ν (fun _ _ => 0) zeroDatum.u0 (fun _ _ => 0) (fun _ _ => 0) where
  smooth_u := contDiffOn_const
  smooth_p := contDiffOn_const
  momentum := by
    intro x t _
    simp [dt, conv, lap, gradP, dx]
  incompressible := by
    intro x t _
    simp [dx]
  initial := by
    intro x
    rfl
  energy := by
    refine ⟨0, fun t _ => ⟨?_, ?_⟩⟩
    · simp
    · simp

#print axioms MCore.FinalFail.Semantic.NavierStokesClay.zero_datum_has_zero_solution

end MCore.FinalFail.Semantic.NavierStokesClay
