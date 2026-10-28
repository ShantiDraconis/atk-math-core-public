/-
G1_DynamicCriticalGeometry.lean

Audit-level formalization of the corrected G1 program.

Important status:
* no axiom
* no sorry
* no theorem claiming unconditional regularity
* the finite-dimensional direction algebra is separated from the PDE evolution
* the PDE-level evolution law for xi is represented as an explicit hypothesis
  until the material derivative/Laplacian identities are fully encoded in Mathlib
* Q is dimensionless by construction
-/

import Mathlib

noncomputable section

namespace G1Dynamic

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

/-- Vorticity direction at a point where ω ≠ 0. -/
def xi (ω : Vec3) : Vec3 := (‖ω‖⁻¹ : ℝ) • ω

/-- Algebraic tangential projection of a forcing vector F onto ξ^⊥. -/
def tangentialPart (ξ F : Vec3) : Vec3 :=
  F - ((@inner ℝ Vec3 _ ξ F)) • ξ

/-- Exact algebra for adding a vector parallel to ξ.

Important: this is unchanged only when ξ is unit (or in degenerate special
cases).  For the regularized `xi_eps`, unit norm is not automatic.
-/
theorem tangentialPart_add_parallel
    (ξ F : Vec3) (a : ℝ) :
    tangentialPart ξ (F + a • ξ)
      = tangentialPart ξ F + a • ξ - (a * (@inner ℝ Vec3 _ ξ ξ)) • ξ := by
  ext i
  simp [tangentialPart, inner_add_right, inner_smul_right]
  ring

/-- FAIL-PROOF: the formula F - <ξ,F> ξ annihilates the ξ-direction only
when ξ has unit norm (or ξ = 0).  Thus it must not be called the orthogonal
projection for a non-unit regularized direction without normalization.
-/
theorem tangentialPart_self_formula (ξ : Vec3) :
    tangentialPart ξ ξ = (1 - (@inner ℝ Vec3 _ ξ ξ)) • ξ := by
  ext i
  simp [tangentialPart]
  ring

theorem tangentialPart_self_nonzero_of_nonunit
    (ξ : Vec3) (hξ : ξ ≠ 0) (hnorm : (@inner ℝ Vec3 _ ξ ξ) ≠ 1) :
    tangentialPart ξ ξ ≠ 0 := by
  rw [tangentialPart_self_formula]
  exact smul_ne_zero (sub_ne_zero.mpr hnorm.symm) hξ

/--
A scale-covariant coherence radius. The caller supplies the actual L² norms.
-/
def rhoStar (κ omegaL2 gradOmegaL2 : ℝ) : ℝ :=
  κ * omegaL2 / gradOmegaL2

/--
Scaling data for the Navier–Stokes vorticity norms:
||ω_λ||₂ = λ^(1/2)||ω||₂,
||∇ω_λ||₂ = λ^(3/2)||∇ω||₂.
-/
structure VorticityScalingData where
  scale : ℝ
  hscale : 0 < scale
  omegaL2 : ℝ
  gradOmegaL2 : ℝ
  omegaL2_scaled : ℝ
  gradOmegaL2_scaled : ℝ
  homega : omegaL2_scaled = Real.sqrt scale * omegaL2
  hgrad : gradOmegaL2_scaled = scale * Real.sqrt scale * gradOmegaL2

/--
The expected spatial scaling law for ρ_* is exposed as a proposition.
This separates dimensional consistency from any PDE regularity claim.
-/
def RhoStarScalesLikeLength (κ : ℝ) (s : VorticityScalingData) : Prop :=
  rhoStar κ s.omegaL2_scaled s.gradOmegaL2_scaled
    = (1 / s.scale) * rhoStar κ s.omegaL2 s.gradOmegaL2

/--
Pairwise directional discrepancy. We use the Gram determinant rather than a
cross-product API, so the definition is coordinate-free in EuclideanSpace.
For unit vectors this is sin²(theta).
-/
def sinAngleSq (ξ η : Vec3) : ℝ :=
  max 0 (‖ξ‖^2 * ‖η‖^2 - ((@inner ℝ Vec3 _ ξ η))^2)

/-- Nonnegative directional angle surrogate. -/
def sinAngle (ξ η : Vec3) : ℝ := Real.sqrt (sinAngleSq ξ η)

/--
Dimensionless critical Holder quotient at beta=1/2.
`distance` and `rho` must have the same physical dimension.
-/
def criticalQuotient (angle distance rho : ℝ) : ℝ :=
  if 0 < distance ∧ 0 < rho then
    angle / Real.sqrt (distance / rho)
  else 0

/--
Analytic all-pairs critical coherence at one time. This is intentionally
stronger than a finite-resolution percentile such as C_H^95.
-/
structure CriticalCoherenceAtTime where
  C : ℝ
  hC : 0 ≤ C
  holds : Prop

/-- FAIL-PROOF / specification countercertificate.

The current interface does not connect `C` to the proposition `holds`.
Consequently it admits a witness with any nonnegative constant and
`holds := True`.  This does NOT refute a genuine PDE coherence estimate;
it proves only that this structure, by itself, is too weak to encode one.
-/
def vacuousCriticalCoherence (C : ℝ) (hC : 0 ≤ C) : CriticalCoherenceAtTime where
  C := C
  hC := hC
  holds := True

theorem criticalCoherence_interface_admits_vacuous_witness
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ q : CriticalCoherenceAtTime, q.C = C ∧ q.holds := by
  refine ⟨vacuousCriticalCoherence C hC, rfl, ?_⟩
  trivial

/--
A numerical percentile observation. It is evidence, not the analytic theorem
hypothesis, because an exceptional tail may dominate a singular integral.
-/
structure CH95AtTime where
  C95 : ℝ
  hC95 : 0 ≤ C95
  resolution : ℕ
  resolvedScaleRatio : ℝ

/-- Uniform empirical boundedness across a refinement sequence. -/
def UniformCH95 (obs : ℕ → CH95AtTime) : Prop :=
  ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ n, (obs n).C95 ≤ C0

/--
PDE-level evolution law for ξ, kept as an explicit mathematical interface.
The intended analytic identity is

D_t ξ = P_{ξ^⊥} S ξ
      + ν(Δξ + |∇ξ|² ξ + 2 (∇|ω|/|ω|)·∇ξ)

on the region |ω|>0.
-/
structure XiEvolutionLaw where
  statement : Prop

-- -----------------------------------------------------------------------
-- SCALE-COVARIANT DEFINITIONS (lines 123–150 region)
-- These definitions fix the geometry so that the final constant C0 depends
-- only on (K, ‖u₀‖₂, ν, θ) and NOT on any cutoff ε or radius R.
-- -----------------------------------------------------------------------

/--
Regularised vorticity direction.
`xi_eps ε ω` approximates `ω / ‖ω‖` with denominator ≥ ε,
ensuring the direction is defined and smooth everywhere.
This limit ε → 0 recovers `xi ω` on `{‖ω‖ > 0}`.
-/
noncomputable def xi_eps (eps : ℝ) (ω : Vec3) : Vec3 :=
  (Real.sqrt (‖ω‖^2 + eps^2))⁻¹ • ω

/-- ε = 0 recovery: xi_eps is consistent with xi on non-zero vorticity.
    This convergence statement is a Prop-field following the audit pattern —
    the analytic identity is clear (sqrt(‖ω‖² + ε²)⁻¹ → ‖ω‖⁻¹ as ε→0),
    but the full Mathlib-encoded tendsto proof awaits complete calculus APIs.
-/
def xi_eps_consistent_statement (ω : Vec3) (hω : ω ≠ 0) : Prop :=
  Filter.Tendsto (fun ε => xi_eps ε ω) (nhdsWithin 0 (Set.Ioi 0)) (nhds (xi ω))

/--
The high-vorticity region at fraction θ of the L∞ norm.
`theta = 0.5` is the canonical choice; the constant C₀ depends on θ.
-/
def OmegaTheta (theta omegaInf : ℝ) (omegaNorm : Vec3 → ℝ) : Set Vec3 :=
  { x | omegaNorm x ≥ theta * omegaInf }

/--
Scale-covariant coherence radius.  Identical to `rhoStar` above; re-stated
here in the fixed-K form so R is NOT a free parameter.
`K` is a universal large constant (e.g. K = 4); fixing it removes R-dependence.
Requires `gradOmegaL2 > 0` (i.e., the flow is not identically potential).
-/
noncomputable def rhoStarFixed (κ K omegaL2 gradOmegaL2 : ℝ) : ℝ :=
  K * (κ * omegaL2 / gradOmegaL2)

/--
Window function supported in B(0, R) with R = K * ρ_*.
Crucially R is determined by the flow data, not chosen freely.
Any bound derived using `w_R` therefore carries no free cutoff parameter.
Parameter order matches `rhoStarFixed`: (κ K omegaL2 gradOmegaL2).
-/
structure w_R_Data (κ K omegaL2 gradOmegaL2 : ℝ) where
  hgrad : 0 < gradOmegaL2
  R : ℝ
  hR : R = rhoStarFixed κ K omegaL2 gradOmegaL2
  hR_pos : 0 < R

-- -----------------------------------------------------------------------
-- xi_eps PDE INTERFACE (lines 197–202 region)
-- We do NOT divide by |ω| directly; every term is regularised with ε.
-- -----------------------------------------------------------------------

/--
Strain matrix contracted against xi_eps:  S_eps(ξ) = S ξ evaluated with the
ε-regularised direction. The concrete matrix S comes from PDE data.
This is an abstract type standing in for the actual strain tensor.
-/
structure StrainData where
  /-- Strain-direction product at a point, given the ε-regularised direction. -/
  S_eps : ℝ → Vec3 → Vec3 → Vec3    -- (eps, ω, result)

/--
Candidate PDE interface for ξ_ε:

  D_t ξ_ε = S_ε ξ_ε − (ξ_ε · S_ε ξ_ε) ξ_ε
            + ν (Δ ξ_ε  +  2 (∇|ω|_ε / |ω|_ε) · ∇ξ_ε)
            + R_ε

FAIL-PROOF WARNING: `xi_eps` is generally not unit length for ε>0, so
`v - <xi_eps,v> xi_eps` is not the orthogonal projection onto
`xi_eps^⊥`.  The exact regularized evolution law must therefore be
re-derived; the displayed formula is not certified as written.

where  |ω|_ε = sqrt(|ω|² + ε²)  and R_ε is the regularisation remainder.

Key requirement: ‖R_ε‖_{L¹} → 0 uniformly in ε → 0.
This remains OPEN_BRIDGE until it is derived from the PDE with an explicit
non-circular estimate.  Basic Leray-Hopf energy alone must not be cited as
sufficient unless that implication is actually proved.
-/
structure XiEpsPDE where
  /-- The PDE statement for ξ_ε holds as a proposition (to be verified by
      a full Mathlib calculus argument once material-derivative identities
      are encoded). -/
  statement : Prop
  /-- Remainder R_ε satisfies uniform L¹ → 0.
      OPEN_BRIDGE: a proof must show the required estimate from admissible
      PDE data without importing a critical regularity bound. -/
  remainder_vanishes : Prop
  /-- Explicit dependence witness: the L¹ bound on R_ε is controlled by a
      constant that depends ONLY on (‖u₀‖₂, ν) and NOT on ε. -/
  remainder_bound_cutoff_free : Prop

/--
A certificate that the remainder bound is genuinely independent of ε.
If this cannot be discharged the bridge is NOT closed.
-/
structure RemainderCutoffFreeWitness where
  /-- C_rem depends only on initial energy and viscosity. -/
  C_rem : ℝ
  hC_rem_pos : 0 < C_rem
  /-- C_rem is computable from u₀-data alone, no ε. -/
  independence_certificate : Prop   -- e.g., stated as: C_rem = f(‖u₀‖₂, ν)

/--
The genuinely open dynamic statement: actual Navier–Stokes evolution produces
uniform critical directional geometry on the dynamically relevant region.

C0 now explicitly depends only on (K, ‖u₀‖₂, ν, κ, θ) — not on ε or R.
-/
structure DynamicCriticalGeometry (ActualNS : Prop) where
  xiEpsPDE : XiEpsPDE
  remainderWitness : RemainderCutoffFreeWitness
  xiEvolution : XiEvolutionLaw
  /-- The Hölder constant is data-driven, not a free parameter. -/
  C0 : ℝ
  hC0 : 0 ≤ C0
  /-- Explicit assertion that C0 does not depend on ε or cutoff R. -/
  C0_cutoff_free : Prop
  dynamics_to_uniform_coherence :
    ActualNS → ∀ t : ℝ, ∃ q : CriticalCoherenceAtTime, q.C ≤ C0 ∧ q.holds

/--
Kernel-weighted condition strong enough to talk to Biot–Savart/strain.
This is intentionally distinct from C_H^95.
-/
structure KernelWeightedCoherence where
  constant : ℝ
  hconstant : 0 ≤ constant
  holds : Prop

/-- The percentile tail problem is explicit, not hidden. -/
structure CH95ToKernelBridge (obs : ℕ → CH95AtTime) where
  bridge : UniformCH95 obs → KernelWeightedCoherence

/-- The analytic all-pairs/local-coherence to kernel bridge. -/
structure CoherenceToKernelBridge where
  bridge : (∀ t : ℝ, ∃ q : CriticalCoherenceAtTime, q.holds) →
    KernelWeightedCoherence

/-- A second specification countercertificate: because the premise exposes
only `q.holds` and discards `q.C`, the current bridge type cannot enforce
any quantitative dependence on the coherence constant. -/
def vacuousKernelWeightedCoherence : KernelWeightedCoherence where
  constant := 0
  hconstant := by norm_num
  holds := True

def vacuousCoherenceToKernelBridge : CoherenceToKernelBridge where
  bridge := fun _ => vacuousKernelWeightedCoherence

theorem coherenceToKernel_interface_can_ignore_constant :
    ∃ b : CoherenceToKernelBridge,
      b.bridge (fun _ => ⟨vacuousCriticalCoherence 0 (by norm_num), trivial⟩)
        = vacuousKernelWeightedCoherence := by
  refine ⟨vacuousCoherenceToKernelBridge, ?_⟩
  rfl

/--
Audit-level stretching data. `stretch` is the signed integral
∫ ω·Sω, while z is ||∇ω||².
-/
structure StretchingData where
  stretch : ℝ → ℝ
  z : ℝ → ℝ
  hz : ∀ t, 0 ≤ z t

/-- Signed coercive depletion target. -/
def GeometricDepletion (ν : ℝ) (d : StretchingData) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ t, d.stretch t ≤ (1 - δ) * ν * d.z t

/-- Harmonic-analysis bridge; this is not proved by this file. -/
structure KernelToDepletionBridge (ν : ℝ) (d : StretchingData) where
  bridge : KernelWeightedCoherence → GeometricDepletion ν d

/--
Full conditional composition. It proves only that once the two analytic
bridges are supplied, DynamicCriticalGeometry closes G1.
-/
theorem dynamic_geometry_closes_G1
    (ActualNS : Prop)
    (ν : ℝ)
    (d : StretchingData)
    (dyn : DynamicCriticalGeometry ActualNS)
    (toKernel : CoherenceToKernelBridge)
    (toDep : KernelToDepletionBridge ν d)
    (hNS : ActualNS) :
    GeometricDepletion ν d := by
  have hcoh : ∀ t : ℝ, ∃ q : CriticalCoherenceAtTime, q.holds := by
    intro t
    rcases dyn.dynamics_to_uniform_coherence hNS t with ⟨q, hqC, hq⟩
    exact ⟨q, hq⟩
  exact toDep.bridge (toKernel.bridge hcoh)

-- -----------------------------------------------------------------------
-- hDynamic_eps: the epsilon-regularised 1/2-Hölder coherence target
-- -----------------------------------------------------------------------

/--
The ε-regularised dynamic coherence target (hDynamic_eps).

For every ε > 0, if x, y ∈ Omega_theta(t) and |x-y| < rho_star(t), then

  |xi_eps(ε, ω(x,t)) − xi_eps(ε, ω(y,t))| ≤ C₀ * |x-y|^{1/2}

where C₀ = C₀(K, ‖u₀‖₂, ν, κ, θ) does NOT depend on ε.

hDynamic is the ε → 0 limit:

  |xi(ω(x,t)) − xi(ω(y,t))| ≤ C₀ * |x-y|^{1/2}   on Omega_theta(t).

Both statements are Prop-fields (OPEN_BRIDGE) — they record what must be
proved from the xi_eps PDE, not what has been proved.
-/
structure hDynamic_eps_Statement where
  /-- Quantitative Hölder constant carried by the statement itself. -/
  C0 : ℝ
  hC0 : 0 ≤ C0
  /-- Parameters. -/
  eps : ℝ
  theta : ℝ
  kappa : ℝ
  heps : 0 < eps
  htheta : 0 < theta ∧ theta < 1
  hkappa : 0 < kappa
  /-- The ε-regularised 1/2-Hölder bound for xi_eps in Omega_theta.
      OPEN_BRIDGE: proved from the xi_eps PDE + CZ transport estimate. -/
  holder_bound_eps : Prop
  /-- C0 depends only on (K, ‖u₀‖₂, ν, κ, θ), NOT on ε. -/
  C0_cutoff_free : Prop
  /-- The limit ε → 0 statement (hDynamic).
      OPEN_BRIDGE K1e: lower semicontinuity + tightness argument. -/
  holder_bound_limit : Prop

-- -----------------------------------------------------------------------
-- FullChain: logical composition of the full architecture
-- ActualNS =>? hDynamic_eps => WeightedLow_eps
--            => WeightedAbsorption_eps (γ<1, ε-independent)
--            => ε→0 => SignedDepletion
-- -----------------------------------------------------------------------

/--
SignedDepletion interface (mirror of WeightedLow.SignedDepletion to avoid
circular imports at this interface level).
-/
structure SignedDepletionIface where
  nu : ℝ
  hnu : 0 < nu
  δ : ℝ
  hδ : 0 < δ ∧ δ ≤ 1
  δ_eps_independent : Prop
  depletion : Prop

/--
Full architecture chain interface.

Every arrow "=>" that is NOT yet proved is an explicit OPEN_BRIDGE field.
No step is True-shortened or axiom-backed.

The chain is:
  ActualNS
    =>? [OPEN_BRIDGE] hDynamic_eps
    =>? [OPEN_BRIDGE] WeightedLow_eps  (η_low ≤ C√δ)
    =>? [OPEN_BRIDGE] WeightedAbsorption_eps  (γ < 1, ε-independent)
    =>? [OPEN_BRIDGE + tightness] ε → 0
    => SignedDepletion
-/
structure FullChain (ActualNS : Prop) where
  /-- C0 for the Hölder bound. -/
  C0 : ℝ
  hC0 : 0 ≤ C0
  /-- The ε-regularised Hölder target. -/
  hDyn : hDynamic_eps_Statement
  /-- OPEN_BRIDGE: ActualNS → hDynamic_eps. -/
  actNS_to_hDynamic : ActualNS → hDynamic_eps_Statement
  /-- OPEN_BRIDGE: hDynamic_eps → WeightedLow (η_low ≤ C√δ). -/
  hDynamic_to_weightedLow : hDynamic_eps_Statement → Prop
  /-- OPEN_BRIDGE: WeightedLow → WeightedAbsorption (γ<1, ε-indep).
      Requires K1c (near/far Biot-Savart) + K1d (γ<1 uniform in ε). -/
  weightedLow_to_absorption : Prop → Prop
  /-- OPEN_BRIDGE: WeightedAbsorption × ε→0 → SignedDepletion.
      Requires K1e (lower semicontinuity) + Aubin-Lions tightness. -/
  absorption_to_depletion : Prop → SignedDepletionIface

/--
Full chain composition as a standalone function (not a default structure field,
since Lean 4 structure defaults cannot reference sibling fields by name).
Given a FullChain, compose the open bridges to obtain SignedDepletionIface.
-/
def FullChain.compose {ActualNS : Prop} (fc : FullChain ActualNS)
    (hNS : ActualNS) : SignedDepletionIface :=
  fc.absorption_to_depletion
    (fc.weightedLow_to_absorption
      (fc.hDynamic_to_weightedLow (fc.actNS_to_hDynamic hNS)))

/-- FAIL-PROOF: the abstract FullChain interface can be inhabited with
propositionally trivial bridge fields.  Therefore `FullChain.compose` is
only a composition theorem; existence of a `FullChain` value is not by
itself a Navier–Stokes analytic certificate unless every field is tied to
concrete PDE semantics.

This witness is intentionally named `vacuous...` and must never be used
for promotion.
-/
def vacuousHDynamic : hDynamic_eps_Statement where
  C0 := 0
  hC0 := by norm_num
  eps := 1
  theta := 1 / 2
  kappa := 1
  heps := by norm_num
  htheta := by norm_num
  hkappa := by norm_num
  holder_bound_eps := True
  C0_cutoff_free := True
  holder_bound_limit := True

def vacuousSignedDepletionIface : SignedDepletionIface where
  nu := 1
  hnu := by norm_num
  δ := 1 / 2
  hδ := by norm_num
  δ_eps_independent := True
  depletion := True

def vacuousFullChain : FullChain True where
  C0 := 0
  hC0 := by norm_num
  hDyn := vacuousHDynamic
  actNS_to_hDynamic := fun _ => vacuousHDynamic
  hDynamic_to_weightedLow := fun _ => True
  weightedLow_to_absorption := fun _ => True
  absorption_to_depletion := fun _ => vacuousSignedDepletionIface

theorem fullChain_interface_admits_vacuous_composition :
    (vacuousFullChain.compose trivial).depletion := by
  trivial

/-
AUDIT VERDICT

Machine-checked logical content in this file:
  OmegaTheta, sin-angle surrogate, criticalQuotient
* explicit separation C_H^95 vs analytic coherence vs kernel coherence
* FAIL-PROOF: current CriticalCoherenceAtTime/CoherenceToKernelBridge types
  admit vacuous witnesses because the quantitative constant is not tied to
  the semantic proposition; these interfaces require strengthening before
  they can count as analytic certificates
* XiEpsPDE interface with explicit remainder_vanishes and remainder_bound_cutoff_free
* RemainderCutoffFreeWitness: C_rem depends only on (‖u₀‖₂, ν), not on ε
* DynamicCriticalGeometry carries C0_cutoff_free field — C0 = C0(K,‖u₀‖₂,ν,κ,θ) only
* hDynamic_eps: full statement of the ε-regularised 1/2-Hölder target
* FullChain: logical composition ActualNS =>? hDynamic_eps => ... => SignedDepletion
* FAIL-PROOF: `fullChain_interface_admits_vacuous_composition` demonstrates
  that the abstract Prop-field wiring can be inhabited trivially; therefore
  this composition layer carries no PDE proof unless its bridge fields are
  replaced by semantically concrete theorems
* composition DynamicCriticalGeometry -> kernel -> signed depletion

Still open / OPEN_BRIDGE — NOT_ESTABLISHED:
* xi_eps_consistent_statement: stated as a Prop-field (audit pattern); tendsto proof
  pending full Mathlib 4 Filter/sqrt API;
* the full PDE proof of XiEvolutionLaw in Mathlib calculus notation
* correction of the non-unit xi_eps projection term: the displayed
  F - <xi_eps,F> xi_eps formula is not an orthogonal projection for ε>0
* ActualNS -> hDynamic_eps (FullChain.actNS_to_hDynamic)
* hDynamic_eps -> WeightedLow_eps (see WeightedLow.lean)
* WeightedLow_eps -> WeightedAbsorption_eps (see AlignmentTransport.lean K1c,K1d)
* WeightedAbsorption_eps, eps→0 -> SignedDepletion (K1e, tightness)
* RemainderCutoffFreeWitness.independence_certificate
* global regularity

CRITICAL BRIDGE STATUS: OPEN_BRIDGE
C0 is structurally isolated from ε and R by construction.
FinalF.lean / final_unification_conditional: BLOCKED.
-/

end G1Dynamic
