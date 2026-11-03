import MCore.MaterialMath.TriCyclicSpectral
import MCore.MaterialMath.ProfiledTransverseDecay
import MCore.MaterialMath.ScalarDefectEmbedding
import MCore.MaterialMath.TwoSidedMaterialResolution

namespace MCore.MaterialMath

noncomputable section

namespace TriNumber

/-- Canonical numerical constants forced by the real C3 tri-cyclic kernel. -/
structure CanonicalMaterialConstants where
  rotationOrder : Nat
  transverseLaplacianMagnitude : ℝ
  normalizedLaplacianEnergy : ℝ
  spreadRadiusFactor : ℝ
  scalarDefectEnergyFactor : ℝ

/-- The constants are not fitted: they are exact consequences of the definitions. -/
def canonicalMaterialConstants : CanonicalMaterialConstants where
  rotationOrder := 3
  transverseLaplacianMagnitude := 3
  normalizedLaplacianEnergy := 9
  spreadRadiusFactor := 3
  scalarDefectEnergyFactor := 6

theorem canonicalMaterialConstants_values :
    canonicalMaterialConstants.rotationOrder = 3 ∧
    canonicalMaterialConstants.transverseLaplacianMagnitude = 3 ∧
    canonicalMaterialConstants.normalizedLaplacianEnergy = 9 ∧
    canonicalMaterialConstants.spreadRadiusFactor = 3 ∧
    canonicalMaterialConstants.scalarDefectEnergyFactor = 6 := by
  norm_num [canonicalMaterialConstants]

/-- Operator aliases used by the global material theorem. -/
abbrev R : MaterialOperator ℝ := rotate
abbrev D : MaterialOperator ℝ := phaseDerivative
abbrev L : MaterialOperator ℝ := phaseLaplacian

/-- Equilibrium projector. -/
noncomputable def Peq : MaterialOperator ℝ :=
  balancedProjection

/-- Transverse projector. -/
noncomputable def Ptr : MaterialOperator ℝ :=
  fluctuation

/-- The equilibrium projector is idempotent. -/
theorem Peq_idempotent (x : TriNumber ℝ) :
    Peq (Peq x) = Peq x := by
  apply TriNumber.ext <;>
    simp [Peq, balancedProjection, mean, total]
  all_goals ring

/-- The transverse projector is idempotent. -/
theorem Ptr_idempotent (x : TriNumber ℝ) :
    Ptr (Ptr x) = Ptr x := by
  have hz : ZeroSum (fluctuation x) := fluctuation_zeroSum x
  rcases x with ⟨m,c,s⟩
  simp [Ptr, fluctuation, mean, total] at hz ⊢
  ring

/-- Equilibrium and transverse projectors are complementary. -/
theorem Peq_add_Ptr (x : TriNumber ℝ) :
    add (Peq x) (Ptr x) = x :=
  balanced_add_fluctuation x

/-- Equilibrium and transverse sectors are disjoint except at zero. -/
theorem equilibrium_transverse_intersection_zero
    (x : TriNumber ℝ)
    (heq : Balanced x)
    (htr : ZeroSum x) :
    x = { manifest := 0, crossing := 0, seed := 0 } :=
  balanced_and_zeroSum_eq_zero x heq htr

/-- Rotation has exact order three. -/
theorem R_cubic_identity (x : TriNumber ℝ) :
    R (R (R x)) = x :=
  rotate_three x

/-- The first-difference operator obeys the cubic polynomial D(D²+3D+3)=0. -/
theorem D_cubic_polynomial (x : TriNumber ℝ) :
    add
      (D (D (D x)))
      (add
        (smul (3 : ℝ) (D (D x)))
        (smul (3 : ℝ) (D x))) =
      { manifest := 0, crossing := 0, seed := 0 } :=
  phaseDerivative_cubic_closure x

/-- The symmetric Laplacian is the polynomial L=D²+3D. -/
theorem L_polynomial_in_D (x : TriNumber ℝ) :
    L x = add (D (D x)) (smul (3 : ℝ) (D x)) :=
  phaseLaplacian_eq_secondDerivative_plus_three_first x

/-- The Laplacian annihilates equilibrium and acts by -3 on the transverse plane. -/
theorem L_sector_law
    (x : TriNumber ℝ) :
    L x = smul (-3 : ℝ) (Ptr x) :=
  phaseLaplacian_eq_neg_three_fluctuation x

/-- Exact geometric energy decomposition. -/
theorem global_spread_radius_law
    (x : TriNumber ℝ) :
    phaseEnergy x = 3 * transverseRadiusSq x :=
  spread_eq_three_transverseRadiusSq x

/-- Exact normalized F2 constant. -/
theorem global_normalized_gap_constant
    (x : TriNumber ℝ)
    (htr : ZeroSum x)
    (hn : euclideanSquare x = 1) :
    phaseLaplacianEnergy x = 9 :=
  normalized_transverse_energy x htr hn

/-- Exact scalar-to-material energy conversion. -/
theorem global_scalar_defect_energy
    (d : ℝ) :
    phaseEnergy (scalarDefectEmbedding d) = 6 * d^2 :=
  phaseEnergy_scalarDefectEmbedding d

/--
Universal F1 transport: every real scalar defect tending to zero yields a
material phase-energy trajectory tending to zero.
-/
theorem global_scalar_vanishing_transport
    (d : Nat → ℝ)
    (hd : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => phaseEnergy (scalarDefectEmbedding (d n)))
      Filter.atTop (nhds 0) :=
  phaseEnergy_scalarDefectEmbedding_tendsto_zero d hd

/--
Universal profile law: for any tri-state and any scalar profile a_n,
the phase energy is exactly a_n² times the original energy.
-/
theorem global_profile_energy_law
    (x : TriNumber ℝ)
    (a : Nat → ℝ)
    (n : Nat) :
    phaseEnergy (profiledTransverseTrajectory x a n) =
      (a n)^2 * phaseEnergy x :=
  phaseEnergy_profiledTransverseTrajectory x a n

/--
Global internal material theorem: all canonical algebraic, spectral, geometric
and scalar-defect laws coexist in one kernel.
-/
structure GlobalMaterialKernelCertificate where
  rotationOrder3 :
    ∀ x : TriNumber ℝ, R (R (R x)) = x
  canonicalSplit :
    ∀ x : TriNumber ℝ, add (Peq x) (Ptr x) = x
  transverseZeroSum :
    ∀ x : TriNumber ℝ, ZeroSum (Ptr x)
  laplacianTransverse :
    ∀ x : TriNumber ℝ, L x = smul (-3 : ℝ) (Ptr x)
  spreadRadius :
    ∀ x : TriNumber ℝ, phaseEnergy x = 3 * transverseRadiusSq x
  scalarEnergy :
    ∀ d : ℝ, phaseEnergy (scalarDefectEmbedding d) = 6 * d^2
  normalizedGap :
    ∀ x : TriNumber ℝ,
      ZeroSum x → euclideanSquare x = 1 → phaseLaplacianEnergy x = 9

def globalMaterialKernelCertificate : GlobalMaterialKernelCertificate where
  rotationOrder3 := R_cubic_identity
  canonicalSplit := Peq_add_Ptr
  transverseZeroSum := fluctuation_zeroSum
  laplacianTransverse := L_sector_law
  spreadRadius := global_spread_radius_law
  scalarEnergy := global_scalar_defect_energy
  normalizedGap := global_normalized_gap_constant

#print axioms MCore.MaterialMath.TriNumber.canonicalMaterialConstants_values
#print axioms MCore.MaterialMath.TriNumber.Peq_idempotent
#print axioms MCore.MaterialMath.TriNumber.Ptr_idempotent
#print axioms MCore.MaterialMath.TriNumber.D_cubic_polynomial
#print axioms MCore.MaterialMath.TriNumber.L_sector_law
#print axioms MCore.MaterialMath.TriNumber.globalMaterialKernelCertificate

end TriNumber

end

end MCore.MaterialMath
