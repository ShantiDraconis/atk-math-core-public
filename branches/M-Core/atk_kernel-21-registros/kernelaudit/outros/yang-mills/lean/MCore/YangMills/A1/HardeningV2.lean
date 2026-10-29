import Mathlib
import MCore.YangMills.A1.Hardening

namespace MCore.YangMills.A1

open MeasureTheory

/-!
A1 B3/B4/B5 hardening v2.

This module does not claim a Yang--Mills construction.  It replaces the
previous phantom/trivially-inhabited interfaces by types whose laws refer
directly to the regulated fibers, measure, observables and action data of the
same construction C.

The physical construction still has to be supplied.  No theorem below creates
it from the legacy Props.
-/

/-- Extra concrete data missing from the legacy `RegulatedYM4Construction`.
The base construction stores the *type* of actions but no actual action/kernel;
this layer supplies those data without changing frozen K21--K30. -/
structure A1PhysicalData (C : RegulatedYM4Construction) where
  cutoffValue : C.Signature.Regulator → ℝ
  volumeValue : C.Signature.Volume → ℝ
  observableToReal : C.ObservableValue → ℝ
  reflection :
    ∀ (a : C.Signature.Regulator) (L : C.Signature.Volume),
      (C.fiber a L).State → (C.fiber a L).State
  regulatedAction :
    ∀ (_a : C.Signature.Regulator) (_L : C.Signature.Volume),
      C.Signature.Action
  kernelFromAction :
    ∀ (a : C.Signature.Regulator) (L : C.Signature.Volume),
      C.Signature.Action →
      (C.fiber a L).State → (C.fiber a L).State → ℂ
  cutoffCofinal :
    ∀ ε : ℝ, 0 < ε →
      ∃ (a : C.Signature.Regulator) (L : C.Signature.Volume),
        C.admissible a L ∧
        0 < cutoffValue a ∧ cutoffValue a < ε
  volumeCofinal :
    ∀ R : ℝ,
      ∃ (a : C.Signature.Regulator) (L : C.Signature.Volume),
        C.admissible a L ∧ R < volumeValue L
  observableNontrivial :
    ∃ (a : C.Signature.Regulator) (L : C.Signature.Volume)
      (O : C.Signature.Observable) (x : (C.fiber a L).State),
      observableToReal (C.observable a L O x) ≠ 0

/-- The transfer kernel used by B4 is definitionally the kernel built from the
actual regulated action selected by the same physical-data package. -/
def A1PhysicalData.transferKernel
    {C : RegulatedYM4Construction} (P : A1PhysicalData C)
    (a : C.Signature.Regulator) (L : C.Signature.Volume) :
    (C.fiber a L).State → (C.fiber a L).State → ℂ :=
  P.kernelFromAction a L (P.regulatedAction a L)

/-- B3 v2: pairing is not free data.  It is required to equal the reflected
observable pairing integrated against the exact regulated measure of C. -/
structure ReflectionPositivityDataV2
    (C : RegulatedYM4Construction) (P : A1PhysicalData C) where
  pairing :
    ∀ a L,
      C.Signature.Observable → C.Signature.Observable → ℝ
  h_pairing_def :
    ∀ a L (f g : C.Signature.Observable),
      pairing a L f g =
        ∫ x,
          P.observableToReal
              (C.observable a L f (P.reflection a L x)) *
            P.observableToReal
              (C.observable a L g x)
          ∂(C.fiber a L).measure
  h_reflection_pos :
    ∀ a L (f : C.Signature.Observable),
      0 ≤ pairing a L f f

/-- A measure-bound pre-L2 vector.  We deliberately avoid pretending that the
quotient Hilbert L2 construction has already been formalized; square
integrability is nevertheless tied to the exact measure of C. -/
structure RegulatedL2Vector
    (C : RegulatedYM4Construction)
    (a : C.Signature.Regulator) (L : C.Signature.Volume) where
  toFun : (C.fiber a L).State → ℂ
  squareIntegrable :
    Integrable (fun x => ‖toFun x‖ ^ 2) (C.fiber a L).measure

noncomputable def regulatedNormSq
    {C : RegulatedYM4Construction}
    {a : C.Signature.Regulator} {L : C.Signature.Volume}
    (ψ : RegulatedL2Vector C a L) : ℝ :=
  ∫ x, ‖ψ.toFun x‖ ^ 2 ∂(C.fiber a L).measure

noncomputable def regulatedInner
    {C : RegulatedYM4Construction}
    {a : C.Signature.Regulator} {L : C.Signature.Volume}
    (ψ φ : RegulatedL2Vector C a L) : ℂ :=
  ∫ x, star (ψ.toFun x) * φ.toFun x ∂(C.fiber a L).measure

/-- B4 v2: the transfer operator acts on the same measure-bound state space,
and its pointwise action is required to equal the integral operator built from
P.transferKernel and C's exact regulated measure. -/
structure PositiveTransferDataV2
    (C : RegulatedYM4Construction) (P : A1PhysicalData C) where
  observableState :
    ∀ a L, C.Signature.Observable → RegulatedL2Vector C a L
  h_observable_state :
    ∀ a L (O : C.Signature.Observable) (x : (C.fiber a L).State),
      (observableState a L O).toFun x =
        Complex.ofReal (P.observableToReal (C.observable a L O x))
  transferOp :
    ∀ a L, RegulatedL2Vector C a L → RegulatedL2Vector C a L
  h_transfer_from_C :
    ∀ a L (ψ : RegulatedL2Vector C a L) (x : (C.fiber a L).State),
      (transferOp a L ψ).toFun x =
        ∫ y,
          P.transferKernel a L x y * ψ.toFun y
          ∂(C.fiber a L).measure
  vacuum :
    ∀ a L, RegulatedL2Vector C a L
  h_vacuum_fixed :
    ∀ a L, transferOp a L (vacuum a L) = vacuum a L
  h_positive :
    ∀ a L (ψ : RegulatedL2Vector C a L),
      0 ≤ (regulatedInner ψ (transferOp a L ψ)).re
  h_symmetric :
    ∀ a L (ψ φ : RegulatedL2Vector C a L),
      regulatedInner (transferOp a L ψ) φ =
        regulatedInner ψ (transferOp a L φ)
  h_contraction :
    ∀ a L (ψ : RegulatedL2Vector C a L),
      regulatedNormSq (transferOp a L ψ) ≤ regulatedNormSq ψ
  spectralGap :
    C.Signature.Regulator → C.Signature.Volume → ℝ
  h_spectral_gap_nonneg :
    ∀ a L, 0 ≤ spectralGap a L
  h_spectral_gap_controls_transfer :
    ∀ a L (ψ : RegulatedL2Vector C a L),
      regulatedInner ψ (vacuum a L) = 0 →
      regulatedNormSq (transferOp a L ψ) ≤
        Real.exp (-P.cutoffValue a * spectralGap a L) *
          regulatedNormSq ψ

/-- B5 v2: the mass scale is explicit, strictly positive, tied exactly to B4's
spectral-gap function, and uniform over every admissible regulated model below
one fixed positive cutoff threshold.  Since P.cutoffCofinal supplies
arbitrarily small admissible cutoffs and h_uniform quantifies every volume,
the old identically-zero estimate cannot inhabit this type. -/
structure UniformRegulatorControlV2
    (C : RegulatedYM4Construction)
    (P : A1PhysicalData C)
    (B3 : ReflectionPositivityDataV2 C P)
    (B4 : PositiveTransferDataV2 C P) where
  m0 : ℝ
  hm0 : 0 < m0
  a0 : ℝ
  ha0 : 0 < a0
  gapAt : C.Signature.Regulator → C.Signature.Volume → ℝ
  h_gap_eq :
    ∀ a L, gapAt a L = B4.spectralGap a L
  h_uniform :
    ∀ a L,
      C.admissible a L →
      0 < P.cutoffValue a →
      P.cutoffValue a < a0 →
      m0 ≤ gapAt a L
  h_reflection_available :
    ∀ a L (O : C.Signature.Observable),
      0 ≤ B3.pairing a L O O

theorem uniform_v2_mass_nonzero
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4) :
    U.m0 ≠ 0 :=
  ne_of_gt U.hm0

theorem uniform_v2_gap_not_identically_zero
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4) :
    ¬ (∀ a L, U.gapAt a L = 0) := by
  intro hzero
  rcases P.cutoffCofinal U.a0 U.ha0 with
    ⟨a, L, hadm, hcutPos, hcutLt⟩
  have hbound := U.h_uniform a L hadm hcutPos hcutLt
  rw [hzero a L] at hbound
  linarith [U.hm0]

theorem uniform_v2_gap_is_transfer_gap
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4) :
    ∀ a L, U.gapAt a L = B4.spectralGap a L :=
  U.h_gap_eq

/-- Hardened A1 endpoint.  B3, B4 and B5 are dependent data, not independent
bare Props. -/
structure A1ScientificWitnessV2 (C : RegulatedYM4Construction) where
  physicalData : A1PhysicalData C
  measureInvariance : MeasureInvariance C
  observableInvariance : ObservableInvariance C
  reflectionPositivity :
    ReflectionPositivityDataV2 C physicalData
  positiveTransfer :
    PositiveTransferDataV2 C physicalData
  uniformMass :
    UniformRegulatorControlV2
      C physicalData reflectionPositivity positiveTransfer

def A1ScientificOpenBridgeV2 (C : RegulatedYM4Construction) : Prop :=
  Nonempty (A1ScientificWitnessV2 C)

/-- B3--B5 are dependent witness data, so their logically correct
packaging is existential rather than a conjunction of Types. -/
def HardenedB3B4B5Package (C : RegulatedYM4Construction) : Prop :=
  ∃ P : A1PhysicalData C,
    ∃ B3 : ReflectionPositivityDataV2 C P,
      ∃ B4 : PositiveTransferDataV2 C P,
        Nonempty (UniformRegulatorControlV2 C P B3 B4)

/-- The hardened open bridge exposes B1 and B2 together with actual dependent
B3/B4/B5 witness data. -/
theorem a1_v2_open_bridge_exposes_B1_B2_B3_B4_B5
    {C : RegulatedYM4Construction}
    (h : A1ScientificOpenBridgeV2 C) :
    MeasureInvariance C ∧
    ObservableInvariance C ∧
    HardenedB3B4B5Package C := by
  rcases h with ⟨W⟩
  refine ⟨W.measureInvariance, W.observableInvariance, ?_⟩
  exact ⟨W.physicalData, W.reflectionPositivity,
    W.positiveTransfer, ⟨W.uniformMass⟩⟩

end MCore.YangMills.A1
