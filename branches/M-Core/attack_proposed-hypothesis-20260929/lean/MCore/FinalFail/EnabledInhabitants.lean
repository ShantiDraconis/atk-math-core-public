import MCore.FinalFail.AcceptedInhabitants
import MCore.FinalFail.BoundaryAtoms

namespace MCore.FinalFail

universe u v

/-!
# Enabled accepted inhabitants

This module activates the seven accepted boundary objects as usable `Nonempty`
inhabitants whenever their accepted mathematical data are present in the local
context.

Important epistemic distinction:
* `enabled` means available to downstream Lean proofs under the stated input;
* `unconditional` means constructible with no such mathematical input.

This file establishes the first property only.  It deliberately records that the
second count remains zero until an actual terminal producer is supplied.
-/

inductive InhabitantOrigin where
  | acceptedHypothesis
  | unconditionalProducer
  deriving DecidableEq, Repr

structure InhabitantActivation where
  problem : ProblemId
  origin : InhabitantOrigin
  enabled : Bool
  deriving Repr

def activationLedger : List InhabitantActivation := [
  { problem := .riemann,       origin := .acceptedHypothesis, enabled := true },
  { problem := .beal,         origin := .acceptedHypothesis, enabled := true },
  { problem := .navierStokes, origin := .acceptedHypothesis, enabled := true },
  { problem := .hodge,        origin := .acceptedHypothesis, enabled := true },
  { problem := .pVsNP,        origin := .acceptedHypothesis, enabled := true },
  { problem := .bsd,          origin := .acceptedHypothesis, enabled := true },
  { problem := .yangMills,    origin := .acceptedHypothesis, enabled := true }
]

def enabledCount : Nat :=
  activationLedger.foldl (fun n r => if r.enabled then n + 1 else n) 0

def unconditionalCount : Nat :=
  activationLedger.foldl
    (fun n r => if r.origin = .unconditionalProducer then n + 1 else n) 0

theorem enabledCount_eq_seven : enabledCount = 7 := by
  decide

theorem unconditionalCount_eq_zero : unconditionalCount = 0 := by
  decide

/-- RH is immediately usable as a `Nonempty` accepted inhabitant once the
chosen off-RH hypothesis is supplied. -/
theorem enableRiemann
    (h : ¬ RiemannHypothesis) :
    Nonempty RiemannAcceptedInhabitant :=
  ⟨produceRiemannAccepted h⟩

theorem enableNavierStokes
    {Flow : Type u} {Stabilizer : Type v}
    {ActualNS : Flow → Prop}
    {stabilizes : Stabilizer → Flow → Prop}
    (component : Stabilizer)
    (h : ∀ u, ActualNS u → stabilizes component u) :
    Nonempty (NavierStokesAcceptedInhabitant
      Flow Stabilizer ActualNS stabilizes) :=
  ⟨produceNavierStokesAccepted component h⟩

theorem enableHodge
    {HodgeClass : Type u} {Cycle : Type v}
    {isRationalHodge : HodgeClass → Prop}
    {realizes : Cycle → HodgeClass → Prop}
    (h : ∀ α, isRationalHodge α → ∃ Z, realizes Z α) :
    Nonempty (HodgeAcceptedInhabitant
      HodgeClass Cycle isRationalHodge realizes) :=
  ⟨produceHodgeAccepted h⟩

theorem enablePvsNP
    {MaterialOrientation : Type u}
    {Genuine : MaterialOrientation → Prop}
    (orientation : MaterialOrientation)
    (h : Genuine orientation) :
    Nonempty (PvsNPAcceptedInhabitant MaterialOrientation Genuine) :=
  ⟨producePvsNPAccepted orientation h⟩

theorem enableBSD
    {Curve : Type u}
    {analyticOrder mordellWeilRank : Curve → Int}
    {refinedFormula : Curve → Prop}
    (hRank : ∀ E, analyticOrder E = mordellWeilRank E)
    (hRefined : ∀ E, refinedFormula E) :
    Nonempty (BSDAcceptedInhabitant
      Curve analyticOrder mordellWeilRank refinedFormula) :=
  ⟨produceBSDAccepted hRank hRefined⟩

theorem enableBeal
    {BealDatum : Type u}
    {Admissible : BealDatum → Prop}
    {CommonPrime : BealDatum → Prop}
    (h : ∀ d, Admissible d → CommonPrime d) :
    Nonempty (BealAcceptedInhabitant BealDatum Admissible CommonPrime) :=
  ⟨produceBealAccepted h⟩

theorem enableYangMills
    {Theory : Type u}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (theory : Theory)
    (h4D : Genuine4D theory)
    (hOS : OSReconstructs theory)
    (hGap : PositiveMassGap theory) :
    Nonempty (YangMillsAcceptedInhabitant
      Theory Genuine4D OSReconstructs PositiveMassGap) :=
  ⟨produceYangMillsAccepted theory h4D hOS hGap⟩

/-- No activation in this file silently upgrades an assumed inhabitant into an
unconditional producer. -/
theorem activation_is_fail_closed :
    ∀ r ∈ activationLedger, r.origin = .acceptedHypothesis := by
  intro r hr
  simp [activationLedger] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end MCore.FinalFail
