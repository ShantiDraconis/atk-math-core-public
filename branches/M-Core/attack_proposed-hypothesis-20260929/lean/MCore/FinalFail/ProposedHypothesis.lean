import MCore.FinalFail.EnabledInhabitants
import MCore.FinalFail.SemanticParallel
import MCore.FinalProofRegistry

namespace MCore.FinalFail.Proposed

open MCore.FinalFail MCore.FinalFail.Semantic

universe u

/-!
# Proposed hypothesis: one object that enables all seven inhabitants

This module packages the accepted boundary hypotheses of the seven active lanes
into a single structure `ProposedHypothesis M`, and derives from it, in one
place, every inhabitant the M-Core stack knows how to consume:

* the semantic targets of `Semantic/` (`RiemannOffCriticalZero`,
  `BealUniversalGCDTarget`, `PvsNPSeparationTarget`, ...);
* the boundary interpretations `BoundaryInterpretation p Target`, i.e. the
  realisation of each free `BoundaryAtom p` as its semantic target;
* the accepted inhabitants of `AcceptedInhabitants.lean` for the two lanes whose
  target is already bound to concrete Mathlib objects (Riemann, Beal).

## Two separate objects

* `LaneModels` holds the model bindings that are still
  `canonicalModelBindingOpen` in `SemanticParallel.lean` (P vs NP, NS, Hodge,
  BSD, YM).  It contains no mathematical claim.
* `ProposedHypothesis M` holds the mathematical content: one field per
  obligation, stated over the concrete Riemann/Beal objects and over the
  models `M` for the other five lanes.

## Fail-closed rules (unchanged)

* No postulated constants, placeholder proofs, oracles or fabricated witnesses.
* Every result below takes `H : ProposedHypothesis M` as an argument; nothing
  here is an `unconditionalProducer`, and `unconditionalCount` stays `0`.
* `FinalProof.registry` is not touched; `provedCount` stays `0`.

## Epistemic warnings

* Consistency is NOT checked here.  If two fields of `ProposedHypothesis`
  contradict each other, the structure is empty and every downstream theorem
  holds vacuously.  The Riemann field is the NEGATION of RH.
* For the five lanes whose model binding is open, a toy `LaneModels`
  (empty types, `False` predicates) makes those fields trivially satisfiable.
  The results are only meaningful once `M` is bound to the canonical models.
-/

/-- Model bindings for the five lanes whose canonical model is still open.
Pure data: no field asserts anything about the Millennium problems. -/
structure LaneModels where
  -- P vs NP: official complexity model
  Language : Type u
  InP : Language → Prop
  InNP : Language → Prop
  SAT : Language
  -- Navier–Stokes: ActualNS model and stabilisation relation
  Flow : Type u
  Stabilizer : Type u
  ActualNS : Flow → Prop
  Stabilizes : Stabilizer → Flow → Prop
  -- Hodge: geometry layer
  Variety : Type u
  Class : Variety → Type u
  Cycle : Variety → Type u
  SmoothProjective : Variety → Prop
  RationalHodge : {X : Variety} → Class X → Prop
  Realizes : {X : Variety} → Cycle X → Class X → Prop
  -- BSD: elliptic-curve domain
  Curve : Type u
  Realizable : Curve → Prop
  AnalyticOrder : Curve → Int
  MordellWeilRank : Curve → Int
  RefinedFormula : Curve → Prop
  -- Yang–Mills: theory representation
  Theory : Type u
  Genuine4D : Theory → Prop
  OSReconstructs : Theory → Prop
  PositiveMassGap : Theory → Prop

/-- The proposed hypothesis: every accepted boundary obligation of the seven
lanes, as one object.  Riemann and Beal are stated over concrete Mathlib /
`ℕ` objects; the other five over the model bindings `M`. -/
structure ProposedHypothesis (M : LaneModels.{u}) where
  /-- Riemann lane: the accepted negation of Mathlib's `RiemannHypothesis`. -/
  notRH : ¬ RiemannHypothesis
  /-- Beal lane: every admissible Beal equation has a nontrivial common gcd. -/
  bealGCD : ∀ d : BealEquationData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)
  /-- P vs NP lane: SAT is in NP and not in P in the bound model. -/
  satInNP : M.InNP M.SAT
  satNotInP : ¬ M.InP M.SAT
  /-- Navier–Stokes lane: one component stabilises every admitted flow. -/
  nsComponent : M.Stabilizer
  nsControls : ∀ v, M.ActualNS v → M.Stabilizes nsComponent v
  /-- Hodge lane: every rational Hodge class on a smooth projective variety is
  realised by an algebraic cycle. -/
  hodgeRealize :
    ∀ X, M.SmoothProjective X →
      ∀ α : M.Class X, M.RationalHodge α →
        ∃ Z : M.Cycle X, M.Realizes Z α
  /-- BSD lane: rank equality and refined formula on the same domain. -/
  bsdRank : ∀ E, M.Realizable E → M.AnalyticOrder E = M.MordellWeilRank E
  bsdRefined : ∀ E, M.Realizable E → M.RefinedFormula E
  /-- Yang–Mills lane: one theory carries 4D, OS reconstruction and a gap. -/
  ymTheory : M.Theory
  ym4D : M.Genuine4D ymTheory
  ymOS : M.OSReconstructs ymTheory
  ymGap : M.PositiveMassGap ymTheory

/-! ## Semantic targets, abbreviated over `M` -/

abbrev PvsNPTarget (M : LaneModels.{u}) :=
  PvsNPSeparationTarget M.Language M.InP M.InNP M.SAT

abbrev NSTarget (M : LaneModels.{u}) :=
  NavierStokesStabilizationTarget M.Flow M.Stabilizer M.ActualNS M.Stabilizes

abbrev HodgeTarget (M : LaneModels.{u}) :=
  HodgeRealizationTarget M.Variety M.Class M.Cycle M.SmoothProjective
    @M.RationalHodge @M.Realizes

abbrev BSDTarget (M : LaneModels.{u}) :=
  BSDRealizableTarget M.Curve M.Realizable M.AnalyticOrder
    M.MordellWeilRank M.RefinedFormula

abbrev YMTarget (M : LaneModels.{u}) :=
  YangMills4DGapTarget M.Theory M.Genuine4D M.OSReconstructs M.PositiveMassGap

section Enable

variable {M : LaneModels.{u}} (H : ProposedHypothesis M)
include H

/-! ## Creation: explicit semantic inhabitants built from `H` -/

def pvsnpTarget : PvsNPTarget M :=
  { sat_in_np := H.satInNP, sat_not_in_p := H.satNotInP }

def nsTarget : NSTarget M :=
  { component := H.nsComponent, controls := H.nsControls }

def hodgeTarget : HodgeTarget M :=
  { realize := H.hodgeRealize }

def bsdTarget : BSDTarget M :=
  { rankEquality := H.bsdRank, refined := H.bsdRefined }

def ymTarget : YMTarget M :=
  { theory := H.ymTheory
    genuine4D := H.ym4D
    reconstructs := H.ymOS
    positiveGap := H.ymGap }

def bealTarget : BealUniversalGCDTarget :=
  { commonGCD := H.bealGCD }

/-! ## Enabling: every lane as a `Nonempty` semantic target -/

theorem riemann_enabled : Nonempty RiemannOffCriticalZero :=
  accepted_not_RH_produces_semantic_inhabitant H.notRH

theorem beal_enabled : Nonempty BealUniversalGCDTarget :=
  ⟨bealTarget H⟩

theorem pvsnp_enabled : Nonempty (PvsNPTarget M) := ⟨pvsnpTarget H⟩

theorem ns_enabled : Nonempty (NSTarget M) := ⟨nsTarget H⟩

theorem hodge_enabled : Nonempty (HodgeTarget M) := ⟨hodgeTarget H⟩

theorem bsd_enabled : Nonempty (BSDTarget M) := ⟨bsdTarget H⟩

theorem ym_enabled : Nonempty (YMTarget M) := ⟨ymTarget H⟩

/-! ## Enabling: every free `BoundaryAtom` interpreted as its target -/

theorem riemann_interpretation_enabled : Nonempty RiemannInterpretation :=
  riemann_interpretation_iff_target.mpr (riemann_enabled H)

theorem beal_interpretation_enabled : Nonempty BealInterpretation :=
  beal_interpretation_iff_target.mpr (beal_enabled H)

theorem pvsnp_interpretation_enabled :
    Nonempty (PvsNPInterpretation M.Language M.InP M.InNP M.SAT) :=
  (pvsnp_interpretation_iff_target _ _ _ _).mpr (pvsnp_enabled H)

theorem ns_interpretation_enabled :
    Nonempty (NavierStokesInterpretation
      M.Flow M.Stabilizer M.ActualNS M.Stabilizes) :=
  (ns_interpretation_iff_target _ _ _ _).mpr (ns_enabled H)

theorem hodge_interpretation_enabled :
    Nonempty (HodgeInterpretation M.Variety M.Class M.Cycle
      M.SmoothProjective @M.RationalHodge @M.Realizes) :=
  (hodge_interpretation_iff_target _ _ _ _ _ _).mpr (hodge_enabled H)

theorem bsd_interpretation_enabled :
    Nonempty (BSDInterpretation M.Curve M.Realizable M.AnalyticOrder
      M.MordellWeilRank M.RefinedFormula) :=
  (bsd_interpretation_iff_target _ _ _ _ _).mpr (bsd_enabled H)

theorem ym_interpretation_enabled :
    Nonempty (YangMillsInterpretation
      M.Theory M.Genuine4D M.OSReconstructs M.PositiveMassGap) :=
  (ym_interpretation_iff_target _ _ _ _).mpr (ym_enabled H)

/-! ## Enabling: the `AcceptedInhabitants` layer -/

theorem riemann_accepted_enabled : Nonempty RiemannAcceptedInhabitant :=
  enableRiemann H.notRH

theorem beal_accepted_enabled :
    Nonempty (BealAcceptedInhabitant BealEquationData (fun _ => True)
      (fun d => 1 < Nat.gcd d.a (Nat.gcd d.b d.c))) :=
  enableBeal (fun d _ => H.bealGCD d)

theorem pvsnp_accepted_enabled :
    Nonempty (PvsNPAcceptedInhabitant M.Language
      (fun L => L = M.SAT ∧ M.InNP L ∧ ¬ M.InP L)) :=
  enablePvsNP M.SAT ⟨rfl, H.satInNP, H.satNotInP⟩

theorem ns_accepted_enabled :
    Nonempty (NavierStokesAcceptedInhabitant
      M.Flow M.Stabilizer M.ActualNS M.Stabilizes) :=
  enableNavierStokes H.nsComponent H.nsControls

theorem ym_accepted_enabled :
    Nonempty (YangMillsAcceptedInhabitant
      M.Theory M.Genuine4D M.OSReconstructs M.PositiveMassGap) :=
  enableYangMills H.ymTheory H.ym4D H.ymOS H.ymGap

/-! ## All seven at once -/

/-- The seven semantic lanes, simultaneously inhabited. -/
structure AllSevenEnabled (M : LaneModels.{u}) : Prop where
  riemann : Nonempty RiemannOffCriticalZero
  beal : Nonempty BealUniversalGCDTarget
  pVsNP : Nonempty (PvsNPTarget M)
  navierStokes : Nonempty (NSTarget M)
  hodge : Nonempty (HodgeTarget M)
  bsd : Nonempty (BSDTarget M)
  yangMills : Nonempty (YMTarget M)

/-- One hypothesis object enables all seven lanes. -/
theorem enableAll : AllSevenEnabled M :=
  { riemann := riemann_enabled H
    beal := beal_enabled H
    pVsNP := pvsnp_enabled H
    navierStokes := ns_enabled H
    hodge := hodge_enabled H
    bsd := bsd_enabled H
    yangMills := ym_enabled H }

end Enable

/-- Conditional form: the hypothesis world enables all seven lanes. -/
theorem proposed_enables_all (M : LaneModels.{u}) :
    ProposedHypothesis M → AllSevenEnabled M :=
  fun H => enableAll H

/-! ## Fail-closed bookkeeping -/

/-- Packaging the hypothesis creates no unconditional producer. -/
theorem proposed_unconditionalCount_eq_zero : unconditionalCount = 0 :=
  unconditionalCount_eq_zero

/-- Packaging the hypothesis promotes no final proof. -/
theorem proposed_provedCount_eq_zero : MCore.FinalProof.provedCount = 0 :=
  MCore.FinalProof.provedCount_eq_zero

/-- Every enabled lane still has origin `acceptedHypothesis`. -/
theorem proposed_is_fail_closed :
    ∀ r ∈ activationLedger, r.origin = .acceptedHypothesis :=
  activation_is_fail_closed

#print axioms MCore.FinalFail.Proposed.enableAll
#print axioms MCore.FinalFail.Proposed.proposed_enables_all
#print axioms MCore.FinalFail.Proposed.hodge_interpretation_enabled

end MCore.FinalFail.Proposed
