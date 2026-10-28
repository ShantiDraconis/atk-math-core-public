import MCore.FinalFail.ExactGapLedger
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore.FinalFail

/-!
# Accepted hypothesis inhabitants

This module turns the user's explicitly accepted boundary hypotheses into typed
objects that can be carried forward by M-Core.

Fail-closed rule:
* these values are HYPOTHESIS inhabitants, not unconditional producers;
* no theorem here changes `FinalProof.registry` to `.proved`;
* no axiom, proof placeholder, oracle, or fabricated witness is introduced;
* every constructor requires the accepted mathematical content as an argument.

The purpose is to stop reopening already-selected boundary objects while keeping
their epistemic status explicit.
-/

universe u v w

/-- Riemann lane: the accepted object is a counterexample to the official
Mathlib Riemann-hypothesis proposition.  Supplying this field is an explicit
hypothesis; this structure does not manufacture such a counterexample. -/
structure RiemannAcceptedInhabitant where
  offCriticalCounterexample : ¬ RiemannHypothesis

def produceRiemannAccepted
    (h : ¬ RiemannHypothesis) : RiemannAcceptedInhabitant :=
  ⟨h⟩

/-- Navier--Stokes lane: a single component that controls every admitted
`ActualNS` flow through the chosen stabilization relation.  The concrete PDE
layer supplies `ActualNS` and `stabilizes`; this kernel does not weaken them. -/
structure NavierStokesAcceptedInhabitant
    (Flow : Type u) (Stabilizer : Type v)
    (ActualNS : Flow → Prop)
    (stabilizes : Stabilizer → Flow → Prop) where
  component : Stabilizer
  controls : ∀ u, ActualNS u → stabilizes component u

def produceNavierStokesAccepted
    {Flow : Type u} {Stabilizer : Type v}
    {ActualNS : Flow → Prop}
    {stabilizes : Stabilizer → Flow → Prop}
    (component : Stabilizer)
    (h : ∀ u, ActualNS u → stabilizes component u) :
    NavierStokesAcceptedInhabitant Flow Stabilizer ActualNS stabilizes :=
  ⟨component, h⟩

/-- Hodge lane: every admitted rational Hodge class receives an algebraic-cycle
realizer.  The geometry layer determines the concrete class/cycle types and the
exact realization relation. -/
structure HodgeAcceptedInhabitant
    (HodgeClass : Type u) (Cycle : Type v)
    (isRationalHodge : HodgeClass → Prop)
    (realizes : Cycle → HodgeClass → Prop) where
  realize : ∀ α, isRationalHodge α → ∃ Z, realizes Z α

def produceHodgeAccepted
    {HodgeClass : Type u} {Cycle : Type v}
    {isRationalHodge : HodgeClass → Prop}
    {realizes : Cycle → HodgeClass → Prop}
    (h : ∀ α, isRationalHodge α → ∃ Z, realizes Z α) :
    HodgeAcceptedInhabitant HodgeClass Cycle isRationalHodge realizes :=
  ⟨h⟩

/-- P-vs-NP lane: the accepted object is a genuine material orientation.
The canonical repository may instantiate this by its polynomial-SAT or genuine
lower-bound orientation; the genuineness predicate prevents toy inhabitants. -/
structure PvsNPAcceptedInhabitant
    (MaterialOrientation : Type u)
    (Genuine : MaterialOrientation → Prop) where
  orientation : MaterialOrientation
  genuine : Genuine orientation

def producePvsNPAccepted
    {MaterialOrientation : Type u}
    {Genuine : MaterialOrientation → Prop}
    (orientation : MaterialOrientation)
    (h : Genuine orientation) :
    PvsNPAcceptedInhabitant MaterialOrientation Genuine :=
  ⟨orientation, h⟩

/-- BSD lane: rank equality and the refined formula are carried together on the
same curve domain.  This prevents closing only the rank half while silently
dropping the refined leading-coefficient obligation. -/
structure BSDAcceptedInhabitant
    (Curve : Type u)
    (analyticOrder mordellWeilRank : Curve → Int)
    (refinedFormula : Curve → Prop) where
  rankEquality : ∀ E, analyticOrder E = mordellWeilRank E
  refined : ∀ E, refinedFormula E

def produceBSDAccepted
    {Curve : Type u}
    {analyticOrder mordellWeilRank : Curve → Int}
    {refinedFormula : Curve → Prop}
    (hRank : ∀ E, analyticOrder E = mordellWeilRank E)
    (hRefined : ∀ E, refinedFormula E) :
    BSDAcceptedInhabitant Curve analyticOrder mordellWeilRank refinedFormula :=
  ⟨hRank, hRefined⟩

/-- Beal lane: every admissible Beal datum receives the required nontrivial
common-prime witness through the concrete predicate supplied by the Beal layer. -/
structure BealAcceptedInhabitant
    (BealDatum : Type u)
    (Admissible : BealDatum → Prop)
    (CommonPrime : BealDatum → Prop) where
  commonPrimeOf : ∀ d, Admissible d → CommonPrime d

def produceBealAccepted
    {BealDatum : Type u}
    {Admissible : BealDatum → Prop}
    {CommonPrime : BealDatum → Prop}
    (h : ∀ d, Admissible d → CommonPrime d) :
    BealAcceptedInhabitant BealDatum Admissible CommonPrime :=
  ⟨h⟩

/-- Yang--Mills lane: one genuine four-dimensional theory simultaneously carries
OS reconstruction and a positive mass-gap predicate.  All three predicates must
be discharged for the same theory object. -/
structure YangMillsAcceptedInhabitant
    (Theory : Type u)
    (Genuine4D OSReconstructs PositiveMassGap : Theory → Prop) where
  theory : Theory
  genuine4D : Genuine4D theory
  osReconstructs : OSReconstructs theory
  positiveMassGap : PositiveMassGap theory

def produceYangMillsAccepted
    {Theory : Type u}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (theory : Theory)
    (h4D : Genuine4D theory)
    (hOS : OSReconstructs theory)
    (hGap : PositiveMassGap theory) :
    YangMillsAcceptedInhabitant Theory Genuine4D OSReconstructs PositiveMassGap :=
  ⟨theory, h4D, hOS, hGap⟩

/-- Administrative fact only: all seven active problem slots now have an
explicit accepted-hypothesis inhabitant type.  This does not assert that any
such type is unconditionally inhabited. -/
def acceptedHypothesisSlots : List ProblemId :=
  [.riemann, .beal, .navierStokes, .hodge, .pVsNP, .bsd, .yangMills]

theorem acceptedHypothesisSlots_eq_seven :
    acceptedHypothesisSlots.length = 7 := by
  decide

end MCore.FinalFail
