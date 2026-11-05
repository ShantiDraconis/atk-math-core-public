import MCore.ATK.MaterialMultistateDynamics
import MCore.ATK.SevenLaneSpecialization

namespace MCore.ATK.CrossProverClosure

open MCore.ATK.UniversalProducer
open MCore.ATK.MaterialMultistate

/-- The cross-prover contract fixes the mathematics before any prover-specific
proof object is admitted.  Lean/Coq/Isabelle implementations must preserve
these three layers: reduction, exact terminal specification, exact materializer. -/
structure ExactClosurePackage (S : UniversalProblemSpec) where
  materialization : UniversalExactMaterialization S
  seed : UniversalProblemSeed S

/-- Once all seven exact materializers exist, Lean computes all seven exact
terminal inhabitants.  No structural state is substituted for an inhabitant. -/
def closeSeven
    (S : UniversalProblemSpec)
    (P : ExactClosurePackage S) :
    SevenInhabitantBundle (S.materialize P.materialization) :=
  resolveExactSevenInhabitants S P.materialization P.seed

/-- Certificate-level form of the same exact closure. -/
def closeSevenCertificates
    (S : UniversalProblemSpec)
    (P : ExactClosurePackage S) :
    SevenCertificateBundle (S.materialize P.materialization) :=
  buildSevenCertificates
    (S.materialize P.materialization)
    (promoteProblemSeed S P.materialization P.seed)

/-- Global closure does not weaken any lane: every named inhabitant projects
back to the exact predeclared terminal type for that lane. -/
theorem global_closure_projects_riemann
    {S : UniversalProblemSpec}
    (P : ExactClosurePackage S) :
    ((S.materialize P.materialization).lane .riemann).Inhabitant :=
  (closeSeven S P).riemann

theorem global_closure_projects_pnp
    {S : UniversalProblemSpec}
    (P : ExactClosurePackage S) :
    ((S.materialize P.materialization).lane .pnp).Inhabitant :=
  (closeSeven S P).pnp

theorem global_closure_projects_yangMills
    {S : UniversalProblemSpec}
    (P : ExactClosurePackage S) :
    ((S.materialize P.materialization).lane .yangMills).Inhabitant :=
  (closeSeven S P).yangMills

theorem global_closure_projects_navierStokes
    {S : UniversalProblemSpec}
    (P : ExactClosurePackage S) :
    ((S.materialize P.materialization).lane .navierStokes).Inhabitant :=
  (closeSeven S P).navierStokes

theorem global_closure_projects_bsd
    {S : UniversalProblemSpec}
    (P : ExactClosurePackage S) :
    ((S.materialize P.materialization).lane .bsd).Inhabitant :=
  (closeSeven S P).bsd

theorem global_closure_projects_hodge
    {S : UniversalProblemSpec}
    (P : ExactClosurePackage S) :
    ((S.materialize P.materialization).lane .hodge).Inhabitant :=
  (closeSeven S P).hodge

theorem global_closure_projects_beal
    {S : UniversalProblemSpec}
    (P : ExactClosurePackage S) :
    ((S.materialize P.materialization).lane .beal).Inhabitant :=
  (closeSeven S P).beal

/-- Boolean-style gate algebra used by all three prover ports. -/
theorem pair_closed_exactly_when_both_closed
    (a b : GateState) :
    combine a b = .closed ↔
      a = .closed ∧ b = .closed :=
  combine_eq_closed_iff a b

/-- Cross-prover semantic firewall: representing a zero-defect state is not a
replacement for proving the predeclared terminal type. -/
theorem zero_defect_is_not_universal_terminal_constructor :
    ¬ (∀ (R : ReductionLane) (T : TerminalSpec R)
        (x : R.State), R.defect x = 0 → Nonempty T.Inhabitant) :=
  zero_defect_does_not_erase_terminal_type

#print axioms MCore.ATK.CrossProverClosure.closeSeven
#print axioms MCore.ATK.CrossProverClosure.closeSevenCertificates
#print axioms MCore.ATK.CrossProverClosure.pair_closed_exactly_when_both_closed
#print axioms MCore.ATK.CrossProverClosure.zero_defect_is_not_universal_terminal_constructor

end MCore.ATK.CrossProverClosure
