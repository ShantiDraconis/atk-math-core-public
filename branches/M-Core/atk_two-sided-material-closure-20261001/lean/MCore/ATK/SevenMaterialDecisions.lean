import MCore.ATK.StructuralDefect
import MCore.ATK.MaterialDecisionClosure

namespace MCore.ATK.SevenMaterialDecisions

open MCore.ATK.StructuralDefect
open MCore.ATK.MaterialDecision

/--
Per-lane target and concrete evidence carriers.
The target proposition is declared, never assumed.
-/
structure LaneDecisionSpec where
  statement : Prop
  PositiveObject : Type
  NegativeObject : Type
  Observable : Type
  system :
    ObservableDecisionSystem
      statement PositiveObject NegativeObject Observable

/-- Seven independent decision specifications. -/
structure SevenDecisionSpec where
  lane : ProblemKind → LaneDecisionSpec

/--
Material evidence supplied for one lane.  It contains concrete objects only.
-/
abbrev LaneEvidence (L : LaneDecisionSpec) :=
  MaterialAlternative L.PositiveObject L.NegativeObject

/--
Result of interpreting one concrete lane evidence object.
-/
def decideLane
    (L : LaneDecisionSpec)
    (e : LaneEvidence L) :
    DecisionEvidence L.statement :=
  decideFromAlternative
    L.system.toMaterialDecisionSystem e

/--
A materially decided lane is one carrying either a genuine positive object or
a genuine negative object.  The open state is excluded.
-/
structure ClosedLane (L : LaneDecisionSpec) where
  evidence : LaneEvidence L
  decision : Decided L.statement
  consistentWithEvidence :
    materialDecision L.system.toMaterialDecisionSystem evidence =
      some decision

/--
The global seven-lane bundle records a material decision for every problem.
It does not erase whether a lane was proved or refuted.
-/
structure SevenDecisionBundle (S : SevenDecisionSpec) where
  riemann : ClosedLane (S.lane .riemann)
  pnp : ClosedLane (S.lane .pnp)
  yangMills : ClosedLane (S.lane .yangMills)
  navierStokes : ClosedLane (S.lane .navierStokes)
  bsd : ClosedLane (S.lane .bsd)
  hodge : ClosedLane (S.lane .hodge)
  beal : ClosedLane (S.lane .beal)

/-- Global closure means all seven questions have concrete material decisions. -/
def GlobalMaterialDecision
    (S : SevenDecisionSpec) : Prop :=
  Nonempty (SevenDecisionBundle S)

/-- Every global bundle projects back to the exact Riemann decision. -/
theorem global_projects_riemann
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    Nonempty (Decided (S.lane .riemann).statement) :=
  ⟨G.riemann.decision⟩

theorem global_projects_pnp
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    Nonempty (Decided (S.lane .pnp).statement) :=
  ⟨G.pnp.decision⟩

theorem global_projects_yangMills
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    Nonempty (Decided (S.lane .yangMills).statement) :=
  ⟨G.yangMills.decision⟩

theorem global_projects_navierStokes
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    Nonempty (Decided (S.lane .navierStokes).statement) :=
  ⟨G.navierStokes.decision⟩

theorem global_projects_bsd
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    Nonempty (Decided (S.lane .bsd).statement) :=
  ⟨G.bsd.decision⟩

theorem global_projects_hodge
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    Nonempty (Decided (S.lane .hodge).statement) :=
  ⟨G.hodge.decision⟩

theorem global_projects_beal
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    Nonempty (Decided (S.lane .beal).statement) :=
  ⟨G.beal.decision⟩

/--
No global truth collapse: a global decision bundle yields decisions, not proofs
that every statement is true.
-/
inductive DecisionPolarity (P : Prop) where
  | positive (hp : P)
  | negative (hn : ¬ P)

def polarityOfDecided
    {P : Prop} :
    Decided P → DecisionPolarity P
  | .proved hp => .positive hp
  | .refuted hn => .negative hn

/--
A consistent global bundle has exactly one polarity per lane.
The impossible both-state has already been eliminated by materialDecision.
-/
structure SevenPolarityBundle (S : SevenDecisionSpec) where
  riemann : DecisionPolarity (S.lane .riemann).statement
  pnp : DecisionPolarity (S.lane .pnp).statement
  yangMills : DecisionPolarity (S.lane .yangMills).statement
  navierStokes : DecisionPolarity (S.lane .navierStokes).statement
  bsd : DecisionPolarity (S.lane .bsd).statement
  hodge : DecisionPolarity (S.lane .hodge).statement
  beal : DecisionPolarity (S.lane .beal).statement

def SevenDecisionBundle.toPolarityBundle
    {S : SevenDecisionSpec}
    (G : SevenDecisionBundle S) :
    SevenPolarityBundle S where
  riemann := polarityOfDecided G.riemann.decision
  pnp := polarityOfDecided G.pnp.decision
  yangMills := polarityOfDecided G.yangMills.decision
  navierStokes := polarityOfDecided G.navierStokes.decision
  bsd := polarityOfDecided G.bsd.decision
  hodge := polarityOfDecided G.hodge.decision
  beal := polarityOfDecided G.beal.decision

#print axioms MCore.ATK.SevenMaterialDecisions.decideLane
#print axioms MCore.ATK.SevenMaterialDecisions.global_projects_riemann
#print axioms MCore.ATK.SevenMaterialDecisions.global_projects_pnp
#print axioms MCore.ATK.SevenMaterialDecisions.SevenDecisionBundle.toPolarityBundle

end MCore.ATK.SevenMaterialDecisions
