import MCore.A2SelfRef

namespace MCore

/-- Reflexive-transitive reachability in an arbitrary audit graph. -/
inductive Reachable (G : Graph) : Node → Node → Prop where
  | refl (x : Node) : Reachable G x x
  | step {x y z : Node} : HasEdge G x y → Reachable G y z → Reachable G x z

/-- Nonempty transitive reachability: every witness contains at least one edge. -/
inductive ReachablePlus (G : Graph) : Node → Node → Prop where
  | single {x y : Node} : HasEdge G x y → ReachablePlus G x y
  | trans {x y z : Node} : HasEdge G x y → ReachablePlus G y z → ReachablePlus G x z

/-- Obligation #15: forbidden G1/G4 feedback, detected through arbitrary
nonempty paths rather than direct-edge matching. -/
def HasG1G4Feedback (G : Graph) : Prop :=
  ReachablePlus G .g1 .g4 ∧ ReachablePlus G .g4 .g1

/-- Obligation #16: the target/conclusion must not feed back into a(t), even
through intermediate nodes. -/
def HasDownstreamViolation (G : Graph) : Prop :=
  ReachablePlus G .targetY .coeffA ∨ ReachablePlus G .I .coeffA

/-- Strong DAG gate used by the M-Core audit. -/
def PassesDownstreamGate (G : Graph) : Prop :=
  ¬ HasG1G4Feedback G ∧ ¬ HasDownstreamViolation G

/-- Explicit forbidden fixture: G1/G4 feedback and I -> a(t) readback. -/
def forbiddenFixture : Graph :=
  [(.g1, .g4), (.g4, .g1), (.I, .coeffA), (.coeffA, .targetY), (.targetY, .I)]

/-- The forbidden fixture contains a genuinely nonempty G1 cycle:
G1 -> G4 -> G1. No reflexivity constructor is used. -/
theorem forbiddenFixture_g1CycleNonempty :
    ReachablePlus forbiddenFixture .g1 .g1 := by
  apply ReachablePlus.trans (y := .g4)
  · simp [HasEdge, forbiddenFixture]
  · exact ReachablePlus.single (by simp [HasEdge, forbiddenFixture])

theorem forbiddenFixture_hasFeedback : HasG1G4Feedback forbiddenFixture := by
  constructor
  · exact ReachablePlus.single (by simp [HasEdge, forbiddenFixture])
  · exact ReachablePlus.single (by simp [HasEdge, forbiddenFixture])

theorem forbiddenFixture_hasDownstreamViolation :
    HasDownstreamViolation forbiddenFixture := by
  right
  exact ReachablePlus.single (by simp [HasEdge, forbiddenFixture])

/-- #15-16 negative fixture: both violations are detected and the strong gate
rejects the graph. -/
theorem forbidden_detected_rejected :
    HasG1G4Feedback forbiddenFixture ∧
    HasDownstreamViolation forbiddenFixture ∧
    ¬ PassesDownstreamGate forbiddenFixture := by
  refine ⟨forbiddenFixture_hasFeedback, forbiddenFixture_hasDownstreamViolation, ?_⟩
  intro h
  exact h.1 forbiddenFixture_hasFeedback

/-- Clean fixture: dependencies flow from G1 to a(t) to G4 only. -/
def downstreamFixture : Graph := [(.g1, .coeffA), (.coeffA, .g4)]

private theorem downstream_no_from_g4 {z : Node} :
    ¬ ReachablePlus downstreamFixture .g4 z := by
  intro h
  cases h with
  | single hedge => simp [HasEdge, downstreamFixture] at hedge
  | trans hedge _ => simp [HasEdge, downstreamFixture] at hedge

private theorem downstream_no_from_targetY {z : Node} :
    ¬ ReachablePlus downstreamFixture .targetY z := by
  intro h
  cases h with
  | single hedge => simp [HasEdge, downstreamFixture] at hedge
  | trans hedge _ => simp [HasEdge, downstreamFixture] at hedge

private theorem downstream_no_from_I {z : Node} :
    ¬ ReachablePlus downstreamFixture .I z := by
  intro h
  cases h with
  | single hedge => simp [HasEdge, downstreamFixture] at hedge
  | trans hedge _ => simp [HasEdge, downstreamFixture] at hedge

theorem downstreamFixture_noFeedback : ¬ HasG1G4Feedback downstreamFixture := by
  intro h
  exact downstream_no_from_g4 h.2

theorem downstreamFixture_noViolation :
    ¬ HasDownstreamViolation downstreamFixture := by
  intro h
  cases h with
  | inl hy => exact downstream_no_from_targetY hy
  | inr hi => exact downstream_no_from_I hi

/-- #15-16 positive fixture: no forbidden feedback/readback exists and the
strong downstream gate accepts the graph. -/
theorem downstream_accepted :
    ¬ HasG1G4Feedback downstreamFixture ∧
    ¬ HasDownstreamViolation downstreamFixture ∧
    PassesDownstreamGate downstreamFixture := by
  exact ⟨downstreamFixture_noFeedback, downstreamFixture_noViolation,
    downstreamFixture_noFeedback, downstreamFixture_noViolation⟩

end MCore
