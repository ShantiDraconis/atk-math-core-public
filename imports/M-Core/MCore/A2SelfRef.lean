import MCore.Core
import Mathlib

namespace MCore

inductive Node where
  | g1 | I | coeffA | targetY | g4
  deriving DecidableEq, Repr

abbrev Edge := Node × Node
abbrev Graph := List Edge

/-- A directed edge is explicitly present in the audit graph. -/
def HasEdge (G : Graph) (x y : Node) : Prop := (x, y) ∈ G

/-- The canonical forbidden self-reference pattern: I needs a, a needs Y,
and Y is established through I. -/
def HasCanonicalSelfRef (G : Graph) : Prop :=
  HasEdge G .I .coeffA ∧ HasEdge G .coeffA .targetY ∧ HasEdge G .targetY .I

/-- M-Core's DAG gate rejects the canonical cycle. -/
def PassesSelfRefGate (G : Graph) : Prop := ¬ HasCanonicalSelfRef G

example :
    ¬ PassesSelfRefGate [(.I, .coeffA), (.coeffA, .targetY), (.targetY, .I)] := by
  intro h
  apply h
  simp [HasCanonicalSelfRef, HasEdge]

end MCore
