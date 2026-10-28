import MCore.V22.State

namespace MCore.V22

structure MatrixCell where
  row : Node
  column : Node
  rowState : ProofState
  columnState : ProofState
  pairState : PairState
  scenarioMode : ScenarioMode
  closureSite : MCore.V21.ClosureSite
  deriving Repr

def allDirectedNodePairs : List (Node × Node) :=
  allNodes.flatMap (fun a => allNodes.map (fun b => (a, b)))

theorem allDirectedNodePairs_count : allDirectedNodePairs.length = 1521 := by
  native_decide

inductive EdgeKind where
  | internal
  | crossProblem
  | self
  deriving DecidableEq, Repr

def edgeKind (a b : Node) : EdgeKind :=
  if a = b then .self else if a.problem = b.problem then .internal else .crossProblem

end MCore.V22
