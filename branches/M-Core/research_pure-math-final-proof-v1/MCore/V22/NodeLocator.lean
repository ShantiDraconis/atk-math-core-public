import MCore.V22.FrontierRegistry

namespace MCore.V22

inductive NodeAuditState where
  | structuralClosed
  | blockingFrontier
  | downstreamPending
  | solvedControl
  | unassigned
  deriving DecidableEq, Repr

def isOpenPrimaryProblem : ProblemId → Bool
  | .bsd | .hodge | .navierStokes | .riemann | .pVsNP | .yangMills | .beal => true
  | _ => false

def isKernelSlot : ProblemId → Bool
  | .kernel0 | .kernel1 | .kernel2 | .kernel3 | .kernel4 => true
  | _ => false

def nodeAuditState (n : Node) : NodeAuditState :=
  if isKernelSlot n.problem then
    .unassigned
  else if n.problem = .poincare then
    .solvedControl
  else if isOpenPrimaryProblem n.problem then
    match n.stage with
    | .start => .structuralClosed
    | .middle => .blockingFrontier
    | .finish => .downstreamPending
  else
    .unassigned

def blockingNodes : List Node :=
  allNodes.filter (fun n => nodeAuditState n = .blockingFrontier)

def unassignedNodes : List Node :=
  allNodes.filter (fun n => nodeAuditState n = .unassigned)

theorem blocking_nodes_count : blockingNodes.length = 7 := by
  native_decide

theorem kernel_unassigned_nodes_count : unassignedNodes.length = 15 := by
  native_decide

theorem hodge_blocker_is_middle :
    nodeAuditState { problem := .hodge, stage := .middle } = .blockingFrontier := by
  rfl

theorem bsd_blocker_is_middle :
    nodeAuditState { problem := .bsd, stage := .middle } = .blockingFrontier := by
  rfl

theorem beal_blocker_is_middle :
    nodeAuditState { problem := .beal, stage := .middle } = .blockingFrontier := by
  rfl

theorem pnp_blocker_is_middle :
    nodeAuditState { problem := .pVsNP, stage := .middle } = .blockingFrontier := by
  rfl

theorem rh_blocker_is_middle :
    nodeAuditState { problem := .riemann, stage := .middle } = .blockingFrontier := by
  rfl

theorem ym_blocker_is_middle :
    nodeAuditState { problem := .yangMills, stage := .middle } = .blockingFrontier := by
  rfl

theorem ns_blocker_is_middle :
    nodeAuditState { problem := .navierStokes, stage := .middle } = .blockingFrontier := by
  rfl

inductive FrontierStage where
  | input
  | constructor
  | validity
  | endpoint
  deriving DecidableEq, Repr

structure FrontierSubnode where
  problem : ProblemId
  stage : FrontierStage
  deriving DecidableEq, Repr

def primaryBlockingProblems : List ProblemId :=
  [.bsd, .hodge, .navierStokes, .riemann, .pVsNP, .yangMills, .beal]

def allFrontierSubnodes : List FrontierSubnode :=
  primaryBlockingProblems.flatMap (fun p =>
    [.input, .constructor, .validity, .endpoint].map (fun s =>
      { problem := p, stage := s }))

theorem frontier_subnode_count : allFrontierSubnodes.length = 28 := by
  native_decide

/-- Initial attack state: known inputs/endpoints are structurally represented;
    the constructor is the first unresolved mathematical motor. Validity is
    tested after a candidate constructor exists. -/
inductive FrontierSubnodeState where
  | represented
  | blocking
  | waitingOnConstructor
  deriving DecidableEq, Repr

def frontierSubnodeState (n : FrontierSubnode) : FrontierSubnodeState :=
  match n.stage with
  | .input => .represented
  | .constructor => .blocking
  | .validity => .waitingOnConstructor
  | .endpoint => .represented

def constructorBlockers : List FrontierSubnode :=
  allFrontierSubnodes.filter (fun n => frontierSubnodeState n = .blocking)

theorem constructor_blocker_count : constructorBlockers.length = 7 := by
  native_decide

end MCore.V22
