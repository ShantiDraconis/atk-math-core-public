import MCore.FinalFail.Semantic.Riemann
import MCore.FinalFail.Semantic.Beal
import MCore.FinalFail.Semantic.PvsNP
import MCore.FinalFail.Semantic.NavierStokes
import MCore.FinalFail.Semantic.Hodge
import MCore.FinalFail.Semantic.BSD
import MCore.FinalFail.Semantic.YangMills
import MCore.FinalFail.AcceptedSemanticActivation

namespace MCore.FinalFail.Semantic

inductive SemanticLaneState where
  | concreteTargetBound
  | canonicalModelBindingOpen
  | interpretationOpen
  deriving DecidableEq, Repr

structure SemanticLane where
  problem : ProblemId
  target : String
  modelState : SemanticLaneState
  interpretationState : SemanticLaneState
  deriving Repr

/-- Seven semantic lanes are now explicit.  An `interpretationOpen` entry means
exactly that no unconditional classical inhabitant has been constructed. -/
def semanticLanes : List SemanticLane := [
  { problem := .riemann,
    target := "RiemannOffCriticalZero",
    modelState := .concreteTargetBound,
    interpretationState := .interpretationOpen },
  { problem := .beal,
    target := "BealUniversalGCDTarget",
    modelState := .concreteTargetBound,
    interpretationState := .interpretationOpen },
  { problem := .pVsNP,
    target := "PvsNPSeparationTarget(official model)",
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .navierStokes,
    target := "NavierStokesStabilizationTarget(ActualNS model)",
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .hodge,
    target := "HodgeRealizationTarget(genuine geometry)",
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .bsd,
    target := "BSDRealizableTarget(genuine elliptic curves)",
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .yangMills,
    target := "YangMills4DGapTarget(genuine 4D theory)",
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen }
]

def semanticLaneCount : Nat := semanticLanes.length

def concreteTargetBoundCount : Nat :=
  semanticLanes.foldl
    (fun n lane =>
      if lane.modelState = .concreteTargetBound then n + 1 else n) 0

def classicalInterpretationCount : Nat :=
  semanticLanes.foldl
    (fun n lane =>
      if lane.interpretationState ≠ .interpretationOpen then n + 1 else n) 0

theorem semanticLaneCount_eq_seven : semanticLaneCount = 7 := by
  decide

theorem concreteTargetBoundCount_eq_two : concreteTargetBoundCount = 2 := by
  decide

theorem classicalInterpretationCount_eq_zero :
    classicalInterpretationCount = 0 := by
  decide

end MCore.FinalFail.Semantic
