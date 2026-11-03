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

/-- Logical orientation of the selected semantic target.
A refutational lane witnesses failure of the positive conjecture rather than
establishing it. -/
inductive SemanticOrientation where
  | positive
  | refutational
  deriving DecidableEq, Repr

structure SemanticLane where
  problem : ProblemId
  target : String
  orientation : SemanticOrientation
  modelState : SemanticLaneState
  interpretationState : SemanticLaneState
  deriving Repr

/-- Seven semantic lanes are now explicit.  An `interpretationOpen` entry means
exactly that no unconditional classical inhabitant has been constructed. -/
def semanticLanes : List SemanticLane := [
  { problem := .riemann,
    target := "RiemannOffCriticalZero",
    orientation := .refutational,
    modelState := .concreteTargetBound,
    interpretationState := .interpretationOpen },
  { problem := .beal,
    target := "BealUniversalGCDTarget",
    orientation := .positive,
    modelState := .concreteTargetBound,
    interpretationState := .interpretationOpen },
  { problem := .pVsNP,
    target := "PvsNPSeparationTarget(official model)",
    orientation := .positive,
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .navierStokes,
    target := "NavierStokesStabilizationTarget(ActualNS model)",
    orientation := .positive,
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .hodge,
    target := "HodgeRealizationTarget(genuine geometry)",
    orientation := .positive,
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .bsd,
    target := "BSDRealizableTarget(genuine elliptic curves)",
    orientation := .positive,
    modelState := .canonicalModelBindingOpen,
    interpretationState := .interpretationOpen },
  { problem := .yangMills,
    target := "YangMills4DGapTarget(genuine 4D theory)",
    orientation := .positive,
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

def positiveOrientationCount : Nat :=
  semanticLanes.foldl
    (fun n lane =>
      if lane.orientation = .positive then n + 1 else n) 0

def refutationalOrientationCount : Nat :=
  semanticLanes.foldl
    (fun n lane =>
      if lane.orientation = .refutational then n + 1 else n) 0

theorem semanticLaneCount_eq_seven : semanticLaneCount = 7 := by
  decide

theorem concreteTargetBoundCount_eq_two : concreteTargetBoundCount = 2 := by
  decide

theorem classicalInterpretationCount_eq_zero :
    classicalInterpretationCount = 0 := by
  decide

theorem positiveOrientationCount_eq_six :
    positiveOrientationCount = 6 := by
  decide

theorem refutationalOrientationCount_eq_one :
    refutationalOrientationCount = 1 := by
  decide

end MCore.FinalFail.Semantic
