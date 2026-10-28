import MCore.V21.ProblemEmbedding

namespace MCore.V22

inductive ProblemId where
  | bsd
  | hodge
  | navierStokes
  | riemann
  | pVsNP
  | yangMills
  | poincare
  | beal
  | kernel0
  | kernel1
  | kernel2
  | kernel3
  | kernel4
  deriving DecidableEq, Repr

def allProblems : List ProblemId :=
  [.bsd, .hodge, .navierStokes, .riemann, .pVsNP, .yangMills,
   .poincare, .beal, .kernel0, .kernel1, .kernel2, .kernel3, .kernel4]

theorem allProblems_count : allProblems.length = 13 := by rfl

inductive Stage where
  | start
  | middle
  | finish
  deriving DecidableEq, Repr

def allStages : List Stage := [.start, .middle, .finish]

theorem allStages_count : allStages.length = 3 := by rfl

structure Node where
  problem : ProblemId
  stage : Stage
  deriving DecidableEq, Repr

def allNodes : List Node :=
  allProblems.flatMap (fun p => allStages.map (fun s => { problem := p, stage := s }))

theorem allNodes_count : allNodes.length = 39 := by native_decide

end MCore.V22
