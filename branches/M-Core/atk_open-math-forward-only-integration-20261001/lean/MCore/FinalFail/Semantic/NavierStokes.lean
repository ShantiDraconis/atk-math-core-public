import MCore.FinalFail.BoundaryAtoms

namespace MCore.FinalFail.Semantic

universe u v

/-- Active NS orientation from the accepted-premise program: a concrete
stabilizing component controls every flow admitted by the fixed ActualNS
predicate.  Flow/Stabilizer/ActualNS are parameters until the canonical PDE
model is bound. -/
structure NavierStokesStabilizationTarget
    (Flow : Type u)
    (Stabilizer : Type v)
    (ActualNS : Flow → Prop)
    (Stabilizes : Stabilizer → Flow → Prop) where
  component : Stabilizer
  controls : ∀ u, ActualNS u → Stabilizes component u

/-- Negative Navier--Stokes resolution target: admissible smooth data/forcing
for which no global smooth solution exists.  This is deliberately separate
from the positive stabilization target, because the official problem accepts
either orientation. -/
structure NavierStokesBreakdownTarget
    (Data : Type u)
    (Force : Type v)
    (Solution : Type*)
    (AdmissibleData : Data → Prop)
    (AdmissibleForce : Force → Prop)
    (GlobalSmoothSolution : Data → Force → Solution → Prop) where
  data : Data
  force : Force
  data_admissible : AdmissibleData data
  force_admissible : AdmissibleForce force
  no_global_smooth_solution :
    ¬ ∃ sol : Solution, GlobalSmoothSolution data force sol

/-- Fail-closed two-orientation target for Navier--Stokes.
The left branch is global stabilization/regularity; the right branch is a
genuine breakdown witness.  Neither branch is manufactured by this sum. -/
abbrev NavierStokesResolutionTarget
    (Flow : Type u)
    (Stabilizer : Type v)
    (ActualNS : Flow → Prop)
    (Stabilizes : Stabilizer → Flow → Prop)
    (Data : Type u)
    (Force : Type v)
    (Solution : Type*)
    (AdmissibleData : Data → Prop)
    (AdmissibleForce : Force → Prop)
    (GlobalSmoothSolution : Data → Force → Solution → Prop) :=
  Sum
    (NavierStokesStabilizationTarget Flow Stabilizer ActualNS Stabilizes)
    (NavierStokesBreakdownTarget
      Data Force Solution AdmissibleData AdmissibleForce GlobalSmoothSolution)

theorem ns_resolution_of_stabilization
    {Flow : Type u} {Stabilizer : Type v}
    {ActualNS : Flow → Prop} {Stabilizes : Stabilizer → Flow → Prop}
    {Data : Type u} {Force : Type v} {Solution : Type*}
    {AdmissibleData : Data → Prop} {AdmissibleForce : Force → Prop}
    {GlobalSmoothSolution : Data → Force → Solution → Prop}
    (h : NavierStokesStabilizationTarget Flow Stabilizer ActualNS Stabilizes) :
    NavierStokesResolutionTarget
      Flow Stabilizer ActualNS Stabilizes
      Data Force Solution AdmissibleData AdmissibleForce GlobalSmoothSolution :=
  Sum.inl h

theorem ns_resolution_of_breakdown
    {Flow : Type u} {Stabilizer : Type v}
    {ActualNS : Flow → Prop} {Stabilizes : Stabilizer → Flow → Prop}
    {Data : Type u} {Force : Type v} {Solution : Type*}
    {AdmissibleData : Data → Prop} {AdmissibleForce : Force → Prop}
    {GlobalSmoothSolution : Data → Force → Solution → Prop}
    (h :
      NavierStokesBreakdownTarget
        Data Force Solution AdmissibleData AdmissibleForce GlobalSmoothSolution) :
    NavierStokesResolutionTarget
      Flow Stabilizer ActualNS Stabilizes
      Data Force Solution AdmissibleData AdmissibleForce GlobalSmoothSolution :=
  Sum.inr h

abbrev NavierStokesInterpretation
    (Flow : Type u)
    (Stabilizer : Type v)
    (ActualNS : Flow → Prop)
    (Stabilizes : Stabilizer → Flow → Prop) :=
  BoundaryInterpretation .navierStokes
    (NavierStokesStabilizationTarget Flow Stabilizer ActualNS Stabilizes)

theorem ns_interpretation_iff_target
    (Flow : Type u)
    (Stabilizer : Type v)
    (ActualNS : Flow → Prop)
    (Stabilizes : Stabilizer → Flow → Prop) :
    Nonempty (NavierStokesInterpretation Flow Stabilizer ActualNS Stabilizes) ↔
      Nonempty (NavierStokesStabilizationTarget Flow Stabilizer ActualNS Stabilizes) :=
  nonempty_boundaryInterpretation_iff_nonempty_target

end MCore.FinalFail.Semantic
