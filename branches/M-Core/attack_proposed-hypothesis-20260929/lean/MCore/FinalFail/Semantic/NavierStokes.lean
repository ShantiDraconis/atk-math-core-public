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
