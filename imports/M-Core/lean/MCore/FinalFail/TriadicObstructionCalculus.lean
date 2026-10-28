namespace MCore.FinalFail

inductive Fin3 where
  | start | middle | finish
  deriving DecidableEq

structure ClosedTriad where
  Carrier : Type
  start : Carrier
  middle : Carrier
  finish : Carrier
  startClosed : Prop
  middleClosed : Prop
  finishClosed : Prop

namespace ClosedTriad

variable (T : ClosedTriad)

def site : Fin3 → T.Carrier
  | .start => T.start
  | .middle => T.middle
  | .finish => T.finish

def compressSite : Fin3 → Fin3
  | .start => .middle
  | .middle => .middle
  | .finish => .middle

theorem compression_meets_at_middle :
    compressSite .start = .middle ∧
    compressSite .middle = .middle ∧
    compressSite .finish = .middle := by
  exact ⟨rfl, rfl, rfl⟩

theorem compression_idempotent (x : Fin3) :
    compressSite (compressSite x) = compressSite x := by
  cases x <;> rfl

inductive Boundary where
  | towardStart | towardFinish
  deriving DecidableEq

def retractSite : Boundary → Fin3 → Fin3
  | .towardStart, .middle => .start
  | .towardStart, x => x
  | .towardFinish, .middle => .finish
  | .towardFinish, x => x

theorem middle_is_compression_fixed_and_retraction_branch :
    compressSite .middle = .middle ∧
    retractSite Boundary.towardStart .middle = .start ∧
    retractSite Boundary.towardFinish .middle = .finish := by
  exact ⟨rfl, rfl, rfl⟩

end ClosedTriad

structure RigidNucleus where
  Obstruction : Type
  closed : Obstruction → Prop

structure ObstructionPresentation (Endpoint : Prop) where
  nucleus : RigidNucleus
  obstruction : nucleus.Obstruction
  endpoint_iff_closed : Endpoint ↔ nucleus.closed obstruction

theorem endpoint_of_closed_obstruction {Endpoint : Prop}
    (P : ObstructionPresentation Endpoint)
    (h : P.nucleus.closed P.obstruction) : Endpoint :=
  P.endpoint_iff_closed.mpr h

theorem closed_obstruction_of_endpoint {Endpoint : Prop}
    (P : ObstructionPresentation Endpoint)
    (h : Endpoint) : P.nucleus.closed P.obstruction :=
  P.endpoint_iff_closed.mp h

structure Complexification where
  RealPart : Type
  ImagPart : Type
  ComplexObject : Type
  realPart : ComplexObject → RealPart
  imagPart : ComplexObject → ImagPart
  zeroR : RealPart
  zeroI : ImagPart
  zeroC : ComplexObject
  zero_iff_parts_zero :
    ∀ z, z = zeroC ↔ realPart z = zeroR ∧ imagPart z = zeroI

structure DecimalInterpretation where
  Meaning : Nat → Type
  inRange : ∀ n, n < 10 → Prop

end MCore.FinalFail
