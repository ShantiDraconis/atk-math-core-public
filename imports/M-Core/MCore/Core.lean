import Mathlib

namespace MCore

/-- Scientific status is explicit and never inferred from a filename. -/
inductive Status where
  | proved
  | conditional
  | definitionInterface
  | numericalEvidence
  | openProblem
  deriving DecidableEq, Repr

/-- Frozen initial data. The fields are abstract on purpose: adapters choose their own domains. -/
structure FrozenState (U IStar Nu Chi N Time : Type*) where
  u0 : U
  Istar0 : IStar
  nu0 : Nu
  chi0 : Chi
  N0 : N
  T0 : Time

/-- M0: a transformation preserves the designated frozen state exactly.
This is an interface predicate; it does not assert physical invariance. -/
def PreservesS0
    {U IStar Nu Chi N Time : Type*}
    (S0 : FrozenState U IStar Nu Chi N Time)
    (F : FrozenState U IStar Nu Chi N Time → FrozenState U IStar Nu Chi N Time) : Prop :=
  F S0 = S0

/-- M1: an admissible transformation carries its preservation obligation as data.
Concrete adapters must supply this proof; no physical invariance is inferred here. -/
structure AdmissibleTransform
    {U IStar Nu Chi N Time : Type*}
    (S0 : FrozenState U IStar Nu Chi N Time) where
  map : FrozenState U IStar Nu Chi N Time → FrozenState U IStar Nu Chi N Time
  preserves : PreservesS0 S0 map

/-- M2: every admissible transform preserves the designated frozen state by its interface contract. -/
theorem admissible_preserves_S0
    {U IStar Nu Chi N Time : Type*}
    {S0 : FrozenState U IStar Nu Chi N Time}
    (F : AdmissibleTransform S0) :
    F.map S0 = S0 :=
  F.preserves

/-- M-Core's only permitted downstream rule. -/
inductive DAGRule where
  | downstreamOfG1Only
  deriving DecidableEq, Repr

/-- The minimal core object. -/
structure Core (U IStar Nu Chi N Time : Type*) where
  S0 : FrozenState U IStar Nu Chi N Time
  dagRule : DAGRule := .downstreamOfG1Only

end MCore
