import Mathlib

namespace MCore
namespace KernelTruncation

structure SearchNode where
  target : Prop
  depth : Nat

abbrev StrictlySmaller := SearchNode → SearchNode → Prop

structure MinimalBlocker
    (smaller : StrictlySmaller)
    (n : SearchNode) : Prop where
  no_smaller : ¬ ∃ m : SearchNode, smaller m n

structure SearchFixedPoint
    (smaller : StrictlySmaller)
    (n : SearchNode) : Prop where
  minimal : MinimalBlocker smaller n
  reopens_to_same : ∀ m : SearchNode, smaller m n → False

inductive ClosureStatus
  | materialWitness
  | materialCounterWitness
  | closedByTruncation
  | openResidual
  | inconsistency
  deriving DecidableEq, Repr

def truncateAtMinimalBlocker
    {smaller : StrictlySmaller}
    {n : SearchNode}
    (_h : SearchFixedPoint smaller n) : ClosureStatus :=
  .closedByTruncation

theorem truncateAtMinimalBlocker_is_closed
    {smaller : StrictlySmaller}
    {n : SearchNode}
    (h : SearchFixedPoint smaller n) :
    truncateAtMinimalBlocker h = .closedByTruncation := by
  rfl

structure MaterialExtractor
    (smaller : StrictlySmaller)
    (n : SearchNode) where
  extract : SearchFixedPoint smaller n → n.target

theorem target_closed_of_truncation_and_extractor
    {smaller : StrictlySmaller}
    {n : SearchNode}
    (E : MaterialExtractor smaller n)
    (h : SearchFixedPoint smaller n) :
    n.target :=
  E.extract h

structure TruncatedCertificate
    (smaller : StrictlySmaller)
    (n : SearchNode) where
  fixedPoint : SearchFixedPoint smaller n

theorem truncated_certificate_terminal
    {smaller : StrictlySmaller}
    {n : SearchNode}
    (C : TruncatedCertificate smaller n) :
    truncateAtMinimalBlocker C.fixedPoint = .closedByTruncation := by
  rfl

structure TruncationClaimsTarget
    (smaller : StrictlySmaller)
    (n : SearchNode) where
  fixedPoint : SearchFixedPoint smaller n
  truncation_implies_target : SearchFixedPoint smaller n → n.target

theorem truncation_claim_is_exactly_an_extractor
    {smaller : StrictlySmaller}
    {n : SearchNode}
    (C : TruncationClaimsTarget smaller n) :
    MaterialExtractor smaller n :=
  ⟨C.truncation_implies_target⟩

#print axioms MCore.KernelTruncation.truncateAtMinimalBlocker_is_closed
#print axioms MCore.KernelTruncation.target_closed_of_truncation_and_extractor
#print axioms MCore.KernelTruncation.truncated_certificate_terminal
#print axioms MCore.KernelTruncation.truncation_claim_is_exactly_an_extractor

end KernelTruncation
end MCore
