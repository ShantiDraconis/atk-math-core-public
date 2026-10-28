import MCore.ProofEngine.CanonicalNode
namespace MCore.ProofEngine
inductive RetryDecision | retry | escalateAttackable | classifyResearch deriving DecidableEq, Repr
def retryDecision (attempt : Nat) : RetryDecision := if attempt < 3 then .retry else .escalateAttackable
theorem fourth_attempt_escalates : retryDecision 3 = .escalateAttackable := by rfl
end MCore.ProofEngine
