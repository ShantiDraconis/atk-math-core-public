import MCore.V22.Operators

namespace MCore.V22.Tests

theorem node_count_is_39 : allNodes.length = 39 := allNodes_count

theorem relation_count_is_1521 : allDirectedNodePairs.length = 1521 :=
  allDirectedNodePairs_count

theorem open_open_classifies : classifyPair .open .open = .bothOpen := by rfl

theorem closed_open_classifies : classifyPair .provedTrue .open = .mixed := by rfl

theorem false_true_is_both_closed : classifyPair .provedFalse .provedTrue = .bothClosed := by rfl

theorem indeterminate_absorbs_left : classifyPair .indeterminate .provedTrue = .indeterminateCollision := by rfl

theorem indeterminate_absorbs_right : classifyPair .open .indeterminate = .indeterminateCollision := by rfl

#print axioms node_count_is_39
#print axioms relation_count_is_1521
#print axioms open_open_classifies
#print axioms closed_open_classifies
#print axioms false_true_is_both_closed
#print axioms indeterminate_absorbs_left
#print axioms indeterminate_absorbs_right

end MCore.V22.Tests
