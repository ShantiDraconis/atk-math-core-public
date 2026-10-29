import MCore.K25

namespace MCore

/-- K26 records the reverse-engineered minimal cut.  Once a certified boundary
    is fixed, the remaining general Hodge statement is exactly the concrete
    algebraicity payload, by the already-proved K20 equivalence. -/
theorem k26_minimal_cut
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) :
    GradedRationalHodgeConjecture G ↔ ConcreteAlgebraicityPayload M :=
  hodge_iff_payload_at_boundary B

/-- A proposed descendant formulated as a proposition equivalent to the
    concrete algebraicity payload cannot reduce the mathematical frontier:
    under the boundary it is itself equivalent to Hodge. -/
theorem k26_equivalent_reformulation_is_circular
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (P : Prop)
    (hP : P ↔ ConcreteAlgebraicityPayload M) :
    P ↔ GradedRationalHodgeConjecture G := by
  calc
    P ↔ ConcreteAlgebraicityPayload M := hP
    _ ↔ GradedRationalHodgeConjecture G := (hodge_iff_payload_at_boundary B).symm

/-- Merely adding K25 model-realization evidence does not discharge the
    algebraicity cut.  Closure still requires an independent algebraicity
    obligation. -/
theorem k26_realization_does_not_remove_cut
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (model : RealizedConcreteModelObligation G M)
    (geometry : GeometryObligation G M)
    (algebraicity : AlgebraicityObligation G M) :
    GradedRationalHodgeConjecture G :=
  k25_closure_is_conditional model geometry algebraicity

/-- Status vocabulary local to the audit: this is metadata, not a mathematical
    proof object exported as evidence for Hodge. -/
inductive K26PathStatus where
  | usefulReduction
  | closedPath
  | refutedFormulation
  | terminalOpenMathematics
  deriving Repr, DecidableEq

structure K26MinimalCutFrontier where
  coefficientDescendants : K26PathStatus
  modelOnlyDescendants : K26PathStatus
  equivalentPayloadReformulations : K26PathStatus
  algebraicityCut : K26PathStatus
  hodge : SignatureStatus

/-- Reverse-DAG pruning result.  Coefficient/model-only descendants do not
    remove the algebraicity cut; equivalent payload renamings are circular.
    The general algebraicity cut remains terminal open mathematics. -/
def k26_frontier : K26MinimalCutFrontier :=
  { coefficientDescendants := .closedPath
    modelOnlyDescendants := .closedPath
    equivalentPayloadReformulations := .refutedFormulation
    algebraicityCut := .terminalOpenMathematics
    hodge := .openBridge }

theorem k26_coefficients_pruned :
    k26_frontier.coefficientDescendants = .closedPath := rfl

theorem k26_model_only_pruned :
    k26_frontier.modelOnlyDescendants = .closedPath := rfl

theorem k26_equivalent_payload_pruned :
    k26_frontier.equivalentPayloadReformulations = .refutedFormulation := rfl

theorem k26_algebraicity_terminal :
    k26_frontier.algebraicityCut = .terminalOpenMathematics := rfl

theorem k26_hodge_still_open : k26_frontier.hodge = .openBridge := rfl

def k26_reduction_status : SignatureStatus := .provedProperty

#print axioms k26_minimal_cut
#print axioms k26_equivalent_reformulation_is_circular
#print axioms k26_realization_does_not_remove_cut
#print axioms k26_coefficients_pruned
#print axioms k26_model_only_pruned
#print axioms k26_equivalent_payload_pruned
#print axioms k26_algebraicity_terminal
#print axioms k26_hodge_still_open

end MCore
