import MCore.K18

namespace MCore

/-- External geometry interface for facts about the cycle-class map that are
    intentionally not manufactured by the logical reduction chain. -/
structure CycleClassGeometryInterface (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) : Prop where
  cycleClass_isTypePP :
    ∀ {X : G.Variety} (p : Nat) (z : G.CycleQ X p),
      G.isTypePP p (M.cycleClass p z)

/-- Codimension-one algebraicity payload.  This is the p=1 slice only; K19
    does not generalize it to arbitrary p. -/
def CodimensionOneAlgebraicityPayload {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (α : G.CohomologyQ X (2 * 1)),
    G.isSmoothProjective X → G.isTypePP 1 α → InConcreteCycleSpan M α

/-- The full concrete payload mechanically implies its codimension-one slice. -/
theorem concretePayload_implies_codimensionOne
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (h : ConcreteAlgebraicityPayload M) :
    CodimensionOneAlgebraicityPayload M := by
  intro X α hsp hpp
  exact h X 1 α hsp hpp

/-- Cycle-class soundness follows only when the external geometry interface is
    explicitly supplied.  This theorem is conditional, not a proof that such
    an interface exists. -/
theorem geometryInterface_implies_cycleClassSoundness
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (E : CycleClassGeometryInterface G M) : CycleClassSoundness M := by
  intro X p z
  exact E.cycleClass_isTypePP p z

/-- K19 firewall: codimension-one evidence is deliberately weaker than the
    all-codimension concrete payload; no converse is asserted. -/
def k19_geometry_interface_status : SignatureStatus := .openBridge

def k19_codimension_one_status : SignatureStatus := .openBridge

def k19_full_algebraicity_status : SignatureStatus := .openBridge

def k19_reduction_status : SignatureStatus := .provedProperty

theorem k19_geometry_still_open :
    k19_geometry_interface_status = .openBridge := rfl

theorem k19_full_algebraicity_still_open :
    k19_full_algebraicity_status = .openBridge := rfl

#print axioms concretePayload_implies_codimensionOne
#print axioms geometryInterface_implies_cycleClassSoundness

end MCore
