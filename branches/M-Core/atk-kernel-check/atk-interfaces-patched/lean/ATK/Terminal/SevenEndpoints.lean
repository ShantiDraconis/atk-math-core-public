import ATK.Terminal.IndependentCore

/-! Explicit interfaces. These are CONDITIONAL theorem statements, not solutions. -/
namespace ATK.Terminal
structure Endpoint where
  concreteStatement : Prop
  materialObligation : Prop
  materialImpliesStatement : materialObligation → concreteStatement

/-- The concrete conclusion is proved only when the material obligation is discharged. -/
theorem close (e : Endpoint) (proof : e.materialObligation) :
    e.concreteStatement := e.materialImpliesStatement proof

-- Domain-specific endpoint definitions must be imported from the original
-- repositories. No arbitrary Prop may be substituted for a conjecture.
end ATK.Terminal
