import Mathlib

/-!
ATK kernel-facing interfaces. These are conditional proof constructors.
No theorem here asserts an unsolved conjecture.
-/
namespace ATK.KernelInterfaces

structure Obligation (Target : Prop) where
  Material : Prop
  material : Material
  bridge : Material → Target

theorem discharge {Target : Prop} (o : Obligation Target) : Target :=
  o.bridge o.material

theorem seven_targets
    {RH NS YM BSD Hodge Beal PNP : Prop}
    (rh : Obligation RH) (ns : Obligation NS)
    (ym : Obligation YM) (bsd : Obligation BSD)
    (hodge : Obligation Hodge) (beal : Obligation Beal)
    (pnp : Obligation PNP) :
    RH ∧ NS ∧ YM ∧ BSD ∧ Hodge ∧ Beal ∧ PNP := by
  exact ⟨discharge rh, discharge ns, discharge ym,
    discharge bsd, discharge hodge, discharge beal, discharge pnp⟩

-- A concrete demonstration of the danger of unconstrained propositions:
theorem arbitrary_wrapper_is_inhabited :
    ∃ P : Prop, P := ⟨True, trivial⟩

-- A genuinely unconditional auxiliary inhabitant:
theorem finite_group_has_element (G : Type*) [Group G] : Nonempty G :=
  ⟨1⟩

end ATK.KernelInterfaces
