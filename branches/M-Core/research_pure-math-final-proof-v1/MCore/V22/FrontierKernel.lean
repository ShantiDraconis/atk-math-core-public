import MCore.V22.FrontierRegistry

namespace MCore.V22

/-- Common logical shape of a still-open middle. Input is established data,
    Witness is the missing construction, and Valid states what makes it close
    the instance. -/
structure FrontierKernel where
  Input : Type
  Witness : Input → Type
  Valid : (x : Input) → Witness x → Prop

def FrontierKernel.InstanceClosed (K : FrontierKernel) (x : K.Input) : Prop :=
  ∃ w : K.Witness x, K.Valid x w

def FrontierKernel.GloballyClosed (K : FrontierKernel) : Prop :=
  ∀ x : K.Input, K.InstanceClosed x

structure FrontierConstructor (K : FrontierKernel) where
  build : (x : K.Input) → K.Witness x
  valid : ∀ x, K.Valid x (build x)

theorem constructor_closes_frontier
    {K : FrontierKernel}
    (C : FrontierConstructor K) :
    K.GloballyClosed := by
  intro x
  exact ⟨C.build x, C.valid x⟩

noncomputable def closed_frontier_to_constructor
    {K : FrontierKernel}
    (h : K.GloballyClosed) :
    FrontierConstructor K where
  build := fun x => Classical.choose (h x)
  valid := fun x => Classical.choose_spec (h x)

theorem frontier_constructor_iff_global
    {K : FrontierKernel} :
    Nonempty (FrontierConstructor K) ↔ K.GloballyClosed := by
  constructor
  · rintro ⟨C⟩
    exact constructor_closes_frontier C
  · intro h
    exact ⟨closed_frontier_to_constructor h⟩

#print axioms constructor_closes_frontier
#print axioms frontier_constructor_iff_global

end MCore.V22
