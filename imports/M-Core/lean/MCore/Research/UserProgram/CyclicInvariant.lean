import MCore.Research.UserProgram.C3Action

namespace MCore.Research.UserProgram

def CyclicInvariant {β : Type} (f : I3State → β) : Prop :=
  ∀ s, f s.next = f s

theorem cyclicInvariant_constant {β : Type} (b : β) :
    CyclicInvariant (fun _ : I3State => b) := by
  intro s
  rfl

theorem cyclicInvariant_all_equal {β : Type} {f : I3State → β}
    (h : CyclicInvariant f) :
    f .manifesto = f .travessia ∧
    f .travessia = f .semente := by
  constructor
  · simpa [I3State.next] using (h I3State.manifesto).symm
  · simpa [I3State.next] using (h I3State.travessia).symm

theorem cyclicInvariant_eq_manifesto {β : Type} {f : I3State → β}
    (h : CyclicInvariant f) (s : I3State) :
    f s = f .manifesto := by
  cases s
  · rfl
  · simpa [I3State.next] using (h I3State.manifesto).symm
  ·
    have h1 := h I3State.manifesto
    have h2 := h I3State.travessia
    simpa [I3State.next] using h2.symm.trans h1.symm

end MCore.Research.UserProgram
