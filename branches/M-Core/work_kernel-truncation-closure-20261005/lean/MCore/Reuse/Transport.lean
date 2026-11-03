namespace MCore.Reuse

theorem nonempty_map {α β : Sort _} (f : α → β) :
    Nonempty α → Nonempty β := by
  intro h
  rcases h with ⟨a⟩
  exact ⟨f a⟩

theorem implication_comp {P Q R : Prop} (hPQ : P → Q) (hQR : Q → R) :
    P → R := by
  intro hP
  exact hQR (hPQ hP)

theorem iff_forward {P Q : Prop} (h : P ↔ Q) : P → Q :=
  h.mp

theorem iff_backward {P Q : Prop} (h : P ↔ Q) : Q → P :=
  h.mpr

end MCore.Reuse
