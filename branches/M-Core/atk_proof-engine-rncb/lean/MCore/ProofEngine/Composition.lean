import MCore.ProofEngine.Obligation

namespace MCore.ProofEngine

/-- A certified producer is an actual implication, not registry metadata. -/
structure Producer (P Q : Prop) where
  run : P → Q

def Producer.id (P : Prop) : Producer P P := ⟨fun h => h⟩

def Producer.comp {P Q R : Prop}
    (g : Producer Q R) (f : Producer P Q) : Producer P R :=
  ⟨fun h => g.run (f.run h)⟩

@[simp] theorem Producer.id_run (P : Prop) (h : P) :
    (Producer.id P).run h = h := rfl

theorem Producer.comp_apply {P Q R : Prop}
    (g : Producer Q R) (f : Producer P Q) (h : P) :
    (g.comp f).run h = g.run (f.run h) := rfl

end MCore.ProofEngine
