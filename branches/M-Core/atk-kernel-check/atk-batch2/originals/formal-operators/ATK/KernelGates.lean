/-! Generic kernel-checked assembly: this theorem never constructs missing material proofs. -/
namespace ATK
structure TerminalGate (Target : Prop) where
  Material : Prop
  inhabitant : Material
  bridge : Material → Target

def TerminalGate.close {Target : Prop} (g : TerminalGate Target) : Target :=
  g.bridge g.inhabitant

theorem close_seven
    {C1 C2 C3 C4 C5 C6 C7 : Prop}
    (g1 : TerminalGate C1) (g2 : TerminalGate C2)
    (g3 : TerminalGate C3) (g4 : TerminalGate C4)
    (g5 : TerminalGate C5) (g6 : TerminalGate C6)
    (g7 : TerminalGate C7) :
    C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ C6 ∧ C7 := by
  exact ⟨g1.close, g2.close, g3.close, g4.close,
         g5.close, g6.close, g7.close⟩
end ATK
