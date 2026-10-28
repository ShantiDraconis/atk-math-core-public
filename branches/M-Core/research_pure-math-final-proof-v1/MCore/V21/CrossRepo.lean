import MCore.V21.ClosedChain

namespace MCore.V21

/-- Cross-repository material may be reused as a construction shape. It does
    not import the truth of another open conjecture. -/
structure OperatorTemplate (Input Output : Type*) where
  run : Input → Output

/-- If another conjectural statement is genuinely required, it remains an
    explicit hypothesis. This blocks A-closes-B/B-closes-A promotion. -/
structure ConditionalOperator
    (Hyp : Prop) (Input Output : Type*) where
  run : Hyp → Input → Output

def ConditionalOperator.map
    {Hyp : Prop} {A B C : Type*}
    (f : ConditionalOperator Hyp A B)
    (g : OperatorTemplate B C) :
    ConditionalOperator Hyp A C :=
  ⟨fun h a => g.run (f.run h a)⟩

def composeTemplates
    {A B C : Type*}
    (f : OperatorTemplate A B)
    (g : OperatorTemplate B C) :
    OperatorTemplate A C :=
  ⟨fun a => g.run (f.run a)⟩

end MCore.V21
