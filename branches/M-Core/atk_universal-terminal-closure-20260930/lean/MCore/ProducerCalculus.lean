import MCore.UniversalTerminalClosure

namespace MCore.FinalProof

universe u v w

/--
A producer reduction is an explicit map from one witness type to another.
It is the only admissible way for an upstream construction to discharge a
downstream producer obligation in the universal terminal calculus.
-/
structure ProducerReduction (A : Type u) (B : Type v) where
  map : A → B

namespace ProducerReduction

def id (A : Type u) : ProducerReduction A A where
  map := fun a => a

def comp {A : Type u} {B : Type v} {C : Type w}
    (g : ProducerReduction B C)
    (f : ProducerReduction A B) :
    ProducerReduction A C where
  map := fun a => g.map (f.map a)

@[simp] theorem id_map (A : Type u) (a : A) :
    (id A).map a = a := rfl

@[simp] theorem comp_map {A : Type u} {B : Type v} {C : Type w}
    (g : ProducerReduction B C)
    (f : ProducerReduction A B)
    (a : A) :
    (comp g f).map a = g.map (f.map a) := rfl

theorem nonempty_forward {A : Type u} {B : Type v}
    (f : ProducerReduction A B)
    (h : Nonempty A) :
    Nonempty B := by
  rcases h with ⟨a⟩
  exact ⟨f.map a⟩

end ProducerReduction

/-- Bidirectional producer transport. This changes representation, not difficulty. -/
structure ProducerEquiv (A : Type u) (B : Type v) where
  forward : ProducerReduction A B
  backward : ProducerReduction B A

theorem producerEquiv_nonempty_iff {A : Type u} {B : Type v}
    (e : ProducerEquiv A B) :
    Nonempty A ↔ Nonempty B := by
  constructor
  · exact e.forward.nonempty_forward
  · exact e.backward.nonempty_forward

/--
A hypothesis wrapper is terminally neutral whenever it can be constructed
from and projected back to the wrapped producer.
-/
structure NeutralWrapper (A : Type u) (W : Type v) where
  wrap : A → W
  unwrap : W → A

theorem neutralWrapper_nonempty_iff {A : Type u} {W : Type v}
    (N : NeutralWrapper A W) :
    Nonempty W ↔ Nonempty A := by
  constructor
  · rintro ⟨w⟩
    exact ⟨N.unwrap w⟩
  · rintro ⟨a⟩
    exact ⟨N.wrap a⟩

/-- Product composition: two independent producer obligations require both inhabitants. -/
def productReductionLeft (A : Type u) (B : Type v) :
    ProducerReduction (A × B) A where
  map := Prod.fst

def productReductionRight (A : Type u) (B : Type v) :
    ProducerReduction (A × B) B where
  map := Prod.snd

theorem product_nonempty_iff {A : Type u} {B : Type v} :
    Nonempty (A × B) ↔ Nonempty A ∧ Nonempty B := by
  constructor
  · rintro ⟨⟨a, b⟩⟩
    exact ⟨⟨a⟩, ⟨b⟩⟩
  · rintro ⟨⟨a⟩, ⟨b⟩⟩
    exact ⟨(a, b)⟩

/-- A concrete producer reduction into a terminal lane closes that lane. -/
theorem TerminalLane.closed_of_upstream
    (L : TerminalLane)
    {A : Type u}
    (r : ProducerReduction A L.Producer)
    (hA : Nonempty A) :
    L.Closed := by
  exact r.nonempty_forward hA

/--
Reduction composition preserves terminal closure. This is the formal operator
behind source -> inhabitant -> terminal-certificate chains.
-/
theorem TerminalLane.target_of_reduction_chain
    (L : TerminalLane)
    {A : Type u} {B : Type v}
    (ab : ProducerReduction A B)
    (bp : ProducerReduction B L.Producer)
    (hA : Nonempty A) :
    L.Target := by
  apply L.target_of_closed
  exact (ProducerReduction.comp bp ab).nonempty_forward hA

/--
Seven-lane closure can be fed by one upstream producer family, provided each
lane has an explicit reduction from its upstream witness to its terminal
producer. No lane is discharged by naming or equivalence alone.
-/
theorem universal_closure_from_reductions
    (S : SevenLaneSystem)
    (Upstream : Fin 7 → Type u)
    (reduce : ∀ i : Fin 7, ProducerReduction (Upstream i) (S.lane i).Producer)
    (inhabited : ∀ i : Fin 7, Nonempty (Upstream i)) :
    S.FinalRoot := by
  apply universal_terminal_closure S
  intro i
  exact (reduce i).nonempty_forward (inhabited i)

/--
A conditional constructor alone is not terminal evidence. There is no
universal rule turning mere inhabitance of a function type A -> P into P:
the domain A may itself be uninhabited.
-/
theorem no_universal_conditional_promotion :
    ¬ (∀ (A : Type) (P : Prop), Nonempty (A → P) → P) := by
  intro h
  have hf : Nonempty (Empty → False) := by
    exact ⟨fun e => nomatch e⟩
  exact h Empty False hf

/-- The missing ingredient for a conditional constructor is exactly an inhabitant of its input type. -/
theorem conditional_constructor_closes
    {A : Type u} {P : Prop}
    (f : A → P)
    (hA : Nonempty A) :
    P := by
  rcases hA with ⟨a⟩
  exact f a
/--
Conservation law for proposition wrappers: an equivalence P <-> Q transports
inhabitance of their canonical wrappers in both directions and creates no
new proof of either proposition.
-/
theorem proposition_equivalence_conserves_wrapper
    (P Q : Prop)
    (e : P ↔ Q) :
    Nonempty (EquivalentWrapper P) ↔
      Nonempty (EquivalentWrapper Q) := by
  rw [equivalentWrapper_nonempty_iff, equivalentWrapper_nonempty_iff]
  exact e

#print axioms MCore.FinalProof.ProducerReduction.nonempty_forward
#print axioms MCore.FinalProof.producerEquiv_nonempty_iff
#print axioms MCore.FinalProof.neutralWrapper_nonempty_iff
#print axioms MCore.FinalProof.product_nonempty_iff
#print axioms MCore.FinalProof.TerminalLane.target_of_reduction_chain
#print axioms MCore.FinalProof.universal_closure_from_reductions
#print axioms MCore.FinalProof.no_universal_conditional_promotion
#print axioms MCore.FinalProof.conditional_constructor_closes
#print axioms MCore.FinalProof.proposition_equivalence_conserves_wrapper

end MCore.FinalProof
