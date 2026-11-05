import MCore.FinalFail.GlobalPositiveMaterialFrontier

namespace MCore.FinalFail.MaterialCalculus

universe uL uF uS uV uC uZ uE uT

/-!
# Material producer calculus

This module is deliberately conservative.

It adds algebraic structure around terminal producers, refuters, evidence states,
discrete changes, and dependency topology. It never manufactures an inhabitant
of an external mathematical target.
-/

/-! ## 1. Typed material producers and refuters -/

structure MaterialProducer (P : Prop) where
  produce : P

structure MaterialRefuter (P : Prop) where
  refute : ¬ P

namespace MaterialProducer

def pure {P : Prop} (h : P) : MaterialProducer P :=
  ⟨h⟩

def map {P Q : Prop} (f : P → Q) (p : MaterialProducer P) :
    MaterialProducer Q :=
  ⟨f p.produce⟩

def tensor {P Q : Prop}
    (p : MaterialProducer P) (q : MaterialProducer Q) :
    MaterialProducer (P ∧ Q) :=
  ⟨p.produce, q.produce⟩

def left {P Q : Prop} (pq : MaterialProducer (P ∧ Q)) :
    MaterialProducer P :=
  ⟨pq.produce.1⟩

def right {P Q : Prop} (pq : MaterialProducer (P ∧ Q)) :
    MaterialProducer Q :=
  ⟨pq.produce.2⟩

def transportIff {P Q : Prop} (h : P ↔ Q) (p : MaterialProducer P) :
    MaterialProducer Q :=
  map h.mp p

theorem map_id {P : Prop} (p : MaterialProducer P) :
    map (fun h : P => h) p = p := by
  cases p
  rfl

theorem map_comp {P Q R : Prop}
    (f : P → Q) (g : Q → R) (p : MaterialProducer P) :
    map g (map f p) = map (fun h => g (f h)) p := by
  cases p
  rfl

theorem tensor_left {P Q : Prop}
    (p : MaterialProducer P) (q : MaterialProducer Q) :
    left (tensor p q) = p := by
  cases p
  cases q
  rfl

theorem tensor_right {P Q : Prop}
    (p : MaterialProducer P) (q : MaterialProducer Q) :
    right (tensor p q) = q := by
  cases p
  cases q
  rfl

end MaterialProducer

namespace MaterialRefuter

def pure {P : Prop} (h : ¬ P) : MaterialRefuter P :=
  ⟨h⟩

def contramap {P Q : Prop} (f : P → Q) (r : MaterialRefuter Q) :
    MaterialRefuter P :=
  ⟨fun hP => r.refute (f hP)⟩

def transportIff {P Q : Prop} (h : P ↔ Q) (r : MaterialRefuter P) :
    MaterialRefuter Q :=
  ⟨fun hQ => r.refute (h.mpr hQ)⟩

theorem contramap_id {P : Prop} (r : MaterialRefuter P) :
    contramap (fun h : P => h) r = r := by
  cases r
  rfl

end MaterialRefuter

theorem producer_refuter_incompatible {P : Prop}
    (p : MaterialProducer P) (r : MaterialRefuter P) :
    False :=
  r.refute p.produce

/-! ## 2. Three-state evidence algebra

The state open is epistemic, not a third truth value. The operations below
describe conservative evidence propagation for conjunction and disjunction.
-/

inductive EvidenceState where
  | refuted
  | open
  | proved
  deriving DecidableEq, Repr

namespace EvidenceState

def code : EvidenceState → Int
  | .refuted => -1
  | .open => 0
  | .proved => 1

def dual : EvidenceState → EvidenceState
  | .refuted => .proved
  | .open => .open
  | .proved => .refuted

def conj : EvidenceState → EvidenceState → EvidenceState
  | .refuted, _ => .refuted
  | _, .refuted => .refuted
  | .proved, .proved => .proved
  | _, _ => .open

def disj : EvidenceState → EvidenceState → EvidenceState
  | .proved, _ => .proved
  | _, .proved => .proved
  | .refuted, .refuted => .refuted
  | _, _ => .open

instance : LE EvidenceState where
  le a b := code a ≤ code b

theorem dual_involutive (a : EvidenceState) :
    dual (dual a) = a := by
  cases a <;> rfl

theorem code_dual (a : EvidenceState) :
    code (dual a) = - code a := by
  cases a <;> norm_num [dual, code]

theorem conj_comm (a b : EvidenceState) :
    conj a b = conj b a := by
  cases a <;> cases b <;> rfl

theorem conj_assoc (a b c : EvidenceState) :
    conj (conj a b) c = conj a (conj b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem conj_idem (a : EvidenceState) :
    conj a a = a := by
  cases a <;> rfl

theorem disj_comm (a b : EvidenceState) :
    disj a b = disj b a := by
  cases a <;> cases b <;> rfl

theorem disj_assoc (a b c : EvidenceState) :
    disj (disj a b) c = disj a (disj b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem disj_idem (a : EvidenceState) :
    disj a a = a := by
  cases a <;> rfl

theorem deMorgan_conj (a b : EvidenceState) :
    dual (conj a b) = disj (dual a) (dual b) := by
  cases a <;> cases b <;> rfl

theorem deMorgan_disj (a b : EvidenceState) :
    dual (disj a b) = conj (dual a) (dual b) := by
  cases a <;> cases b <;> rfl

theorem conj_proved_iff (a b : EvidenceState) :
    conj a b = .proved ↔ a = .proved ∧ b = .proved := by
  cases a <;> cases b <;> simp [conj]

theorem disj_refuted_iff (a b : EvidenceState) :
    disj a b = .refuted ↔ a = .refuted ∧ b = .refuted := by
  cases a <;> cases b <;> simp [disj]

/-! ## 3. Evidence arithmetic and discrete derivatives -/

def derivative (f : Nat → EvidenceState) (n : Nat) : Int :=
  code (f (n + 1)) - code (f n)

theorem code_bounds (a : EvidenceState) :
    -1 ≤ code a ∧ code a ≤ 1 := by
  cases a <;> norm_num [code]

theorem derivative_bounds (f : Nat → EvidenceState) (n : Nat) :
    -2 ≤ derivative f n ∧ derivative f n ≤ 2 := by
  unfold derivative
  have h1 := code_bounds (f (n + 1))
  have h0 := code_bounds (f n)
  omega

theorem derivative_eq_zero_iff (f : Nat → EvidenceState) (n : Nat) :
    derivative f n = 0 ↔ code (f (n + 1)) = code (f n) := by
  unfold derivative
  omega

theorem code_injective : Function.Injective code := by
  intro a b h
  cases a <;> cases b <;> simp [code] at h ⊢

theorem derivative_eq_zero_iff_state_stable
    (f : Nat → EvidenceState) (n : Nat) :
    derivative f n = 0 ↔ f (n + 1) = f n := by
  constructor
  · intro h
    apply code_injective
    exact (derivative_eq_zero_iff f n).mp h
  · intro h
    rw [h]
    simp [derivative]

/-! ## 4. Dependency topology -/

def IsEvidenceOpen (U : EvidenceState → Prop) : Prop :=
  ∀ ⦃a b⦄, U a → code a ≤ code b → U b

theorem evidenceOpen_univ :
    IsEvidenceOpen (fun _ => True) := by
  intro a b ha hab
  trivial

theorem evidenceOpen_inter
    {U V : EvidenceState → Prop}
    (hU : IsEvidenceOpen U) (hV : IsEvidenceOpen V) :
    IsEvidenceOpen (fun x => U x ∧ V x) := by
  intro a b h hab
  exact ⟨hU h.1 hab, hV h.2 hab⟩

theorem evidenceOpen_union
    {U V : EvidenceState → Prop}
    (hU : IsEvidenceOpen U) (hV : IsEvidenceOpen V) :
    IsEvidenceOpen (fun x => U x ∨ V x) := by
  intro a b h hab
  rcases h with h | h
  · exact Or.inl (hU h hab)
  · exact Or.inr (hV h hab)

def ProvenNeighborhood : EvidenceState → Prop :=
  fun s => s = .proved

theorem provenNeighborhood_open :
    IsEvidenceOpen ProvenNeighborhood := by
  intro a b ha hab
  subst a
  cases b <;> simp [ProvenNeighborhood, code] at hab ⊢

/-! ## 5. Seven-lane evidence vectors -/

structure SevenEvidenceVector where
  riemann : EvidenceState
  beal : EvidenceState
  pvsnp : EvidenceState
  navierStokes : EvidenceState
  hodge : EvidenceState
  bsd : EvidenceState
  yangMills : EvidenceState
  deriving Repr

namespace SevenEvidenceVector

def aggregate (v : SevenEvidenceVector) : EvidenceState :=
  EvidenceState.conj v.riemann <|
  EvidenceState.conj v.beal <|
  EvidenceState.conj v.pvsnp <|
  EvidenceState.conj v.navierStokes <|
  EvidenceState.conj v.hodge <|
  EvidenceState.conj v.bsd v.yangMills

theorem aggregate_proved_iff (v : SevenEvidenceVector) :
    aggregate v = .proved ↔
      v.riemann = .proved ∧
      v.beal = .proved ∧
      v.pvsnp = .proved ∧
      v.navierStokes = .proved ∧
      v.hodge = .proved ∧
      v.bsd = .proved ∧
      v.yangMills = .proved := by
  simp [aggregate, EvidenceState.conj_proved_iff]

def currentMaterialFrontier : SevenEvidenceVector :=
  {
    riemann := .open
    beal := .open
    pvsnp := .open
    navierStokes := .open
    hodge := .open
    bsd := .open
    yangMills := .open
  }

theorem currentMaterialFrontier_aggregate_open :
    currentMaterialFrontier.aggregate = .open := by
  rfl

end SevenEvidenceVector

/-! ## 6. Connection to the positive global root -/

open MCore.FinalFail.Semantic

def provedEvidenceVectorOfPositiveRoot
    {Language : Type uL}
    {InP InNP : Language → Prop}
    {SAT : Language}
    {Flow : Type uF}
    {Stabilizer : Type uS}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    {Variety : Type uV}
    {Class : Variety → Type uC}
    {Cycle : Variety → Type uZ}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    {Curve : Type uE}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    {Theory : Type uT}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (_ :
      GlobalPositiveMaterialRoot
        Language InP InNP SAT
        Flow Stabilizer ActualNS Stabilizes
        Variety Class Cycle SmoothProjective RationalHodge Realizes
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
        Theory Genuine4D OSReconstructs PositiveMassGap) :
    SevenEvidenceVector :=
  {
    riemann := .proved
    beal := .proved
    pvsnp := .proved
    navierStokes := .proved
    hodge := .proved
    bsd := .proved
    yangMills := .proved
  }

theorem positiveRoot_evidence_aggregate_proved
    {Language : Type uL}
    {InP InNP : Language → Prop}
    {SAT : Language}
    {Flow : Type uF}
    {Stabilizer : Type uS}
    {ActualNS : Flow → Prop}
    {Stabilizes : Stabilizer → Flow → Prop}
    {Variety : Type uV}
    {Class : Variety → Type uC}
    {Cycle : Variety → Type uZ}
    {SmoothProjective : Variety → Prop}
    {RationalHodge : {X : Variety} → Class X → Prop}
    {Realizes : {X : Variety} → Cycle X → Class X → Prop}
    {Curve : Type uE}
    {Realizable : Curve → Prop}
    {AnalyticOrder MordellWeilRank : Curve → Int}
    {RefinedFormula : Curve → Prop}
    {Theory : Type uT}
    {Genuine4D OSReconstructs PositiveMassGap : Theory → Prop}
    (G :
      GlobalPositiveMaterialRoot
        Language InP InNP SAT
        Flow Stabilizer ActualNS Stabilizes
        Variety Class Cycle SmoothProjective RationalHodge Realizes
        Curve Realizable AnalyticOrder MordellWeilRank RefinedFormula
        Theory Genuine4D OSReconstructs PositiveMassGap) :
    (provedEvidenceVectorOfPositiveRoot G).aggregate = .proved := by
  rfl

end MCore.FinalFail.MaterialCalculus
