import MCore.FinalFail.MaterialAlgebra
import MCore.FinalFail.MaterialProducerCalculus

namespace MCore.FinalFail.MaterialDerived

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState
abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector
abbrev EState := MCore.FinalFail.MaterialCalculus.EvidenceState

/-!
# Derived material arithmetic and topology

Everything in this file is derived from the kernel-checked finite algebras in
MaterialAlgebra and MaterialProducerCalculus.

No theorem here constructs an inhabitant of RH, Beal, P vs NP, Navier--Stokes,
Hodge, BSD, or Yang--Mills. These are internal algebraic laws of the ATK
bookkeeping/material calculus.
-/

/-! ## 1. TriState arithmetic laws -/

namespace TriState

def code : TState → Nat
  | .seed => 0
  | .transit => 1
  | .manifest => 2

theorem code_lt_three (x : TState) : code x < 3 := by
  cases x <;> decide

theorem code_injective : Function.Injective code := by
  intro x y h
  cases x <;> cases y <;> simp [code] at h ⊢

theorem code_add_mod_three (x y : TState) :
    code (x + y) = (code x + code y) % 3 := by
  cases x <;> cases y <;> decide

theorem code_mul_mod_three (x y : TState) :
    code (x * y) = (code x * code y) % 3 := by
  cases x <;> cases y <;> decide

@[simp] theorem transit_add_transit :
    (.transit : TState) + .transit = .manifest := rfl

@[simp] theorem manifest_add_transit :
    (.manifest : TState) + .transit = .seed := rfl

@[simp] theorem manifest_add_manifest :
    (.manifest : TState) + .manifest = .transit := rfl

theorem characteristic_three (x : TState) :
    (x + x) + x = .seed := by
  cases x <;> rfl

theorem frobenius_three (x : TState) :
    (x * x) * x = x :=
  MCore.FinalFail.MaterialAlgebra.TriState.cubic_idempotence x

theorem mul_eq_zero_iff (x y : TState) :
    x * y = 0 ↔ x = 0 ∨ y = 0 := by
  cases x <;> cases y <;> decide

theorem mul_left_cancel_nonzero
    {a b c : TState} (ha : a ≠ 0)
    (h : a * b = a * c) :
    b = c := by
  have hsq : a * a = 1 :=
    MCore.FinalFail.MaterialAlgebra.TriState.nonzero_square_eq_one a ha
  have h2 : a * (a * b) = a * (a * c) :=
    congrArg (fun t => a * t) h
  rw [
    ← MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc,
    ← MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc,
    hsq,
    MCore.FinalFail.MaterialAlgebra.TriState.one_mul,
    MCore.FinalFail.MaterialAlgebra.TriState.one_mul
  ] at h2
  exact h2
theorem inv_eq_self (x : TState) :
    x⁻¹ = x := by
  cases x <;> rfl

theorem nonzero_mul_self
    (x : TState) (hx : x ≠ 0) :
    x * x = 1 :=
  MCore.FinalFail.MaterialAlgebra.TriState.nonzero_square_eq_one x hx

theorem rotate_eq_add_one (x : TState) :
    x.rotate = x + .transit := by
  cases x <;> rfl

theorem rotate_twice_eq_add_manifest (x : TState) :
    x.rotate.rotate = x + .manifest := by
  cases x <;> rfl

theorem rotate_add (x y : TState) :
    (x + y).rotate = x.rotate + y := by
  cases x <;> cases y <;> rfl

/-- The rotation orbit has exact period dividing three. -/
theorem orbit_three_step (x : TState) :
    x.rotate.rotate.rotate = x :=
  MCore.FinalFail.MaterialAlgebra.TriState.rotate_three x

end TriState

/-! ## 2. Seven-lane vector arithmetic -/

namespace SevenLaneVector

def neg (x : LaneVector) : LaneVector where
  riemann := -x.riemann
  beal := -x.beal
  pvsnp := -x.pvsnp
  navierStokes := -x.navierStokes
  hodge := -x.hodge
  bsd := -x.bsd
  yangMills := -x.yangMills

instance : Neg LaneVector where
  neg := neg

def smul (a : TState) (x : LaneVector) : LaneVector where
  riemann := a * x.riemann
  beal := a * x.beal
  pvsnp := a * x.pvsnp
  navierStokes := a * x.navierStokes
  hodge := a * x.hodge
  bsd := a * x.bsd
  yangMills := a * x.yangMills

@[simp] theorem add_neg (x : LaneVector) :
    x + (-x) = MCore.FinalFail.MaterialAlgebra.SevenLaneVector.zero := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x.riemann
  · exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x.beal
  · exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x.pvsnp
  · exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x.navierStokes
  · exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x.hodge
  · exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x.bsd
  · exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x.yangMills

theorem smul_add (a : TState) (x y : LaneVector) :
    smul a (x + y) = smul a x + smul a y := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · exact MCore.FinalFail.MaterialAlgebra.TriState.left_distrib a x.riemann y.riemann
  · exact MCore.FinalFail.MaterialAlgebra.TriState.left_distrib a x.beal y.beal
  · exact MCore.FinalFail.MaterialAlgebra.TriState.left_distrib a x.pvsnp y.pvsnp
  · exact MCore.FinalFail.MaterialAlgebra.TriState.left_distrib a x.navierStokes y.navierStokes
  · exact MCore.FinalFail.MaterialAlgebra.TriState.left_distrib a x.hodge y.hodge
  · exact MCore.FinalFail.MaterialAlgebra.TriState.left_distrib a x.bsd y.bsd
  · exact MCore.FinalFail.MaterialAlgebra.TriState.left_distrib a x.yangMills y.yangMills

theorem add_smul (a b : TState) (x : LaneVector) :
    smul (a + b) x = smul a x + smul b x := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · exact MCore.FinalFail.MaterialAlgebra.TriState.right_distrib a b x.riemann
  · exact MCore.FinalFail.MaterialAlgebra.TriState.right_distrib a b x.beal
  · exact MCore.FinalFail.MaterialAlgebra.TriState.right_distrib a b x.pvsnp
  · exact MCore.FinalFail.MaterialAlgebra.TriState.right_distrib a b x.navierStokes
  · exact MCore.FinalFail.MaterialAlgebra.TriState.right_distrib a b x.hodge
  · exact MCore.FinalFail.MaterialAlgebra.TriState.right_distrib a b x.bsd
  · exact MCore.FinalFail.MaterialAlgebra.TriState.right_distrib a b x.yangMills

theorem smul_assoc (a b : TState) (x : LaneVector) :
    smul (a * b) x = smul a (smul b x) := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · exact MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc a b x.riemann
  · exact MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc a b x.beal
  · exact MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc a b x.pvsnp
  · exact MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc a b x.navierStokes
  · exact MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc a b x.hodge
  · exact MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc a b x.bsd
  · exact MCore.FinalFail.MaterialAlgebra.TriState.mul_assoc a b x.yangMills

@[simp] theorem one_smul (x : LaneVector) :
    smul 1 x = x := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · exact MCore.FinalFail.MaterialAlgebra.TriState.one_mul x.riemann
  · exact MCore.FinalFail.MaterialAlgebra.TriState.one_mul x.beal
  · exact MCore.FinalFail.MaterialAlgebra.TriState.one_mul x.pvsnp
  · exact MCore.FinalFail.MaterialAlgebra.TriState.one_mul x.navierStokes
  · exact MCore.FinalFail.MaterialAlgebra.TriState.one_mul x.hodge
  · exact MCore.FinalFail.MaterialAlgebra.TriState.one_mul x.bsd
  · exact MCore.FinalFail.MaterialAlgebra.TriState.one_mul x.yangMills

@[simp] theorem zero_smul (x : LaneVector) :
    smul 0 x = MCore.FinalFail.MaterialAlgebra.SevenLaneVector.zero := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · change 0 * x.riemann = 0
    exact MCore.FinalFail.MaterialAlgebra.TriState.zero_mul x.riemann
  · change 0 * x.beal = 0
    exact MCore.FinalFail.MaterialAlgebra.TriState.zero_mul x.beal
  · change 0 * x.pvsnp = 0
    exact MCore.FinalFail.MaterialAlgebra.TriState.zero_mul x.pvsnp
  · change 0 * x.navierStokes = 0
    exact MCore.FinalFail.MaterialAlgebra.TriState.zero_mul x.navierStokes
  · change 0 * x.hodge = 0
    exact MCore.FinalFail.MaterialAlgebra.TriState.zero_mul x.hodge
  · change 0 * x.bsd = 0
    exact MCore.FinalFail.MaterialAlgebra.TriState.zero_mul x.bsd
  · change 0 * x.yangMills = 0
    exact MCore.FinalFail.MaterialAlgebra.TriState.zero_mul x.yangMills

theorem cubic_scalar_identity (a : TState) (x : LaneVector) :
    smul ((a * a) * a) x = smul a x := by
  rw [MCore.FinalFail.MaterialAlgebra.TriState.cubic_idempotence]

end SevenLaneVector

/-! ## 3. Evidence order, closure, interior, and boundary -/

namespace EvidenceState

theorem le_iff_code_le (a b : EState) :
    a ≤ b ↔
      MCore.FinalFail.MaterialCalculus.EvidenceState.code a ≤
      MCore.FinalFail.MaterialCalculus.EvidenceState.code b :=
  Iff.rfl

def closure (S : EState → Prop) : EState → Prop :=
  fun x => ∃ y, S y ∧
    MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
    MCore.FinalFail.MaterialCalculus.EvidenceState.code y

def interior (S : EState → Prop) : EState → Prop :=
  fun x => S x ∧
    ∀ y,
      MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
      MCore.FinalFail.MaterialCalculus.EvidenceState.code y →
      S y

def boundary (S : EState → Prop) : EState → Prop :=
  fun x => closure S x ∧ ¬ interior S x

theorem subset_closure (S : EState → Prop) :
    ∀ x, S x → closure S x := by
  intro x hx
  exact ⟨x, hx, le_rfl⟩

theorem interior_subset (S : EState → Prop) :
    ∀ x, interior S x → S x := by
  intro x hx
  change S x ∧
    (∀ y,
      MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
      MCore.FinalFail.MaterialCalculus.EvidenceState.code y →
      S y) at hx
  exact hx.1

theorem closure_monotone
    {S T : EState → Prop}
    (hST : ∀ x, S x → T x) :
    ∀ x, closure S x → closure T x := by
  intro x hx
  change ∃ y, S y ∧
    MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
    MCore.FinalFail.MaterialCalculus.EvidenceState.code y at hx
  change ∃ y, T y ∧
    MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
    MCore.FinalFail.MaterialCalculus.EvidenceState.code y
  rcases hx with ⟨y, hy, hxy⟩
  exact ⟨y, hST y hy, hxy⟩

theorem interior_monotone
    {S T : EState → Prop}
    (hST : ∀ x, S x → T x) :
    ∀ x, interior S x → interior T x := by
  intro x hx
  change S x ∧
    (∀ y,
      MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
      MCore.FinalFail.MaterialCalculus.EvidenceState.code y →
      S y) at hx
  change T x ∧
    (∀ y,
      MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
      MCore.FinalFail.MaterialCalculus.EvidenceState.code y →
      T y)
  refine ⟨hST x hx.1, ?_⟩
  intro y hxy
  exact hST y (hx.2 y hxy)

theorem closure_idempotent (S : EState → Prop) :
    ∀ x, closure (closure S) x ↔ closure S x := by
  intro x
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    exact ⟨z, hz, le_trans hxy hyz⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, ⟨y, hy, le_rfl⟩, hxy⟩

theorem interior_idempotent (S : EState → Prop) :
    ∀ x, interior (interior S) x ↔ interior S x := by
  intro x
  constructor
  · intro hx
    exact interior_subset (interior S) x hx
  · intro hx
    change S x ∧
      (∀ y,
        MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
        MCore.FinalFail.MaterialCalculus.EvidenceState.code y →
        S y) at hx
    change interior S x ∧
      (∀ y,
        MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
        MCore.FinalFail.MaterialCalculus.EvidenceState.code y →
        interior S y)
    refine ⟨?_, ?_⟩
    · exact hx
    · intro y hxy
      change S y ∧
        (∀ z,
          MCore.FinalFail.MaterialCalculus.EvidenceState.code y ≤
          MCore.FinalFail.MaterialCalculus.EvidenceState.code z →
          S z)
      refine ⟨hx.2 y hxy, ?_⟩
      intro z hyz
      have hxz :
          MCore.FinalFail.MaterialCalculus.EvidenceState.code x ≤
            MCore.FinalFail.MaterialCalculus.EvidenceState.code z :=
        le_trans hxy hyz
      exact hx.2 z hxz

theorem proven_closure_all (x : EState) :
    closure
      MCore.FinalFail.MaterialCalculus.EvidenceState.ProvenNeighborhood x := by
  refine ⟨.proved, rfl, ?_⟩
  cases x <;> decide

theorem proven_interior_iff (x : EState) :
    interior
      MCore.FinalFail.MaterialCalculus.EvidenceState.ProvenNeighborhood x ↔
      x = .proved := by
  constructor
  · intro h
    exact interior_subset
      MCore.FinalFail.MaterialCalculus.EvidenceState.ProvenNeighborhood x h
  · intro hx
    subst x
    change
      (.proved : EState) = .proved ∧
      (∀ y : EState,
        MCore.FinalFail.MaterialCalculus.EvidenceState.code .proved ≤
          MCore.FinalFail.MaterialCalculus.EvidenceState.code y →
        y = .proved)
    refine ⟨rfl, ?_⟩
    intro y hy
    cases y <;>
      norm_num [MCore.FinalFail.MaterialCalculus.EvidenceState.code] at hy ⊢
theorem proven_boundary_iff_not_proved (x : EState) :
    boundary
      MCore.FinalFail.MaterialCalculus.EvidenceState.ProvenNeighborhood x ↔
      x ≠ .proved := by
  rw [boundary]
  constructor
  · intro h hx
    subst x
    exact h.2 ((proven_interior_iff .proved).2 rfl)
  · intro hx
    exact ⟨proven_closure_all x,
      fun hi => hx ((proven_interior_iff x).1 hi)⟩

/-- Telescoping law for two consecutive evidence derivatives. -/
theorem derivative_two_step
    (f : Nat → EState) (n : Nat) :
    MCore.FinalFail.MaterialCalculus.EvidenceState.derivative f n +
      MCore.FinalFail.MaterialCalculus.EvidenceState.derivative f (n + 1) =
    MCore.FinalFail.MaterialCalculus.EvidenceState.code (f (n + 2)) -
      MCore.FinalFail.MaterialCalculus.EvidenceState.code (f n) := by
  unfold MCore.FinalFail.MaterialCalculus.EvidenceState.derivative
  rw [show n + 1 + 1 = n + 2 by omega]
  ring

end EvidenceState

/-! ## 4. Producer/refuter polarity operators -/

def negateProducer {P : Prop}
    (p : MCore.FinalFail.MaterialCalculus.MaterialProducer P) :
    MCore.FinalFail.MaterialCalculus.MaterialRefuter (¬ P) :=
  ⟨fun hNot => hNot p.produce⟩

def negateRefuter {P : Prop}
    (r : MCore.FinalFail.MaterialCalculus.MaterialRefuter P) :
    MCore.FinalFail.MaterialCalculus.MaterialProducer (¬ P) :=
  ⟨r.refute⟩

theorem negate_refuter_producer_roundtrip
    {P : Prop}
    (r : MCore.FinalFail.MaterialCalculus.MaterialRefuter P) :
    (negateRefuter r).produce = r.refute :=
  rfl

def evidenceOfProducer {P : Prop}
    (_ : MCore.FinalFail.MaterialCalculus.MaterialProducer P) : EState :=
  .proved

def evidenceOfRefuter {P : Prop}
    (_ : MCore.FinalFail.MaterialCalculus.MaterialRefuter P) : EState :=
  .refuted

@[simp] theorem evidenceOfProducer_eq_proved
    {P : Prop}
    (p : MCore.FinalFail.MaterialCalculus.MaterialProducer P) :
    evidenceOfProducer p = .proved := rfl

@[simp] theorem evidenceOfRefuter_eq_refuted
    {P : Prop}
    (r : MCore.FinalFail.MaterialCalculus.MaterialRefuter P) :
    evidenceOfRefuter r = .refuted := rfl

#print axioms MCore.FinalFail.MaterialDerived.TriState.code_add_mod_three
#print axioms MCore.FinalFail.MaterialDerived.TriState.code_mul_mod_three
#print axioms MCore.FinalFail.MaterialDerived.TriState.mul_eq_zero_iff
#print axioms MCore.FinalFail.MaterialDerived.TriState.mul_left_cancel_nonzero
#print axioms MCore.FinalFail.MaterialDerived.TriState.characteristic_three
#print axioms MCore.FinalFail.MaterialDerived.TriState.rotate_eq_add_one
#print axioms MCore.FinalFail.MaterialDerived.SevenLaneVector.smul_add
#print axioms MCore.FinalFail.MaterialDerived.SevenLaneVector.add_smul
#print axioms MCore.FinalFail.MaterialDerived.EvidenceState.closure_idempotent
#print axioms MCore.FinalFail.MaterialDerived.EvidenceState.interior_idempotent
#print axioms MCore.FinalFail.MaterialDerived.EvidenceState.proven_boundary_iff_not_proved
#print axioms MCore.FinalFail.MaterialDerived.negateProducer

end MCore.FinalFail.MaterialDerived
