import MCore.Core

namespace MCore.CertifiedFirewalls

/-- A concrete counterexample blocks universal promotion. -/
theorem counterexample_blocks_universal
    {α : Type} {P : α → Prop}
    (h : ∃ x, ¬ P x) :
    ¬ ∀ x, P x := by
  rintro hall
  rcases h with ⟨x, hx⟩
  exact hx (hall x)

/-- An existential witness does not by itself justify a universal claim. -/
theorem exists_and_counterexample_blocks_forall
    {α : Type} {P : α → Prop}
    (hex : ∃ x, P x)
    (hbad : ∃ x, ¬ P x) :
    (∃ x, P x) ∧ ¬ ∀ x, P x := by
  exact ⟨hex, counterexample_blocks_universal hbad⟩

/-- Generic quantifier-order countermodel:
pointwise upper bounds exist, but no one natural upper bound works uniformly. -/
theorem pointwise_does_not_imply_uniform_nat :
    (∀ n : Nat, ∃ k : Nat, n < k) ∧
    ¬ (∃ k : Nat, ∀ n : Nat, n < k) := by
  constructor
  · intro n
    exact ⟨n + 1, Nat.lt_succ_self n⟩
  · rintro ⟨k, hk⟩
    exact (Nat.lt_irrefl k) (hk k)

/-- A finite prefix can agree with a property while the property fails later. -/
theorem finite_prefix_does_not_imply_global_bool
    (N : Nat) :
    ∃ s : Nat → Bool,
      (∀ n, n ≤ N → s n = false) ∧
      ∃ n, s n = true := by
  let s : Nat → Bool := fun n => decide (N < n)
  refine ⟨s, ?_, N + 1, ?_⟩
  · intro n hn
    simp [s, Nat.not_lt_of_ge hn]
  · simp [s]

/-- A witness is promotable only when the semantic predicate travels with it. -/
structure VerifiedWitness (α : Type) (P : α → Prop) where
  witness : α
  verified : P witness

theorem verifiedWitness_nonempty
    {α : Type} {P : α → Prop}
    (w : VerifiedWitness α P) :
    ∃ x, P x :=
  ⟨w.witness, w.verified⟩

/-- Typed parameter use: a certified output carries an explicit relation to input. -/
structure VerifiedRelation (α β : Type) (R : α → β → Prop) where
  input : α
  output : β
  verified : R input output

theorem verifiedRelation_holds
    {α β : Type} {R : α → β → Prop}
    (v : VerifiedRelation α β R) :
    R v.input v.output :=
  v.verified

#print axioms MCore.CertifiedFirewalls.counterexample_blocks_universal
#print axioms MCore.CertifiedFirewalls.exists_and_counterexample_blocks_forall
#print axioms MCore.CertifiedFirewalls.pointwise_does_not_imply_uniform_nat
#print axioms MCore.CertifiedFirewalls.finite_prefix_does_not_imply_global_bool
#print axioms MCore.CertifiedFirewalls.verifiedWitness_nonempty
#print axioms MCore.CertifiedFirewalls.verifiedRelation_holds

end MCore.CertifiedFirewalls
