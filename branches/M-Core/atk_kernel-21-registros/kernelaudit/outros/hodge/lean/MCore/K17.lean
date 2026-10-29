import MCore.K16

namespace MCore

/-- Empty finite cycle combination. -/
def CycleCombination.empty {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) (X : G.Variety) (p : Nat) :
    CycleCombination G M X p :=
  ⟨[]⟩

/-- Single-term finite cycle combination. -/
def CycleCombination.single {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) {X : G.Variety} (p : Nat)
    (a : M.Coeff) (z : G.CycleQ X p) :
    CycleCombination G M X p :=
  ⟨[(a, z)]⟩

/-- Evaluation of the empty combination is definitionally the supplied zero
    class. -/
theorem CycleCombination.eval_empty
    {G : GradedRationalHodgeData} (M : CycleSpanMechanics G)
    (X : G.Variety) (p : Nat) :
    (CycleCombination.empty M X p).eval M = M.zeroClass := by
  rfl

/-- Evaluation of a singleton is one scalar multiple plus the supplied zero
    class.  No additive identity law is silently assumed. -/
theorem CycleCombination.eval_single
    {G : GradedRationalHodgeData} (M : CycleSpanMechanics G)
    {X : G.Variety} (p : Nat) (a : M.Coeff) (z : G.CycleQ X p) :
    (CycleCombination.single M p a z).eval M =
      M.addClass (M.smul a (M.cycleClass p z)) M.zeroClass := by
  rfl

/-- The supplied zero class always has a concrete finite-span witness. -/
theorem zeroClass_in_concrete_span
    {G : GradedRationalHodgeData} (M : CycleSpanMechanics G)
    (X : G.Variety) (p : Nat) :
    InConcreteCycleSpan M (M.zeroClass : G.CohomologyQ X (2 * p)) := by
  exact ⟨CycleCombination.empty M X p, CycleCombination.eval_empty M X p⟩

/-- Algebraic laws deliberately separated from raw mechanics.  K17 does not
    assert these laws for an arbitrary interface; downstream stages may supply
    or formalize them without contaminating the finite-witness kernel. -/
structure CycleSpanLaws (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) : Prop where
  add_zero : ∀ {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)),
    M.addClass α M.zeroClass = α
  zero_add : ∀ {X : G.Variety} {p : Nat} (α : G.CohomologyQ X (2 * p)),
    M.addClass M.zeroClass α = α
  add_assoc : ∀ {X : G.Variety} {p : Nat}
    (α β γ : G.CohomologyQ X (2 * p)),
    M.addClass (M.addClass α β) γ = M.addClass α (M.addClass β γ)

/-- Under an explicitly supplied additive identity law, every scalar multiple
    of a cycle class has a singleton finite-span witness. -/
theorem smul_cycleClass_in_concrete_span
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (L : CycleSpanLaws G M) {X : G.Variety} (p : Nat)
    (a : M.Coeff) (z : G.CycleQ X p) :
    InConcreteCycleSpan M (M.smul a (M.cycleClass p z)) := by
  refine ⟨CycleCombination.single M p a z, ?_⟩
  simpa [CycleCombination.eval_single] using
    L.add_zero (M.smul a (M.cycleClass p z))

def k17_finite_mechanics_status : SignatureStatus := .provedProperty

def k17_additive_laws_status : SignatureStatus := .definitionInterface

def k17_hodge_surjectivity_status : SignatureStatus := .openBridge

theorem k17_surjectivity_still_open :
    k17_hodge_surjectivity_status = .openBridge := rfl

#print axioms CycleCombination.eval_empty
#print axioms CycleCombination.eval_single
#print axioms zeroClass_in_concrete_span
#print axioms smul_cycleClass_in_concrete_span

end MCore
