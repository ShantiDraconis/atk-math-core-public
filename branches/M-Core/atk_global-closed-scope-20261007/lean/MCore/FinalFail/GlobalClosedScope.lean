import MCore.YangMills.A1.B60ConcretePhysicalAdapter

namespace MCore.FinalFail.ClosedScope

structure ClosedMathEntry : Type 1 where
  statement : Prop
  witness : statement

structure GlobalClosedScope : Type 1 where
  entries : List ClosedMathEntry

theorem entry_is_closed
    (C : GlobalClosedScope)
    (e : ClosedMathEntry)
    (_hmem : e ∈ C.entries) :
    e.statement := by
  exact e.witness

def GlobalClosedScopeCertificate (C : GlobalClosedScope) : Prop :=
  ∀ e, e ∈ C.entries → e.statement

theorem certify (C : GlobalClosedScope) :
    GlobalClosedScopeCertificate C := by
  intro e hmem
  exact entry_is_closed C e hmem

def cons
    (P : Prop)
    (hP : P)
    (C : GlobalClosedScope) :
    GlobalClosedScope :=
  ⟨⟨P, hP⟩ :: C.entries⟩

theorem certify_cons
    (P : Prop)
    (hP : P)
    (C : GlobalClosedScope) :
    GlobalClosedScopeCertificate (cons P hP C) :=
  certify _

/-!
The first concrete payload entry is deliberately the full universally
quantified conditional theorem already proved in the imported YM source.
It does NOT assert existence of B60ConcretePhysicalAdapter.
-/

open MCore.YangMills.A1

def YMConditionalClosedStatement : Prop :=
  ∀ {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G},
    B60ConcretePhysicalAdapter C F D H G O →
      ∃ gap : D.Scale, K14MassGap D H G gap

theorem ymConditionalClosedWitness : YMConditionalClosedStatement := by
  intro C F D H G O A
  exact b60_adapter_closes_conditional_chain A

def materializedClosedScope : GlobalClosedScope :=
  ⟨[⟨YMConditionalClosedStatement, ymConditionalClosedWitness⟩]⟩

theorem materializedClosedScope_certified :
    GlobalClosedScopeCertificate materializedClosedScope :=
  certify _

#print axioms MCore.FinalFail.ClosedScope.entry_is_closed
#print axioms MCore.FinalFail.ClosedScope.certify
#print axioms MCore.FinalFail.ClosedScope.certify_cons
#print axioms MCore.FinalFail.ClosedScope.ymConditionalClosedWitness
#print axioms MCore.FinalFail.ClosedScope.materializedClosedScope_certified

end MCore.FinalFail.ClosedScope
