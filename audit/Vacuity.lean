/-!
# Auditoria de vacuidade — alvos semânticos parametrizados de `MCore.FinalFail.Semantic`

Cópias verbatim (só Lean core) de:
* `NavierStokesStabilizationTarget` (`Semantic/NavierStokes.lean`);
* `TerminalInhabitants` / `AllSeven` (`UniversalTerminalClosure.lean`).

Resultados certificados pelo kernel:
* o alvo NS é habitável sem matemática de fluidos enquanto `Stabilizes`/`ActualNS` forem
  parâmetros livres (`ns_target_trivial`, `ns_target_no_flows`) — ele só significa algo quando
  ligado ao modelo PDE canônico (por exemplo `ATK.Exact.ClayA`); estado **CONDICIONAL**;
* a agregação universal é exatamente a conjunção dos sete alvos (`allSeven_true`,
  `allSeven_false`): ela não produz nada sozinha — correto e não vacuoso, desde que cada alvo
  seja o enunciado oficial.
-/

namespace Audit.MathCore

universe u v

structure NavierStokesStabilizationTarget
    (Flow : Type u)
    (Stabilizer : Type v)
    (ActualNS : Flow → Prop)
    (Stabilizes : Stabilizer → Flow → Prop) where
  component : Stabilizer
  controls : ∀ u, ActualNS u → Stabilizes component u

/-- Com `Stabilizes` trivial o alvo NS vale para qualquer classe de fluxos. -/
theorem ns_target_trivial (Flow : Type u) (ActualNS : Flow → Prop) :
    Nonempty (NavierStokesStabilizationTarget Flow Unit ActualNS (fun _ _ => True)) :=
  ⟨⟨(), fun _ _ => trivial⟩⟩

/-- Com `ActualNS` vazio o alvo NS vale para qualquer noção de estabilização. -/
theorem ns_target_no_flows (Flow : Type u) (Stabilizer : Type v) (s : Stabilizer)
    (Stabilizes : Stabilizer → Flow → Prop) :
    Nonempty (NavierStokesStabilizationTarget Flow Stabilizer (fun _ => False) Stabilizes) :=
  ⟨⟨s, fun _ h => h.elim⟩⟩

/-- E com `Stabilizes` falso e um fluxo admitido ele falha: o conteúdo está nos parâmetros. -/
theorem ns_target_false (Flow : Type u) (Stabilizer : Type v) (f : Flow) :
    ¬ Nonempty (NavierStokesStabilizationTarget Flow Stabilizer (fun _ => True)
      (fun _ _ => False)) :=
  fun ⟨t⟩ => t.controls f trivial

def AllSeven
    (Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop) : Prop :=
  Riemann ∧ Beal ∧ PvsNP ∧ NavierStokes ∧ Hodge ∧ BSD ∧ YangMills

theorem allSeven_true : AllSeven True True True True True True True :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem allSeven_false (B P N H D Y : Prop) : ¬ AllSeven False B P N H D Y :=
  fun h => And.left h

end Audit.MathCore

#print axioms Audit.MathCore.ns_target_trivial
#print axioms Audit.MathCore.ns_target_no_flows
#print axioms Audit.MathCore.ns_target_false
#print axioms Audit.MathCore.allSeven_true
#print axioms Audit.MathCore.allSeven_false
