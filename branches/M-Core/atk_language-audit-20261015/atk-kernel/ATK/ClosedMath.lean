import ATK.Conditional

/-!
# ATK — Estrutura condicional para CLOSED_MATH (teorema-mestre, obrigações e firewall)

`CLOSED_MATH` = os 7 enunciados provados. Este arquivo NÃO os prova; ele fixa exatamente o
que falta:

  `closedMath_of_obligations : Bridges M → OpenObligations M → SevenStatements M`

* `Bridges` — 7 leis-ponte: teoremas publicados, ainda não formalizados na Mathlib.
* `OpenObligations` — 8 obrigações abertas (`OPEN_MATH`).
* Para os 5 enunciados paramétricos (NS, P vs NP, Hodge, BSD, YM) existe ainda a obrigação de
  LIGAÇÃO: construir o modelo `M` a partir dos objetos reais. Sem ela, `SevenStatements M` não diz
  nada — `ns_toy_model_vacuous` e `pnp_toy_model_vacuous` provam o enunciado em modelos de
  brinquedo, exatamente para mostrar isso.

O portão: `CLOSED_MATH` só vira `true` no auditor se existir `ATK/ClosedMathGate.lean` com
`theorem closed_math` SEM hipóteses, certificado (axiomas padrão, sem `sorry`/`axiom`), sobre os
modelos genuínos. Hoje esse arquivo não existe.
-/

namespace ATK.ClosedMath

/-- Os modelos dos 5 enunciados paramétricos (universos fixados em `Type`). -/
structure Models where
  ns : ATK.Conditional.NavierStokes.NSModel.{0}
  cx : ATK.Conditional.PvsNP.ComplexityModel.{0}
  sat : cx.Lang
  hodge : ATK.Conditional.Hodge.HodgeModel.{0, 0}
  bsd : ATK.Conditional.BSD.BSDModel.{0}
  ym : ATK.Conditional.YangMills.YMModel.{0, 0, 0}

/-- Conjunção de sete proposições (cinco dependem do modelo `M`); definir esta proposição não prova seus componentes. -/
def SevenStatements (M : Models) : Prop :=
  RiemannHypothesis ∧
  ATK.Conditional.Beal.BealConjecture ∧
  ATK.Conditional.NavierStokes.ClayStatementA M.ns ∧
  ATK.Conditional.PvsNP.PneNP M.cx ∧
  ATK.Conditional.Hodge.HodgeConjecture M.hodge ∧
  ATK.Conditional.BSD.BSDFull M.bsd ∧
  ATK.Conditional.YangMills.ClayYM M.ym

/-- As 7 leis-ponte (literatura publicada; obrigação: formalizar). -/
structure Bridges (M : Models) : Prop where
  baezDuarte : ATK.Conditional.Riemann.BaezDuarteCriterion
  fermat : FermatLastTheorem
  leray : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion M.ns
  cookLevin : ATK.Conditional.PvsNP.CookLevin M.cx M.sat
  lefschetz : ATK.Conditional.Hodge.KnownCases M.hodge
  grossZagierKolyvagin : ATK.Conditional.BSD.GrossZagierKolyvagin M.bsd
  osterwalderSchrader : ATK.Conditional.YangMills.OSReconstruction M.ym

/-- As 8 obrigações abertas (`OPEN_MATH`). -/
structure OpenObligations (M : Models) : Prop where
  rh : ATK.Conditional.Riemann.UniformLogBound
  beal : ATK.Conditional.Beal.GCDLowerBoundSmallExponents
  ns : ATK.Conditional.NavierStokes.EnstrophyAPrioriBound M.ns
  pnp : ATK.Conditional.PvsNP.SATNotInP M.cx M.sat
  hodge : ATK.Conditional.Hodge.MiddleCodimension M.hodge
  bsdRank : ATK.Conditional.BSD.RankOpen M.bsd
  bsdRefined : ATK.Conditional.BSD.RefinedOpen M.bsd
  ym : ATK.Conditional.YangMills.ConstructiveYM4D M.ym

/-- **Redução condicional**: pontes + obrigações abertas ⇒ conjunção paramétrica; as hipóteses não são descarregadas. -/
theorem closedMath_of_obligations {M : Models} (hB : Bridges M) (hO : OpenObligations M) :
    SevenStatements M :=
  ⟨ATK.Conditional.Riemann.riemann_conditional hB.baezDuarte hO.rh,
   ATK.Conditional.Beal.beal_conditional hB.fermat hO.beal,
   ATK.Conditional.NavierStokes.ns_conditional hB.leray hO.ns,
   ATK.Conditional.PvsNP.pvsnp_conditional hB.cookLevin hO.pnp,
   ATK.Conditional.Hodge.hodge_conditional hB.lefschetz hO.hodge,
   ATK.Conditional.BSD.bsd_conditional hB.grossZagierKolyvagin hO.bsdRank hO.bsdRefined,
   ATK.Conditional.YangMills.ym_conditional hB.osterwalderSchrader hO.ym⟩

/-- Parte com enunciado OFICIAL (sem modelo): RH ∧ Beal. -/
def ClosedMathFaithful : Prop :=
  RiemannHypothesis ∧ ATK.Conditional.Beal.BealConjecture

/-- Os dois enunciados oficiais a partir de 2 pontes + 2 obrigações abertas. -/
theorem closedMathFaithful_of_obligations
    (hBD : ATK.Conditional.Riemann.BaezDuarteCriterion) (hFLT : FermatLastTheorem)
    (hRH : ATK.Conditional.Riemann.UniformLogBound)
    (hBeal : ATK.Conditional.Beal.GCDLowerBoundSmallExponents) :
    ClosedMathFaithful :=
  ⟨ATK.Conditional.Riemann.riemann_conditional hBD hRH,
   ATK.Conditional.Beal.beal_conditional hFLT hBeal⟩

/-! ## Firewall: por que modelos de brinquedo não fecham nada -/

/-- Num modelo de brinquedo (`GlobalSmooth := True`) o enunciado de NS vale trivialmente.
Isto NÃO é Navier–Stokes; mostra só que um "CLOSED" sobre modelo paramétrico sem a
obrigação de ligação é vazio. -/
theorem ns_toy_model_vacuous :
    ∃ M : ATK.Conditional.NavierStokes.NSModel.{0},
      ATK.Conditional.NavierStokes.ClayStatementA M :=
  ⟨{ Data := Unit, Admissible := fun _ => True, SmoothOn := fun _ _ => True,
     GlobalSmooth := fun _ => True, enstrophy := fun _ _ => 0 },
   fun _ _ => trivial⟩

/-- Num modelo de brinquedo (P = ∅, NP = tudo) "P ≠ NP" vale trivialmente. Isto NÃO é
P vs NP; mostra só que o enunciado paramétrico precisa do modelo genuíno. -/
theorem pnp_toy_model_vacuous :
    ∃ M : ATK.Conditional.PvsNP.ComplexityModel.{0}, ATK.Conditional.PvsNP.PneNP M :=
  ⟨{ Lang := Bool, P := ∅, NP := Set.univ, Red := fun _ _ => False,
     P_subset_NP := Set.empty_subset _,
     P_closed_under_red := fun h _ => False.elim h },
   Set.empty_ne_univ⟩

end ATK.ClosedMath

#print axioms ATK.ClosedMath.closedMath_of_obligations
#print axioms ATK.ClosedMath.closedMathFaithful_of_obligations
#print axioms ATK.ClosedMath.ns_toy_model_vacuous
#print axioms ATK.ClosedMath.pnp_toy_model_vacuous
