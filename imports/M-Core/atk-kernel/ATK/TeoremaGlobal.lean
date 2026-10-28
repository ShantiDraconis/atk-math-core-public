import ATK.ClosedMath
import ATK.BaezDuarteBridge
import ATK.BealFermatDescent

/-!
# ATK — Teorema Global (versão de integração), reduzido ao estado atual

Há duas versões do "Teorema Global ATK":

1. **Integração** — `(⋀ Hᵢ) ∧ (⋀ (Hᵢ → Tᵢ)) → ⋀ Tᵢ`. É lógica; está provada aqui
   (`integracao`) e, na forma concreta, em `ATK.ClosedMath.closedMath_of_obligations`.
2. **Terminal** — `⊢ ⋀ Tᵢ` sem hipóteses. **Não** está provada: exigiria as sete provas.
   O portão `ATK/ClosedMathGate.lean` continua ausente e `CLOSED_MATH = false`.

`integracao_sem_conteudo` mostra por que a versão 1 sozinha não certifica nada: ela vale também
quando todo `Tᵢ` é falso. O conteúdo está em **quais** `Hᵢ` sobram e quão fracas elas são.

**O que este arquivo acrescenta.** Com a ponte B1 provada (`ATK.BaezDuarteBridge`) e Beal reduzida
sem FLT (`ATK.BealFermatDescent`), o teorema-mestre perde **duas pontes** e as obrigações de RH e
Beal ficam mais fracas:

* `teorema_global`: `PontesRestantes M → ObrigacoesTerminais M → SevenStatements M`, com 5 pontes
  (antes 7);
* `global_oficial`: RH ∧ Beal (enunciados oficiais) a partir de `inf_N D_N = 0` e do residual de
  Beal, **sem nenhuma ponte**;
* `global_oficial_iff`: para Beal a obrigação é **exata** —
  `RH ∧ Beal ↔ RH ∧ ExclusaoResidualDescidaPairwise`;
* `rh_obrigacao_mais_fraca`: a antiga O1 (`UniformLogBound`) implica a nova (`inf_N D_N = 0`).
-/

namespace ATK.TeoremaGlobal

open ATK.ClosedMath ATK.Conditional.Riemann

/-- **Versão 1 (integração)**, forma abstrata: `(∀ i, Hᵢ) → (∀ i, Hᵢ → Tᵢ) → ∀ i, Tᵢ`. -/
theorem integracao {ι : Sort*} {H T : ι → Prop} (hH : ∀ i, H i) (hHT : ∀ i, H i → T i) :
    ∀ i, T i :=
  fun i => hHT i (hH i)

/-- A integração **sozinha** não carrega informação: as implicações valem com todo `Tᵢ` falso. -/
theorem integracao_sem_conteudo :
    ∃ H T : Fin 7 → Prop, (∀ i, H i → T i) ∧ ¬ ∀ i, T i :=
  ⟨fun _ => False, fun _ => False, fun _ h => h, fun h => h 0⟩

/-- As pontes que **ainda** faltam formalizar (5; B1 e FLT já não são necessárias). -/
structure PontesRestantes (M : Models) : Prop where
  leray : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion M.ns
  cookLevin : ATK.Conditional.PvsNP.CookLevin M.cx M.sat
  lefschetz : ATK.Conditional.Hodge.KnownCases M.hodge
  grossZagierKolyvagin : ATK.Conditional.BSD.GrossZagierKolyvagin M.bsd
  osterwalderSchrader : ATK.Conditional.YangMills.OSReconstruction M.ym

/-- As obrigações terminais na forma mais fraca hoje certificada. -/
structure ObrigacoesTerminais (M : Models) : Prop where
  rh : ⨅ N, DN N = 0
  beal : ATK.BealFermatDescent.ExclusaoResidualDescidaPairwise
  ns : ATK.Conditional.NavierStokes.EnstrophyAPrioriBound M.ns
  pnp : ATK.Conditional.PvsNP.SATNotInP M.cx M.sat
  hodge : ATK.Conditional.Hodge.MiddleCodimension M.hodge
  bsdRank : ATK.Conditional.BSD.RankOpen M.bsd
  bsdRefined : ATK.Conditional.BSD.RefinedOpen M.bsd
  ym : ATK.Conditional.YangMills.ConstructiveYM4D M.ym

/-- **Teorema Global (integração), reduzido**: 5 pontes + obrigações terminais ⇒ os 7 enunciados. -/
theorem teorema_global {M : Models} (hB : PontesRestantes M) (hO : ObrigacoesTerminais M) :
    SevenStatements M :=
  ⟨ATK.BaezDuarteBridge.riemann_of_iInf_zero hO.rh,
   ATK.BealFermatDescent.beal_iff_residual_descida_pairwise.mpr hO.beal,
   ATK.Conditional.NavierStokes.ns_conditional hB.leray hO.ns,
   ATK.Conditional.PvsNP.pvsnp_conditional hB.cookLevin hO.pnp,
   ATK.Conditional.Hodge.hodge_conditional hB.lefschetz hO.hodge,
   ATK.Conditional.BSD.bsd_conditional hB.grossZagierKolyvagin hO.bsdRank hO.bsdRefined,
   ATK.Conditional.YangMills.ym_conditional hB.osterwalderSchrader hO.ym⟩

/-- **Parte oficial (RH ∧ Beal) sem nenhuma ponte**. -/
theorem global_oficial (hRH : ⨅ N, DN N = 0)
    (hBeal : ATK.BealFermatDescent.ExclusaoResidualDescidaPairwise) : ClosedMathFaithful :=
  ⟨ATK.BaezDuarteBridge.riemann_of_iInf_zero hRH,
   ATK.BealFermatDescent.beal_iff_residual_descida_pairwise.mpr hBeal⟩

/-- Para Beal a obrigação é exata: `RH ∧ Beal ↔ RH ∧ residual`. -/
theorem global_oficial_iff :
    ClosedMathFaithful ↔
      RiemannHypothesis ∧ ATK.BealFermatDescent.ExclusaoResidualDescidaPairwise := by
  unfold ClosedMathFaithful
  rw [ATK.BealFermatDescent.beal_iff_residual_descida_pairwise]

/-- A antiga obrigação O1 (`UniformLogBound`) implica a nova (`inf_N D_N = 0`). -/
theorem rh_obrigacao_mais_fraca (h : UniformLogBound) : ⨅ N, DN N = 0 :=
  ATK.RiemannConcrete.O1_iff_iInf_zero.mp (DN_tendsto_zero h)

/-- O teorema-mestre antigo continua derivável: as obrigações antigas dão as novas (para RH) e
Beal sai pela ponte FLT antiga. -/
theorem teorema_global_de_antigo {M : Models} (hB : Bridges M) (hO : OpenObligations M) :
    SevenStatements M :=
  closedMath_of_obligations hB hO

end ATK.TeoremaGlobal

#print axioms ATK.TeoremaGlobal.integracao
#print axioms ATK.TeoremaGlobal.integracao_sem_conteudo
#print axioms ATK.TeoremaGlobal.teorema_global
#print axioms ATK.TeoremaGlobal.global_oficial
#print axioms ATK.TeoremaGlobal.global_oficial_iff
#print axioms ATK.TeoremaGlobal.rh_obrigacao_mais_fraca
#print axioms ATK.TeoremaGlobal.teorema_global_de_antigo
