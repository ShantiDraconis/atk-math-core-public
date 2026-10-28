import ATK.BridgeReduction
import ATK.RiemannConcrete

/-!
# ATK — Teorema-mestre mínimo: só B3–B7 e obrigações do tamanho exato dos problemas

`ATK.BridgeReduction.closedMath_of_restantes` usa 6 pontes e as 8 obrigações originais. Duas
dessas obrigações são **mais fortes** que os problemas, e uma ponte ainda sobra:

* O1 (`UniformLogBound`, `D_N ≤ K/log(N+2)`) é mais forte que RH;
* O2 (`GCDLowerBoundSmallExponents`) só fecha Beal com a ponte FLT(p ≥ 5).

Este arquivo troca O1 por `D_N → 0` e O2 pela forma residual de Beal, e prova:

* `closedMath_minimo`: **5 pontes paramétricas (B3–B7) + obrigações mínimas ⇒ os 7
  enunciados** — sem B1 (provada) e sem B2 (dispensada pela forma residual);
* `minimas_de_originais`: as obrigações originais (com FLT(p ≥ 5)) implicam as mínimas, então
  o novo enunciado é estritamente mais fraco nas hipóteses;
* as obrigações mínimas têm o tamanho exato dos problemas: `beal_obrigacao_iff` (⟺ Beal),
  `rh_obrigacao_suficiente` (⇒ RH; a volta é a direção de necessidade de Báez-Duarte, publicada
  e não formalizada), `pnp_obrigacao_iff`, `hodge_obrigacao_iff`, `bsd_obrigacao_iff` (⟺ o
  enunciado, dada a ponte).

Fechar `CLOSED_MATH` passa a significar exatamente resolver os problemas (e formalizar B3–B7 e
as ligações L1–L5) — nada além disso. **CLOSED_MATH continua false.**
-/

namespace ATK.ObrigacoesMinimas

open Filter Topology ATK.ClosedMath ATK.BridgeReduction ATK.Conditional.Riemann

/-- As pontes que o teorema-mestre mínimo ainda usa: só as paramétricas B3–B7. -/
structure PontesParametricas (M : Models) : Prop where
  leray : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion M.ns
  cookLevin : ATK.Conditional.PvsNP.CookLevin M.cx M.sat
  lefschetz : ATK.Conditional.Hodge.KnownCases M.hodge
  grossZagierKolyvagin : ATK.Conditional.BSD.GrossZagierKolyvagin M.bsd
  osterwalderSchrader : ATK.Conditional.YangMills.OSReconstruction M.ym

/-- Obrigações mínimas: O1 enfraquecida para `D_N → 0`, O2 trocada pela forma residual de Beal. -/
structure Obrigacoes (M : Models) : Prop where
  rh : Tendsto DN atTop (𝓝 0)
  beal : ATK.BealFermatDescent.ExclusaoResidualDescida
  ns : ATK.Conditional.NavierStokes.EnstrophyAPrioriBound M.ns
  pnp : ATK.Conditional.PvsNP.SATNotInP M.cx M.sat
  hodge : ATK.Conditional.Hodge.MiddleCodimension M.hodge
  bsdRank : ATK.Conditional.BSD.RankOpen M.bsd
  bsdRefined : ATK.Conditional.BSD.RefinedOpen M.bsd
  ym : ATK.Conditional.YangMills.ConstructiveYM4D M.ym

/-- As 6 pontes restantes contêm as 5 paramétricas. -/
theorem parametricas_de_restantes {M : Models} (h : PontesRestantes M) : PontesParametricas M :=
  ⟨h.leray, h.cookLevin, h.lefschetz, h.grossZagierKolyvagin, h.osterwalderSchrader⟩

/-- As obrigações originais, com a ponte FLT(p ≥ 5), implicam as mínimas. -/
theorem minimas_de_originais {M : Models} (hF : FLTPrimosGeCinco) (hO : OpenObligations M) :
    Obrigacoes M :=
  ⟨DN_tendsto_zero hO.rh,
    ATK.BealFermatDescent.beal_iff_residual_descida.mp (beal_conditional_reduzido hF hO.beal),
    hO.ns, hO.pnp, hO.hodge, hO.bsdRank, hO.bsdRefined, hO.ym⟩

/-- **Teorema-mestre mínimo**: B3–B7 + obrigações mínimas ⇒ os 7 enunciados. -/
theorem closedMath_minimo {M : Models} (hB : PontesParametricas M) (hO : Obrigacoes M) :
    SevenStatements M :=
  ⟨ATK.BaezDuarteBridge.baezDuarteCriterion hO.rh,
    ATK.BealFermatDescent.beal_iff_residual_descida.mpr hO.beal,
    ATK.Conditional.NavierStokes.ns_conditional hB.leray hO.ns,
    ATK.Conditional.PvsNP.pvsnp_conditional hB.cookLevin hO.pnp,
    ATK.Conditional.Hodge.hodge_conditional hB.lefschetz hO.hodge,
    ATK.Conditional.BSD.bsd_conditional hB.grossZagierKolyvagin hO.bsdRank hO.bsdRefined,
    ATK.Conditional.YangMills.ym_conditional hB.osterwalderSchrader hO.ym⟩

/-- O teorema-mestre mínimo recupera o anterior. -/
theorem closedMath_of_restantes_min {M : Models} (hB : PontesRestantes M) (hO : OpenObligations M) :
    SevenStatements M :=
  closedMath_minimo (parametricas_de_restantes hB) (minimas_de_originais hB.fermatPrimos hO)

/-- O1 original é mais forte que a obrigação mínima de RH. -/
theorem O1_implica_minima : UniformLogBound → Tendsto DN atTop (𝓝 0) :=
  DN_tendsto_zero

/-- A obrigação mínima de RH basta para RH. -/
theorem rh_obrigacao_suficiente : Tendsto DN atTop (𝓝 0) → RiemannHypothesis :=
  ATK.BaezDuarteBridge.baezDuarteCriterion

/-- A obrigação mínima de RH é `inf_N D_N = 0`. -/
theorem rh_obrigacao_iff_iInf : Tendsto DN atTop (𝓝 0) ↔ ⨅ N, DN N = 0 :=
  ATK.RiemannConcrete.O1_iff_iInf_zero

/-- A obrigação mínima de Beal **é** Beal. -/
theorem beal_obrigacao_iff :
    ATK.BealFermatDescent.ExclusaoResidualDescida ↔ ATK.Conditional.Beal.BealConjecture :=
  ATK.BealFermatDescent.beal_iff_residual_descida.symm

/-- Dada Cook–Levin, a obrigação de P vs NP **é** `P ≠ NP`. -/
theorem pnp_obrigacao_iff {M : Models} (hB : ATK.Conditional.PvsNP.CookLevin M.cx M.sat) :
    ATK.Conditional.PvsNP.SATNotInP M.cx M.sat ↔ ATK.Conditional.PvsNP.PneNP M.cx :=
  (ATK.Conditional.PvsNP.pneNP_iff_sat_not_in_P hB).symm

/-- Dados os casos conhecidos, a obrigação de Hodge **é** a conjectura de Hodge do modelo. -/
theorem hodge_obrigacao_iff {M : Models} (hB : ATK.Conditional.Hodge.KnownCases M.hodge) :
    ATK.Conditional.Hodge.MiddleCodimension M.hodge ↔
      ATK.Conditional.Hodge.HodgeConjecture M.hodge := by
  constructor
  · exact ATK.Conditional.Hodge.hodge_conditional hB
  · intro h X hX p α _ _ hα
    exact h X hX p α hα

/-- Dado Gross–Zagier–Kolyvagin, as obrigações de BSD **são** BSD. -/
theorem bsd_obrigacao_iff {M : Models}
    (hB : ATK.Conditional.BSD.GrossZagierKolyvagin M.bsd) :
    (ATK.Conditional.BSD.RankOpen M.bsd ∧ ATK.Conditional.BSD.RefinedOpen M.bsd) ↔
      ATK.Conditional.BSD.BSDFull M.bsd := by
  constructor
  · rintro ⟨hR, hF⟩
    exact ATK.Conditional.BSD.bsd_conditional hB hR hF
  · rintro ⟨hRank, hRef⟩
    exact ⟨fun E _ => (hRank E).symm, hRef⟩

end ATK.ObrigacoesMinimas

#print axioms ATK.ObrigacoesMinimas.parametricas_de_restantes
#print axioms ATK.ObrigacoesMinimas.minimas_de_originais
#print axioms ATK.ObrigacoesMinimas.closedMath_minimo
#print axioms ATK.ObrigacoesMinimas.closedMath_of_restantes_min
#print axioms ATK.ObrigacoesMinimas.O1_implica_minima
#print axioms ATK.ObrigacoesMinimas.rh_obrigacao_suficiente
#print axioms ATK.ObrigacoesMinimas.rh_obrigacao_iff_iInf
#print axioms ATK.ObrigacoesMinimas.beal_obrigacao_iff
#print axioms ATK.ObrigacoesMinimas.pnp_obrigacao_iff
#print axioms ATK.ObrigacoesMinimas.hodge_obrigacao_iff
#print axioms ATK.ObrigacoesMinimas.bsd_obrigacao_iff
