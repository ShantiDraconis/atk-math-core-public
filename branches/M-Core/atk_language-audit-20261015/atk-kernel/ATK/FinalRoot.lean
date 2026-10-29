import ATK.ClosedMath
import ATK.BealCompleto
import ATK.ForaDaLinha
import ATK.ContracaoDN

/-!
# ATK — Raiz final (`FINAL_ROOT`) e verde universal (`UNIVERSAL_GREEN`): redução formal condicional

Fixa, no kernel, **tudo o que falta** para o verde universal — sem provar nada que não esteja
provado. Não há `sorry`, `admit` nem `axiom`: o que está aberto entra como **hipótese explícita**.

* `Raiz M` (= `SevenStatements M`): os sete enunciados. `VerdeFiel` (= RH ∧ Beal): a parte com
  enunciado **oficial**, sem modelo paramétrico.
* `PontesRestantes M`: as pontes publicadas que ainda não estão no kernel — **6 + B8**; a ponte B1
  (Báez-Duarte) já foi provada e saiu da lista (`pontes_de_restantes`).
* `Produtores M`: a matemática nova que falta, cada item na forma **mais fina** certificada:
  RH como `IsEmpty ZeroFora` (⟺ RH), Beal como `ExclusaoResidualFinal` (83,21 % dos expoentes),
  e os seis produtores paramétricos.
* **`raiz_de_produtores`**: pontes restantes + produtores ⇒ raiz final.
* **`produtores_fieis_de_raiz`**: a raiz implica os dois produtores fiéis **sem pontes** — não há
  atalho que pule a parte aberta.
* **`verde_fiel_iff`**: `VerdeFiel ⟺ IsEmpty ZeroFora ∧ ExclusaoResidualDescida`, **sem nenhuma
  hipótese**; `verde_fiel_iff_final`: sob B2 + B8, `⟺ IsEmpty ZeroFora ∧ ExclusaoResidualFinal`.
* `produtores_de_obrigacoes`: os produtores novos são **mais fracos** que as obrigações antigas.
* `rotas_RH`, `rota_contracao_morta`: as rotas suficientes para RH já certificadas e a refutada.
* **`ns_depende_do_modelo`, `pnp_depende_do_modelo`**: nos cinco enunciados paramétricos a
  verdade depende do modelo — o verde universal exige também as **ligações** L1–L5 (construir os
  modelos genuínos a partir dos objetos reais), ausentes da Mathlib.

O portão continua o mesmo: `UNIVERSAL_GREEN` e `FINAL_ROOT` só são calculados como verdes pelo
auditor (`scripts/universal_green.py`) quando existirem os teoremas terminais **sem hipóteses** de
`scripts/terminal_gates.json`. Hoje nenhum existe: `UNIVERSAL_GREEN = false`, `FINAL_ROOT = null`.
-/

namespace ATK.FinalRoot

open ATK.ClosedMath ATK.ForaDaLinha ATK.BealCompleto ATK.Conditional.Riemann
  ATK.RiemannConcrete ATK.BaezDuarteBridge ATK.ContracaoDN

/-- **Conjunção paramétrica dos sete enunciados**: não equivale, sem pontes adicionais, à conjunção dos problemas originais. -/
abbrev Raiz (M : Models) : Prop := SevenStatements M

/-- **Verde universal fiel**: a parte com enunciado oficial (RH ∧ Beal). -/
abbrev VerdeFiel : Prop := ClosedMathFaithful

/-- As pontes publicadas que ainda **não** estão provadas no kernel. -/
structure PontesRestantes (M : Models) : Prop where
  /-- B2: Último Teorema de Fermat (Wiles 1995). -/
  fermat : FermatLastTheorem
  /-- B8: Darmon–Merel (1997) para `Aⁿ + Bⁿ = C²` e `Aⁿ + Bⁿ = C³`. -/
  darmonMerel : ATK.BealDarmonMerel.DarmonMerel
  /-- B3: critério de explosão da enstrofia (Leray, Beale–Kato–Majda). -/
  leray : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion M.ns
  /-- B4: Cook–Levin. -/
  cookLevin : ATK.Conditional.PvsNP.CookLevin M.cx M.sat
  /-- B5: casos conhecidos de Hodge (Lefschetz (1,1)). -/
  lefschetz : ATK.Conditional.Hodge.KnownCases M.hodge
  /-- B6: Gross–Zagier–Kolyvagin. -/
  grossZagierKolyvagin : ATK.Conditional.BSD.GrossZagierKolyvagin M.bsd
  /-- B7: reconstrução de Osterwalder–Schrader. -/
  osterwalderSchrader : ATK.Conditional.YangMills.OSReconstruction M.ym

/-- Os **produtores terminais**: a matemática nova que falta. -/
structure Produtores (M : Models) : Prop where
  /-- RH: não existe zero fora da linha (⟺ RH). -/
  rh : IsEmpty ZeroFora
  /-- Beal: nenhuma solução coprima nos expoentes residuais (⟺ Beal sob B2 + B8). -/
  beal : ExclusaoResidualFinal
  ns : ATK.Conditional.NavierStokes.EnstrophyAPrioriBound M.ns
  pnp : ATK.Conditional.PvsNP.SATNotInP M.cx M.sat
  hodge : ATK.Conditional.Hodge.MiddleCodimension M.hodge
  bsdRank : ATK.Conditional.BSD.RankOpen M.bsd
  bsdRefined : ATK.Conditional.BSD.RefinedOpen M.bsd
  ym : ATK.Conditional.YangMills.ConstructiveYM4D M.ym

/-- A ponte B1 está provada: as pontes restantes reconstroem todas as pontes antigas. -/
theorem pontes_de_restantes {M : Models} (hP : PontesRestantes M) : Bridges M :=
  ⟨baezDuarteCriterion, hP.fermat, hP.leray, hP.cookLevin, hP.lefschetz,
    hP.grossZagierKolyvagin, hP.osterwalderSchrader⟩

/-- **Redução condicional**: pontes restantes + produtores ⇒ os sete enunciados parametrizados. -/
theorem raiz_de_produtores {M : Models} (hP : PontesRestantes M) (hO : Produtores M) : Raiz M :=
  ⟨riemann_iff_vazio.mpr hO.rh,
   beal_de_pontes_e_residual hP.fermat hP.darmonMerel hO.beal,
   ATK.Conditional.NavierStokes.ns_conditional hP.leray hO.ns,
   ATK.Conditional.PvsNP.pvsnp_conditional hP.cookLevin hO.pnp,
   ATK.Conditional.Hodge.hodge_conditional hP.lefschetz hO.hodge,
   ATK.Conditional.BSD.bsd_conditional hP.grossZagierKolyvagin hO.bsdRank hO.bsdRefined,
   ATK.Conditional.YangMills.ym_conditional hP.osterwalderSchrader hO.ym⟩

/-- A raiz final contém o verde fiel. -/
theorem raiz_implica_fiel {M : Models} (h : Raiz M) : VerdeFiel := ⟨h.1, h.2.1⟩

/-- **Sem atalho**: a raiz final implica os dois produtores fiéis, sem nenhuma ponte. -/
theorem produtores_fieis_de_raiz {M : Models} (h : Raiz M) :
    IsEmpty ZeroFora ∧ ExclusaoResidualFinal :=
  ⟨riemann_iff_vazio.mp h.1, residual_de_beal h.2.1⟩

/-- **Equivalência incondicional entre proposições (não prova dos seus membros)**:
`RH ∧ Beal ⟺ (não há zero fora da linha) ∧ (residual de descida de Beal)`. -/
theorem verde_fiel_iff :
    VerdeFiel ↔ IsEmpty ZeroFora ∧ ATK.BealFermatDescent.ExclusaoResidualDescida :=
  and_congr riemann_iff_vazio beal_incondicional

/-- **Verde fiel sob B2 + B8**: `RH ∧ Beal ⟺ IsEmpty ZeroFora ∧ ExclusaoResidualFinal`. -/
theorem verde_fiel_iff_final (hFLT : FermatLastTheorem) (hDM : ATK.BealDarmonMerel.DarmonMerel) :
    VerdeFiel ↔ IsEmpty ZeroFora ∧ ExclusaoResidualFinal :=
  and_congr riemann_iff_vazio (beal_teorema_completo hFLT hDM)

/-- Verde fiel a partir dos dois produtores fiéis e das pontes B2, B8. -/
theorem verde_fiel_de_produtores (hFLT : FermatLastTheorem)
    (hDM : ATK.BealDarmonMerel.DarmonMerel) (hRH : IsEmpty ZeroFora)
    (hB : ExclusaoResidualFinal) : VerdeFiel :=
  (verde_fiel_iff_final hFLT hDM).mpr ⟨hRH, hB⟩

/-- Os produtores novos são **mais fracos** que as obrigações antigas (sob B2). -/
theorem produtores_de_obrigacoes {M : Models} (hFLT : FermatLastTheorem)
    (hO : OpenObligations M) : Produtores M :=
  ⟨riemann_iff_vazio.mp (riemann_of_uniformLogBound hO.rh),
   residual_de_beal (ATK.Conditional.Beal.beal_conditional hFLT hO.beal),
   hO.ns, hO.pnp, hO.hodge, hO.bsdRank, hO.bsdRefined, hO.ym⟩

/-- **As rotas para RH já certificadas** (todas suficientes; a última é exata). -/
theorem rotas_RH :
    ((⨅ N, DN N) = 0 → RiemannHypothesis) ∧ (UniformLogBound → RiemannHypothesis) ∧
      (∀ q : ℝ, 0 ≤ q → q < 1 → ∀ N₀ : ℕ, (∀ N ≥ N₀, DN (2 * N) ≤ q * DN N) →
        RiemannHypothesis) ∧
      (RiemannHypothesis ↔ IsEmpty ZeroFora) :=
  ⟨riemann_of_iInf_zero, riemann_of_uniformLogBound,
    fun _ h0 h1 _ hc => riemann_de_contracao h0 h1 hc, riemann_iff_vazio⟩

/-- **A rota de contração está morta**: o piso logarítmico (teorema publicado) a exclui. -/
theorem rota_contracao_morta (h : PisoLog) :
    ¬ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, DN (2 * N) ≤ q * DN N :=
  contracao_impossivel h

/-- **Ligação L1 é necessária**: o enunciado paramétrico de Navier–Stokes é verdadeiro num modelo
e falso noutro — sem o modelo genuíno ele não diz nada sobre a equação. -/
theorem ns_depende_do_modelo :
    (∃ M : ATK.Conditional.NavierStokes.NSModel.{0},
        ATK.Conditional.NavierStokes.ClayStatementA M) ∧
      (∃ M : ATK.Conditional.NavierStokes.NSModel.{0},
        ¬ ATK.Conditional.NavierStokes.ClayStatementA M) := by
  refine ⟨ns_toy_model_vacuous, ?_⟩
  refine ⟨{ Data := Unit, Admissible := fun _ => True, SmoothOn := fun _ _ => True,
            GlobalSmooth := fun _ => False, enstrophy := fun _ _ => 0 }, ?_⟩
  intro h
  exact h () trivial

/-- **Ligação L2 é necessária**: `P ≠ NP` paramétrico é verdadeiro num modelo e falso noutro. -/
theorem pnp_depende_do_modelo :
    (∃ M : ATK.Conditional.PvsNP.ComplexityModel.{0}, ATK.Conditional.PvsNP.PneNP M) ∧
      (∃ M : ATK.Conditional.PvsNP.ComplexityModel.{0}, ¬ ATK.Conditional.PvsNP.PneNP M) := by
  refine ⟨pnp_toy_model_vacuous, ?_⟩
  refine ⟨{ Lang := Bool, P := Set.univ, NP := Set.univ, Red := fun _ _ => True,
            P_subset_NP := subset_refl _,
            P_closed_under_red := fun _ _ => Set.mem_univ _ }, ?_⟩
  intro h
  exact h rfl

end ATK.FinalRoot

#print axioms ATK.FinalRoot.pontes_de_restantes
#print axioms ATK.FinalRoot.raiz_de_produtores
#print axioms ATK.FinalRoot.raiz_implica_fiel
#print axioms ATK.FinalRoot.produtores_fieis_de_raiz
#print axioms ATK.FinalRoot.verde_fiel_iff
#print axioms ATK.FinalRoot.verde_fiel_iff_final
#print axioms ATK.FinalRoot.verde_fiel_de_produtores
#print axioms ATK.FinalRoot.produtores_de_obrigacoes
#print axioms ATK.FinalRoot.rotas_RH
#print axioms ATK.FinalRoot.rota_contracao_morta
#print axioms ATK.FinalRoot.ns_depende_do_modelo
#print axioms ATK.FinalRoot.pnp_depende_do_modelo
