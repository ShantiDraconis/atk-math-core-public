# Estado: CONDICIONAL — os sete problemas no formato da ponte Navier–Stokes

Auditoria de 13/10/2026 sobre o commit `b95238f` deste repositório. Este é o índice do programa:
cada linha aponta para o repositório público em que a ponte foi compilada no kernel.
**OPEN_MATH = true** para todos os sete problemas. Nada aqui é uma prova de qualquer um deles.

## 1. O formato (o estado em que o NS está)

Um problema está **CONDICIONAL** quando existem três peças:

1. **alvo exato** — uma declaração da Mathlib ou de `ATK/Exact.lean` com o enunciado oficial;
2. **hipótese H** — um `Prop` enunciado com precisão, sem campos livres que a tornem vazia;
3. **ponte** — teorema `H → alvo` compilado no kernel do Lean, só com `propext`,
   `Classical.choice` e `Quot.sound`.

A ponte **não** prova o alvo. Ela diz exatamente o que falta: provar H. Por isso cada linha da
tabela registra também o **estado de H**.

## 2. Tabela

| Problema | Alvo exato | Hipótese H | Ponte (kernel) | Estado de H | Repositório |
|---|---|---|---|---|---|
| NS (C) | `ATK.Exact.ClayC` | `FCBreakdownR3` (enunciado da OpenAI, Apache-2.0) | `ATK.NSBridge.clayC_of_fc` | **demonstrada por prova externa** (OpenAI): compila só com axiomas padrão e `atk_clayC_certified : ClayC` foi aceito pelo kernel no ambiente deles (13/10/2026) → (C) **FECHADO por prova externa** | `atk-navier-stokes-public` |
| NS (D) | `ATK.Exact.ClayD` | `FCBreakdownPeriodic` (OpenAI) | `ATK.NSBridgeD.clayD_of_fc` | **demonstrada por prova externa**: `atk_clayD_certified : ClayD` aceito pelo kernel no ambiente deles → (D) **FECHADO por prova externa** | `atk-navier-stokes-public` |
| NS (A)/(B) | `ClayA`, `ClayB` | — | — | **abertos**, sem ponte | `atk-navier-stokes-public` |
| Riemann | `RiemannHypothesis` (Mathlib) | `NoZerosRightOfHalf`: `ζ(s) ≠ 0` em `Re s > 1/2` | `ATK.RHBridge.rh_of_noZerosRightOfHalf` | **aberta**; equivalente ao alvo (`rh_iff_noZerosRightOfHalf`) | `atk-riemann-public` |
| P vs NP | `ATK.Exact.P_ne_NP` (TM2 da Mathlib) | `SAT ∈ NP ∧ G2.1(SAT)` | `ATK.PNPBridge.pne_np_of_H` | P01: teorema clássico **não formalizado**; G2.1 ⇔ `SAT ∉ P` (`g21_iff_not_inP`): **aberta** | `atk-p-vs-np-public` |
| Beal | `ATK.Exact.Beal` | `GCDLowerBoundProducer` (do programa) | `ATK.BealBridge.beal_of_producer` | **aberta**; equivalente ao alvo (`producer_iff_beal`) | `atk-beal-public` |
| BSD | `ATK.BSDBridge.BSDRank` — **novo**: forma oficial do Clay com `WeierstrassCurve.LSeries` da Mathlib | `AnalyticContinuation ∧ RankEquality` | `ATK.BSDBridge.bsd_of_H` | H1: **teorema publicado e aceito** (modularidade), não formalizado; H2: **aberta** | `atk-bsd-public` |
| Yang–Mills | **não enunciável** (sem QFT axiomática em `ℝ⁴` na Mathlib) | — | — | interface `YMClosure` **vacuosa** (kernel) | `atk-yang-mills-public` |
| Hodge | **não enunciável** (sem decomposição de Hodge nem classe de ciclo na Mathlib) | `ConcreteAlgebraicityPayload M` sobre `G` abstrato | `hodge_iff_concretePayload` (no programa) | condicional à construção do `G` real; o enunciado abstrato é independente (kernel) | `atk-hodge-public` |

Onde a tabela diz "equivalente ao alvo", a ponte é uma **reformulação**, não uma redução: provar H
é exatamente tão difícil quanto provar o alvo. Ela continua útil porque fixa o enunciado e liga a
rota do programa ao alvo oficial, sem hipóteses escondidas.

## 2b. Linhas de explosão (adaptação do NS a cada problema)

No NS a explosão (blow-up) fechou (C) e (D). Para cada problema a mesma forma foi escrita no
kernel: **testemunha de explosão** → **refutação** → **dicotomia** `alvo ↔ não há explosão`.
Fechar pela explosão = exibir a testemunha; fechar pelo lado regular = provar que ela não existe.

| Problema | Testemunha de explosão | Dicotomia (kernel) | Testemunha conhecida? |
|---|---|---|---|
| NS (C)/(D) | explosão com força | `clayC_of_fc`, `clayD_of_fc` | **sim** — prova da OpenAI; C e D verificados no kernel |
| NS (A)/(B) | `UnforcedBlowupR3`, `UnforcedBlowupTorus` | `clayA_iff_no_explosion`, `clayB_iff_no_explosion` | não |
| Riemann | `OffLineZero` (zero com `Re s > 1/2`) | `rh_iff_no_explosion` | não |
| P vs NP | `CollapseWitness` (decisor de SAT) ou `LowerBoundExplosion` (G2.1) | `explosion_dichotomy` | não |
| Beal | `PrimitiveSolution` (certificado finito) | `beal_iff_no_explosion`, `descent_iff_no_explosion` | não |
| BSD | `RankDiscrepancy` (ordem ≠ posto) | `bsd_iff_no_explosion` (dada H1) | não |
| Hodge | `HodgeExplosion G` (classe não algébrica) | `hodge_iff_no_explosion` (sobre `G`) | não (a versão inteira explode) |
| Yang–Mills | `GaplessWitness` (sem lacuna) | `producer_iff_no_explosion` (forma) | não enunciável |

## 2c. Linha de fechamento — CLOSED_MATH calculado pelo kernel

Terceira linha, no mesmo formato das outras duas: **alvo exato** → **certificado** (declaração sem
hipóteses, de tipo exatamente o alvo ou a sua negação) → **portão** (`closure_gate.py`: kernel +
axiomas padrão + controles) → **bandeira calculada**. A bandeira não é editável: só muda quando
o registro recebe uma declaração que o kernel aceita.

| Problema | CLOSED_MATH | Certificado aceito | Como pode chegar um certificado | Repositório |
|---|---|---|---|---|
| NS (C) | **true** | `atk_clayC_certified : ClayC` (ambiente externo) | ponte + prova da OpenAI — chegou | `atk-navier-stokes-public` |
| NS (D) | **true** | `atk_clayD_certified : ClayD` (ambiente externo) | ponte + prova da OpenAI — chegou | `atk-navier-stokes-public` |
| NS (A)/(B) | false | — | provar regularidade sem força, ou exibir `UnforcedBlowup*` | `atk-navier-stokes-public` |
| Riemann | false | — | provar `NoZerosRightOfHalf`, ou exibir `OffLineZero` | `atk-riemann-public` |
| P vs NP | false | — | provar `SATInNP` + G2.1, ou um decisor de SAT + Cook–Levin | `atk-p-vs-np-public` |
| Beal | false | — | provar `GCDLowerBoundProducer`/descida, ou exibir `PrimitiveSolution` | `atk-beal-public` |
| BSD | false | — | formalizar H1 e provar H2, ou exibir `RankDiscrepancy` | `atk-bsd-public` |
| Hodge | false (não enunciável) | — | primeiro a fundação (`G` geométrico) | `atk-hodge-public` |
| Yang–Mills | false (não enunciável) | — | primeiro a fundação (axiomas OS/Wightman + lacuna) | `atk-yang-mills-public` |

NS (C)/(D): portão rodado no ambiente externo (run `38387829506` em `atk-navier-stokes-public`).
Em todos os portões os controles passaram: decisão verdadeira de brinquedo aceita; `axiom`,
`sorry`, ponte sem H, explosão sem testemunha e `alvo ∨ ¬alvo` recusados.

## 3. Itens deste repositório — o que precisa ser arrumado

| # | Item | Por que é condicional | O que fechar |
|---|---|---|---|
| M1 | `FinalProofRegistry` / `GlobalOpenCut` registram os alvos terminais como `String` | O kernel não liga uma string a uma declaração: o registro pode divergir do Lean sem que nada falhe | Trocar as strings pelos `Prop` das pontes acima (H de cada linha) |
| M2 | Entrada NS: `ActualNSToSignedGainCore on genuine flow-derived EnstrophyData` | Desatualizada desde set/2026: (C)/(D) têm prova reivindicada por terceiros; o alvo do programa (estabilização/regularidade) é a pergunta sem força, (A)/(B) | Separar: NS-(C)/(D) CONDICIONAL à auditoria externa; NS-(A)/(B) ABERTO |
| M3 | `NavierStokesStabilizationTarget` (`Semantic/NavierStokes.lean`) | **Vacuidade certificada** (`audit/Vacuity.lean`): habitado com `Stabilizes` trivial (`ns_target_trivial`) ou com classe de fluxos vazia (`ns_target_no_flows`) | Ligar `Flow`, `ActualNS` e `Stabilizes` ao modelo PDE de `ATK/Exact.lean` (por exemplo, `ClayA`) |
| M4 | Entrada RH: `FiniteSpanApproximatesChi concreteGeneratorFamily` | Rota de Nyman–Beurling; a implicação "aproximação ⇒ sem zeros em `Re s > 1/2`" ainda não está no kernel | Formalizar essa implicação; ela fecha a cadeia com `rh_of_noZerosRightOfHalf` |
| M5 | Entrada BSD: "3 átomos" (domínio realizável + posto + coeficiente líder) | O enunciado oficial do Clay é a parte do posto, agora exata (`BSDRank`); o coeficiente líder é a forma refinada (não exigida pelo Clay) | Registrar `BSDRank` como alvo e `H_BSD` como hipótese |
| M6 | Entrada YM: `Nonempty (B60ConcretePhysicalAdapter …)` | Definição fora deste instantâneo; o `YMClosure` público é vacuoso | Repetir a auditoria de vacuidade em `B60ConcretePhysicalAdapter` |
| M7 | `TerminalInhabitants` / `AllSeven` | Corretos: a agregação é exatamente a conjunção (`allSeven_true`, `allSeven_false`) e não produz nada sozinha | Nenhum; só depende de cada componente ser o alvo exato |
| M8 | `accepted_not_RH_produces_semantic_inhabitant (hNotRH : ¬ RiemannHypothesis)` | Condicional por construção (hipótese ¬RH) — rotulado corretamente | Não contar como fechamento |
| M9 | Compilação | Instantâneo: importa `MCore.*` e `AxiomaticMillenium.*` ausentes aqui. `audit/Vacuity.lean` compila só com Lean core (workflow `vacuity-check`) | CI a partir dos commits de origem |

## 4. Condição para mudar de estado

CONDICIONAL → FECHADO somente quando H for demonstrada no kernel (ou, no caso do NS-(C), quando a
prova externa compilar e for aceita pelo portão), produzindo uma declaração de tipo **exatamente**
o alvo. Prêmio é outra questão: depende das regras de cada instituição (Clay: publicação
qualificada, dois anos, aceitação geral).

---

**English summary.** Index of the program in the "NS bridge" format: exact target + precisely
stated hypothesis H + kernel-checked bridge `H → target`. Bridges now exist for NS-(C), Riemann,
P vs NP, Beal and BSD (BSD became statable thanks to Mathlib's elliptic-curve L-function). For
Riemann, Beal and SAT-lower-bound, H is equivalent to the target (a reformulation); for BSD, H
splits into a published-but-unformalized theorem (modularity) and the open rank equality; for
NS-(C), H has an external proof that now passes the Lean kernel (OpenAI's environment), so (C) is
closed by an external proof; (A)/(B) remain open. Yang–Mills and Hodge remain not statable in
Mathlib; their current interfaces are shown vacuous/independent by kernel-checked lemmas.
