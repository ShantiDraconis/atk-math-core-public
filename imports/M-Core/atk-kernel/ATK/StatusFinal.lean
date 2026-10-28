import ATK.FechamentoO1
import ATK.EnunciadosOficiais
import ATK.SATemNP
import ATK.FermatRegular
import ATK.Indeterminacy
import ATK.ObligationsClosed

/-!
# Status final certificado: `OPEN_MATH = true`, `CLOSED_MATH = false`

Um **registro auditado**: cada item é uma proposição exata com um estado de evidência
`Quatro = ⟨positiva, negativa⟩` (Belnap–Dunn, `ATK.Indeterminacy`), e o **tipo** obriga:

* evidência positiva só com **prova** (`pro : estado.pos = true → P`);
* evidência negativa só com **refutação** (`contra : estado.neg = true → ¬ P`).

Consequências provadas:

* `nenhum_item_em_B`: no nível de prova **nenhum item pode estar em `B`** (seria `P ∧ ¬P`);
* `closedMath_correto`: se `CLOSED_MATH` de uma lista der `true`, **todas** as proposições valem;
  a flag não mente;
* `open_math_true`, `closed_math_false`: calculadas pelo kernel sobre as **8 obrigações** (O1–O8,
  todas `N`).

Inventário:

* `pontesProvadas` (`T`, com o termo de prova): B1 (Báez-Duarte, suficiência), B4 (Cook–Levin),
  SAT ∈ NP, FLT para `3 ≤ n ≤ 22`, `N(T)` bem definido, entrada de Littlewood para `ε > 1/2`;
* `lacunasMathlib` (`N`): Riemann–von Mangoldt, Hadamard para `ξ`, Littlewood sob RH,
  modularidade, Mordell–Weil;
* `pontesPublicadas` (`N` no kernel): FLT completo (B2), Leray (B3), Lefschetz (B5),
  Gross–Zagier–Kolyvagin (B6), Osterwalder–Schrader (B7);
* `obrigacoes` (`N`): O1–O8 com os enunciados exatos (`Termos`, `ClosedMathReal`, `YMNucleo`).
-/

open ATK.Indeterminacy ATK.Termos

namespace ATK.StatusFinal

/-- Um item auditado: a proposição exata e o estado de evidência, com certificados. -/
structure Item where
  nome : String
  P : Prop
  estado : Quatro
  pro : estado.pos = true → P
  contra : estado.neg = true → ¬ P

/-- Item sem evidência (`N = ⟨false, false⟩`): não exige nada. -/
def itemN (nome : String) (P : Prop) : Item :=
  ⟨nome, P, Quatro.N, fun h => by simp [Quatro.N] at h, fun h => by simp [Quatro.N] at h⟩

/-- Item provado (`T = ⟨true, false⟩`): exige o termo de prova. -/
def itemT (nome : String) (P : Prop) (p : P) : Item :=
  ⟨nome, P, Quatro.T, fun _ => p, fun h => by simp [Quatro.T] at h⟩

/-- **No nível de prova não existe `B`**: um item em `B` daria `P ∧ ¬P`. -/
theorem nenhum_item_em_B (i : Item) : i.estado ≠ Quatro.B := fun h =>
  i.contra (by rw [h]; rfl) (i.pro (by rw [h]; rfl))

/-- Itens em `T` carregam a prova. -/
theorem prova_de_T (i : Item) (h : i.estado = Quatro.T) : i.P := i.pro (by rw [h]; rfl)

/-! ## Flags -/

/-- `CLOSED_MATH`: todas em `T`. -/
def closedMath (l : List Item) : Bool := l.all fun i => decide (i.estado = Quatro.T)

/-- `OPEN_MATH`: alguma não está em `T`. -/
def openMath (l : List Item) : Bool := l.any fun i => decide (i.estado ≠ Quatro.T)

/-- **A flag não mente**: `CLOSED_MATH = true` só se todas as proposições valem. -/
theorem closedMath_correto (l : List Item) (h : closedMath l = true) : ∀ i ∈ l, i.P := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  exact prova_de_T i (of_decide_eq_true this)

/-- As duas flags são complementares. -/
theorem open_iff_not_closed (l : List Item) : openMath l = !closedMath l := by
  unfold openMath closedMath
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.any_cons, List.all_cons, ih, Bool.not_and]
    by_cases h : i.estado = Quatro.T <;> simp [h]

/-! ## Inventário -/

/-- Pontes e resultados **provados no kernel** (`T`). -/
def pontesProvadas : List Item :=
  [ itemT "B1 Báez-Duarte (suficiência)" ATK.Conditional.Riemann.BaezDuarteCriterion
      ATK.ObligationsClosed.B1,
    itemT "B4 Cook–Levin" (ATK.Conditional.PvsNP.CookLevin ATK.ModeloPNP.modeloPNP ATK.ModeloPNP.SAT)
      ATK.ObligationsClosed.B4,
    itemT "SAT ∈ NP" (ATK.ModeloPNP.SAT ∈ ATK.LigacaoPNP.classeNP) ATK.SATemNP.sat_em_NP,
    itemT "FLT para 3 ≤ n ≤ 22" (∀ n, 3 ≤ n → n ≤ 22 → FermatLastTheoremFor n)
      fun _ h3 h22 => ATK.FermatRegular.flt_tres_a_vinte_e_dois h3 h22,
    itemT "N(T) bem definido" (∀ T, (ATK.FechamentoO1.zerosAte T).Finite)
      ATK.FechamentoO1.zerosAte_finito,
    itemT "Littlewood para ε > 1/2" (∀ ε : ℝ, 1 / 2 < ε → ATK.NecessidadeBD.EntradaLittlewood ε)
      fun _ h => ATK.NecessidadeBD.entradaLittlewood_of_gt_half h ]

/-- Teoremas publicados que **faltam na Mathlib** (`N`). -/
def lacunasMathlib : List Item :=
  [ itemN "Riemann–von Mangoldt" ATK.FechamentoO1.RiemannVonMangoldt,
    itemN "Hadamard para ξ" ATK.FechamentoO1.HadamardXi,
    itemN "Littlewood sob RH" ATK.FechamentoO1.LittlewoodSobRH,
    itemN "Modularidade" ATK.LigacaoBSD.Modularidade,
    itemN "Mordell–Weil" ATK.LigacaoBSD.MordellWeil ]

/-- Pontes publicadas **ainda não formalizadas** no kernel (`N`). -/
def pontesPublicadas (C : ATK.HodgeOficial.ConstrucoesHodge)
    (Ym : ATK.Conditional.YangMills.YMModel.{0, 0, 0}) : List Item :=
  [ itemN "B2 Fermat (completo)" FermatLastTheorem,
    itemN "B3 Leray" (NS.ponteB3 ATK.LigacaoNS.modeloNS),
    itemN "B5 Lefschetz" (Hodge.ponteB5 (ATK.HodgeOficial.modelo C)),
    itemN "B6 Gross–Zagier–Kolyvagin" (BSD.ponteB6 ATK.BSDRefinada.modeloCompleto),
    itemN "B7 Osterwalder–Schrader" (YM.ponteB7 Ym) ]

/-- **As oito obrigações** (O1–O8), com os enunciados exatos. -/
def obrigacoes (C : ATK.HodgeOficial.ConstrucoesHodge) : List Item :=
  [ itemN "O1 Riemann" RH.produtor,
    itemN "O2 Beal" Beal.produtor,
    itemN "O3 Navier–Stokes" (NS.produtorO3 ATK.LigacaoNS.modeloNS),
    itemN "O4 P ≠ NP" (PNP.produtorO4 ATK.ModeloPNP.modeloPNP ATK.ModeloPNP.SAT),
    itemN "O5 Hodge" (Hodge.produtorO5 (ATK.HodgeOficial.modelo C)),
    itemN "O6 BSD posto" (BSD.produtorO6 ATK.BSDRefinada.modeloCompleto),
    itemN "O7 BSD refinada" (BSD.produtorO7 ATK.BSDRefinada.modeloCompleto),
    itemN "O8 Yang–Mills" ATK.YMOficial.YMNucleo ]

/-! ## O status, calculado pelo kernel -/

/-- **`OPEN_MATH = true`**. -/
theorem open_math_true (C : ATK.HodgeOficial.ConstrucoesHodge) : openMath (obrigacoes C) = true := rfl

/-- **`CLOSED_MATH = false`**. -/
theorem closed_math_false (C : ATK.HodgeOficial.ConstrucoesHodge) :
    closedMath (obrigacoes C) = false := rfl

/-! ## F.1/O8: "aberto" × "não formalizado"

`OPEN_MATH = true` diz que **nenhuma** obrigação está provada no kernel. Não diz que as oito são
matematicamente abertas. A auditoria F.1/O8 (`conditional/F1_O8.md`) separa as duas coisas para O8:
`YMNucleo` é **sombra** do enunciado do Clay (sem correspondência a Yang–Mills, `nucleo_sem_g`;
"não trivial" = não gaussiana), e tem testemunha candidata na literatura, o quadrado de Wick
`:φ²:` do campo livre massivo. Níveis de evidência:

* kernel: `wick` é a fórmula de Isserlis (`ATK.F1YM.wick_quatro`), e os axiomas `Wightman` só usam
  o campo em `D` (`ATK.F1YM.troca_fora_de_D`, `ATK.F1YM.extensao_de_D`), então o domínio total
  exigido pelo kernel não exclui `:φ²:`;
* por fonte (com lacuna de fonte primária): `:φ²:` restrito ao seu subespaço cíclico satisfaz os
  axiomas, é não gaussiano e tem lacuna `2m`.

`shadowO8` e `natureza` registram isso como **dado**, não como prova (`flag_nao_e_prova`). -/

/-- Natureza matemática de uma obrigação. -/
inductive Natureza
  /-- sem prova conhecida -/
  | aberto
  /-- testemunha ou prova na literatura, não formalizada no kernel -/
  | naoFormalizado
  deriving DecidableEq

/-- **`ShadowO8`**: o O8 contado (`YMNucleo`) é sombra do Clay, não o problema do Clay. -/
def shadowO8 : Bool := true

/-- A natureza de O1–O8, na ordem de `obrigacoes`. -/
def natureza : List Natureza :=
  [.aberto, .aberto, .aberto, .aberto, .aberto, .aberto, .aberto,
    if shadowO8 then .naoFormalizado else .aberto]

theorem natureza_alinhada (C : ATK.HodgeOficial.ConstrucoesHodge) :
    natureza.length = (obrigacoes C).length := rfl

/-- **Sete abertas, uma não formalizada**; `OPEN_MATH` continua `true`. -/
theorem sete_abertas_uma_nao_formalizada (C : ATK.HodgeOficial.ConstrucoesHodge) :
    natureza.count .aberto = 7 ∧ natureza.count .naoFormalizado = 1 ∧
      openMath (obrigacoes C) = true :=
  ⟨by decide, by decide, rfl⟩

/-! ## `CLOSED_MATH` por obrigação: "provado **e** fiel ao Millennium"

O agregado `CLOSED_MATH` seria enganoso mesmo no melhor caso: provar `YMNucleo` (sombra) poria O8
em `T` sem resolver o Clay. O mapa por obrigação só conta um item como fechado no sentido Millennium
se ele estiver provado **e** o enunciado for fiel. A fidelidade só é `fiel` onde o kernel prova que
a obrigação **é** a conjectura real (`obrigacoes_sao_conjecturas`: O1, O2, O4); O8 é `sombra`
(F.1/O8); os demais são `naoConferida` (F.1 não feita). -/

/-- Fidelidade do enunciado registrado ao problema Millennium. -/
inductive Fidelidade
  | fiel
  | sombra
  | naoConferida
  deriving DecidableEq

/-- A fidelidade de O1–O8, na ordem de `obrigacoes`. -/
def fidelidade : List Fidelidade :=
  [.fiel, .fiel, .naoConferida, .fiel, .naoConferida, .naoConferida, .naoConferida,
    if shadowO8 then .sombra else .naoConferida]

/-- Fechado no sentido Millennium: provado (`estado.pos`) **e** fiel. -/
def fechadoMillennium (i : Item) (f : Fidelidade) : Bool := i.estado.pos && decide (f = .fiel)

/-- **Uma sombra nunca conta como Millennium fechado**, qualquer que seja o estado do item. -/
theorem sombra_nunca_millennium (i : Item) : fechadoMillennium i .sombra = false := by
  simp [fechadoMillennium]

/-- **Guarda 1** (`naoConferida` é estável): `fidelidade` é uma definição; nenhum build, run de
CI ou dado numérico a altera. O7 continua `naoConferida` mesmo com a instância numérica
(`conditional/o7_numerico`); só mudar a definição, com conteúdo de kernel como
`obrigacoes_sao_conjecturas`, pode promovê-la. -/
theorem fidelidade_O7 : fidelidade[6]? = some .naoConferida := rfl

/-- **Guarda 2** (`sombra` é absorvente): o que quer que esteja na posição de O8, **mesmo provado**,
não conta como Millennium fechado enquanto `shadowO8 = true`. -/
theorem o8_absorvente (i : Item) :
    fechadoMillennium i (fidelidade[7]?.getD .naoConferida) = false := by
  simp [fidelidade, shadowO8, fechadoMillennium]

/-- O mapa por obrigação. -/
def closedMillennium (C : ATK.HodgeOficial.ConstrucoesHodge) : List Bool :=
  List.zipWith fechadoMillennium (obrigacoes C) fidelidade

/-- **Hoje: nenhuma das oito fechada no sentido Millennium.** -/
theorem closedMillennium_hoje (C : ATK.HodgeOficial.ConstrucoesHodge) :
    closedMillennium C = List.replicate 8 false := rfl

/-- As pontes provadas estão em `T`, e cada uma carrega sua prova. -/
theorem pontesProvadas_T : ∀ i ∈ pontesProvadas, i.estado = Quatro.T := by
  simp [pontesProvadas, itemT]

theorem pontesProvadas_validas : ∀ i ∈ pontesProvadas, i.P :=
  fun i hi => prova_de_T i (pontesProvadas_T i hi)

theorem closed_pontes_true : closedMath pontesProvadas = true := rfl

/-- Contagem: 6 provadas, 5 lacunas da Mathlib, 5 pontes publicadas, 8 obrigações abertas. -/
theorem contagem (C : ATK.HodgeOficial.ConstrucoesHodge)
    (Ym : ATK.Conditional.YangMills.YMModel.{0, 0, 0}) :
    pontesProvadas.length = 6 ∧ lacunasMathlib.length = 5 ∧ (pontesPublicadas C Ym).length = 5 ∧
      (obrigacoes C).length = 8 := ⟨rfl, rfl, rfl, rfl⟩

/-- Para O1, O2 e O4 a obrigação **é** a conjectura real: o status `N` delas é o status da própria
conjectura. -/
theorem obrigacoes_sao_conjecturas :
    (RH.produtor ↔ RiemannHypothesis) ∧
      (Beal.produtor ↔ ATK.Conditional.Beal.BealConjecture) ∧
      (PNP.produtorO4 ATK.ModeloPNP.modeloPNP ATK.ModeloPNP.SAT ↔ ATK.LigacaoPNP.PneNP) :=
  ⟨ATK.ClosedMathReal.lacuna_rh_iff, ATK.ClosedMathReal.lacuna_beal_iff,
    ATK.ClosedMathReal.lacuna_pnp_iff⟩

end ATK.StatusFinal

#print axioms ATK.StatusFinal.nenhum_item_em_B
#print axioms ATK.StatusFinal.prova_de_T
#print axioms ATK.StatusFinal.closedMath_correto
#print axioms ATK.StatusFinal.open_iff_not_closed
#print axioms ATK.StatusFinal.open_math_true
#print axioms ATK.StatusFinal.closed_math_false
#print axioms ATK.StatusFinal.pontesProvadas_T
#print axioms ATK.StatusFinal.pontesProvadas_validas
#print axioms ATK.StatusFinal.closed_pontes_true
#print axioms ATK.StatusFinal.contagem
#print axioms ATK.StatusFinal.obrigacoes_sao_conjecturas
#print axioms ATK.StatusFinal.natureza_alinhada
#print axioms ATK.StatusFinal.sete_abertas_uma_nao_formalizada
#print axioms ATK.StatusFinal.sombra_nunca_millennium
#print axioms ATK.StatusFinal.closedMillennium_hoje
#print axioms ATK.StatusFinal.fidelidade_O7
#print axioms ATK.StatusFinal.o8_absorvente
