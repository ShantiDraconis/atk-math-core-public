import ATK.StatusHonesto

/-!
# ATK — Auditoria Belnap real sobre as 8 pontes, 8 obrigações e as ligações

Este arquivo aplica `ATK.StatusHonesto.Evidencia`/`ValorBelnap` aos itens reais listados em
`scripts/obligations.json` (pontes B1–B8, obrigações O1–O8, ligações L1/L2) **um por um** —
nunca como um único valor agregado para "`OPEN_MATH`" ou "`CLOSED_MATH`" inteiros. Essas duas
camadas são conjunções de itens heterogêneos (`ATK.ClosedMath.OpenObligations`, `Bridges`):
combinar evidência de itens não relacionados sob uma regra "qualquer favor / qualquer contra"
produziria um artefato da agregação, não um veredito que signifique algo sobre a conjunção
inteira. Por isso este arquivo audita cada item separadamente, e nenhuma prova aqui atribui um
`ValorBelnap` a `OPEN_MATH` ou `CLOSED_MATH` como um todo.

Regras seguidas (ver a ressalva em `ATK.StatusHonesto`):
* `temAFavor := true` só quando `scripts/obligations.json` marca o item como
  `PROVADA_NO_KERNEL`/`CLOSED`, citando o `proof_theorem` real.
* `temContra := true` só quando existe, no próprio kernel, uma prova específica que mina a
  reivindicação — nunca a mera ausência de uma prova.
-/

namespace ATK.AuditoriaBelnapReal

open ATK.StatusHonesto

/-! ## Pontes (B1–B8) -/

/-- B1 — ponte de Riemann (Nyman–Beurling–Báez-Duarte): `PROVADA_NO_KERNEL`. -/
def b1 : Evidencia :=
  { camada := "BRIDGE", claim := "B1 (Riemann, Nyman–Beurling–Báez-Duarte)",
    temAFavor := true, temContra := false, fonte := "scripts/obligations.json, B1",
    prova := some "ATK.ObligationsClosed.B1" }

/-- B4 — ponte de P vs NP (Cook–Levin) sobre o modelo genuíno `ATK.ModeloPNP.modeloPNP`:
`PROVADA_NO_KERNEL`. -/
def b4 : Evidencia :=
  { camada := "BRIDGE", claim := "B4 (P vs NP, Cook–Levin)",
    temAFavor := true, temContra := false, fonte := "scripts/obligations.json, B4",
    prova := some "ATK.ObligationsClosed.B4" }

/-- B2 — ponte de Beal (FLT): `PARCIAL_NO_MODELO_DO_LANE`, não certificada como obrigação
fechada. -/
def b2 : Evidencia :=
  { camada := "BRIDGE", claim := "B2 (Beal, FLT)", temAFavor := false, temContra := false,
    fonte := "scripts/obligations.json, B2 (PARCIAL_NO_MODELO_DO_LANE)" }

/-- B3, B5, B6, B7, B8 — publicadas na literatura, não formalizadas no kernel. -/
def b3 : Evidencia :=
  { camada := "BRIDGE", claim := "B3 (Navier–Stokes, Leray)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, B3" }

def b5 : Evidencia :=
  { camada := "BRIDGE", claim := "B5 (Hodge, Lefschetz)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, B5" }

def b6 : Evidencia :=
  { camada := "BRIDGE", claim := "B6 (BSD, Gross–Zagier–Kolyvagin)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, B6" }

def b7 : Evidencia :=
  { camada := "BRIDGE", claim := "B7 (Yang–Mills, Osterwalder–Schrader)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, B7" }

def b8 : Evidencia :=
  { camada := "BRIDGE", claim := "B8 (Beal, Darmon–Merel)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, B8" }

/-! ## Obrigações abertas (O1–O8) -/

/-- Nenhuma das 8 obrigações abertas tem prova nem refutação no kernel. Faltar a prova não é
evidência contra (ver `ATK.StatusHonesto`): é `nenhum`, nunca `ambos`. -/
def o1 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O1 (Riemann, UniformLogBound)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, O1 (OPEN_MATH)" }

def o2 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O2 (Beal, GCDLowerBoundSmallExponents)",
    temAFavor := false, temContra := false, fonte := "scripts/obligations.json, O2 (OPEN_MATH)" }

def o3 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O3 (Navier–Stokes, EnstrophyAPrioriBound)",
    temAFavor := false, temContra := false, fonte := "scripts/obligations.json, O3 (OPEN_MATH)" }

def o4 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O4 (P vs NP, SATNotInP)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, O4 (OPEN_MATH)" }

def o5 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O5 (Hodge, MiddleCodimension)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, O5 (OPEN_MATH)" }

def o6 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O6 (BSD, cota superior do posto)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, O6 (OPEN_MATH)" }

def o7 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O7 (BSD, segunda obrigação)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, O7 (OPEN_MATH)" }

def o8 : Evidencia :=
  { camada := "OPEN_MATH", claim := "O8 (Yang–Mills, mass gap)", temAFavor := false,
    temContra := false, fonte := "scripts/obligations.json, O8 (OPEN_MATH)" }

/-! ## Correção (revisão de PR): o caso do modelo de brinquede não é `ambos` -/

/-- Uma revisão real desta auditoria apontou um erro aqui: `ns_toy_model_vacuous` prova só
`∃ M, ClayStatementA M` (favor, sobre esse `M`); ela não prova `¬ ClayStatementA M'` para
nenhum `M'` — não é uma segunda fonte refutando a mesma reivindicação. Tratar isso como `ambos`
para "`ClayStatementA M`" conflava duas reivindicações diferentes: a verdade do existencial
(incondicionalmente verdadeira — não há como ter evidência contra ela) e a questão separada de
se um `M` não ligado conta como progresso real. É exatamente a conflação entre reivindicações
que este arquivo existe para evitar (ver `ATK.StatusHonesto`).

A reivindicação correta, isolada, é: "**um modelo não ligado (brinquedo) que satisfaz o esquema
conta como progresso em direção a `ClayStatementA`/`PneNP`**". Ninguém afirma isso a favor
(`temAFavor := false`); e há evidência real e específica contra (`temContra := true`):
`ns_toy_model_vacuous` exibe esse `M` como trivial, e `ns_depende_do_modelo` prova que o mesmo
esquema vale para um `M` e falha para outro — logo satisfazê-lo para um `M` não ligado não
mostra nada sobre o problema genuíno. Isso é `falso`, não `ambos`. -/
def esquemaNS_sem_ligacao : Evidencia :=
  { camada := "LIGAÇÃO",
    claim := "um modelo NS não ligado (brinquedo) que satisfaz o esquema conta como progresso",
    temAFavor := false, temContra := true,
    fonte := "ATK.ClosedMath.ns_toy_model_vacuous + ATK.FinalRoot.ns_depende_do_modelo" }

/-- O mesmo para `L2` / P vs NP: `pnp_toy_model_vacuous` + `pnp_depende_do_modelo`. -/
def esquemaPNP_sem_ligacao : Evidencia :=
  { camada := "LIGAÇÃO",
    claim := "um modelo PvsNP não ligado (brinquedo) que satisfaz o esquema conta como progresso",
    temAFavor := false, temContra := true,
    fonte := "ATK.ClosedMath.pnp_toy_model_vacuous + ATK.FinalRoot.pnp_depende_do_modelo" }

/-! ## Teoremas -/

theorem b1_verdadeiro : b1.valor = .verdadeiro := rfl
theorem b4_verdadeiro : b4.valor = .verdadeiro := rfl

theorem pontesNaoProvadas_nenhum :
    b2.valor = .nenhum ∧ b3.valor = .nenhum ∧ b5.valor = .nenhum ∧ b6.valor = .nenhum ∧
      b7.valor = .nenhum ∧ b8.valor = .nenhum :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem obrigacoesAbertas_nenhum :
    o1.valor = .nenhum ∧ o2.valor = .nenhum ∧ o3.valor = .nenhum ∧ o4.valor = .nenhum ∧
      o5.valor = .nenhum ∧ o6.valor = .nenhum ∧ o7.valor = .nenhum ∧ o8.valor = .nenhum :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem esquemaSemLigacao_falso :
    esquemaNS_sem_ligacao.valor = .falso ∧ esquemaPNP_sem_ligacao.valor = .falso :=
  ⟨rfl, rfl⟩

/-!
Depois da correção acima, esta auditoria item a item não contém nenhum caso confirmado de
`ambos`: as 8 obrigações e 6 das 8 pontes são `nenhum`, duas pontes são `verdadeiro` (B1, B4), e
os dois itens de ligação que pareciam `ambos` são, corretamente isolados, `falso`. `ambos`
continua um valor legítimo de `ValorBelnap` (ver `ATK.AnaliseInversao`), só que, até hoje, sem
uma instância real confirmada neste kernel — e não é este arquivo que vai forçar uma só para ter
um exemplo. Nada aqui atribui `ambos`, `verdadeiro` ou qualquer outro valor a `OPEN_MATH` ou
`CLOSED_MATH` como um todo: essas camadas permanecem conjunções heterogêneas, não uma
reivindicação com `ValorBelnap` próprio.
-/

end ATK.AuditoriaBelnapReal

#print axioms ATK.AuditoriaBelnapReal.b1_verdadeiro
#print axioms ATK.AuditoriaBelnapReal.b4_verdadeiro
#print axioms ATK.AuditoriaBelnapReal.pontesNaoProvadas_nenhum
#print axioms ATK.AuditoriaBelnapReal.obrigacoesAbertas_nenhum
#print axioms ATK.AuditoriaBelnapReal.esquemaSemLigacao_falso
