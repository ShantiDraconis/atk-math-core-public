import ATK.Conditional.Beal
import ATK.Conditional.Riemann

/-!
# O mundo hipotético ATK-O1 no kernel — o que acontece

Reconstrói o "mundo hipotético completo" (ATK-O1) dos textos e o submete ao kernel, com
testes que mostram **o que** o kernel aceita e **por quê**.

* **Gramática** (`Formula`, `Conectivo`): átomos, negação, conjunção, disjunção, implicação,
  equivalência; semântica `avaliar` em `Prop`; leis (modus ponens, contrapositiva, De Morgan,
  dupla negação, transitividade) e quantificadores (`¬∀ ↔ ∃¬`, `¬∃ ↔ ∀¬`).
* **Sujeito e predicado** (`Sentenca`): `sujeito`, `predicado`, `afirma = predicado sujeito`.
* **Tempo verbal** (`Fase`): conjectura < construção < verificação < certificação; um
  `Registro P` só carrega prova de `P` na fase de certificação, e existe registro em qualquer
  outra fase **para qualquer** `P`, inclusive `False` (`fase_futura_nao_informa`).
* **Mundo** (`Mundo S`): oito terminais (BSD em dois), produtores `Qᵢ`, testemunhas `qᵢ : Qᵢ`,
  pontes `fᵢ : Qᵢ → Pᵢ`; `fechar_tudo : Mundo S → ∀ i, Pᵢ`; leis de transporte e composição.

## O que o kernel mostra (testes)

| teste | teorema | resultado |
|---|---|---|
| fecha | `fechar_tudo` | aceito, **sem axiomas**: é só aplicar `fᵢ` a `qᵢ` |
| é aplicação | `fechar_tudo_eq` | `rfl`: o fechamento não faz nenhum trabalho matemático |
| equivalência | `mundo_iff` | `Nonempty (Mundo S) ↔ ∀ i, Pᵢ`: o mundo é **exatamente** as conjecturas |
| circular | `mundo_canonico_circular` | o mundo construído das provas tem `Qᵢ = Pᵢ` e `fᵢ = id` |
| vacuidade | `mundo_vazio_de_falso`, `mundo_prova_tudo_se_falso` | se um `Pᵢ` é falso, não há mundo, e "do mundo" segue qualquer coisa |
| explosão | `contraditorio_vazio`, `contraditorio_prova_rh_e_nao_rh` | especificação com `RH` e `¬RH`: o kernel aceita `Mundo → RH ∧ ¬RH` |
| brinquedo | `mundo_brinquedo` | com `Pᵢ := True` há mundo: "fechado" sem dizer nada |
| fidelidade | `fiel_fecha` | só uma especificação fiel (`RH`, `Beal` oficiais) dá os enunciados reais |
| oráculos | `oraculo_beal`, `oraculo_rh`, `oraculo_eq_id` | os `HypotheticalClosureOracle` dos repositórios são a identidade |

Conclusão verificada: o kernel aceita todo fechamento hipotético **porque** ele é condicional.
O conteúdo está inteiro nas hipóteses `Mundo S`; nenhum teorema daqui as produz.
-/

namespace ATK.MundoHipotetico

/-! ## 1. Gramática e semântica -/

/-- Conectivos binários. -/
inductive Conectivo
  | e | ou | implica | equivale
  deriving DecidableEq, Repr

/-- Fórmulas sobre átomos de tipo `α`. -/
inductive Formula (α : Type*)
  | atomo : α → Formula α
  | nao : Formula α → Formula α
  | bin : Conectivo → Formula α → Formula α → Formula α

/-- Interpretação de um conectivo. -/
def Conectivo.interp : Conectivo → Prop → Prop → Prop
  | .e, p, q => p ∧ q
  | .ou, p, q => p ∨ q
  | .implica, p, q => p → q
  | .equivale, p, q => p ↔ q

/-- Semântica: cada átomo recebe uma proposição. -/
def Formula.avaliar {α : Type*} (v : α → Prop) : Formula α → Prop
  | .atomo a => v a
  | .nao φ => ¬ φ.avaliar v
  | .bin c φ ψ => c.interp (φ.avaliar v) (ψ.avaliar v)

section Leis

variable {α : Type*} (v : α → Prop) (φ ψ χ : Formula α)

theorem modus_ponens (h : (Formula.bin .implica φ ψ).avaliar v) (hφ : φ.avaliar v) :
    ψ.avaliar v := h hφ

theorem contrapositiva :
    (Formula.bin .implica φ ψ).avaliar v ↔ (Formula.bin .implica (.nao ψ) (.nao φ)).avaliar v :=
  ⟨fun h hψ hφ => hψ (h hφ), fun h hφ => Classical.byContradiction fun hψ => h hψ hφ⟩

theorem de_morgan_e :
    (Formula.nao (.bin .e φ ψ)).avaliar v ↔ (Formula.bin .ou (.nao φ) (.nao ψ)).avaliar v := by
  simp only [Formula.avaliar, Conectivo.interp]
  tauto

theorem de_morgan_ou :
    (Formula.nao (.bin .ou φ ψ)).avaliar v ↔ (Formula.bin .e (.nao φ) (.nao ψ)).avaliar v := by
  simp only [Formula.avaliar, Conectivo.interp]
  tauto

theorem dupla_negacao : (Formula.nao (.nao φ)).avaliar v ↔ φ.avaliar v := by
  simp only [Formula.avaliar]
  tauto

theorem implica_transitiva (h1 : (Formula.bin .implica φ ψ).avaliar v)
    (h2 : (Formula.bin .implica ψ χ).avaliar v) : (Formula.bin .implica φ χ).avaliar v :=
  fun hφ => h2 (h1 hφ)

theorem equivale_iff :
    (Formula.bin .equivale φ ψ).avaliar v ↔
      (Formula.bin .implica φ ψ).avaliar v ∧ (Formula.bin .implica ψ φ).avaliar v :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Terceiro excluído (lógica clássica do kernel com `Classical.choice`). -/
theorem terceiro_excluido : (Formula.bin .ou φ (.nao φ)).avaliar v := Classical.em _

end Leis

/-- Quantificadores: `¬∀ ↔ ∃¬`. -/
theorem nao_todo {ι : Type*} (P : ι → Prop) : (¬ ∀ i, P i) ↔ ∃ i, ¬ P i := not_forall

/-- Quantificadores: `¬∃ ↔ ∀¬`. -/
theorem nao_existe {ι : Type*} (P : ι → Prop) : (¬ ∃ i, P i) ↔ ∀ i, ¬ P i := not_exists

/-- Uma sentença: sujeito + predicado. -/
structure Sentenca (α : Type*) where
  sujeito : α
  predicado : α → Prop

/-- O que a sentença afirma. -/
def Sentenca.afirma {α : Type*} (s : Sentenca α) : Prop := s.predicado s.sujeito

/-- Trocar o sujeito por um igual não muda a afirmação. -/
theorem afirma_congr {α : Type*} {s t : Sentenca α} (h1 : s.sujeito = t.sujeito)
    (h2 : s.predicado = t.predicado) : s.afirma ↔ t.afirma := by
  simp [Sentenca.afirma, h1, h2]

/-! ## 2. Tempo verbal: fases -/

/-- As fases de uma afirmação. -/
inductive Fase
  | conjectura | construcao | verificacao | certificacao
  deriving DecidableEq, Repr

/-- Ordem das fases. -/
def Fase.nivel : Fase → ℕ
  | .conjectura => 0 | .construcao => 1 | .verificacao => 2 | .certificacao => 3

/-- Um registro de `P` numa fase; só a certificação carrega prova. -/
structure Registro (P : Prop) where
  fase : Fase
  prova : fase = .certificacao → P

theorem registro_certificado {P : Prop} (r : Registro P) (h : r.fase = .certificacao) : P :=
  r.prova h

/-- Tempo futuro não é prova presente: para **qualquer** `P` (até `False`) existe registro em
toda fase anterior à certificação. -/
theorem fase_futura_nao_informa (P : Prop) (f : Fase) (hf : f ≠ .certificacao) :
    ∃ r : Registro P, r.fase = f :=
  ⟨⟨f, fun h => absurd h hf⟩, rfl⟩

theorem certificacao_e_o_topo (f : Fase) : f.nivel ≤ Fase.certificacao.nivel := by
  cases f <;> decide

/-! ## 3. O mundo O1 -/

/-- As oito obrigações terminais (BSD em duas partes). -/
inductive Terminal
  | rh | pnp | ns | ym | bsdPosto | bsdRefinada | hodge | beal
  deriving DecidableEq, Repr

/-- Uma especificação: o enunciado `Pᵢ` de cada terminal. -/
structure Especificacao where
  enunciado : Terminal → Prop

/-- O mundo hipotético: produtores `Qᵢ`, testemunhas `qᵢ` e pontes `fᵢ : Qᵢ → Pᵢ`. -/
structure Mundo (S : Especificacao) where
  produtor : Terminal → Prop
  testemunha : ∀ i, produtor i
  ponte : ∀ i, produtor i → S.enunciado i

/-- **Fechamento**: `(⋀ qᵢ : Qᵢ) ∧ (⋀ fᵢ : Qᵢ → Pᵢ) ⟹ ⋀ Pᵢ`. -/
theorem fechar_tudo {S : Especificacao} (W : Mundo S) : ∀ i, S.enunciado i :=
  fun i => W.ponte i (W.testemunha i)

/-- O fechamento é só a aplicação `fᵢ qᵢ` (`rfl`). -/
theorem fechar_tudo_eq {S : Especificacao} (W : Mundo S) (i : Terminal) :
    fechar_tudo W i = W.ponte i (W.testemunha i) := rfl

/-- Lei de composição de pontes: `Q → R → P`. -/
def compor {S : Especificacao} (R : Terminal → Prop) (W : Mundo ⟨R⟩)
    (g : ∀ i, R i → S.enunciado i) : Mundo S :=
  ⟨W.produtor, W.testemunha, fun i q => g i (W.ponte i q)⟩

/-- Lei de transporte por equivalência. -/
def transportar {S T : Especificacao} (h : ∀ i, S.enunciado i ↔ T.enunciado i) (W : Mundo S) :
    Mundo T :=
  ⟨W.produtor, W.testemunha, fun i q => (h i).1 (W.ponte i q)⟩

/-- O mundo canônico, construído das próprias provas. -/
def mundoCanonico {S : Especificacao} (h : ∀ i, S.enunciado i) : Mundo S :=
  ⟨S.enunciado, h, fun _ q => q⟩

/-- **Teste: equivalência.** Existe mundo **se e só se** todos os enunciados valem. -/
theorem mundo_iff (S : Especificacao) : Nonempty (Mundo S) ↔ ∀ i, S.enunciado i :=
  ⟨fun ⟨W⟩ => fechar_tudo W, fun h => ⟨mundoCanonico h⟩⟩

/-- **Teste: circularidade.** No mundo canônico os produtores são os enunciados e as pontes são
a identidade. -/
theorem mundo_canonico_circular {S : Especificacao} (h : ∀ i, S.enunciado i) :
    (mundoCanonico h).produtor = S.enunciado ∧
      ∀ i (q : (mundoCanonico h).produtor i), (mundoCanonico h).ponte i q = q :=
  ⟨rfl, fun _ _ => rfl⟩

/-- **Teste: vacuidade.** Um enunciado falso torna o mundo vazio. -/
theorem mundo_vazio_de_falso {S : Especificacao} {i : Terminal} (h : ¬ S.enunciado i) :
    IsEmpty (Mundo S) :=
  ⟨fun W => h (fechar_tudo W i)⟩

/-- **Teste: vacuidade.** Do mundo de uma especificação com um enunciado falso segue qualquer
proposição. -/
theorem mundo_prova_tudo_se_falso {S : Especificacao} {i : Terminal} (h : ¬ S.enunciado i)
    (R : Prop) : Mundo S → R :=
  fun W => absurd (fechar_tudo W i) h

/-- Uma especificação contraditória: `RH` num terminal e `¬RH` em outro. -/
def especContraditoria : Especificacao :=
  ⟨fun i => if i = .rh then RiemannHypothesis else if i = .pnp then ¬ RiemannHypothesis else True⟩

/-- **Teste: explosão.** O mundo contraditório é vazio … -/
theorem contraditorio_vazio : IsEmpty (Mundo especContraditoria) :=
  ⟨fun W => by
    have h1 := fechar_tudo W .rh
    have h2 := fechar_tudo W .pnp
    simp [especContraditoria] at h1 h2
    exact h2 h1⟩

/-- … e o kernel aceita, dele, `RH ∧ ¬RH`. Checar consistência é obrigatório. -/
theorem contraditorio_prova_rh_e_nao_rh :
    Mundo especContraditoria → RiemannHypothesis ∧ ¬ RiemannHypothesis :=
  fun W => (contraditorio_vazio.false W).elim

/-- A especificação de brinquedo: todo enunciado é `True`. -/
def especBrinquedo : Especificacao := ⟨fun _ => True⟩

/-- **Teste: brinquedo.** Há mundo, logo "fechamento" — sem conteúdo algum. -/
theorem mundo_brinquedo : Nonempty (Mundo especBrinquedo) :=
  ⟨mundoCanonico fun _ => trivial⟩

/-- Fidelidade aos enunciados oficiais disponíveis na Mathlib/ATK. -/
def Fiel (S : Especificacao) : Prop :=
  S.enunciado .rh = RiemannHypothesis ∧ S.enunciado .beal = ATK.Conditional.Beal.BealConjecture

/-- **Teste: fidelidade.** Só um mundo fiel entrega os enunciados reais. -/
theorem fiel_fecha {S : Especificacao} (hS : Fiel S) (W : Mundo S) :
    RiemannHypothesis ∧ ATK.Conditional.Beal.BealConjecture :=
  ⟨hS.1 ▸ fechar_tudo W .rh, hS.2 ▸ fechar_tudo W .beal⟩

/-- O brinquedo não é fiel: `True ≠ RH` a menos que RH valha. -/
theorem brinquedo_fiel_iff : Fiel especBrinquedo ↔
    RiemannHypothesis ∧ ATK.Conditional.Beal.BealConjecture := by
  unfold Fiel especBrinquedo
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 ▸ trivial, h2 ▸ trivial⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(eq_true h1).symm, (eq_true h2).symm⟩

/-! ## 4. Os oráculos dos repositórios -/

/-- O padrão `HypotheticalClosureOracle`: `HypotheticalClosure := Enunciado`. -/
def oraculo (P : Prop) (H : P) : P := H

/-- **Teste: o oráculo é a identidade.** -/
theorem oraculo_eq_id (P : Prop) : oraculo P = id := rfl

/-- Oráculo de Beal (porte de `m-core-beal/…/HypotheticalClosureOracle.lean`), com o enunciado
elementar completo. -/
theorem oraculo_beal (H : ATK.Conditional.Beal.BealConjecture) (a b c x y z : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hx : 2 < x) (hy : 2 < y) (hz : 2 < z)
    (he : a ^ x + b ^ y = c ^ z) : ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c :=
  oraculo _ H a b c x y z ha hb hc hx hy hz he

/-- Oráculo de RH: devolve o que recebe. -/
theorem oraculo_rh (H : RiemannHypothesis) : RiemannHypothesis := oraculo _ H

end ATK.MundoHipotetico

#print axioms ATK.MundoHipotetico.modus_ponens
#print axioms ATK.MundoHipotetico.contrapositiva
#print axioms ATK.MundoHipotetico.de_morgan_e
#print axioms ATK.MundoHipotetico.de_morgan_ou
#print axioms ATK.MundoHipotetico.dupla_negacao
#print axioms ATK.MundoHipotetico.implica_transitiva
#print axioms ATK.MundoHipotetico.equivale_iff
#print axioms ATK.MundoHipotetico.terceiro_excluido
#print axioms ATK.MundoHipotetico.nao_todo
#print axioms ATK.MundoHipotetico.nao_existe
#print axioms ATK.MundoHipotetico.afirma_congr
#print axioms ATK.MundoHipotetico.registro_certificado
#print axioms ATK.MundoHipotetico.fase_futura_nao_informa
#print axioms ATK.MundoHipotetico.certificacao_e_o_topo
#print axioms ATK.MundoHipotetico.fechar_tudo
#print axioms ATK.MundoHipotetico.fechar_tudo_eq
#print axioms ATK.MundoHipotetico.mundo_iff
#print axioms ATK.MundoHipotetico.mundo_canonico_circular
#print axioms ATK.MundoHipotetico.mundo_vazio_de_falso
#print axioms ATK.MundoHipotetico.mundo_prova_tudo_se_falso
#print axioms ATK.MundoHipotetico.contraditorio_vazio
#print axioms ATK.MundoHipotetico.contraditorio_prova_rh_e_nao_rh
#print axioms ATK.MundoHipotetico.mundo_brinquedo
#print axioms ATK.MundoHipotetico.fiel_fecha
#print axioms ATK.MundoHipotetico.brinquedo_fiel_iff
#print axioms ATK.MundoHipotetico.oraculo_eq_id
#print axioms ATK.MundoHipotetico.oraculo_beal
#print axioms ATK.MundoHipotetico.oraculo_rh
