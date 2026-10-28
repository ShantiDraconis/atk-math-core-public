import ATK.LigacaoBSD
import ATK.Externo.FCBSD
import ATK.PostoLivre

/-!
# ATK — O enunciado de BSD do ATK contra o do formal-conjectures

O ATK enuncia a parte do posto de BSD como `ATK.LigacaoBSD.ClayBSD`: para toda curva elíptica
`E/ℚ` **existe** uma continuação inteira `F` da série L e `analyticOrderAt F 1 = postoMW E`, com
`postoMW E = toENat (Module.rank ℤ E(ℚ))`.

O formal-conjectures enuncia `BSD.Weak ℚ`: para toda curva elíptica `E/ℚ` com `E(ℚ)` f.g. e **toda**
continuação meromorfa `L`, `meromorphicOrderAt L 1 = AddCommGroup.freeRank E(ℚ)`.

Provado aqui:

* `postoMW_eq_freeRank`: com `E(ℚ)` f.g., os dois postos coincidem (via `ATK.PostoLivre`);
* `clayBSD_weak`: **o enunciado do ATK implica o do formal-conjectures, sem hipóteses**;
* `weak_clayBSD`: a volta, dados Hasse–Weil sobre `ℚ` (continuação analítica) e Mordell–Weil — os
  dois são teoremas publicados que o próprio formal-conjectures registra como `research solved` e
  deixa como `sorry`; aqui entram como hipóteses explícitas (`HasseWeilQ`, `MordellWeilQ`);
* `clayBSD_iff_weak`: com essas duas hipóteses, os enunciados são equivalentes;
* `bsdRank_iff_weak`: a parte do posto do modelo do portão (`BSDRank (modeloPosto _)`) equivale a
  `BSD.Weak ℚ`, dadas a modularidade (`Modularidade`) e as duas hipóteses acima.

Nada aqui prova BSD. A fórmula refinada (`BSDFull`) não tem contrapartida no formal-conjectures.
-/

open ATK.LigacaoBSD ATK.FC.HasseWeil ATK.FC.BSD

namespace ATK.IntegracaoFCBSD

/-- Com `E(ℚ)` finitamente gerado, o posto do ATK é o posto livre da Mathlib. -/
theorem postoMW_eq_freeRank (E : WeierstrassCurve ℚ) [AddGroup.FG E.toAffine.Point] :
    postoMW E = AddCommGroup.freeRank E.toAffine.Point := by
  have : Module.Finite ℤ E.toAffine.Point := Module.Finite.iff_addGroup_fg.mpr ‹_›
  rw [postoMW, ATK.PostoLivre.freeRank_eq_finrank, ← Module.finrank_eq_rank, Cardinal.toENat_nat]

/-- Uma continuação inteira (ATK) é uma continuação meromorfa (formal-conjectures). -/
theorem continuacao_meromorfa {E : WeierstrassCurve ℚ} {F : ℂ → ℂ} (hF : Continuacao E F) :
    HasMeromorphicContinuation E F :=
  ⟨fun z => (hF.1.analyticAt z).meromorphicAt, hF.2⟩

/-- Uma continuação analítica (formal-conjectures) é uma continuação inteira (ATK). -/
theorem continuacao_de_analitica {E : WeierstrassCurve ℚ} {L : ℂ → ℂ}
    (hL : HasAnalyticContinuation E L) : Continuacao E L :=
  ⟨fun z => (hL.1 z).differentiableAt, hL.2⟩

/-- **O enunciado de BSD do ATK implica o do formal-conjectures (sobre `ℚ`), sem hipóteses.** -/
theorem clayBSD_weak (h : ClayBSD) : Weak ℚ := by
  intro E hE _ L hL
  obtain ⟨F, hF, hord⟩ := h E hE
  rw [meromorphicOrderAt_congr (hL.unique (continuacao_meromorfa hF) 1),
    (hF.1.analyticAt 1).meromorphicOrderAt_eq, hord, postoMW_eq_freeRank]
  simp

/-- **A volta**, dados Hasse–Weil e Mordell–Weil sobre `ℚ` (hipóteses explícitas). -/
theorem weak_clayBSD (hHW : HasseWeilQ) (hMW : MordellWeilQ) (h : Weak ℚ) : ClayBSD := by
  intro E hE
  have : AddGroup.FG E.toAffine.Point := Module.Finite.iff_addGroup_fg.mp (hMW E)
  obtain ⟨L, hL⟩ := hHW E
  refine ⟨L, continuacao_de_analitica hL, ?_⟩
  have h1 := h E L hL.hasMeromorphicContinuation
  rw [(hL.1 1).meromorphicOrderAt_eq] at h1
  rw [postoMW_eq_freeRank]
  cases hn : analyticOrderAt L 1 with
  | top => rw [hn] at h1; simp at h1
  | coe n =>
    rw [hn] at h1
    simp only [ENat.map_natCast] at h1
    have h2 : (n : ℤ) = (AddCommGroup.freeRank E.toAffine.Point : ℤ) := by exact_mod_cast h1
    exact_mod_cast h2

/-- **Com Hasse–Weil e Mordell–Weil, os dois enunciados de BSD são equivalentes.** -/
theorem clayBSD_iff_weak (hHW : HasseWeilQ) (hMW : MordellWeilQ) : ClayBSD ↔ Weak ℚ :=
  ⟨clayBSD_weak, weak_clayBSD hHW hMW⟩

/-- O Mordell–Weil do formal-conjectures dá o do ATK (`postoMW E ≠ ⊤`). -/
theorem mordellWeil_de_fc (hMW : MordellWeilQ) : MordellWeil := by
  intro E hE
  have : AddGroup.FG E.toAffine.Point := Module.Finite.iff_addGroup_fg.mp (hMW E)
  rw [postoMW_eq_freeRank]
  exact ENat.natCast_ne_top _

/-- **A parte do posto do modelo do portão equivale ao BSD fraco do formal-conjectures**, dadas
a modularidade, Hasse–Weil e Mordell–Weil (teoremas publicados, como hipóteses explícitas). -/
theorem bsdRank_iff_weak (hMod : Modularidade) (hHW : HasseWeilQ) (hMW : MordellWeilQ)
    (refinada : CurvaQ → Prop) :
    ATK.Conditional.BSD.BSDRank (modeloPosto refinada) ↔ Weak ℚ :=
  (posto_iff hMod (mordellWeil_de_fc hMW) refinada).trans (clayBSD_iff_weak hHW hMW)

end ATK.IntegracaoFCBSD

#print axioms ATK.FC.HasseWeil.HasAnalyticContinuation.hasMeromorphicContinuation
#print axioms ATK.FC.HasseWeil.HasMeromorphicContinuation.unique
#print axioms ATK.PostoLivre.freeRank_eq_finrank
#print axioms ATK.IntegracaoFCBSD.postoMW_eq_freeRank
#print axioms ATK.IntegracaoFCBSD.continuacao_meromorfa
#print axioms ATK.IntegracaoFCBSD.continuacao_de_analitica
#print axioms ATK.IntegracaoFCBSD.clayBSD_weak
#print axioms ATK.IntegracaoFCBSD.weak_clayBSD
#print axioms ATK.IntegracaoFCBSD.clayBSD_iff_weak
#print axioms ATK.IntegracaoFCBSD.mordellWeil_de_fc
#print axioms ATK.IntegracaoFCBSD.bsdRank_iff_weak
