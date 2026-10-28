import ATK.IntegracaoFCBSD
import ATK.MordellWeilGeral

/-!
# ATK — BSD do ATK contra o do formal-conjectures, sem a hipótese de Mordell–Weil

`ATK.IntegracaoFCBSD` compara o enunciado de BSD do ATK (`ATK.LigacaoBSD.ClayBSD`) com o do
formal-conjectures (`ATK.FC.BSD.Weak ℚ`) sob duas hipóteses explícitas, `HasseWeilQ` e
`MordellWeilQ`, que o formal-conjectures registra como `research solved` e deixa como `sorry`.

Com o teorema de Mordell–Weil provado no kernel para toda curva elíptica sobre `ℚ`
(`ATK.MordellWeilGeral.mordellWeil_fg`), aqui:

* `mordellWeilQ`: **o enunciado de Mordell–Weil do formal-conjectures (sobre `ℚ`) está provado**;
* `hasseWeilQ_de_modularidade`: a `Modularidade` do ATK implica o `HasseWeilQ` do
  formal-conjectures (uma continuação inteira é uma continuação analítica);
* `weak_clayBSD`, `clayBSD_iff_weak`: as comparações só com `HasseWeilQ`;
* `clayBSD_iff_weak_mod`, `bsdRank_iff_weak`: as mesmas comparações só com `Modularidade`
  (Wiles; Breuil–Conrad–Diamond–Taylor), que continua a única ponte da ligação L4.

A implicação `clayBSD_weak : ClayBSD → Weak ℚ` já era incondicional.

Nada aqui prova BSD: as obrigações O6 (posto analítico ≥ 2) e O7 (fórmula refinada) continuam
abertas. `OPEN_MATH = true`, `CLOSED_MATH = false`.
-/

open ATK.LigacaoBSD ATK.FC.HasseWeil ATK.FC.BSD

namespace ATK.IntegracaoFCBSDMW

/-- **O Mordell–Weil do formal-conjectures sobre `ℚ`**: `E(ℚ)` é um `ℤ`-módulo finito para toda
curva elíptica `E/ℚ`. -/
theorem mordellWeilQ : MordellWeilQ := fun E _ =>
  Module.Finite.iff_addGroup_fg.mpr (ATK.MordellWeilGeral.mordellWeil_fg E)

/-- A `Modularidade` do ATK dá o `HasseWeilQ` do formal-conjectures. -/
theorem hasseWeilQ_de_modularidade (hMod : Modularidade) : HasseWeilQ := by
  intro E _
  obtain ⟨F, hF, -⟩ := hMod E inferInstance
  exact ⟨F, fun z => hF.1.analyticAt z, hF.2⟩

/-- **A volta, só com Hasse–Weil**: o BSD fraco do formal-conjectures implica o do ATK. -/
theorem weak_clayBSD (hHW : HasseWeilQ) (h : Weak ℚ) : ClayBSD :=
  ATK.IntegracaoFCBSD.weak_clayBSD hHW mordellWeilQ h

/-- **Com Hasse–Weil, os dois enunciados de BSD são equivalentes.** -/
theorem clayBSD_iff_weak (hHW : HasseWeilQ) : ClayBSD ↔ Weak ℚ :=
  ATK.IntegracaoFCBSD.clayBSD_iff_weak hHW mordellWeilQ

/-- **Com a modularidade, os dois enunciados de BSD são equivalentes.** -/
theorem clayBSD_iff_weak_mod (hMod : Modularidade) : ClayBSD ↔ Weak ℚ :=
  clayBSD_iff_weak (hasseWeilQ_de_modularidade hMod)

/-- **A parte do posto do modelo do portão equivale ao BSD fraco do formal-conjectures**, só com a
modularidade. -/
theorem bsdRank_iff_weak (hMod : Modularidade) (refinada : CurvaQ → Prop) :
    ATK.Conditional.BSD.BSDRank (modeloPosto refinada) ↔ Weak ℚ :=
  ATK.IntegracaoFCBSD.bsdRank_iff_weak hMod (hasseWeilQ_de_modularidade hMod) mordellWeilQ
    refinada

end ATK.IntegracaoFCBSDMW

#print axioms ATK.IntegracaoFCBSDMW.mordellWeilQ
#print axioms ATK.IntegracaoFCBSDMW.hasseWeilQ_de_modularidade
#print axioms ATK.IntegracaoFCBSDMW.weak_clayBSD
#print axioms ATK.IntegracaoFCBSDMW.clayBSD_iff_weak
#print axioms ATK.IntegracaoFCBSDMW.clayBSD_iff_weak_mod
#print axioms ATK.IntegracaoFCBSDMW.bsdRank_iff_weak
