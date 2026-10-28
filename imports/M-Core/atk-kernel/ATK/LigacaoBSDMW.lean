import ATK.MordellWeilGeral
import ATK.BSDRefinada
import ATK.LigacaoBSDTestes

/-!
# ATK — A ligação L4 sem a hipótese `MordellWeil`

Com o teorema de Mordell–Weil provado para toda curva elíptica sobre `ℚ`
(`ATK.MordellWeilGeral.mordellWeil`), as fidelidades da ligação L4 perdem essa hipótese; resta só
`Modularidade` (Wiles/Breuil–Conrad–Diamond–Taylor), que continua uma ponte explícita:

* `posto_iff_mod`: `BSDRank (modeloPosto _) ↔ ClayBSD` sob `Modularidade`;
* `bsdFull_iff_mod`: `BSDFull modeloCompleto ↔ ClayBSDCompleto` sob `Modularidade`;
* `taylor_iff_incondicional`: a forma de Taylor do Clay (texto oficial) equivale a `ClayBSD`, sem
  hipóteses;
* `posto_finito`: o posto de Mordell–Weil de toda curva elíptica sobre `ℚ` é finito.
-/

namespace ATK.LigacaoBSDMW

/-- **O posto de Mordell–Weil é finito** para toda curva elíptica sobre `ℚ`. -/
theorem posto_finito (E : WeierstrassCurve ℚ) [E.IsElliptic] : ATK.LigacaoBSD.postoMW E ≠ ⊤ :=
  ATK.MordellWeilGeral.mordellWeil E inferInstance

/-- **Fidelidade da parte do posto** só com `Modularidade`. -/
theorem posto_iff_mod (hMod : ATK.LigacaoBSD.Modularidade)
    (refinada : ATK.LigacaoBSD.CurvaQ → Prop) :
    ATK.Conditional.BSD.BSDRank (ATK.LigacaoBSD.modeloPosto refinada) ↔ ATK.LigacaoBSD.ClayBSD :=
  ATK.LigacaoBSD.posto_iff hMod ATK.MordellWeilGeral.mordellWeil refinada

/-- **Fidelidade do modelo completo** só com `Modularidade`. -/
theorem bsdFull_iff_mod (hMod : ATK.LigacaoBSD.Modularidade) :
    ATK.Conditional.BSD.BSDFull ATK.BSDRefinada.modeloCompleto ↔
      ATK.BSDRefinada.ClayBSDCompleto :=
  ATK.BSDRefinada.bsdFull_iff hMod ATK.MordellWeilGeral.mordellWeil

/-- **A forma de Taylor do Clay equivale a `ClayBSD`**, sem hipóteses. -/
theorem taylor_iff_incondicional :
    ATK.LigacaoBSDTestes.ClayBSDTaylor ↔ ATK.LigacaoBSD.ClayBSD :=
  ATK.LigacaoBSDTestes.taylor_iff ATK.MordellWeilGeral.mordellWeil

end ATK.LigacaoBSDMW

#print axioms ATK.LigacaoBSDMW.posto_finito
#print axioms ATK.LigacaoBSDMW.posto_iff_mod
#print axioms ATK.LigacaoBSDMW.bsdFull_iff_mod
#print axioms ATK.LigacaoBSDMW.taylor_iff_incondicional
