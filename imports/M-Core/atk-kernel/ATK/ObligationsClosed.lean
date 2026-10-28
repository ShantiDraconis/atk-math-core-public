import ATK.BaezDuarteBridge
import ATK.CookLevinNP
import ATK.NSCriterio
import ATK.BLProva

/-!
# ATK — Obrigações fechadas por teoremas certificados

Cada teorema aqui tem **literalmente** a proposição Lean da obrigação correspondente em
`scripts/obligations.json` (campo `lean`) como enunciado. O auditor (`scripts/check_axioms.py`)
só marca uma obrigação como `CLOSED` se o teorema listado em `proof_theorem` estiver certificado
(axiomas padrão, sem `sorry`/`admit`/`axiom`) **e** se esta fonte declarar
`theorem <nome> : <proposição da obrigação>`. Nenhum estado é escrito à mão.
-/

namespace ATK.ObligationsClosed

/-- **B1** (ponte de Riemann, Nyman–Beurling–Báez-Duarte): `D_N → 0 ⇒ RH`. -/
theorem B1 : ATK.Conditional.Riemann.BaezDuarteCriterion :=
  ATK.BaezDuarteBridge.baezDuarteCriterion

/-- **B4** (ponte de P vs NP, Cook 1971; Levin 1973) no modelo genuíno da ligação L2
(`ATK.ModeloPNP.modeloPNP`: P e NP sobre `Turing.FinTM2`, reduções de Karp): SAT ∈ NP e toda
L ∈ NP se reduz a SAT em tempo polinomial. -/
theorem B4 : ATK.Conditional.PvsNP.CookLevin ATK.ModeloPNP.modeloPNP ATK.ModeloPNP.SAT :=
  ATK.CookLevinNP.cookLevin
/-- **B3** (ponte de Navier–Stokes, Leray + teoria local): no modelo genuíno `modeloNS`, se não
há solução global suave então há um tempo maximal `T` com solução suave em `[0, T)` e enstrofia
ilimitada em `[0, T)`. -/
theorem B3 : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion ATK.LigacaoNS.modeloNS :=
  ATK.NSCriterio.criterio

end ATK.ObligationsClosed

namespace ATK.ObligationsClosed

/-- **B9** (ponte de Riemann, Bohr–Landau 1914): `N(1/2 + δ, T) = O(T)` para todo `δ > 0` —
quase todos os zeros estão arbitrariamente perto de `1/2`. Prova incondicional em
`ATK/BLJensen.lean`, `ATK/BLEulerMaclaurin.lean`, `ATK/BLCauda.lean`, `ATK/BLDirichlet.lean`,
`ATK/BLMediaZeta.lean`, `ATK/BLProva.lean`. -/
theorem B9 : ATK.BohrLandau.TeoremaBohrLandau :=
  ATK.BLProva.bohrLandau

end ATK.ObligationsClosed

#print axioms ATK.ObligationsClosed.B1
#print axioms ATK.ObligationsClosed.B4
#print axioms ATK.ObligationsClosed.B3
#print axioms ATK.ObligationsClosed.B9
