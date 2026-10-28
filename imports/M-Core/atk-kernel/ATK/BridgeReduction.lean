import ATK.ClosedMath
import ATK.ObligationsClosed
import ATK.BaezDuarteBridge
import ATK.BealFermatDescent

/-!
# ATK — Redução das hipóteses do teorema-mestre ao que o kernel ainda não tem

`ATK.ClosedMath.closedMath_of_obligations : Bridges M → OpenObligations M → SevenStatements M`
recebe 7 pontes e 8 obrigações abertas. Este arquivo descarrega no kernel tudo o que já está
provado e devolve o teorema-mestre com o **conjunto mínimo** de hipóteses atual:

* **B1** (Nyman–Beurling–Báez-Duarte) sai inteira: `ATK.ObligationsClosed.B1`.
* **B2** (`FermatLastTheorem`) encolhe para `FLTPrimosGeCinco` — FLT só para expoentes primos
  `p ≥ 5` —, porque FLT(3) e FLT(4) estão na Mathlib (`fermatLastTheoremThree`,
  `fermatLastTheoremFour`): `flt_iff_primos_ge_cinco` é uma equivalência, não uma implicação.
* `pontes_iff_restantes`: as 7 pontes originais ⟺ as 6 restantes (sem B1, com B2 reduzida).
* `closedMath_of_restantes`: o teorema-mestre com as 6 pontes restantes + as 8 obrigações.
* `closedMathFaithful_sem_pontes`: a parte com enunciado oficial (RH ∧ Beal) depende de
  **duas hipóteses abertas e nenhuma ponte**: `UniformLogBound` (O1) e
  `ExclusaoResidualDescida` (forma residual de Beal, `ATK.BealFermatDescent`).

O que não sai daqui, e por quê:

* B3–B7 são leis sobre modelos paramétricos (`NSModel`, `ComplexityModel`, `HodgeModel`,
  `BSDModel`, `YMModel`). Para um modelo arbitrário elas não são teoremas; só viram teoremas
  depois das ligações L1–L5 (modelos genuínos), que não existem na Mathlib, e aí são
  formalizações grandes (Leray, Cook–Levin, Lefschetz (1,1), Gross–Zagier–Kolyvagin,
  Osterwalder–Schrader).
* `FLTPrimosGeCinco` é o teorema de Wiles–Taylor; a formalização está em andamento fora da
  Mathlib (projeto FLT do Imperial College).
* O1–O8 são os próprios problemas abertos (ou equivalentes a eles).

**CLOSED_MATH continua false.**
-/

namespace ATK.BridgeReduction

open ATK.ClosedMath

/-- Ponte B2 reduzida: Fermat só para expoentes primos `p ≥ 5`. -/
def FLTPrimosGeCinco : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → FermatLastTheoremFor p

/-- **B2 reduzida**: `FermatLastTheorem ⟺ FLT(p)` para todo primo `p ≥ 5`.
(Os expoentes 3 e 4 vêm da Mathlib.) -/
theorem flt_iff_primos_ge_cinco : FermatLastTheorem ↔ FLTPrimosGeCinco := by
  constructor
  · intro h p _ hp5
    exact h p (by omega)
  · intro h
    apply FermatLastTheorem.of_odd_primes
    intro p hp hodd
    by_cases h3 : p = 3
    · subst h3
      exact fermatLastTheoremThree
    · apply h p hp
      have h2 := hp.two_le
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact absurd hodd (by decide)
      have hp4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by decide)
      omega

/-- Beal condicional com a ponte reduzida. -/
theorem beal_conditional_reduzido (hF : FLTPrimosGeCinco)
    (hO : ATK.Conditional.Beal.GCDLowerBoundSmallExponents) :
    ATK.Conditional.Beal.BealConjecture :=
  ATK.Conditional.Beal.beal_conditional (flt_iff_primos_ge_cinco.mpr hF) hO

/-- As pontes que ainda faltam no kernel: B1 saiu, B2 virou `FLTPrimosGeCinco`. -/
structure PontesRestantes (M : Models) : Prop where
  fermatPrimos : FLTPrimosGeCinco
  leray : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion M.ns
  cookLevin : ATK.Conditional.PvsNP.CookLevin M.cx M.sat
  lefschetz : ATK.Conditional.Hodge.KnownCases M.hodge
  grossZagierKolyvagin : ATK.Conditional.BSD.GrossZagierKolyvagin M.bsd
  osterwalderSchrader : ATK.Conditional.YangMills.OSReconstruction M.ym

/-- **As 7 pontes originais ⟺ as 6 restantes** (B1 provada, B2 reduzida). -/
theorem pontes_iff_restantes (M : Models) : Bridges M ↔ PontesRestantes M := by
  constructor
  · intro h
    exact ⟨flt_iff_primos_ge_cinco.mp h.fermat, h.leray, h.cookLevin, h.lefschetz,
      h.grossZagierKolyvagin, h.osterwalderSchrader⟩
  · intro h
    exact ⟨ATK.ObligationsClosed.B1, flt_iff_primos_ge_cinco.mpr h.fermatPrimos, h.leray,
      h.cookLevin, h.lefschetz, h.grossZagierKolyvagin, h.osterwalderSchrader⟩

/-- **Teorema-mestre reduzido**: 6 pontes restantes + 8 obrigações abertas ⇒ os 7 enunciados. -/
theorem closedMath_of_restantes {M : Models} (hB : PontesRestantes M) (hO : OpenObligations M) :
    SevenStatements M :=
  closedMath_of_obligations ((pontes_iff_restantes M).mpr hB) hO

/-- Parte oficial (RH ∧ Beal) na forma do teorema-mestre: O1, O2 e só a ponte FLT(p ≥ 5). -/
theorem closedMathFaithful_reduzido (hF : FLTPrimosGeCinco)
    (hRH : ATK.Conditional.Riemann.UniformLogBound)
    (hBeal : ATK.Conditional.Beal.GCDLowerBoundSmallExponents) : ClosedMathFaithful :=
  closedMathFaithful_of_obligations ATK.ObligationsClosed.B1 (flt_iff_primos_ge_cinco.mpr hF)
    hRH hBeal

/-- **Parte oficial sem nenhuma ponte**: RH ∧ Beal a partir de duas hipóteses abertas,
`UniformLogBound` (O1) e a forma residual de Beal (`ExclusaoResidualDescida`). -/
theorem closedMathFaithful_sem_pontes (hRH : ATK.Conditional.Riemann.UniformLogBound)
    (hBeal : ATK.BealFermatDescent.ExclusaoResidualDescida) : ClosedMathFaithful :=
  ⟨ATK.BaezDuarteBridge.riemann_of_uniformLogBound hRH,
    ATK.BealFermatDescent.beal_iff_residual_descida.mpr hBeal⟩

/-- E, como equivalência para Beal: a parte oficial ⟺ RH ∧ residual (sem pontes). -/
theorem closedMathFaithful_iff :
    ClosedMathFaithful ↔ RiemannHypothesis ∧ ATK.BealFermatDescent.ExclusaoResidualDescida := by
  constructor
  · rintro ⟨hRH, hBeal⟩
    exact ⟨hRH, ATK.BealFermatDescent.beal_iff_residual_descida.mp hBeal⟩
  · rintro ⟨hRH, hRes⟩
    exact ⟨hRH, ATK.BealFermatDescent.beal_iff_residual_descida.mpr hRes⟩

end ATK.BridgeReduction

#print axioms ATK.BridgeReduction.flt_iff_primos_ge_cinco
#print axioms ATK.BridgeReduction.beal_conditional_reduzido
#print axioms ATK.BridgeReduction.pontes_iff_restantes
#print axioms ATK.BridgeReduction.closedMath_of_restantes
#print axioms ATK.BridgeReduction.closedMathFaithful_reduzido
#print axioms ATK.BridgeReduction.closedMathFaithful_sem_pontes
#print axioms ATK.BridgeReduction.closedMathFaithful_iff
