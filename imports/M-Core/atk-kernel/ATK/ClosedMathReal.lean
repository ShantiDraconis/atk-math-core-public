import ATK.Termos
import ATK.CookLevinNP
import ATK.BSDRefinada

/-!
# CLOSED_MATH = true sobre os enunciados reais — a forma condicional

`ATK.ClosedMath.SevenStatements M` fala de modelos `M`. Aqui o alvo usa os **enunciados reais**
que a Mathlib e as ligações já exprimem:

| problema | enunciado real | origem |
|---|---|---|
| RH | `RiemannHypothesis` | Mathlib |
| Beal | `∀ a b c x y z, … aˣ + bʸ = cᶻ → ∃ p primo, p ∣ a, b, c` | `ATK.Conditional.Beal` |
| NS | Clay (A): para `ν > 0` e `u₀ ∈ 𝓢(ℝ³, ℝ³)` com `div u₀ = 0`, existe solução suave global com energia limitada | `ATK.LigacaoNS` |
| P vs NP | `classeP ≠ classeNP` sobre `Turing.FinTM2` em tempo polinomial | `ATK.LigacaoPNP` |
| BSD | Clay (posto) **e** fórmula refinada, para toda curva elíptica sobre `ℚ`, com `WeierstrassCurve.LFunction` | `ATK.LigacaoBSD`, `ATK.BSDRefinada` |
| Hodge | **não exprimível na Mathlib** (falta a cohomologia de variedades projetivas e a classe de ciclo) | modelo `H` |
| YM | **não exprimível na Mathlib** (falta teoria de calibre quântica em `ℝ⁴`) | modelo `Y` |

`closedMath_real` prova o alvo a partir das **lacunas reais** (`Lacunas`): os produtores abertos e
as pontes publicadas que ainda não estão no kernel. A ponte de Cook–Levin (B4) e o critério de
Báez-Duarte (B1) já estão provados e **não** entram como hipótese.

O que o kernel mostra a seguir (`lacunas_*_iff`): para RH, Beal e P vs NP a lacuna é
**equivalente** ao enunciado real. Supor a lacuna é supor a conjectura.

Não existe teorema `closed_math_real : EnunciadosReais` sem hipóteses. O portão
`ATK/ClosedMathGate.lean` continua ausente e **CLOSED_MATH continua false**.
-/

namespace ATK.ClosedMathReal

open ATK.Termos

/-- Navier–Stokes, enunciado (A) do Clay, sobre os objetos da Mathlib. -/
def NSReal : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzMap ATK.LigacaoNS.E3 ATK.LigacaoNS.E3,
    (∀ x, ATK.LigacaoNS.div u₀ x = 0) → ∃ U P, ATK.LigacaoNS.SolucaoGlobal ν u₀ U P

/-- Os enunciados reais exprimíveis hoje: RH, Beal, NS (A), P ≠ NP e BSD completo. -/
def EnunciadosReais : Prop :=
  RiemannHypothesis ∧ ATK.Conditional.Beal.BealConjecture ∧ NSReal ∧ ATK.LigacaoPNP.PneNP ∧
    ATK.BSDRefinada.ClayBSDCompleto

/-- O alvo completo: os cinco reais, mais Hodge e YM sobre modelos (ainda sem enunciado real). -/
def ClosedMathRealAlvo (H : ATK.Conditional.Hodge.HodgeModel.{0, 0})
    (Y : ATK.Conditional.YangMills.YMModel.{0, 0, 0}) : Prop :=
  EnunciadosReais ∧ ATK.Conditional.Hodge.HodgeConjecture H ∧ ATK.Conditional.YangMills.ClayYM Y

/-- As lacunas reais: produtores abertos (`OPEN_MATH`) e pontes publicadas não formalizadas. -/
structure Lacunas (H : ATK.Conditional.Hodge.HodgeModel.{0, 0})
    (Y : ATK.Conditional.YangMills.YMModel.{0, 0, 0}) : Prop where
  /-- O1: não há zero não trivial de ζ fora da reta crítica. -/
  rh : RH.produtor
  /-- O2: exclusão do resíduo de descida de Beal. -/
  beal : Beal.produtor
  /-- B3: critério de explosão de Leray (publicado). -/
  nsB3 : NS.ponteB3 ATK.LigacaoNS.modeloNS
  /-- O3: cota a priori de enstrofia. -/
  nsO3 : NS.produtorO3 ATK.LigacaoNS.modeloNS
  /-- O4: SAT ∉ P sobre as máquinas da Mathlib. -/
  pnp : PNP.produtorO4 ATK.ModeloPNP.modeloPNP ATK.ModeloPNP.SAT
  /-- Modularidade das curvas elípticas sobre ℚ (Wiles, Taylor–Wiles, BCDT; publicado). -/
  modularidade : ATK.LigacaoBSD.Modularidade
  /-- Teorema de Mordell–Weil (publicado). -/
  mordellWeil : ATK.LigacaoBSD.MordellWeil
  /-- B6: Gross–Zagier–Kolyvagin (publicado). -/
  bsdB6 : BSD.ponteB6 ATK.BSDRefinada.modeloCompleto
  /-- O6: BSD para posto ≥ 2. -/
  bsdO6 : BSD.produtorO6 ATK.BSDRefinada.modeloCompleto
  /-- O7: fórmula refinada. -/
  bsdO7 : BSD.produtorO7 ATK.BSDRefinada.modeloCompleto
  /-- B5 e O5 de Hodge, sobre o modelo `H`. -/
  hodgeB5 : Hodge.ponteB5 H
  hodgeO5 : Hodge.produtorO5 H
  /-- B7 e O8 de Yang–Mills, sobre o modelo `Y`. -/
  ymB7 : YM.ponteB7 Y
  ymO8 : YM.produtorO8 Y

/-- **CLOSED_MATH sobre os enunciados reais, na forma condicional**: as lacunas dão o alvo. -/
theorem closedMath_real {H : ATK.Conditional.Hodge.HodgeModel.{0, 0}}
    {Y : ATK.Conditional.YangMills.YMModel.{0, 0, 0}} (L : Lacunas H Y) :
    ClosedMathRealAlvo H Y :=
  ⟨⟨RH.fecha L.rh,
    Beal.fecha L.beal,
    ATK.LigacaoNS.clayA_iff.mp (NS.fecha L.nsB3 L.nsO3),
    ATK.ModeloPNP.fiel.mp (PNP.fecha ATK.CookLevinNP.cookLevin L.pnp),
    (ATK.BSDRefinada.bsdFull_iff L.modularidade L.mordellWeil).mp
      (BSD.fecha L.bsdB6 L.bsdO6 L.bsdO7)⟩,
   Hodge.fecha L.hodgeB5 L.hodgeO5,
   YM.fecha L.ymB7 L.ymO8⟩

/-- Só os cinco enunciados reais. -/
theorem enunciadosReais_de_lacunas {H : ATK.Conditional.Hodge.HodgeModel.{0, 0}}
    {Y : ATK.Conditional.YangMills.YMModel.{0, 0, 0}} (L : Lacunas H Y) : EnunciadosReais :=
  (closedMath_real L).1

/-! ## O que o kernel mostra: as lacunas são as conjecturas -/

/-- RH: a lacuna é **equivalente** ao enunciado real. -/
theorem lacuna_rh_iff : RH.produtor ↔ RiemannHypothesis := RH.exato

/-- Beal: a lacuna é **equivalente** ao enunciado real. -/
theorem lacuna_beal_iff : Beal.produtor ↔ ATK.Conditional.Beal.BealConjecture := Beal.exato

/-- P vs NP: com Cook–Levin provado no kernel, a lacuna é **equivalente** a `P ≠ NP` real. -/
theorem lacuna_pnp_iff :
    PNP.produtorO4 ATK.ModeloPNP.modeloPNP ATK.ModeloPNP.SAT ↔ ATK.LigacaoPNP.PneNP :=
  (PNP.exato ATK.CookLevinNP.cookLevin).trans ATK.ModeloPNP.fiel

/-- Para RH, Beal e P vs NP, supor as lacunas é exatamente supor os enunciados reais. -/
theorem tres_lacunas_iff :
    (RH.produtor ∧ Beal.produtor ∧ PNP.produtorO4 ATK.ModeloPNP.modeloPNP ATK.ModeloPNP.SAT) ↔
      (RiemannHypothesis ∧ ATK.Conditional.Beal.BealConjecture ∧ ATK.LigacaoPNP.PneNP) :=
  and_congr lacuna_rh_iff (and_congr lacuna_beal_iff lacuna_pnp_iff)

/-- Cada lacuna é necessária: refutar um enunciado real derruba toda estrutura de lacunas. -/
theorem sem_lacunas_se_refutado {H : ATK.Conditional.Hodge.HodgeModel.{0, 0}}
    {Y : ATK.Conditional.YangMills.YMModel.{0, 0, 0}} (h : ¬ EnunciadosReais) :
    IsEmpty (Lacunas H Y) :=
  ⟨fun L => h (enunciadosReais_de_lacunas L)⟩

end ATK.ClosedMathReal

#print axioms ATK.ClosedMathReal.closedMath_real
#print axioms ATK.ClosedMathReal.enunciadosReais_de_lacunas
#print axioms ATK.ClosedMathReal.lacuna_rh_iff
#print axioms ATK.ClosedMathReal.lacuna_beal_iff
#print axioms ATK.ClosedMathReal.lacuna_pnp_iff
#print axioms ATK.ClosedMathReal.tres_lacunas_iff
#print axioms ATK.ClosedMathReal.sem_lacunas_se_refutado
