import ATK.ClosedMathReal
import ATK.YMOficial
import ATK.HodgeOficial

/-!
# Os sete enunciados oficiais, num só lugar

| problema | enunciado | grau de fidelidade |
|---|---|---|
| RH | `RiemannHypothesis` (zeta da Mathlib) | **REAL** |
| Beal | `aˣ + bʸ = cᶻ`, `x, y, z > 2` ⇒ primo comum | **REAL** |
| Navier–Stokes | Clay (A): `ν > 0`, `u₀ ∈ 𝓢(ℝ³, ℝ³)`, `div u₀ = 0` ⇒ solução suave global, energia limitada | **REAL** |
| P vs NP | `classeP ≠ classeNP` sobre `Turing.FinTM2` em tempo polinomial | **REAL** |
| BSD | posto (Clay) e fórmula refinada, toda curva elíptica sobre `ℚ`, `WeierstrassCurve.LFunction` | **REAL** |
| Hodge | variedade projetiva lisa sobre `ℂ` (esquema, `Proj`, `SmoothOfRelativeDimension`), ciclos algébricos e homologia singular da Mathlib | **REAL relativo a 3 construções ausentes**: analitificação, decomposição de Hodge, classe de ciclo |
| Yang–Mills | `𝔤` compacta simples, teoria de Wightman em `ℝ⁴`, não gaussiana, lacuna `Δ > 0` | **núcleo REAL**; a "correspondência a Yang–Mills" não tem definição formal no texto do Clay e é um parâmetro |

`Sete C Corr` é a conjunção. `sete_condicional` a deriva das lacunas reais, com hipóteses
explícitas. Não existe aqui teorema `Sete` sem hipóteses: **CLOSED_MATH continua false**.
-/

namespace ATK.EnunciadosOficiais

open ATK.Termos

/-- Riemann. -/
def RH : Prop := RiemannHypothesis

/-- Beal. -/
def Beal : Prop := ATK.Conditional.Beal.BealConjecture

/-- Navier–Stokes, enunciado (A) do Clay. -/
def NS : Prop := ATK.ClosedMathReal.NSReal

/-- P vs NP. -/
def PNP : Prop := ATK.LigacaoPNP.PneNP

/-- Birch–Swinnerton-Dyer: posto e fórmula refinada. -/
def BSD : Prop := ATK.BSDRefinada.ClayBSDCompleto

/-- Hodge, relativo às construções `C`. -/
def Hodge (C : ATK.HodgeOficial.ConstrucoesHodge) : Prop := ATK.HodgeOficial.HodgeOficial C

/-- Tipo do critério de correspondência a Yang–Mills clássico. -/
abbrev Correspondencia : Type 1 := ∀ (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (H : Type)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], ATK.L5Base.Wightman H → Prop

/-- Yang–Mills, com o critério de correspondência `Corr`. -/
def YM (Corr : Correspondencia) : Prop := ATK.YMOficial.YMClay Corr

/-- Os sete. -/
def Sete (C : ATK.HodgeOficial.ConstrucoesHodge) (Corr : Correspondencia) : Prop :=
  RH ∧ Beal ∧ NS ∧ PNP ∧ BSD ∧ Hodge C ∧ YM Corr

/-! ## Fidelidade -/

/-- NS é o enunciado (A) do Clay no modelo genuíno. -/
theorem ns_iff_clay : NS ↔ ATK.Conditional.NavierStokes.ClayStatementA ATK.LigacaoNS.modeloNS :=
  ATK.LigacaoNS.clayA_iff.symm

/-- P vs NP é o enunciado do modelo genuíno. -/
theorem pnp_iff_modelo : PNP ↔ ATK.Conditional.PvsNP.PneNP ATK.ModeloPNP.modeloPNP :=
  ATK.ModeloPNP.fiel.symm

/-- Hodge é `HodgeConjecture` no modelo das construções. -/
theorem hodge_iff_modelo (C : ATK.HodgeOficial.ConstrucoesHodge) :
    Hodge C ↔ ATK.Conditional.Hodge.HodgeConjecture (ATK.HodgeOficial.modelo C) :=
  ATK.HodgeOficial.hodgeOficial_iff_modelo C

/-- YM implica o núcleo formal, qualquer que seja o critério de correspondência. -/
theorem ym_nucleo (Corr : Correspondencia) : YM Corr → ATK.YMOficial.YMNucleo :=
  ATK.YMOficial.clay_implica_nucleo

/-! ## Refutação: o que refutaria cada enunciado real -/

/-- Refutar RH é exibir um zero não trivial de ζ fora da reta crítica. -/
theorem rh_refutacao : ¬ RH ↔ ∃ s : ℂ, riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1 ∧ s.re ≠ 1 / 2 :=
  RH.refutacao_iff

/-! ## Fechamento condicional dos sete -/

/-- **Os sete enunciados** a partir das lacunas reais (`ClosedMathReal.Lacunas`) e das lacunas de
Hodge no modelo das construções `C`. YM entra como hipótese porque a sua correspondência não tem
critério formal no texto oficial. -/
theorem sete_condicional {C : ATK.HodgeOficial.ConstrucoesHodge} {Corr : Correspondencia}
    {Hm : ATK.Conditional.Hodge.HodgeModel.{0, 0}} {Ym : ATK.Conditional.YangMills.YMModel.{0, 0, 0}}
    (L : ATK.ClosedMathReal.Lacunas Hm Ym)
    (hB5 : Hodge.ponteB5 (ATK.HodgeOficial.modelo C)) (hO5 : Hodge.produtorO5 (ATK.HodgeOficial.modelo C))
    (hYM : YM Corr) : Sete C Corr := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, -, -⟩ := ATK.ClosedMathReal.closedMath_real L
  exact ⟨h1, h2, h3, h4, h5, (hodge_iff_modelo C).mpr (Hodge.fecha hB5 hO5), hYM⟩

/-- Se qualquer um dos sete for refutado, as hipóteses do fechamento não podem valer todas. -/
theorem sete_refutado {C : ATK.HodgeOficial.ConstrucoesHodge} {Corr : Correspondencia}
    (h : ¬ Sete C Corr) {Hm : ATK.Conditional.Hodge.HodgeModel.{0, 0}}
    {Ym : ATK.Conditional.YangMills.YMModel.{0, 0, 0}} (L : ATK.ClosedMathReal.Lacunas Hm Ym)
    (hB5 : Hodge.ponteB5 (ATK.HodgeOficial.modelo C))
    (hO5 : Hodge.produtorO5 (ATK.HodgeOficial.modelo C)) : ¬ YM Corr :=
  fun hYM => h (sete_condicional L hB5 hO5 hYM)

end ATK.EnunciadosOficiais

#print axioms ATK.EnunciadosOficiais.ns_iff_clay
#print axioms ATK.EnunciadosOficiais.pnp_iff_modelo
#print axioms ATK.EnunciadosOficiais.hodge_iff_modelo
#print axioms ATK.EnunciadosOficiais.ym_nucleo
#print axioms ATK.EnunciadosOficiais.rh_refutacao
#print axioms ATK.EnunciadosOficiais.sete_condicional
#print axioms ATK.EnunciadosOficiais.sete_refutado
