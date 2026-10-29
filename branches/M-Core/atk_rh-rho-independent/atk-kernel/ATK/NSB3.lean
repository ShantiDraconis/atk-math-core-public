import ATK.NSUnicidade
import ATK.AtaqueNS

/-!
# ATK — Navier–Stokes: a ponte B3 no modelo genuíno

Camada 23 do ataque a B3. Os quatro enunciados da redução `ATK.NSClasse.b3_de_classeD` estão
provados na classe de Fourier (`ATK.NSClasse.ClasseF`):

* existência local — `ATK.NSClasse.existenciaLocalF`;
* unicidade fraca–forte — `ATK.NSUnicidade.unicidadeF` (passos U-1…U-8: forma fraca, forma fraca
  de Fourier, Duhamel, identificação, `N = N(bt, bt)`, estimativas trilineares, energia, Gronwall);
* continuação — `ATK.NSContinuacao.continuacaoF`;
* desigualdade de energia — `ATK.NSClasse.desigualdadeEnergiaF`.

Logo o critério de explosão da enstrofia (Leray 1934 + teoria local clássica) vale no modelo
genuíno `ATK.LigacaoNS.modeloNS`, sem hipóteses: `b3_modeloNS`.

Consequência: no modelo genuíno, o enunciado (A) de Clay reduz-se exatamente à obrigação O3
(cota a priori da enstrofia, `EnstrophyAPrioriBound`), que continua **ABERTA**.

**CLOSED_MATH continua false.**
-/

namespace ATK.NSB3

open ATK.LigacaoNS

/-- **A ponte B3 (critério de explosão da enstrofia) no modelo genuíno**, sem hipóteses. -/
theorem b3_modeloNS : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion modeloNS :=
  ATK.NSClasse.b3_de_classeD (fun d => ATK.NSClasse.ClasseF d.1)
    (fun d => ATK.NSClasse.local_ClasseF d.1) ATK.NSClasse.existenciaLocalF
    ATK.NSUnicidade.unicidadeF ATK.NSContinuacao.continuacaoF ATK.NSClasse.desigualdadeEnergiaF

/-- **Clay (A) no modelo genuíno a partir só de O3** (a cota a priori da enstrofia, aberta). -/
theorem clay_ns_de_O3
    (hO3 : ATK.Conditional.NavierStokes.EnstrophyAPrioriBound modeloNS) :
    ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzMap E3 E3, (∀ x, div u₀ x = 0) →
      ∃ U P, SolucaoGlobal ν u₀ U P :=
  clay_ns_condicional b3_modeloNS hO3

/-- **O que um certificado de explosão precisa exibir**, agora sem ponte: explosão ⇒ enstrofia
ilimitada em `[0, T)` para algum `T > 0` em que a solução suave existe. -/
theorem explosao_enstrofia (h : ATK.AtaqueNS.Explosao) :
    ∃ d, modeloNS.Admissible d ∧ ∃ T : ℝ, 0 < T ∧ modeloNS.SmoothOn d T ∧
      ∀ B : ℝ, ∃ t ∈ Set.Ico 0 T, B < modeloNS.enstrophy d t :=
  ATK.AtaqueNS.explosao_enstrofia b3_modeloNS h

/-- **A saída de regularidade** é exatamente a cota a priori O3. -/
theorem regularidade_de_cota
    (hA : ATK.Conditional.NavierStokes.EnstrophyAPrioriBound modeloNS) :
    ¬ ATK.AtaqueNS.Explosao :=
  ATK.AtaqueNS.regularidade_de_cota b3_modeloNS hA

end ATK.NSB3

#print axioms ATK.NSB3.b3_modeloNS
#print axioms ATK.NSB3.clay_ns_de_O3
#print axioms ATK.NSB3.explosao_enstrofia
#print axioms ATK.NSB3.regularidade_de_cota
