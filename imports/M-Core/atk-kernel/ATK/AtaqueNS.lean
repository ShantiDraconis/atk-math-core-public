/-
ATK — Programa de ataque, frente Navier–Stokes: as duas saídas do enunciado A.

Sobre o modelo genuíno `ATK.LigacaoNS.modeloNS` (ℝ³, sem força, dados de Schwartz de divergência
nula):

* **`Explosao`**: existe dado admissível sem solução suave global (o contraexemplo, alvo da
  aposta por prova assistida por computador);
* **`explosao_iff`**: `Explosao ⟺ ¬ ClayStatementA` — as duas saídas são exatamente
  complementares, e **`dicotomia`**: uma delas vale (lógica clássica, sem conteúdo matemático);
* **`explosao_enstrofia`**: com a ponte do critério de explosão (Leray 1934, já no kernel),
  uma explosão força enstrofia ilimitada antes de um tempo finito `T` — é o que um certificado
  numérico de explosão precisa exibir;
* **`regularidade_de_cota`**: a outra saída, regularidade, é exatamente a cota a priori da
  enstrofia (`ns_conditional`), refutada no kernel para a rota G5 e aberta em geral.

O método de Chen–Hou (perfil quase autossimilar, estabilidade linear certificada por aritmética
intervalar, estabilidade não linear) entra pela infraestrutura `ATK.BaseIntervalar`; o perfil e as
estimativas de estabilidade são os próximos marcos (ver `ATAQUE.md`).
-/
import ATK.LigacaoNS

namespace ATK.AtaqueNS

open ATK.Conditional.NavierStokes ATK.LigacaoNS

/-- **Explosão**: existe dado admissível sem solução suave global. -/
def Explosao : Prop := ∃ d, modeloNS.Admissible d ∧ ¬ modeloNS.GlobalSmooth d

/-- As duas saídas são complementares. -/
theorem explosao_iff : Explosao ↔ ¬ ClayStatementA modeloNS := by
  constructor
  · rintro ⟨d, hd, hng⟩ h
    exact hng (h d hd)
  · intro h
    by_contra hne
    apply h
    intro d hd
    by_contra hg
    exact hne ⟨d, hd, hg⟩

/-- Uma das duas saídas vale. -/
theorem dicotomia : ClayStatementA modeloNS ∨ Explosao := by
  by_cases h : ClayStatementA modeloNS
  · exact Or.inl h
  · exact Or.inr (explosao_iff.mpr h)

/-- **O que um certificado de explosão precisa exibir**: com a ponte do critério de Leray,
explosão ⇒ enstrofia ilimitada em `[0, T)` para algum `T > 0` em que a solução suave existe. -/
theorem explosao_enstrofia (hB : EnstrophyBlowupCriterion modeloNS) (h : Explosao) :
    ∃ d, modeloNS.Admissible d ∧ ∃ T : ℝ, 0 < T ∧ modeloNS.SmoothOn d T ∧
      ∀ B : ℝ, ∃ t ∈ Set.Ico 0 T, B < modeloNS.enstrophy d t := by
  obtain ⟨d, hd, hng⟩ := h
  exact ⟨d, hd, hB d hd hng⟩

/-- **A saída de regularidade** é a cota a priori da enstrofia (com a mesma ponte). -/
theorem regularidade_de_cota (hB : EnstrophyBlowupCriterion modeloNS)
    (hA : EnstrophyAPrioriBound modeloNS) : ¬ Explosao :=
  fun h => explosao_iff.mp h (ns_conditional hB hA)

end ATK.AtaqueNS

#print axioms ATK.AtaqueNS.explosao_iff
#print axioms ATK.AtaqueNS.dicotomia
#print axioms ATK.AtaqueNS.explosao_enstrofia
#print axioms ATK.AtaqueNS.regularidade_de_cota
