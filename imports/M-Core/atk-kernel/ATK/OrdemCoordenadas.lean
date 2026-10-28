import ATK.ClosedMathToro

/-!
# ATK — B18: a ordem de um zero não muda por mudança de coordenadas conforme

* `ordem_coordenadas` (**B18**): se `φ` é analítica em `a` com `φ'(a) ≠ 0`, então
  `ord_a(F ∘ φ) = ord_{φ(a)}(F)` (Mathlib: `analyticOrderAt_comp_of_deriv_ne_zero`).
* `ordem_composicao`: em geral as ordens **multiplicam**, `ord_a(F ∘ φ) = ord_{φ(a)}(F) · ord_a(φ − φ(a))`;
  por isso `φ'(a) = 0` (ordem de `φ − φ(a)` maior que 1) multiplica a ordem.
* `transporte_ordem` (**B17 + B18**): no transporte `G(φ(s)) = u(s)·F(s)` com `u(a) ≠ 0` e `φ'(a) ≠ 0`,
  o zero de `G` em `φ(a)` tem exatamente a ordem do zero de `F` em `a`.
-/

open Complex

namespace ATK.ClosedMath

/-- **B18**: mudança de coordenadas com `φ'(a) ≠ 0` preserva a ordem do zero. -/
theorem ordem_coordenadas {F φ : ℂ → ℂ} {a : ℂ} (hφ : AnalyticAt ℂ φ a) (hφ' : deriv φ a ≠ 0) :
    analyticOrderAt (F ∘ φ) a = analyticOrderAt F (φ a) :=
  analyticOrderAt_comp_of_deriv_ne_zero hφ hφ'

/-- Composição geral: as ordens multiplicam. -/
theorem ordem_composicao {F φ : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F (φ a))
    (hφ : AnalyticAt ℂ φ a) :
    analyticOrderAt (F ∘ φ) a = analyticOrderAt F (φ a) * analyticOrderAt (fun z => φ z - φ a) a :=
  hF.analyticOrderAt_comp hφ

/-- **B17 + B18**: o transporte `G(φ(s)) = u(s) F(s)`, `u(a) ≠ 0`, `φ'(a) ≠ 0`, preserva a ordem. -/
theorem transporte_ordem {F G φ u : ℂ → ℂ} {a : ℂ} (h : TransporteZero F G φ u)
    (hF : AnalyticAt ℂ F a) (hu : AnalyticAt ℂ u a) (hua : u a ≠ 0)
    (hφ : AnalyticAt ℂ φ a) (hφ' : deriv φ a ≠ 0) :
    analyticOrderAt G (φ a) = analyticOrderAt F a := by
  rw [← ordem_coordenadas hφ hφ']
  have e : G ∘ φ = fun z => u z * F z := funext fun s => h s
  rw [e, ordem_preservada hF hu hua]

end ATK.ClosedMath

-- Auditoria de axiomas (kernel)
#print axioms ATK.ClosedMath.ordem_coordenadas
#print axioms ATK.ClosedMath.ordem_composicao
#print axioms ATK.ClosedMath.transporte_ordem
