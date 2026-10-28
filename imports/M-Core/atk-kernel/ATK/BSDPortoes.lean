import ATK.LigacaoBSD

/-!
# BSD em dois portões: BSD_CLAY (posto) e BSD_REFINED (fórmula refinada)

O enunciado oficial do Clay para BSD é a parte do posto; a fórmula do coeficiente líder é a forma
refinada. O alvo do projeto continua sendo **BSD_FULL = BSD_CLAY ∧ BSD_REFINED**: nada aqui
enfraquece a linha BSD. A separação só torna cada parte um portão auditável por si.

* `full_iff`: `BSDFull M ↔ BSDClay M ∧ BSDRefinada M` (por definição);
* `clay_iff`: BSD_CLAY = ponte B6 (Gross–Zagier–Kolyvagin) ∧ produtor O6;
* `refinada_iff`: BSD_REFINED = produtor O7;
* `clay_fiel`: com modularidade e Mordell–Weil (teoremas publicados, hipóteses explícitas),
  BSD_CLAY no modelo do posto é **exatamente** `ClayBSD`, o enunciado do Clay sobre a Mathlib;
* `clay_nao_implica_full`, `refinada_nao_implica_clay`: os dois portões são independentes
  (modelos-teste), então tirar um deles do alvo o enfraqueceria de fato.
-/

namespace ATK.BSDPortoes

open ATK.Conditional.BSD

universe u

/-- **BSD_CLAY**: a parte do posto, `ord_{s=1} L(E,s) = posto E(ℚ)` para toda curva. -/
def BSDClay (M : BSDModel.{u}) : Prop := BSDRank M

/-- **BSD_REFINED**: Ш finito e a fórmula do coeficiente líder para toda curva. -/
def BSDRefinada (M : BSDModel.{u}) : Prop := RefinedOpen M

/-- **BSD_FULL = BSD_CLAY ∧ BSD_REFINED.** -/
theorem full_iff (M : BSDModel.{u}) : BSDFull M ↔ BSDClay M ∧ BSDRefinada M := Iff.rfl

theorem full_clay {M : BSDModel.{u}} (h : BSDFull M) : BSDClay M := h.1

theorem full_refinada {M : BSDModel.{u}} (h : BSDFull M) : BSDRefinada M := h.2

theorem full_de_partes {M : BSDModel.{u}} (h1 : BSDClay M) (h2 : BSDRefinada M) : BSDFull M :=
  ⟨h1, h2⟩

/-- BSD_CLAY = ponte B6 ∧ produtor O6. -/
theorem clay_iff (M : BSDModel.{u}) : BSDClay M ↔ GrossZagierKolyvagin M ∧ RankOpen M := by
  constructor
  · intro h
    exact ⟨fun E _ => (h E).symm, fun E _ => (h E).symm⟩
  · rintro ⟨hb, h6⟩
    exact bsd_rank_conditional hb h6

/-- BSD_REFINED = produtor O7. -/
theorem refinada_iff (M : BSDModel.{u}) : BSDRefinada M ↔ RefinedOpen M := Iff.rfl

/-- **Fidelidade de BSD_CLAY ao Clay**: no modelo do posto (L4), com modularidade e Mordell–Weil,
o portão BSD_CLAY é exatamente `ClayBSD`. -/
theorem clay_fiel (hMod : ATK.LigacaoBSD.Modularidade) (hMW : ATK.LigacaoBSD.MordellWeil)
    (r : ATK.LigacaoBSD.CurvaQ → Prop) :
    BSDClay (ATK.LigacaoBSD.modeloPosto r) ↔ ATK.LigacaoBSD.ClayBSD :=
  ATK.LigacaoBSD.posto_iff hMod hMW r

/-- Modelo-teste: postos iguais, fórmula refinada falsa. -/
def modeloSoPosto : BSDModel.{0} := ⟨Unit, fun _ => 0, fun _ => 0, fun _ => False⟩

/-- Modelo-teste: fórmula refinada verdadeira, postos diferentes. -/
def modeloSoRefinada : BSDModel.{0} := ⟨Unit, fun _ => 0, fun _ => 1, fun _ => True⟩

/-- BSD_CLAY não implica BSD_FULL: tirar a fórmula refinada do alvo o enfraquece. -/
theorem clay_nao_implica_full : BSDClay modeloSoPosto ∧ ¬ BSDFull modeloSoPosto :=
  ⟨fun _ => rfl, fun h => h.2 ()⟩

/-- BSD_REFINED não implica BSD_CLAY: as duas partes são independentes. -/
theorem refinada_nao_implica_clay : BSDRefinada modeloSoRefinada ∧ ¬ BSDClay modeloSoRefinada :=
  ⟨fun _ => trivial, fun h => Nat.one_ne_zero (h ())⟩

end ATK.BSDPortoes

#print axioms ATK.BSDPortoes.full_iff
#print axioms ATK.BSDPortoes.full_clay
#print axioms ATK.BSDPortoes.full_refinada
#print axioms ATK.BSDPortoes.full_de_partes
#print axioms ATK.BSDPortoes.clay_iff
#print axioms ATK.BSDPortoes.refinada_iff
#print axioms ATK.BSDPortoes.clay_fiel
#print axioms ATK.BSDPortoes.clay_nao_implica_full
#print axioms ATK.BSDPortoes.refinada_nao_implica_clay
