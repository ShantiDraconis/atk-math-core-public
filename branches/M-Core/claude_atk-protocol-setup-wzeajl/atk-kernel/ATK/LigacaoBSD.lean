import ATK.Conditional.BSD
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# ATK — Ligação L4 (parte do posto): o enunciado de BSD do Clay sobre os objetos da Mathlib

A Mathlib v4.34.1 já tem a função L de uma curva de Weierstrass sobre um corpo de números
(`WeierstrassCurve.LFunction`, `WeierstrassCurve.LSeries`), com os fatores locais certos em todo
primo (modelo minimal, redução boa, multiplicativa partida/não partida, aditiva), e o grupo dos
pontos racionais (`E.toAffine.Point`). Com isso o **enunciado do Clay** (Wiles, descrição oficial):

> a expansão de Taylor de `L(E, s)` em `s = 1` tem a forma `c (s − 1)^r + …` com `c ≠ 0` e
> `r = rank E(ℚ)`,

escreve-se sem objeto novo:

* `Continuacao E F`: `F` é inteira e coincide com a série L de `E` no semiplano `Re s > 3/2`
  (onde o produto de Euler converge absolutamente);
* `postoMW E`: o posto de Mordell–Weil, `rank_ℤ E(ℚ)` em `ℕ∞`;
* `ClayBSD`: para toda curva elíptica `E/ℚ`, existe a continuação e a sua ordem em `s = 1` é o posto.

Provado aqui: a continuação é única (`continuacao_unica`), a ordem não depende da escolha
(`ordem_bem_definida`), e o corolário do Clay `L(E, 1) = 0 ⟺ posto > 0` (`zero_iff_posto_pos`).

Para usar o modelo paramétrico (`ATK.Conditional.BSD.BSDModel`, postos em `ℕ`) é preciso que a
continuação exista com ordem finita (modularidade: Wiles, Taylor–Wiles, Breuil–Conrad–Diamond–Taylor)
e que o posto seja finito (teorema de Mordell–Weil). São teoremas publicados que ainda não estão na
Mathlib: entram como hipóteses explícitas (`Modularidade`, `MordellWeil`), nunca como axiomas
(`posto_iff`).

**Falta** para a ligação L4 completa: a fórmula refinada (período `Ω_E`, regulador de Néron–Tate,
`Ш`, números de Tamagawa, torção), exigida pelo portão `BSDFull`. Nada aqui prova BSD.
-/

open WeierstrassCurve Complex

namespace ATK.LigacaoBSD

/-- `F` continua a série L de `E`: é inteira e coincide com `L(E, s)` em `Re s > 3/2`. -/
def Continuacao (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

/-- Posto de Mordell–Weil de `E(ℚ)`, em `ℕ∞` (`⊤` se não fosse finito). -/
noncomputable def postoMW (E : WeierstrassCurve ℚ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℤ E.toAffine.Point)

/-- **O enunciado de Birch e Swinnerton-Dyer do Clay** (parte do posto). -/
def ClayBSD : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ F : ℂ → ℂ, Continuacao E F ∧ analyticOrderAt F 1 = postoMW E

/-- **A continuação é única**: duas funções inteiras que coincidem em `Re s > 3/2` são iguais. -/
theorem continuacao_unica {E : WeierstrassCurve ℚ} {F G : ℂ → ℂ} (hF : Continuacao E F)
    (hG : Continuacao E G) : F = G := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.1.analyticAt z
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.1.analyticAt z
  refine hFa.eq_of_eventuallyEq hGa (z₀ := 2) ?_
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  filter_upwards [hopen.mem_nhds hmem] with s hs
  rw [hF.2 s hs, hG.2 s hs]

/-- A ordem em `s = 1` não depende da continuação escolhida. -/
theorem ordem_bem_definida {E : WeierstrassCurve ℚ} {F G : ℂ → ℂ} (hF : Continuacao E F)
    (hG : Continuacao E G) : analyticOrderAt F 1 = analyticOrderAt G 1 := by
  rw [continuacao_unica hF hG]

/-- **Corolário do Clay**: sob a igualdade de BSD, `L(E, 1) = 0` exatamente quando o posto é
positivo (isto é, quando `E(ℚ)` é infinito). -/
theorem zero_iff_posto_pos {E : WeierstrassCurve ℚ} {F : ℂ → ℂ} (hF : Continuacao E F)
    (h : analyticOrderAt F 1 = postoMW E) : F 1 = 0 ↔ 0 < postoMW E := by
  rw [← h, pos_iff_ne_zero, Ne, analyticOrderAt_eq_zero]
  have ha : AnalyticAt ℂ F 1 := hF.1.analyticAt 1
  constructor
  · intro h0 hc
    rcases hc with hc | hc
    · exact hc ha
    · exact hc h0
  · intro hn
    by_contra h0
    exact hn (Or.inr h0)

/-- Modularidade (com `L(E, s) ≢ 0`): a continuação existe e tem ordem finita em `s = 1`. -/
def Modularidade : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ F : ℂ → ℂ, Continuacao E F ∧ analyticOrderAt F 1 ≠ ⊤

/-- Teorema de Mordell–Weil (parte usada): o posto de `E(ℚ)` é finito. -/
def MordellWeil : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → postoMW E ≠ ⊤

/-- Curvas elípticas sobre `ℚ`. -/
abbrev CurvaQ := {E : WeierstrassCurve ℚ // E.IsElliptic}

open Classical in
/-- Posto analítico em `ℕ`: a ordem da continuação em `s = 1` (valor-lixo `posto + 1` se não houver
continuação, para que a igualdade de BSD falhe nesse caso). -/
noncomputable def postoAnalitico (E : CurvaQ) : ℕ :=
  if h : ∃ F : ℂ → ℂ, Continuacao E.1 F then (analyticOrderAt (Classical.choose h) 1).toNat
  else (postoMW E.1).toNat + 1

/-- **A parte do posto do modelo genuíno** (`BSDModel` sem a fórmula refinada). -/
noncomputable def modeloPosto (refinada : CurvaQ → Prop) : ATK.Conditional.BSD.BSDModel.{0} where
  Curve := CurvaQ
  rank E := (postoMW E.1).toNat
  analyticRank := postoAnalitico
  RefinedFormula := refinada

/-- **Fidelidade da parte do posto**: com modularidade e Mordell–Weil (teoremas publicados, como
hipóteses explícitas), a igualdade de postos do modelo é exatamente o enunciado do Clay. -/
theorem posto_iff (hMod : Modularidade) (hMW : MordellWeil) (refinada : CurvaQ → Prop) :
    ATK.Conditional.BSD.BSDRank (modeloPosto refinada) ↔ ClayBSD := by
  constructor
  · intro h E hE
    obtain ⟨F, hF, hfin⟩ := hMod E hE
    refine ⟨F, hF, ?_⟩
    have hE' := h ⟨E, hE⟩
    simp only [modeloPosto, postoAnalitico] at hE'
    have hex : ∃ F : ℂ → ℂ, Continuacao E F := ⟨F, hF⟩
    rw [dite_eq_left_of_eq_true (eq_true hex)] at hE'
    rw [ordem_bem_definida (Classical.choose_spec hex) hF] at hE'
    have hr := hMW E hE
    rw [← ENat.natCast_toNat hfin, ← ENat.natCast_toNat hr, hE']
  · intro h ⟨E, hE⟩
    obtain ⟨F, hF, hord⟩ := h E hE
    simp only [modeloPosto, postoAnalitico]
    have hex : ∃ F : ℂ → ℂ, Continuacao E F := ⟨F, hF⟩
    rw [dite_eq_left_of_eq_true (eq_true hex), ordem_bem_definida (Classical.choose_spec hex) hF, hord]

end ATK.LigacaoBSD

#print axioms ATK.LigacaoBSD.continuacao_unica
#print axioms ATK.LigacaoBSD.ordem_bem_definida
#print axioms ATK.LigacaoBSD.zero_iff_posto_pos
#print axioms ATK.LigacaoBSD.posto_iff
