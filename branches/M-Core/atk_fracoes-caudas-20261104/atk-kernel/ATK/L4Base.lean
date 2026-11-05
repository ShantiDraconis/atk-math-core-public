import ATK.LigacaoBSDTestes

/-!
# ATK — L4, base: a conjectura de BSD (parte do posto) em forma de biblioteca

Rascunho no estilo da Mathlib para a ligação L4 (o PR sugerido "L4 BSD"): uma estrutura para a
continuação analítica da série L de uma curva de Weierstrass sobre `ℚ`, o posto analítico e o
enunciado de BSD por curva, sobre os objetos que a Mathlib já tem (`WeierstrassCurve.LSeries`, o
grupo `E.toAffine.Point`).

* `LFunctionContinued E`: função inteira que coincide com `E.LSeries` em `Re s > 3/2`. O semiplano
  é `3/2` e não `1`: `LSeries` da Mathlib é uma soma `tsum`, que vale `0` fora da somabilidade
  absoluta; com `1 < Re s` a estrutura pediria `L s = 0` na faixa `1 < Re s ≤ 3/2`, onde a série
  de uma curva elíptica não é absolutamente somável, e ficaria vazia para as curvas verdadeiras.
  Pela cota de Hasse, `3/2` é o semiplano de convergência absoluta.
* `LFunctionContinued` tem no máximo um elemento (`subsingleton`): a continuação é única.
* `BSDConjecture E`: existe a continuação e sua ordem em `s = 1` é o posto de Mordell–Weil.
* `clayBSD_iff`: `ATK.LigacaoBSD.ClayBSD` (o enunciado do Clay, parte do posto) é exatamente
  `BSDConjecture` para toda curva elíptica.
* **Teste de sanidade** na curva `y² = x³ − x` (posto 0, calculado no grupo de pontos da
  Mathlib): `BSDConjecture E ⟺ ∃ continuação com L(E, 1) ≠ 0`.

Nada aqui prova BSD. **CLOSED_MATH continua false.**
-/

open WeierstrassCurve Complex ATK.LigacaoBSD

namespace ATK.L4Base

/-- Continuação analítica da série L de `E`: inteira e igual a `E.LSeries` em `Re s > 3/2`. -/
structure LFunctionContinued (E : WeierstrassCurve ℚ) where
  /-- A função continuada. -/
  L : ℂ → ℂ
  /-- É inteira. -/
  entire : Differentiable ℂ L
  /-- Coincide com o produto de Euler no semiplano de convergência absoluta. -/
  euler_eq : ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

namespace LFunctionContinued

variable {E : WeierstrassCurve ℚ}

theorem continuacao (Lc : LFunctionContinued E) : Continuacao E Lc.L := ⟨Lc.entire, Lc.euler_eq⟩

/-- A continuação de uma `Continuacao`. -/
def ofContinuacao {F : ℂ → ℂ} (h : Continuacao E F) : LFunctionContinued E := ⟨F, h.1, h.2⟩

theorem ext_L {Lc Lc' : LFunctionContinued E} (h : Lc.L = Lc'.L) : Lc = Lc' := by
  cases Lc; cases Lc'; simp only at h; subst h; rfl

/-- **Unicidade**: há no máximo uma continuação. -/
instance subsingleton : Subsingleton (LFunctionContinued E) :=
  ⟨fun Lc Lc' => ext_L (continuacao_unica Lc.continuacao Lc'.continuacao)⟩

/-- Posto analítico: a ordem do zero em `s = 1`. -/
noncomputable def analyticRank (Lc : LFunctionContinued E) : ℕ∞ := analyticOrderAt Lc.L 1

end LFunctionContinued

/-- Posto de Mordell–Weil de `E(ℚ)` (em `ℕ∞`). -/
noncomputable def rank (E : WeierstrassCurve ℚ) : ℕ∞ := postoMW E

/-- **Conjectura de Birch e Swinnerton-Dyer** (parte do posto) para a curva `E`. -/
def BSDConjecture (E : WeierstrassCurve ℚ) : Prop :=
  ∃ Lc : LFunctionContinued E, Lc.analyticRank = rank E

/-- Como a continuação é única, "existe" e "para toda" coincidem quando ela existe. -/
theorem bsd_iff_forall {E : WeierstrassCurve ℚ} :
    BSDConjecture E ↔ Nonempty (LFunctionContinued E) ∧ ∀ Lc : LFunctionContinued E,
      Lc.analyticRank = rank E := by
  constructor
  · rintro ⟨Lc, h⟩
    exact ⟨⟨Lc⟩, fun Lc' => by rw [Subsingleton.elim Lc' Lc]; exact h⟩
  · rintro ⟨⟨Lc⟩, h⟩
    exact ⟨Lc, h Lc⟩

/-- **Fidelidade**: o enunciado do Clay (parte do posto) é `BSDConjecture` para toda curva
elíptica sobre `ℚ`. -/
theorem clayBSD_iff : ClayBSD ↔ ∀ E : WeierstrassCurve ℚ, E.IsElliptic → BSDConjecture E := by
  constructor
  · intro h E hE
    obtain ⟨F, hF, hord⟩ := h E hE
    exact ⟨LFunctionContinued.ofContinuacao hF, hord⟩
  · intro h E hE
    obtain ⟨Lc, hLc⟩ := h E hE
    exact ⟨Lc.L, Lc.continuacao, hLc⟩

/-- `L(E, 1) = 0` exatamente quando o posto analítico é positivo. -/
theorem L_one_eq_zero_iff {E : WeierstrassCurve ℚ} (Lc : LFunctionContinued E) :
    Lc.L 1 = 0 ↔ 0 < Lc.analyticRank := by
  have ha : AnalyticAt ℂ Lc.L 1 := Lc.entire.analyticAt 1
  rw [LFunctionContinued.analyticRank, pos_iff_ne_zero, Ne, analyticOrderAt_eq_zero]
  constructor
  · intro h0 hc
    rcases hc with hc | hc
    · exact hc ha
    · exact hc h0
  · intro hn
    by_contra h0
    exact hn (Or.inr h0)

/-! ## Teste de sanidade: `y² = x³ − x` -/

/-- A curva `y² = x³ − x` (`ATK.CongruentCurve.E`). -/
abbrev E32 : WeierstrassCurve ℚ := ATK.CongruentCurve.E

theorem E32_eliptica : E32.IsElliptic := ATK.LigacaoBSDTestes.curva32_eliptica

/-- Posto 0, calculado no grupo de pontos racionais da Mathlib. -/
theorem rank_E32 : rank E32 = 0 := ATK.LigacaoBSDTestes.posto_curva32

/-- **Teste**: para `y² = x³ − x`, BSD diz exatamente que a continuação existe e não se anula em
`s = 1`. -/
theorem bsd_E32_iff : BSDConjecture E32 ↔ ∃ Lc : LFunctionContinued E32, Lc.L 1 ≠ 0 := by
  constructor
  · rintro ⟨Lc, h⟩
    refine ⟨Lc, fun h0 => ?_⟩
    have := (L_one_eq_zero_iff Lc).mp h0
    rw [h, rank_E32] at this
    exact lt_irrefl _ this
  · rintro ⟨Lc, h⟩
    refine ⟨Lc, ?_⟩
    rw [rank_E32]
    by_contra hne
    exact h ((L_one_eq_zero_iff Lc).mpr (pos_iff_ne_zero.mpr hne))

/-- Teste: sob o enunciado do Clay, toda continuação de `y² = x³ − x` é não nula em `s = 1`. -/
theorem clay_E32 (h : ClayBSD) (Lc : LFunctionContinued E32) : Lc.L 1 ≠ 0 := by
  obtain ⟨Lc', hLc'⟩ := bsd_E32_iff.mp (clayBSD_iff.mp h E32 E32_eliptica)
  rw [Subsingleton.elim Lc Lc']
  exact hLc'

end ATK.L4Base

#print axioms ATK.L4Base.LFunctionContinued.continuacao
#print axioms ATK.L4Base.LFunctionContinued.ext_L
#print axioms ATK.L4Base.bsd_iff_forall
#print axioms ATK.L4Base.clayBSD_iff
#print axioms ATK.L4Base.L_one_eq_zero_iff
#print axioms ATK.L4Base.E32_eliptica
#print axioms ATK.L4Base.rank_E32
#print axioms ATK.L4Base.bsd_E32_iff
#print axioms ATK.L4Base.clay_E32
