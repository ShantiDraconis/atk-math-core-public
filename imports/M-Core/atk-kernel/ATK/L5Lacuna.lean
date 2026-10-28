import ATK.L5Base

/-!
# ATK — Ligação L5: a lacuna de massa sobre os axiomas de Wightman

O campo `GapAtLeast` do modelo paramétrico `ATK.Conditional.YangMills.YMModel` ("o espectro do
hamiltoniano está em `{0} ∪ [Δ, ∞)`") ganha aqui uma definição genuína sobre a estrutura
`ATK.L5Base.Wightman`, no mesmo formato da condição espectral (`U(a) = e^{i P·a}`, medida espectral
testada contra `𝓕 g`):

* `LacunaAoMenos W Δ`: no complemento ortogonal do vácuo, a medida espectral de energia-momento está
  em `{p | Δ ≤ p⁰}` — energia `≥ Δ` para todo estado ortogonal ao vácuo (formulação do Clay);
* `TemLacuna W`: existe `Δ > 0` com `LacunaAoMenos W Δ`.

Testes de sanidade:
* `lacuna_mono`: lacuna `Δ` ⇒ lacuna `Δ'` para `Δ' ≤ Δ`;
* `lacuna_nao_positiva`: para `Δ ≤ 0`, `LacunaAoMenos W Δ` **segue da condição espectral** dos
  axiomas (a definição é coerente com eles);
* `trivial_temLacuna`: a teoria trivial tem lacuna (para todo `Δ`): `Ω^⊥ = 0`.

O problema do Clay pede uma teoria de Yang–Mills **não trivial** com `TemLacuna`; o campo
`IsQuantumYM` (campos de calibre, grupo compacto simples) continua sem definição na Mathlib, e a
ligação L5 continua `NAO_EXISTE_NA_MATHLIB`.
-/

open scoped FourierTransform InnerProductSpace
open MeasureTheory

namespace ATK.L5Lacuna

open ATK.L5Base

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Lacuna de massa `≥ Δ`**: para `ψ, χ ⊥ Ω`, a medida espectral `μ_{χψ}` de `P` está em
`{p | Δ ≤ p⁰}` (testada contra `g` com suporte fora dessa região). -/
def LacunaAoMenos (W : Wightman H) (Δ : ℝ) : Prop :=
  ∀ ψ χ : H, ⟪W.Ω, ψ⟫_ℂ = 0 → ⟪W.Ω, χ⟫_ℂ = 0 →
    ∀ g : SchwartzMap ET ℂ, Disjoint (tsupport g) {p : ET | Δ ≤ p 0} →
      ∫ b, ⟪χ, W.U ((2 * Real.pi) • refl b) Lorentz.id ψ⟫_ℂ * (𝓕 g) b = 0

/-- A teoria tem lacuna de massa positiva. -/
def TemLacuna (W : Wightman H) : Prop := ∃ Δ : ℝ, 0 < Δ ∧ LacunaAoMenos W Δ

theorem lacuna_mono {W : Wightman H} {Δ Δ' : ℝ} (h : LacunaAoMenos W Δ) (hΔ : Δ' ≤ Δ) :
    LacunaAoMenos W Δ' := by
  intro ψ χ hψ hχ g hg
  refine h ψ χ hψ hχ g (hg.mono_right fun p hp => ?_)
  simp only [Set.mem_ofPred_eq] at hp ⊢
  linarith

/-- Para `Δ ≤ 0`, a lacuna segue da condição espectral (`V̄₊ ⊆ {Δ ≤ p⁰}`). -/
theorem lacuna_nao_positiva (W : Wightman H) {Δ : ℝ} (hΔ : Δ ≤ 0) : LacunaAoMenos W Δ := by
  intro ψ χ _ _ g hg
  refine W.espectral ψ χ g (hg.mono_right fun p hp => ?_)
  simp only [Set.mem_ofPred_eq]
  exact hΔ.trans hp.1

/-- **Teste**: a teoria trivial tem lacuna para todo `Δ` (`Ω^⊥ = 0` em `H = ℂ`). -/
theorem trivial_lacuna (Δ : ℝ) : LacunaAoMenos trivial Δ := by
  intro ψ χ hψ _ g _
  have hψ0 : ψ = 0 := by
    have : ⟪(1 : ℂ), ψ⟫_ℂ = 0 := hψ
    simpa using this
  subst hψ0
  simp

theorem trivial_temLacuna : TemLacuna trivial := ⟨1, one_pos, trivial_lacuna 1⟩

end ATK.L5Lacuna

#print axioms ATK.L5Lacuna.lacuna_mono
#print axioms ATK.L5Lacuna.lacuna_nao_positiva
#print axioms ATK.L5Lacuna.trivial_lacuna
#print axioms ATK.L5Lacuna.trivial_temLacuna
