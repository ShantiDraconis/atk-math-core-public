import ATK.ZetaSimetria

/-!
# ATK — Riemann reduzida à faixa `1/2 < Re s ≤ θ`

`ZeroLivreAcima θ`: `ζ` não tem zeros com `Re s > θ`. A Mathlib dá `θ = 1`
(`riemannZeta_ne_zero_of_one_le_re`). A **quasi-hipótese de Riemann** da OpenAI (`openai/math`,
família 003, setembro de 2026, formalizada em Lean como
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`) dá `θ = 7/8`; ela é compilada e usada por este
arquivo no pacote `atk-kernel/externo`. Aqui ela entra só como hipótese explícita.

Provado aqui, sem hipóteses além das escritas:

* `rh_iff_metade`: **RH ⟺ não há zeros com `Re s > 1/2`** (pela equação funcional,
  `ATK.ZetaSimetria.tensao_mem_Z`, os zeros com `Re s < 1/2` são espelhos desses);
* `rh_iff_faixa`: se `ZeroLivreAcima θ`, então **RH ⟺ não há zeros na faixa `1/2 < Re s ≤ θ`**;
* `rh_iff_faixa_um`: o caso `θ = 1`, incondicional;
* `rh_iff_faixa_sete_oitavos`: o caso `θ = 7/8`, com a quasi-RH como hipótese.

O resíduo aberto de RH, depois da quasi-RH, é exatamente `FaixaLivre (1/2) (7/8)`.
**Nada aqui prova RH.**
-/

open Complex

namespace ATK.QuasiRiemann

open ATK.ZetaSimetria

/-- `ζ` não tem zeros no semiplano `Re s > θ`. -/
def ZeroLivreAcima (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- `ζ` não tem zeros na faixa `a < Re s ≤ b`. -/
def FaixaLivre (a b : ℝ) : Prop := ∀ s : ℂ, a < s.re → s.re ≤ b → riemannZeta s ≠ 0

/-- A quasi-RH da OpenAI, como enunciado (provada no pacote `atk-kernel/externo`). -/
def QuasiRH : Prop := ZeroLivreAcima (7 / 8)

/-- A Mathlib: não há zeros com `Re s ≥ 1`. -/
theorem zeroLivre_um : ZeroLivreAcima 1 :=
  fun _ hs => riemannZeta_ne_zero_of_one_le_re hs.le

theorem zeroLivre_mono {θ θ' : ℝ} (h : θ ≤ θ') (hθ : ZeroLivreAcima θ) : ZeroLivreAcima θ' :=
  fun s hs => hθ s (lt_of_le_of_lt h hs)

/-- **RH ⟺ não há zeros com `Re s > 1/2`.** -/
theorem rh_iff_metade : RiemannHypothesis ↔ ZeroLivreAcima (1 / 2) := by
  constructor
  · intro h s hs hz
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
    have hs1 : s ≠ 1 := by intro h'; rw [h', one_re] at h1; exact h1 le_rfl
    have hnt : ¬ ∃ n : ℕ, s = -2 * (n + 1) := fun ht => by
      have := re_trivial ht; linarith
    have := h s hz hnt hs1
    linarith
  · intro h s hz hnt hs1
    have hZ : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, hnt⟩
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · have hT := tensao_mem_Z hZ
      exact absurd hT.1 (h _ (by rw [re_tensao]; linarith))
    · exact heq
    · exact absurd hz (h s hgt)

/-- **Com `ζ` sem zeros acima de `θ`, RH ⟺ não há zeros na faixa `1/2 < Re s ≤ θ`.** -/
theorem rh_iff_faixa {θ : ℝ} (hθ : ZeroLivreAcima θ) :
    RiemannHypothesis ↔ FaixaLivre (1 / 2) θ := by
  rw [rh_iff_metade]
  constructor
  · exact fun h s hs _ => h s hs
  · intro h s hs
    by_cases hb : s.re ≤ θ
    · exact h s hs hb
    · exact hθ s (not_le.mp hb)

/-- O caso `θ = 1` (Mathlib), incondicional. -/
theorem rh_iff_faixa_um : RiemannHypothesis ↔ FaixaLivre (1 / 2) 1 :=
  rh_iff_faixa zeroLivre_um

/-- **O caso `θ = 7/8`**: com a quasi-RH, o resíduo de RH é a faixa `1/2 < Re s ≤ 7/8`. -/
theorem rh_iff_faixa_sete_oitavos (hq : QuasiRH) : RiemannHypothesis ↔ FaixaLivre (1 / 2) (7 / 8) :=
  rh_iff_faixa hq

/-- A quasi-RH e a faixa juntas dão RH (sentido usado pelo portão). -/
theorem rh_de_quasi_e_faixa (hq : QuasiRH) (hf : FaixaLivre (1 / 2) (7 / 8)) : RiemannHypothesis :=
  (rh_iff_faixa_sete_oitavos hq).mpr hf

/-- RH implica a quasi-RH (sanidade: a hipótese não é mais forte que RH). -/
theorem quasi_de_rh (h : RiemannHypothesis) : QuasiRH :=
  zeroLivre_mono (by norm_num) (rh_iff_metade.mp h)

end ATK.QuasiRiemann

#print axioms ATK.QuasiRiemann.zeroLivre_um
#print axioms ATK.QuasiRiemann.zeroLivre_mono
#print axioms ATK.QuasiRiemann.rh_iff_metade
#print axioms ATK.QuasiRiemann.rh_iff_faixa
#print axioms ATK.QuasiRiemann.rh_iff_faixa_um
#print axioms ATK.QuasiRiemann.rh_iff_faixa_sete_oitavos
#print axioms ATK.QuasiRiemann.rh_de_quasi_e_faixa
#print axioms ATK.QuasiRiemann.quasi_de_rh
