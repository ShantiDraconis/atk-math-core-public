import ATK.ForaDaLinha

/-!
# ATK-RH — A linha crítica como incógnita, e o ponto `1/2`

Duas propostas separadas, testadas contra a zeta original:

* **A reta como incógnita.** Se todos os zeros não triviais estão numa mesma reta vertical
  `Re s = λ` e existe pelo menos um, então `λ = 1/2` (`linha_forcada`): a simetria `s ↦ 1 − s`
  leva a reta `λ` na reta `1 − λ`. A reta não é um parâmetro livre; é o eixo da equação funcional.
  Qualquer reta `λ ≠ 1/2` é espelhada em `1 − λ` (`reta_espelhada`), então nenhuma reta além de
  `1/2` pode conter sozinha os zeros de um lado e do outro.
  (A existência de um zero não trivial — o primeiro tem altura 14,1347… — não está na Mathlib;
  por isso aparece como hipótese `hne`.)
* **O ponto `1/2` como zero.** Nenhum ponto real da faixa é zero (`ATK.ZetaSimetria.zeta_real_neg`:
  `ζ(σ) < 0` para `0 < σ < 1`); em particular **`ζ(1/2) ≠ 0`** (`zeta_meio_ne_zero`).

Nada aqui prova nem refuta RH.
-/

namespace ATK.LinhaIncognita

open ATK.ZetaSimetria

/-- Nenhum ponto real `σ ∈ (0,1)` é zero da zeta. -/
theorem zeta_real_ne_zero {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : riemannZeta (σ : ℂ) ≠ 0 :=
  zeta_ne_zero_real h0 h1

/-- **`ζ(1/2) ≠ 0`**: o ponto `1/2` não é zero da zeta original. -/
theorem zeta_meio_ne_zero : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  have h := zeta_ne_zero_real (σ := 1 / 2) (by norm_num) (by norm_num)
  have e : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by push_cast; ring
  rwa [e] at h

/-- **A reta espelhada**: um zero na reta `Re s = λ` tem um parceiro na reta `Re s = 1 − λ`. -/
theorem reta_espelhada {ρ : ℂ} (hρ : ρ ∈ Z) {l : ℝ} (hl : ρ.re = l) :
    tensao ρ ∈ Z ∧ (tensao ρ).re = 1 - l :=
  ⟨tensao_mem_Z hρ, by rw [re_tensao, hl]⟩

/-- **A reta incógnita é forçada**: se existe um zero não trivial e todos estão em `Re s = λ`,
então `λ = 1/2`. -/
theorem linha_forcada {l : ℝ} (hne : ∃ ρ, ρ ∈ Z) (h : ∀ ρ ∈ Z, ρ.re = l) : l = 1 / 2 := by
  obtain ⟨ρ, hρ⟩ := hne
  have h1 := h ρ hρ
  have h2 := h _ (tensao_mem_Z hρ)
  rw [re_tensao] at h2
  linarith

/-- Contrapositiva: uma reta `λ ≠ 1/2` nunca contém todos os zeros (se houver algum). -/
theorem nenhuma_outra_reta {l : ℝ} (hl : l ≠ 1 / 2) (hne : ∃ ρ, ρ ∈ Z) :
    ∃ ρ ∈ Z, ρ.re ≠ l := by
  by_contra hc
  exact hl (linha_forcada hne fun ρ hρ => by
    by_contra hne'
    exact hc ⟨ρ, hρ, hne'⟩)

end ATK.LinhaIncognita

#print axioms ATK.LinhaIncognita.zeta_real_ne_zero
#print axioms ATK.LinhaIncognita.zeta_meio_ne_zero
#print axioms ATK.LinhaIncognita.reta_espelhada
#print axioms ATK.LinhaIncognita.linha_forcada
#print axioms ATK.LinhaIncognita.nenhuma_outra_reta
