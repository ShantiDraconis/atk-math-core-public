import ATK.ZeroCritico
import ATK.LinhaIncognita
import ATK.TruncamentoZero
import ATK.ZeroIncognito

/-!
# ATK — Descarregando a hipótese "existe um zero não trivial"

Com `ATK.ZeroCert.zero_na_linha` (o primeiro zero, certificado no kernel), as hipóteses `hne` de

* `ATK.LinhaIncognita.linha_forcada` e `nenhuma_outra_reta`,
* `ATK.TruncamentoZero.eixo_unico`,
* `ATK.ZeroIncognito.incognita_resolvida` e `centro_exato` (para `T ≥ 15`)

deixam de ser hipóteses: as versões abaixo são **incondicionais**. Nenhuma delas é HR.
-/

open Complex Metric

namespace ATK.ZeroCertAplicado

open ATK.ZetaSimetria ATK.ZeroCert

/-- O zero certificado tem `14 < Im ρ < 15`. -/
theorem existe_zero_altura : ∃ ρ ∈ Z, ρ.re = 1 / 2 ∧ 14 < ρ.im ∧ ρ.im < 15 := by
  obtain ⟨ρ, hρ, hre, hB, -⟩ := zero_na_linha
  have h := (re_im_prox hB).2
  rw [t0_val, show ((rr : ℚ) : ℝ) = 1 / 10 ^ 6 by simp [rr], abs_le] at h
  exact ⟨ρ, hρ, hre, by linarith [h.1], by linarith [h.2]⟩

/-- **`linha_forcada` incondicional**: se todos os zeros não triviais estão em `Re s = λ`, então
`λ = ½`. -/
theorem linha_forcada {l : ℝ} (h : ∀ ρ ∈ Z, ρ.re = l) : l = 1 / 2 :=
  ATK.LinhaIncognita.linha_forcada Z_nao_vazio h

/-- **Nenhuma outra reta** contém todos os zeros (incondicional). -/
theorem nenhuma_outra_reta {l : ℝ} (hl : l ≠ 1 / 2) : ∃ ρ ∈ Z, ρ.re ≠ l :=
  ATK.LinhaIncognita.nenhuma_outra_reta hl Z_nao_vazio

/-- **Eixo único** incondicional: zeros simétricos em torno de `Re s = κ` ⇒ `κ = ½`. -/
theorem eixo_unico {κ : ℝ} (hsim : ∀ ρ ∈ Z, ATK.TruncamentoZero.refl κ ρ ∈ Z) : κ = 1 / 2 :=
  ATK.TruncamentoZero.eixo_unico Z_nao_vazio hsim

/-- Há zeros até a altura `T ≥ 15`. -/
theorem todos_nao_vazio {T : ℝ} (hT : 15 ≤ T) : (ATK.BohrLandau.todos T).Nonempty := by
  obtain ⟨ρ, hρ, -, h14, h15⟩ := existe_zero_altura
  exact ⟨ρ, hρ, by linarith, by linarith⟩

/-- **A incógnita é resolvida** (incondicional, `T ≥ 15`): `Σ (β − κ) = 0 ⟺ κ = ½`. -/
theorem incognita_resolvida (κ : ℝ) {T : ℝ} (hT : 15 ≤ T) :
    ∑ ρ ∈ ATK.ZeroIncognito.F T, (ρ.re - κ) = 0 ↔ κ = 1 / 2 :=
  ATK.ZeroIncognito.incognita_resolvida κ T (todos_nao_vazio hT)

/-- **O centro é exato** (incondicional, `T ≥ 15`): a média das partes reais é `½`. -/
theorem centro_exato {T : ℝ} (hT : 15 ≤ T) :
    (∑ ρ ∈ ATK.ZeroIncognito.F T, ρ.re) / (ATK.ZeroIncognito.F T).card = 1 / 2 :=
  ATK.ZeroIncognito.centro_exato T (todos_nao_vazio hT)

end ATK.ZeroCertAplicado

-- Auditoria de axiomas (kernel)
#print axioms ATK.ZeroCertAplicado.existe_zero_altura
#print axioms ATK.ZeroCertAplicado.linha_forcada
#print axioms ATK.ZeroCertAplicado.nenhuma_outra_reta
#print axioms ATK.ZeroCertAplicado.eixo_unico
#print axioms ATK.ZeroCertAplicado.todos_nao_vazio
#print axioms ATK.ZeroCertAplicado.incognita_resolvida
#print axioms ATK.ZeroCertAplicado.centro_exato
