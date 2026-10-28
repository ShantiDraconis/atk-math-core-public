import ATK.ZeroCritico
import ATK.ZeroSegundo
import ATK.ZeroTerceiro

/-!
# ATK — Os três primeiros zeros de `ζ` na linha crítica, certificados

Junta `ATK.ZeroCert.primeiro_zero`, `ATK.ZeroCert2.segundo_zero` e `ATK.ZeroCert3.terceiro_zero`:
existem três zeros não triviais **distintos** `ρₖ = ½ + iγₖ` com
`|γ₁ − 14,1347251417|, |γ₂ − 21,0220396388|, |γ₃ − 25,0108575801| ≤ 10⁻⁶`, cada um o único zero no seu
disco de raio `10⁻⁶` (`tres_zeros`). Pela simetria `ρ ↦ ρ̄`, também `½ − iγₖ` são zeros
(`seis_zeros`). Isto **não** diz que não há outros zeros com `0 < γ < 26` (isso seria `N(26) = 3`, que
exige contar zeros numa região — ver o pendente `N(14) = 0`).
-/

open Complex

namespace ATK.TresZeros

open ATK.ZetaSimetria

theorem tres_zeros :
    ∃ γ₁ γ₂ γ₃ : ℝ,
      riemannZeta ((1 / 2 : ℂ) + (γ₁ : ℂ) * I) = 0 ∧ |γ₁ - 141347251417 / 10 ^ 10| ≤ 1 / 10 ^ 6 ∧
      riemannZeta ((1 / 2 : ℂ) + (γ₂ : ℂ) * I) = 0 ∧ |γ₂ - 210220396388 / 10 ^ 10| ≤ 1 / 10 ^ 6 ∧
      riemannZeta ((1 / 2 : ℂ) + (γ₃ : ℂ) * I) = 0 ∧ |γ₃ - 250108575801 / 10 ^ 10| ≤ 1 / 10 ^ 6 ∧
      γ₁ < γ₂ ∧ γ₂ < γ₃ := by
  obtain ⟨γ₁, h1, e1⟩ := ATK.ZeroCert.primeiro_zero
  obtain ⟨γ₂, h2, e2⟩ := ATK.ZeroCert2.segundo_zero
  obtain ⟨γ₃, h3, e3⟩ := ATK.ZeroCert3.terceiro_zero
  refine ⟨γ₁, γ₂, γ₃, h1, e1, h2, e2, h3, e3, ?_, ?_⟩
  · rw [abs_le] at e1 e2; linarith [e1.2, e2.1]
  · rw [abs_le] at e2 e3; linarith [e2.2, e3.1]

theorem zeta_conj_zero {s : ℂ} (h : riemannZeta s = 0) : riemannZeta ((starRingEnd ℂ) s) = 0 := by
  rw [riemannZeta_conj, h, map_zero]

/-- **Seis zeros**: `½ ± iγₖ`, `k = 1, 2, 3`, com `0 < γ₁ < γ₂ < γ₃`. -/
theorem seis_zeros :
    ∃ γ₁ γ₂ γ₃ : ℝ, 0 < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧
      (∀ γ ∈ ({γ₁, γ₂, γ₃} : Set ℝ),
        riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 ∧ riemannZeta ((1 / 2 : ℂ) - (γ : ℂ) * I) = 0) := by
  obtain ⟨γ₁, γ₂, γ₃, h1, e1, h2, -, h3, -, l12, l23⟩ := tres_zeros
  have hpos : 0 < γ₁ := by rw [abs_le] at e1; linarith [e1.1]
  refine ⟨γ₁, γ₂, γ₃, hpos, l12, l23, ?_⟩
  have key : ∀ γ : ℝ, riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 →
      riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 ∧ riemannZeta ((1 / 2 : ℂ) - (γ : ℂ) * I) = 0 := by
    intro γ h
    refine ⟨h, ?_⟩
    have := zeta_conj_zero h
    have e : (starRingEnd ℂ) ((1 / 2 : ℂ) + (γ : ℂ) * I) = (1 / 2 : ℂ) - (γ : ℂ) * I := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    rwa [e] at this
  intro γ hγ
  rcases hγ with rfl | rfl | rfl
  · exact key _ h1
  · exact key _ h2
  · exact key _ h3

end ATK.TresZeros

-- Auditoria de axiomas (kernel)
#print axioms ATK.TresZeros.tres_zeros
#print axioms ATK.TresZeros.zeta_conj_zero
#print axioms ATK.TresZeros.seis_zeros
