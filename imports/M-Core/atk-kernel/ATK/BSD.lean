import Mathlib

/-!
# ATK — BSD: regulador de posto 2, identidade determinantal, recuperação condicional

* `regulator_det_identity` — det [[h₁, p], [p, h₂]] = h₁ h₂ - p².
* `regulator_two_pos`      — se a forma de altura é definida positiva em ℝ², o regulador é > 0.
* `sha_recovery`           — SE a fórmula BSD refinada vale para uma curva, e Ω, Reg, Π c_p, #tors ≠ 0,
                             então #Ш é determinado pelos demais termos.

Nada aqui prova BSD: `sha_recovery` assume a própria fórmula como hipótese.
-/

namespace ATK.BSD

open Matrix

theorem regulator_det_identity (h₁ h₂ p : ℝ) :
    Matrix.det !![h₁, p; p, h₂] = h₁ * h₂ - p ^ 2 := by
  rw [Matrix.det_fin_two_of]
  ring

theorem regulator_two_pos {h₁ h₂ p : ℝ}
    (hpd : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < h₁ * a ^ 2 + 2 * p * a * b + h₂ * b ^ 2) :
    0 < h₁ * h₂ - p ^ 2 := by
  have h1 : 0 < h₁ := by
    have := hpd 1 0 (Or.inl one_ne_zero)
    simpa using this
  have key := hpd (-p) h₁ (Or.inr h1.ne')
  have hprod : 0 < h₁ * (h₁ * h₂ - p ^ 2) := by nlinarith [key]
  nlinarith [hprod, h1]

theorem sha_recovery {L Ω R S c t : ℝ}
    (hΩ : Ω ≠ 0) (hR : R ≠ 0) (hc : c ≠ 0) (ht : t ≠ 0)
    (hBSD : L = Ω * R * S * c / t ^ 2) :
    S = L * t ^ 2 / (Ω * R * c) := by
  have hden : Ω * R * c ≠ 0 := mul_ne_zero (mul_ne_zero hΩ hR) hc
  rw [eq_div_iff hden, hBSD, div_mul_cancel₀ _ (pow_ne_zero 2 ht)]
  ring

end ATK.BSD

#print axioms ATK.BSD.regulator_det_identity
#print axioms ATK.BSD.regulator_two_pos
#print axioms ATK.BSD.sha_recovery
