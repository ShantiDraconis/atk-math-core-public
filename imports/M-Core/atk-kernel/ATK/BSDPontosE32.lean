import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# `y² = x³ − x` sobre `𝔽_p`, `p ≡ 3 (mod 4)`: `p` pontos afins, `a_p = 0`

Primeiro tijolo da função `L` da curva `y² = x³ − x` (condutor 32): nos primos `p ≡ 3 (mod 4)`
a curva é supersingular, `#E(𝔽_p) = p + 1` e o traço de Frobenius `a_p = p + 1 − #E(𝔽_p)` é `0`.

Prova: `#{y : y² = a} = χ(a) + 1` (caractere quadrático), logo
`#{(x, y) : y² = x³ − x} = p + Σ_x χ(x³ − x)`; e `x ↦ −x` troca `x³ − x` por `−(x³ − x)` com
`χ(−1) = −1` quando `p ≡ 3 (mod 4)`, então a soma é `0`.

Não toca O6/O7 nem B6: é um fato local (fator de Euler em `p`).
-/

namespace ATK.BSDPontosE32

open Finset

variable {p : ℕ} [Fact p.Prime]

theorem caracteristica_ne_dois (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

/-- `χ(−1) = −1` para `p ≡ 3 (mod 4)`. -/
theorem chi_menos_um (h3 : p % 4 = 3) : quadraticChar (ZMod p) (-1) = -1 := by
  rw [quadraticChar_neg_one (caracteristica_ne_dois h3), ZMod.card]
  exact ZMod.χ₄_nat_three_mod_four h3

/-- `Σ_x χ(x³ − x) = 0` para `p ≡ 3 (mod 4)`. -/
theorem soma_chi_zero (h3 : p % 4 = 3) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) = 0 := by
  have hterm : ∀ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 - -x) =
      -quadraticChar (ZMod p) (x ^ 3 - x) := by
    intro x
    have : (-x) ^ 3 - -x = (-1) * (x ^ 3 - x) := by ring
    rw [this, map_mul, chi_menos_um h3, neg_one_mul]
  have h1 : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) =
      ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 - -x) :=
    Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => by simp only [Equiv.neg_apply, neg_neg])
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_neg_distrib] at h1
  linarith

/-- `#{y : y² = x³ − x} = χ(x³ − x) + 1`. -/
theorem card_raizes (h3 : p % 4 = 3) (x : ZMod p) :
    ((univ.filter (fun y : ZMod p => y ^ 2 = x ^ 3 - x)).card : ℤ) =
      quadraticChar (ZMod p) (x ^ 3 - x) + 1 := by
  rw [← quadraticChar_card_sqrts (caracteristica_ne_dois h3) (x ^ 3 - x)]
  congr 2
  ext y
  simp

/-- **`#{(x, y) ∈ 𝔽_p² : y² = x³ − x} = p`** para `p ≡ 3 (mod 4)`. -/
theorem card_afim (h3 : p % 4 = 3) :
    ((univ.filter (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)).card : ℤ) = p := by
  have hprod : (univ.filter (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)).card =
      ∑ x : ZMod p, (univ.filter (fun y : ZMod p => y ^ 2 = x ^ 3 - x)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x _ => (Finset.card_filter _ _).symm)
  rw [hprod]
  push_cast
  rw [Finset.sum_congr rfl (fun x _ => card_raizes h3 x), Finset.sum_add_distrib, soma_chi_zero h3]
  simp [ZMod.card]

/-- Com o ponto no infinito: `#E(𝔽_p) = p + 1`. -/
theorem card_projetivo (h3 : p % 4 = 3) :
    ((univ.filter (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)).card : ℤ) + 1 = p + 1 := by
  rw [card_afim h3]

/-- **Traço de Frobenius**: `a_p = p + 1 − #E(𝔽_p) = 0` para `p ≡ 3 (mod 4)` (supersingular). -/
theorem traco_zero (h3 : p % 4 = 3) :
    (p : ℤ) + 1 - (((univ.filter (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)).card : ℤ) + 1)
      = 0 := by
  rw [card_afim h3]
  ring

end ATK.BSDPontosE32

#print axioms ATK.BSDPontosE32.caracteristica_ne_dois
#print axioms ATK.BSDPontosE32.chi_menos_um
#print axioms ATK.BSDPontosE32.soma_chi_zero
#print axioms ATK.BSDPontosE32.card_raizes
#print axioms ATK.BSDPontosE32.card_afim
#print axioms ATK.BSDPontosE32.card_projetivo
#print axioms ATK.BSDPontosE32.traco_zero
