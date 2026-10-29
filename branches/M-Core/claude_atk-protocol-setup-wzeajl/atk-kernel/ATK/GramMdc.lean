import ATK.GramExato

/-!
# ATK — GramMdc (corolário explícito de `escala`: G(i,j) = (1/d)·G(a,b) via mdc)

`ATK.GramExato.escala` já prova, de forma incondicional,
`∫ ρ_{d·h} ρ_{d·k} = (1/d) ∫ ρ_h ρ_k`.

Este arquivo deriva o corolário explícito na forma "mdc, reduzido a coprimos":
para quaisquer `i, j : ℕ` positivos, com `d = mdc(i,j)`, `a = i/d`, `b = j/d`
(logo `mdc(a,b) = 1`),

  G(i,j) = (1/d) · G(a,b)

aplicando `escala` com `h := a`, `k := b`, usando `d·a = i` e `d·b = j`
(de `Nat.mul_div_cancel'` com `mdc(i,j) ∣ i` e `mdc(i,j) ∣ j`).

Não decide nada sobre D_N nem RH — é só a forma explícita, em termos de mdc, de
uma identidade já certificada no kernel (`ATK.GramExato.escala`).
-/

namespace ATK.GramMdc

open MeasureTheory Set
open ATK.Conditional.Riemann (rho)
open ATK.GramExato (escala)

/-- `mdc(i,j) ≥ 1` quando `i > 0`. -/
theorem gcd_pos {i j : ℕ} (hi : 0 < i) : 0 < Nat.gcd i j :=
  Nat.gcd_pos_of_pos_left j hi

/-- **G(i,j) = (1/d)·G(a,b)**, com `d = mdc(i,j)`, `a = i/d`, `b = j/d` (`mdc(a,b)=1`). -/
theorem gram_scaling_gcd (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    ∫ t in Ioi (0 : ℝ), rho i t * rho j t =
      (Nat.gcd i j : ℝ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), rho (i / Nat.gcd i j) t * rho (j / Nat.gcd i j) t := by
  have hd_pos : 1 ≤ Nat.gcd i j := gcd_pos hi
  have hia : Nat.gcd i j * (i / Nat.gcd i j) = i := Nat.mul_div_cancel' (Nat.gcd_dvd_left i j)
  have hjb : Nat.gcd i j * (j / Nat.gcd i j) = j := Nat.mul_div_cancel' (Nat.gcd_dvd_right i j)
  have h := escala (Nat.gcd i j) (i / Nat.gcd i j) (j / Nat.gcd i j) hd_pos
  rw [hia, hjb] at h
  exact h

/-- `mdc(a,b) = 1` para `a = i/mdc(i,j)`, `b = j/mdc(i,j)`: a redução de `gram_scaling_gcd`
é sempre a um par coprimo. -/
theorem gcd_div_gcd_eq_one (i j : ℕ) (hi : 0 < i) :
    Nat.gcd (i / Nat.gcd i j) (j / Nat.gcd i j) = 1 :=
  Nat.coprime_div_gcd_div_gcd (gcd_pos hi)

end ATK.GramMdc

#print axioms ATK.GramMdc.gcd_pos
#print axioms ATK.GramMdc.gram_scaling_gcd
#print axioms ATK.GramMdc.gcd_div_gcd_eq_one
