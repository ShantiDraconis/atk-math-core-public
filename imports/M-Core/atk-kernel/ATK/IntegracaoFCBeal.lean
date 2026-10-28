import ATK.Conditional.Beal
import ATK.Externo.FCBeal

/-!
# ATK — Integração com o formal-conjectures: Beal e RH

* **Beal.** O ATK enuncia Beal com um primo comum a `a, b, c`; o formal-conjectures, com
  `1 < mdc {A, B, C}`. `beal_iff_fc` prova no kernel que os dois enunciados são equivalentes,
  sem hipóteses.
* **RH.** O formal-conjectures usa o próprio `RiemannHypothesis` da Mathlib, o mesmo do ATK
  (`ATK.Conditional.Riemann`), então os enunciados são idênticos por definição.

Nada aqui prova Beal ou RH. **CLOSED_MATH continua false.**
-/

namespace ATK.IntegracaoFCBeal

open ATK.Conditional.Beal

/-- `mdc {A, B, C} = mdc(A, mdc(B, C))`. -/
theorem gcd_triplo (A B C : ℕ) : Finset.gcd {A, B, C} id = Nat.gcd A (Nat.gcd B C) := by
  classical
  rw [Finset.gcd_insert, Finset.gcd_insert, Finset.gcd_singleton]
  simp only [id, normalize_eq, gcd_eq_nat_gcd]

/-- **Os enunciados de Beal do ATK e do formal-conjectures são equivalentes.** -/
theorem beal_iff_fc : BealConjecture ↔ ATK.FC.bealConjecture := by
  constructor
  · intro h A B C x y z hA hB hC hx hy hz heq
    rw [gcd_triplo, one_lt_gcd_iff (Nat.pos_of_ne_zero hA)]
    exact h A B C x y z (Nat.pos_of_ne_zero hA) (Nat.pos_of_ne_zero hB) (Nat.pos_of_ne_zero hC)
      hx hy hz heq
  · intro h a b c x y z ha hb hc hx hy hz heq
    have hg := h ha.ne' hb.ne' hc.ne' hx hy hz heq
    rwa [gcd_triplo, one_lt_gcd_iff ha] at hg

/-- RH: o enunciado do formal-conjectures é o `RiemannHypothesis` da Mathlib, o mesmo do ATK. -/
theorem rh_mesmo_enunciado : RiemannHypothesis ↔ RiemannHypothesis := Iff.rfl

end ATK.IntegracaoFCBeal

#print axioms ATK.IntegracaoFCBeal.gcd_triplo
#print axioms ATK.IntegracaoFCBeal.beal_iff_fc
#print axioms ATK.IntegracaoFCBeal.rh_mesmo_enunciado
