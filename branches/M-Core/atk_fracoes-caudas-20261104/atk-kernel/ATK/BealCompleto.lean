import ATK.BealDarmonMerel

/-!
# ATK — Teorema completo de Beal: o que está provado, o que é ponte, o que resta

Junta num só enunciado tudo o que o kernel certifica sobre Beal:

* `beal_incondicional`: `BealConjecture ↔ ExclusaoResidualDescida`, **sem pontes** (FLT(3) e
  FLT(4) da Mathlib, `x⁴ + y⁴ ≠ z²`, `x⁴ − y⁴ ≠ z²`, redução a soluções coprimas);
* `beal_teorema_completo`: sob as pontes publicadas **B2** (`FermatLastTheorem`, Wiles 1995) e
  **B8** (`DarmonMerel`), `BealConjecture ↔ ExclusaoResidualFinal`;
* `beal_de_pontes_e_residual`: B2 ∧ B8 ∧ residual final ⇒ Beal;
* `residual_de_beal`: Beal ⇒ residual final, sem pontes (não há atalho que pule o residual).

`ResidualFinal x y z` é o conjunto de expoentes que nenhum resultado cobre: `x, y, z > 2`,
`mdc(x, y, z) ≤ 2`, fora das famílias `(4,4,2)`, `(4,2,4)`, `(2,4,4)` e das famílias de
Darmon–Merel (`mdc(x, y) ≥ 4 ∧ 2 ∣ z`, `mdc(x, y) ≥ 3 ∧ 3 ∣ z`).

Cobertura de todos os triplos de expoentes em `3..200` (7.762.392 triplos):
* incondicional (kernel): 762.844 = **9,83%**;
* sob B2 + B8: 1.303.296 = **16,79%**;
* residual final, **aberto**: 6.459.096 = **83,21%**.

**Status.** B2 e B8 são teoremas publicados, não formalizados (dependem de modularidade, ausente da
Mathlib); entram como hipóteses, nunca como axiomas. `ExclusaoResidualFinal` é a parte aberta da
conjectura de Beal. O2 continua aberta; `CLOSED_MATH = false`.
-/

namespace ATK.BealCompleto

open ATK.Conditional.Beal ATK.BealFermatDescent ATK.BealDarmonMerel

/-- Expoentes que nenhum resultado (provado no kernel ou publicado) cobre. -/
abbrev ResidualFinal (x y z : ℕ) : Prop :=
  2 < x ∧ 2 < y ∧ 2 < z ∧ Nat.gcd x (Nat.gcd y z) ≤ 2 ∧
    ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) ∧ ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) ∧ ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) ∧
    ¬ (4 ≤ Nat.gcd x y ∧ 2 ∣ z) ∧ ¬ (3 ≤ Nat.gcd x y ∧ 3 ∣ z)

/-- **A parte aberta de Beal**: nenhuma solução com `a, b` coprimos nos expoentes residuais. -/
def ExclusaoResidualFinal : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → ResidualFinal x y z →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

/-- Sob FLT (B2), o residual de Darmon–Merel equivale ao residual final (`mdc ≤ 2`). -/
theorem dm_iff_final (hFLT : FermatLastTheorem) : ExclusaoResidualDM ↔ ExclusaoResidualFinal := by
  constructor
  · intro h a b c x y z ha hb hc hR hab
    obtain ⟨hx, hy, hz, hg, h1, h2, h5, h6, h7⟩ := hR
    have hgpos : 0 < Nat.gcd x (Nat.gcd y z) := Nat.gcd_pos_of_pos_left _ (by omega)
    exact h a b c x y z ha hb hc hx hy hz (by omega) (by omega) h1 h2 h5 h6 h7 hab
  · intro h a b c x y z ha hb hc hx hy hz _ _ h1 h2 h5 h6 h7 hab heq
    have hg := exponent_gcd_le_two hFLT ha.ne' hb.ne' hc.ne' heq
    exact h a b c x y z ha hb hc ⟨hx, hy, hz, hg, h1, h2, h5, h6, h7⟩ hab heq

/-- **Parte incondicional** (kernel, sem pontes). -/
theorem beal_incondicional : BealConjecture ↔ ExclusaoResidualDescida :=
  beal_iff_residual_descida

/-- **Teorema completo de Beal no ATK**: sob B2 (FLT) e B8 (Darmon–Merel),
Beal equivale a excluir soluções coprimas no residual final. -/
theorem beal_teorema_completo (hFLT : FermatLastTheorem) (hDM : DarmonMerel) :
    BealConjecture ↔ ExclusaoResidualFinal :=
  (beal_iff_residual_dm hDM).trans (dm_iff_final hFLT)

/-- Forma implicativa: faltam exatamente B2, B8 e o residual final. -/
theorem beal_de_pontes_e_residual (hFLT : FermatLastTheorem) (hDM : DarmonMerel)
    (hRes : ExclusaoResidualFinal) : BealConjecture :=
  (beal_teorema_completo hFLT hDM).mpr hRes

/-- Beal implica o residual final **sem pontes**: não há atalho que pule a parte aberta. -/
theorem residual_de_beal (hB : BealConjecture) : ExclusaoResidualFinal := by
  intro a b c x y z ha hb hc hR hab heq
  obtain ⟨hx, hy, hz, -⟩ := hR
  obtain ⟨p, hp, hpa, hpb, -⟩ := hB a b c x y z ha hb hc hx hy hz heq
  have h1 : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  rw [Nat.Coprime.gcd_eq_one hab] at h1
  exact hp.ne_one (Nat.dvd_one.mp h1)

/-- O residual final não é vazio e exclui o que deve excluir. -/
theorem residual_final_exemplos :
    ResidualFinal 3 4 5 ∧ ResidualFinal 3 5 7 ∧ ResidualFinal 5 7 3 ∧
      ¬ ResidualFinal 3 3 3 ∧ ¬ ResidualFinal 4 4 6 ∧ ¬ ResidualFinal 4 6 4 ∧
      ¬ ResidualFinal 4 4 3 ∧ ¬ ResidualFinal 5 5 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ResidualFinal] <;> decide

end ATK.BealCompleto

#print axioms ATK.BealCompleto.dm_iff_final
#print axioms ATK.BealCompleto.beal_incondicional
#print axioms ATK.BealCompleto.beal_teorema_completo
#print axioms ATK.BealCompleto.beal_de_pontes_e_residual
#print axioms ATK.BealCompleto.residual_de_beal
#print axioms ATK.BealCompleto.residual_final_exemplos
