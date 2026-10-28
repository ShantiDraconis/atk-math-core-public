import ATK.BealResidual
import Mathlib.Data.Nat.Factorization.Basic

/-!
# ATK — Beal com o Último Teorema de Fermat: a lacuna se reduz a `mdc(x, y, z) ∈ {1, 2}`

Lema aritmético (incondicional): todo `g ≥ 3` tem um divisor `d` que é `4` ou um primo ímpar
(`divisor_fermat`). Como `FLT(d)` exclui todas as soluções com `d` dividindo os três expoentes
(`ATK.BealPartial.sem_solucao_de_flt_divisor`), o enunciado `FermatLastTheorem` **da Mathlib**
(hoje uma ponte — B2 —, em formalização no projeto de Buzzard) implica:

* `beal_mdc_ge_tres`: nenhuma solução com `mdc(x, y, z) ≥ 3`;
* `beal_iff_mdc_pequeno`: **Beal ⟺ nenhuma solução coprima com `mdc(x, y, z) ≤ 2`**;
* `beal_iff_mdc_pequeno_pairwise`: idem com `a, b, c` dois a dois coprimos.

Incondicionalmente (FLT(3), FLT(4) da Mathlib), `beal_mdc_div_por_tres_ou_quatro` já exclui `3 ∣ g`
ou `4 ∣ g`; e `beal_mdc_primo_de_flt` exclui `p ∣ g` para cada primo `p` com `FLT(p)` provado.
A parte com `mdc ∈ {1, 2}` é exatamente onde nenhum caso de Fermat ajuda: é a lacuna de Beal.
-/

namespace ATK.BealFLT

open ATK.Conditional.Beal ATK.BealReduction ATK.BealPartial ATK.BealResidual

/-- **Todo `g ≥ 3` tem um divisor `4` ou primo ímpar.** -/
theorem divisor_fermat {g : ℕ} (hg : 3 ≤ g) :
    ∃ d, d ∣ g ∧ (d = 4 ∨ (Nat.Prime d ∧ d ≠ 2)) := by
  obtain ⟨k, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (show g ≠ 0 by omega)
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hgm
    refine ⟨4, ?_, Or.inl rfl⟩
    have hk : 2 ≤ k := by
      by_contra h
      interval_cases k <;> simp_all
    rw [hgm, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hk
  · refine ⟨m.minFac, ?_, Or.inr ⟨Nat.minFac_prime hm1, ?_⟩⟩
    · rw [hgm]; exact dvd_mul_of_dvd_right (Nat.minFac_dvd m) _
    · intro h2
      have h2m : 2 ∣ m := h2 ▸ Nat.minFac_dvd m
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2m)

theorem dvd_xyz {d x y z : ℕ} (h : d ∣ Nat.gcd x (Nat.gcd y z)) : d ∣ x ∧ d ∣ y ∧ d ∣ z :=
  ⟨h.trans (Nat.gcd_dvd_left _ _), h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)),
    h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))⟩

/-- Exclusão para cada primo `p` cujo `FLT(p)` esteja provado. -/
theorem beal_mdc_primo_de_flt {p a b c x y z : ℕ} (hF : FermatLastTheoremFor p)
    (hp : p ∣ Nat.gcd x (Nat.gcd y z)) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨hx, hy, hz⟩ := dvd_xyz hp
  exact sem_solucao_de_flt_divisor hF hx hy hz ha hb hc

/-- Incondicional: `3 ∣ g` ou `4 ∣ g` exclui soluções. -/
theorem beal_mdc_div_por_tres_ou_quatro {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 3 ∣ Nat.gcd x (Nat.gcd y z) ∨ 4 ∣ Nat.gcd x (Nat.gcd y z)) : a ^ x + b ^ y ≠ c ^ z :=
  sem_solucao_mdc ha hb hc h

/-- **Com FLT: nenhuma solução com `mdc(x, y, z) ≥ 3`.** -/
theorem beal_mdc_ge_tres (hF : FermatLastTheorem) {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hg : 3 ≤ Nat.gcd x (Nat.gcd y z)) : a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨d, hd, hd'⟩ := divisor_fermat hg
  have hd3 : 3 ≤ d := by
    rcases hd' with rfl | ⟨hp, h2⟩
    · norm_num
    · have := hp.two_le; omega
  exact beal_mdc_primo_de_flt (hF d hd3) hd ha hb hc

/-- A lacuna de Beal depois de Fermat: soluções coprimas com `mdc(x, y, z) ≤ 2`. -/
def ExclusaoMdcPequeno : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    Nat.gcd x (Nat.gcd y z) ≤ 2 → Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

/-- **Com FLT: Beal ⟺ nenhuma solução coprima com `mdc(x, y, z) ≤ 2`.** -/
theorem beal_iff_mdc_pequeno (hF : FermatLastTheorem) : BealConjecture ↔ ExclusaoMdcPequeno := by
  rw [beal_iff_primitive]
  constructor
  · intro h a b c x y z ha hb hc hx hy hz _ hab
    exact h a b c x y z ha hb hc hx hy hz hab
  · intro h a b c x y z ha hb hc hx hy hz hab
    by_cases hg : 3 ≤ Nat.gcd x (Nat.gcd y z)
    · exact beal_mdc_ge_tres hF ha hb hc hg
    · exact h a b c x y z ha hb hc hx hy hz (by omega) hab

def ExclusaoMdcPequenoPairwise : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    Nat.gcd x (Nat.gcd y z) ≤ 2 → Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c →
      a ^ x + b ^ y ≠ c ^ z

theorem mdc_pequeno_iff_pairwise : ExclusaoMdcPequeno ↔ ExclusaoMdcPequenoPairwise := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz hg hab _ _
    exact h a b c x y z ha hb hc hx hy hz hg hab
  · intro h a b c x y z ha hb hc hx hy hz hg hab heq
    exact h a b c x y z ha hb hc hx hy hz hg hab
      (coprime_ac_de_ab (by omega) (by omega) heq hab)
      (coprime_bc_de_ab (by omega) (by omega) heq hab) heq

/-- **Com FLT: Beal ⟺ nenhuma solução dois a dois coprima com `mdc(x, y, z) ∈ {1, 2}`.** -/
theorem beal_iff_mdc_pequeno_pairwise (hF : FermatLastTheorem) :
    BealConjecture ↔ ExclusaoMdcPequenoPairwise :=
  (beal_iff_mdc_pequeno hF).trans mdc_pequeno_iff_pairwise

/-- A lacuna de Beal é exatamente o residual com `mdc ≤ 2` (incondicionalmente, o residual atual
contém o de `mdc ≤ 2`). -/
theorem residual_contem_mdc_pequeno (h : ExclusaoResidual) : ExclusaoMdcPequeno := by
  intro a b c x y z ha hb hc hx hy hz hg hab
  refine h a b c x y z ha hb hc hx hy hz ?_ ?_ hab
  · intro h3; have := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
      intro h0; rw [Nat.gcd_eq_zero_iff] at h0; omega)) h3; omega
  · intro h4; have := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
      intro h0; rw [Nat.gcd_eq_zero_iff] at h0; omega)) h4; omega

/-- Testes: `(3, 4, 5)` tem `mdc 1` e `(4, 6, 10)` tem `mdc 2`: ambos na lacuna; `(6, 9, 15)` tem
`mdc 3`: fora dela (FLT(3)). -/
theorem exemplos_lacuna : Nat.gcd 3 (Nat.gcd 4 5) = 1 ∧ Nat.gcd 4 (Nat.gcd 6 10) = 2 ∧
    Nat.gcd 6 (Nat.gcd 9 15) = 3 := by decide

end ATK.BealFLT

#print axioms ATK.BealFLT.divisor_fermat
#print axioms ATK.BealFLT.dvd_xyz
#print axioms ATK.BealFLT.beal_mdc_primo_de_flt
#print axioms ATK.BealFLT.beal_mdc_div_por_tres_ou_quatro
#print axioms ATK.BealFLT.beal_mdc_ge_tres
#print axioms ATK.BealFLT.beal_iff_mdc_pequeno
#print axioms ATK.BealFLT.mdc_pequeno_iff_pairwise
#print axioms ATK.BealFLT.beal_iff_mdc_pequeno_pairwise
#print axioms ATK.BealFLT.residual_contem_mdc_pequeno
#print axioms ATK.BealFLT.exemplos_lacuna
