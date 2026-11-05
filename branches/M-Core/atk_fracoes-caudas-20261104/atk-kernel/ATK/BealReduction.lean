import ATK.Conditional.Beal

/-!
# ATK — Redução exata de Beal às soluções primitivas (produtor `C_Beal`)

O produtor proposto para Beal é a **exclusão primitiva**: não existe solução de
`aˣ + bʸ = cᶻ` (`x, y, z > 2`) com `a, b, c` sem fator comum. Este arquivo prova, no kernel,
que essa exclusão é **exatamente equivalente** ao enunciado oficial `BealConjecture` — em três
formas (coprimos `a, b`; dois a dois coprimos; `mdc(a, b, c) = 1`) — e prova incondicionalmente
o caso diagonal `a = b`.

Lei de propagação usada em tudo (nova, incondicional): **um primo que divide dois dos três
termos divide o terceiro.** Logo uma solução ou é primitiva (dois a dois coprima), ou já
satisfaz a conclusão de Beal.

Nada aqui prova `BealConjecture`; a obrigação O2 passa a ser exatamente `BealPairwise`
(nenhuma solução dois a dois coprima), sem perda de generalidade.
-/

namespace ATK.BealReduction

open ATK.Conditional.Beal

/-- Exclusão primitiva com `a, b` coprimos. -/
def BealPrimitive : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

/-- Exclusão primitiva com `a, b, c` dois a dois coprimos. -/
def BealPairwise : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c → a ^ x + b ^ y ≠ c ^ z

/-- Exclusão primitiva na forma `mdc(a, b, c) = 1` (o `C_Beal` do texto). -/
def BealGcdOne : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    Nat.gcd a (Nat.gcd b c) = 1 → a ^ x + b ^ y ≠ c ^ z

/-! ## Propagação de primos -/

/-- Um primo que divide `a` e `b` divide `c`. -/
theorem primo_ab_divide_c {a b c x y z p : ℕ} (hp : p.Prime) (hx : 0 < x) (hy : 0 < y)
    (heq : a ^ x + b ^ y = c ^ z) (ha : p ∣ a) (hb : p ∣ b) : p ∣ c := by
  have h1 : p ∣ a ^ x := dvd_pow ha hx.ne'
  have h2 : p ∣ b ^ y := dvd_pow hb hy.ne'
  have h3 : p ∣ c ^ z := heq ▸ dvd_add h1 h2
  exact hp.dvd_of_dvd_pow h3

/-- Um primo que divide `a` e `c` divide `b`. -/
theorem primo_ac_divide_b {a b c x y z p : ℕ} (hp : p.Prime) (hx : 0 < x) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z) (ha : p ∣ a) (hc : p ∣ c) : p ∣ b := by
  have h1 : p ∣ a ^ x := dvd_pow ha hx.ne'
  have h3 : p ∣ c ^ z := dvd_pow hc hz.ne'
  rw [← heq] at h3
  exact hp.dvd_of_dvd_pow ((Nat.dvd_add_right h1).mp h3)

/-- Um primo que divide `b` e `c` divide `a`. -/
theorem primo_bc_divide_a {a b c x y z p : ℕ} (hp : p.Prime) (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z) (hb : p ∣ b) (hc : p ∣ c) : p ∣ a := by
  have h2 : p ∣ b ^ y := dvd_pow hb hy.ne'
  have h3 : p ∣ c ^ z := dvd_pow hc hz.ne'
  rw [← heq] at h3
  exact hp.dvd_of_dvd_pow ((Nat.dvd_add_left h2).mp h3)

/-- Em uma solução, `a, b` coprimos implica `a, c` coprimos. -/
theorem coprime_ac_de_ab {a b c x y z : ℕ} (hx : 0 < x) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z) (hab : Nat.Coprime a b) : Nat.Coprime a c := by
  by_contra h
  obtain ⟨p, hp, hpa, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpb := primo_ac_divide_b hp hx hz heq hpa hpc
  exact hp.not_dvd_one (by rw [← hab.gcd_eq_one]; exact Nat.dvd_gcd hpa hpb)

/-- Em uma solução, `a, b` coprimos implica `b, c` coprimos. -/
theorem coprime_bc_de_ab {a b c x y z : ℕ} (hy : 0 < y) (hz : 0 < z)
    (heq : a ^ x + b ^ y = c ^ z) (hab : Nat.Coprime a b) : Nat.Coprime b c := by
  by_contra h
  obtain ⟨p, hp, hpb, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpa := primo_bc_divide_a hp hy hz heq hpb hpc
  exact hp.not_dvd_one (by rw [← hab.gcd_eq_one]; exact Nat.dvd_gcd hpa hpb)

/-! ## Equivalências exatas -/

/-- **Beal ⟺ exclusão primitiva** (coprimos `a, b`). -/
theorem beal_iff_primitive : BealConjecture ↔ BealPrimitive := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz hcop heq
    obtain ⟨p, hp, hpa, hpb, -⟩ := h a b c x y z ha hb hc hx hy hz heq
    exact hp.not_dvd_one (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hpa hpb)
  · intro h a b c x y z ha hb hc hx hy hz heq
    by_cases hcop : Nat.Coprime a b
    · exact absurd heq (h a b c x y z ha hb hc hx hy hz hcop)
    · obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      exact ⟨p, hp, hpa, hpb, primo_ab_divide_c hp (by omega) (by omega) heq hpa hpb⟩

/-- Exclusão com `a, b` coprimos ⟺ exclusão dois a dois coprima. -/
theorem primitive_iff_pairwise : BealPrimitive ↔ BealPairwise := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz hab _ _
    exact h a b c x y z ha hb hc hx hy hz hab
  · intro h a b c x y z ha hb hc hx hy hz hab heq
    exact h a b c x y z ha hb hc hx hy hz hab
      (coprime_ac_de_ab (by omega) (by omega) heq hab)
      (coprime_bc_de_ab (by omega) (by omega) heq hab) heq

/-- **Beal ⟺ nenhuma solução dois a dois coprima** (forma final da obrigação O2). -/
theorem beal_iff_pairwise : BealConjecture ↔ BealPairwise :=
  beal_iff_primitive.trans primitive_iff_pairwise

/-- **Beal ⟺ `C_Beal`** (nenhuma solução com `mdc(a, b, c) = 1`). -/
theorem beal_iff_gcdOne : BealConjecture ↔ BealGcdOne := by
  rw [beal_iff_gcdLowerBound]
  constructor
  · intro h a b c x y z ha hb hc hx hy hz hg heq
    have := h a b c x y z ha hb hc hx hy hz heq
    omega
  · intro h a b c x y z ha hb hc hx hy hz heq
    have hpos : 0 < Nat.gcd a (Nat.gcd b c) := Nat.gcd_pos_of_pos_left _ ha
    by_contra hle
    exact h a b c x y z ha hb hc hx hy hz (by omega) heq

/-! ## Caso incondicional: diagonal `a = b` -/

/-- **Beal vale incondicionalmente quando `a = b`** (qualquer `x, y > 0`, `z > 2`). -/
theorem beal_diagonal {a c x y z : ℕ} (ha : 0 < a) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hz : 2 < z) (heq : a ^ x + a ^ y = c ^ z) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ a ∧ p ∣ c := by
  by_cases h1 : a = 1
  · subst h1
    simp only [one_pow] at heq
    by_cases hc1 : c = 1
    · subst hc1; simp at heq
    · have hc2 : 2 ≤ c := by omega
      have h8 : 2 ^ 3 ≤ c ^ z :=
        (Nat.pow_le_pow_right (by norm_num) (show 3 ≤ z from hz)).trans (Nat.pow_le_pow_left hc2 z)
      omega
  · have hp := Nat.minFac_prime h1
    exact ⟨a.minFac, hp, Nat.minFac_dvd a, Nat.minFac_dvd a,
      primo_ab_divide_c hp hx hy heq (Nat.minFac_dvd a) (Nat.minFac_dvd a)⟩

/-- Teste: a família `2ⁿ + 2ⁿ = 2ⁿ⁺¹` (Beal tem soluções não primitivas; a conclusão vale). -/
theorem exemplo_nao_primitivo : (2 : ℕ) ^ 3 + 2 ^ 3 = 2 ^ 4 := by norm_num

/-- Teste: a hipótese `x, y, z > 2` é necessária — `3² + 4² = 5²` é primitiva. -/
theorem contraexemplo_expoente_dois : (3 : ℕ) ^ 2 + 4 ^ 2 = 5 ^ 2 ∧ Nat.Coprime 3 4 := by
  exact ⟨by norm_num, by decide⟩

end ATK.BealReduction

#print axioms ATK.BealReduction.primo_ab_divide_c
#print axioms ATK.BealReduction.primo_ac_divide_b
#print axioms ATK.BealReduction.primo_bc_divide_a
#print axioms ATK.BealReduction.coprime_ac_de_ab
#print axioms ATK.BealReduction.coprime_bc_de_ab
#print axioms ATK.BealReduction.beal_iff_primitive
#print axioms ATK.BealReduction.primitive_iff_pairwise
#print axioms ATK.BealReduction.beal_iff_pairwise
#print axioms ATK.BealReduction.beal_iff_gcdOne
#print axioms ATK.BealReduction.beal_diagonal
#print axioms ATK.BealReduction.exemplo_nao_primitivo
#print axioms ATK.BealReduction.contraexemplo_expoente_dois
