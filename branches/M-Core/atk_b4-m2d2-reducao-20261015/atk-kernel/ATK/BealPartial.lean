import ATK.Conditional.Beal
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# ATK — Casos de Beal provados incondicionalmente (fragmento da obrigação O2)

`BealConjecture` (em `ATK.Conditional.Beal`): para `a, b, c > 0` e `x, y, z > 2`,
`aˣ + bʸ = cᶻ ⇒` existe primo dividindo `a`, `b` e `c`.

Com os teoremas de Fermat para expoentes 3 e 4 **já formalizados na Mathlib**
(`fermatLastTheoremThree`, `fermatLastTheoremFour`) e a monotonia
`FermatLastTheoremFor.mono`, o kernel prova:

* `beal_expoentes_iguais_de_flt`: Beal no caso `x = y = z = n` segue de FLT(n) — a hipótese fica
  vazia (não há solução alguma);
* `beal_expoentes_iguais_mult3` / `beal_expoentes_iguais_mult4`: **incondicional** para todo `n`
  múltiplo de 3 ou de 4 (`n = 3, 4, 6, 8, 9, 12, 15, 16, …`);
* `beal_igual_de_FLT`: Beal com expoentes iguais, em geral, a partir do enunciado completo de Fermat
  (`FermatLastTheorem` da Mathlib; provado por Wiles–Taylor, ainda não formalizado na Mathlib).

Expoentes distintos: `sem_solucao_de_flt_divisor` mostra que se `d` divide `x, y, z` e vale
FLT(d), não há solução — logo Beal vale incondicionalmente para todo triplo com
`3 ∣ mdc(x, y, z)` ou `4 ∣ mdc(x, y, z)` (`beal_mdc_expoentes`), p.ex. `(3, 6, 9)`, `(4, 8, 12)`.

O caso geral (a obrigação O2) continua aberto: com `ATK.BealReduction.beal_iff_pairwise`, resta
exatamente excluir soluções dois a dois coprimas com `3 ∤ mdc` e `4 ∤ mdc` dos expoentes.
-/

namespace ATK.BealPartial

open ATK.Conditional.Beal

/-- Beal restrito a expoentes iguais `x = y = z = n`. -/
def BealIgual (n : ℕ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → 2 < n →
    a ^ n + b ^ n = c ^ n → ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

/-- `BealConjecture` implica cada caso de expoentes iguais (o fragmento é de fato parte de O2). -/
theorem bealIgual_de_beal (h : BealConjecture) (n : ℕ) : BealIgual n :=
  fun a b c ha hb hc hn heq => h a b c n n n ha hb hc hn hn hn heq

/-- **Beal com expoentes iguais segue de FLT(n)**: não há solução, a hipótese é vazia. -/
theorem beal_expoentes_iguais_de_flt {n : ℕ} (hF : FermatLastTheoremFor n) : BealIgual n :=
  fun a b c ha hb hc _ heq =>
    absurd heq (hF a b c (Nat.pos_iff_ne_zero.mp ha) (Nat.pos_iff_ne_zero.mp hb)
      (Nat.pos_iff_ne_zero.mp hc))

/-- **Incondicional**: Beal para `x = y = z = n` com `3 ∣ n`. -/
theorem beal_expoentes_iguais_mult3 {n : ℕ} (h3 : 3 ∣ n) : BealIgual n :=
  beal_expoentes_iguais_de_flt (fermatLastTheoremThree.mono h3)

/-- **Incondicional**: Beal para `x = y = z = n` com `4 ∣ n`. -/
theorem beal_expoentes_iguais_mult4 {n : ℕ} (h4 : 4 ∣ n) : BealIgual n :=
  beal_expoentes_iguais_de_flt (fermatLastTheoremFour.mono h4)

/-- Casos concretos verificados: `n = 3, 4, 6, 8, 9, 12`. -/
theorem beal_igual_pequenos :
    BealIgual 3 ∧ BealIgual 4 ∧ BealIgual 6 ∧ BealIgual 8 ∧ BealIgual 9 ∧ BealIgual 12 :=
  ⟨beal_expoentes_iguais_mult3 (dvd_refl 3), beal_expoentes_iguais_mult4 (dvd_refl 4),
    beal_expoentes_iguais_mult3 ⟨2, rfl⟩, beal_expoentes_iguais_mult4 ⟨2, rfl⟩,
    beal_expoentes_iguais_mult3 ⟨3, rfl⟩, beal_expoentes_iguais_mult3 ⟨4, rfl⟩⟩

/-- Beal com expoentes iguais, para todo `n > 2`, a partir do enunciado de Fermat (ponte B2). -/
theorem beal_igual_de_FLT (hF : FermatLastTheorem) (n : ℕ) (hn : 3 ≤ n) : BealIgual n :=
  beal_expoentes_iguais_de_flt (hF n hn)

/-! ## Expoentes distintos com fator comum 3 ou 4 (incondicional) -/

/-- Beal para um triplo fixo de expoentes. -/
def BealFor (x y z : ℕ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    a ^ x + b ^ y = c ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

/-- `BealConjecture` ⟺ `BealFor x y z` para todo triplo com `x, y, z > 2`. -/
theorem beal_iff_forall_bealFor :
    BealConjecture ↔ ∀ x y z : ℕ, 2 < x → 2 < y → 2 < z → BealFor x y z := by
  constructor
  · intro h x y z hx hy hz a b c ha hb hc heq
    exact h a b c x y z ha hb hc hx hy hz heq
  · intro h a b c x y z ha hb hc hx hy hz heq
    exact h x y z hx hy hz a b c ha hb hc heq

/-- Se `d` divide os três expoentes e vale FLT(d), **não há solução alguma**. -/
theorem sem_solucao_de_flt_divisor {d a b c x y z : ℕ} (hF : FermatLastTheoremFor d)
    (hx : d ∣ x) (hy : d ∣ y) (hz : d ∣ z) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := hz
  intro heq
  apply hF (a ^ r) (b ^ s) (c ^ t) (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne')
    (pow_ne_zero _ hc.ne')
  rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm r d, mul_comm s d, mul_comm t d]
  exact heq

/-- **Incondicional**: Beal para todo triplo `(x, y, z)` com `3 ∣ x, y, z`
(ex.: `(3, 6, 9)`, `(6, 9, 12)`, `(3, 3, 15)`, …). -/
theorem beal_expoentes_mult3 {x y z : ℕ} (hx : 3 ∣ x) (hy : 3 ∣ y) (hz : 3 ∣ z) :
    BealFor x y z :=
  fun _ _ _ ha hb hc heq =>
    absurd heq (sem_solucao_de_flt_divisor fermatLastTheoremThree hx hy hz ha hb hc)

/-- **Incondicional**: Beal para todo triplo `(x, y, z)` com `4 ∣ x, y, z`
(ex.: `(4, 8, 12)`, `(4, 4, 20)`, …). -/
theorem beal_expoentes_mult4 {x y z : ℕ} (hx : 4 ∣ x) (hy : 4 ∣ y) (hz : 4 ∣ z) :
    BealFor x y z :=
  fun _ _ _ ha hb hc heq =>
    absurd heq (sem_solucao_de_flt_divisor fermatLastTheoremFour hx hy hz ha hb hc)

/-- Forma via mdc: `3 ∣ mdc(x, y, z)` ou `4 ∣ mdc(x, y, z)` ⇒ Beal para `(x, y, z)`. -/
theorem beal_mdc_expoentes {x y z : ℕ}
    (h : 3 ∣ Nat.gcd x (Nat.gcd y z) ∨ 4 ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z := by
  rcases h with h | h
  · exact beal_expoentes_mult3 (h.trans (Nat.gcd_dvd_left _ _))
      (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)))
      (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)))
  · exact beal_expoentes_mult4 (h.trans (Nat.gcd_dvd_left _ _))
      (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)))
      (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)))

/-- Instâncias concretas de expoentes **distintos**. -/
theorem beal_exemplos_distintos :
    BealFor 3 6 9 ∧ BealFor 6 9 12 ∧ BealFor 4 8 12 ∧ BealFor 12 8 4 :=
  ⟨beal_expoentes_mult3 (dvd_refl 3) ⟨2, rfl⟩ ⟨3, rfl⟩,
    beal_expoentes_mult3 ⟨2, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩,
    beal_expoentes_mult4 (dvd_refl 4) ⟨2, rfl⟩ ⟨3, rfl⟩,
    beal_expoentes_mult4 ⟨3, rfl⟩ ⟨2, rfl⟩ (dvd_refl 4)⟩

end ATK.BealPartial

#print axioms ATK.BealPartial.bealIgual_de_beal
#print axioms ATK.BealPartial.beal_expoentes_iguais_de_flt
#print axioms ATK.BealPartial.beal_expoentes_iguais_mult3
#print axioms ATK.BealPartial.beal_expoentes_iguais_mult4
#print axioms ATK.BealPartial.beal_igual_pequenos
#print axioms ATK.BealPartial.beal_igual_de_FLT
#print axioms ATK.BealPartial.beal_iff_forall_bealFor
#print axioms ATK.BealPartial.sem_solucao_de_flt_divisor
#print axioms ATK.BealPartial.beal_expoentes_mult3
#print axioms ATK.BealPartial.beal_expoentes_mult4
#print axioms ATK.BealPartial.beal_mdc_expoentes
#print axioms ATK.BealPartial.beal_exemplos_distintos
