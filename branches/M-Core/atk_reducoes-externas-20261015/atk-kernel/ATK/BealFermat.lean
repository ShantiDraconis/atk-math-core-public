import ATK.Conditional.Beal
import Mathlib.NumberTheory.FLT.Basic

/-!
# ATK — Beal reduzida a `mdc(x, y, z) ≤ 2`, dado o Último Teorema de Fermat

Se `d ∣ x, y, z` e `aˣ + bʸ = cᶻ`, então `(a^{x/d})ᵈ + (b^{y/d})ᵈ = (c^{z/d})ᵈ`. Com FLT para o
expoente `d ≥ 3`, não há solução nenhuma. Logo, com FLT geral, Beal vale para todo triplo cujo
`mdc` é pelo menos 3, e o que sobra é exatamente o caso `mdc ∈ {1, 2}` (a obrigação O2).

FLT geral está provado em Lean: `anthropics/fermats-last-theorem` (setembro de 2026, Lean
4.33.1, Mathlib `v4.33.0`; `fermat_last_theorem` só com os três axiomas padrão, e
`FinalCheck.lean` deriva dele o `FermatLastTheorem` da Mathlib). Esse projeto tem 60 474
módulos; compilá-lo pede cerca de 530 horas de CPU, até 36 GB de memória por módulo e ~300 GB
de disco, o que não cabe no CI hospedado do GitHub. Por isso aqui FLT entra como **hipótese
explícita** (`FermatLastTheorem`, a definição da Mathlib), nunca como axioma. O subprojeto
`atk-fermat` (execução manual, máquina própria) é onde ela é descarregada.

Provado aqui:

* `sem_solucao_mdc`: FLT(d) e `d ∣ mdc(x, y, z)` ⟹ nenhuma solução;
* `beal_de_mdc_ge_tres`: com FLT, Beal vale para todo triplo com `mdc ≥ 3`;
* `beal_iff_residual`: com FLT, **`BealConjecture ⟺ ResidualMdcAteDois`**;
* `residual_de_beal`: o resíduo não é mais forte que Beal (sanidade).
-/

namespace ATK.BealFermat

/-- Beal para um triplo fixo de expoentes. -/
def BealFor (x y z : ℕ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    a ^ x + b ^ y = c ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

/-- O resíduo de Beal depois de FLT: triplos com `mdc(x, y, z) ≤ 2`. -/
def ResidualMdcAteDois : Prop :=
  ∀ x y z : ℕ, 2 < x → 2 < y → 2 < z → Nat.gcd x (Nat.gcd y z) ≤ 2 → BealFor x y z

theorem beal_iff_forall_bealFor :
    ATK.Conditional.Beal.BealConjecture ↔ ∀ x y z : ℕ, 2 < x → 2 < y → 2 < z → BealFor x y z :=
  ⟨fun h x y z hx hy hz a b c ha hb hc heq => h a b c x y z ha hb hc hx hy hz heq,
    fun h a b c x y z ha hb hc hx hy hz heq => h x y z hx hy hz a b c ha hb hc heq⟩

/-- Se `d` divide os três expoentes e vale FLT(d), **não há solução alguma**. -/
theorem sem_solucao_de_divisor {d a b c x y z : ℕ} (hF : FermatLastTheoremFor d)
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

/-- Forma via `mdc(x, y, z)`. -/
theorem sem_solucao_mdc {d a b c x y z : ℕ} (hF : FermatLastTheoremFor d)
    (h : d ∣ Nat.gcd x (Nat.gcd y z)) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ x + b ^ y ≠ c ^ z :=
  sem_solucao_de_divisor hF (h.trans (Nat.gcd_dvd_left _ _))
    (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)))
    (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))) ha hb hc

/-- **Com FLT, Beal vale para todo triplo com `mdc(x, y, z) ≥ 3`** (não há soluções). -/
theorem beal_de_mdc_ge_tres (hF : FermatLastTheorem) {x y z : ℕ}
    (h : 3 ≤ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  fun _ _ _ ha hb hc heq => absurd heq (sem_solucao_mdc (hF _ h) dvd_rfl ha hb hc)

/-- **Com FLT, Beal ⟺ o resíduo `mdc(x, y, z) ≤ 2`.** -/
theorem beal_iff_residual (hF : FermatLastTheorem) :
    ATK.Conditional.Beal.BealConjecture ↔ ResidualMdcAteDois := by
  rw [beal_iff_forall_bealFor]
  constructor
  · exact fun h x y z hx hy hz _ => h x y z hx hy hz
  · intro h x y z hx hy hz
    by_cases hd : Nat.gcd x (Nat.gcd y z) ≤ 2
    · exact h x y z hx hy hz hd
    · exact beal_de_mdc_ge_tres hF (by omega)

/-- O resíduo segue de Beal (a redução não pede mais do que Beal). -/
theorem residual_de_beal (h : ATK.Conditional.Beal.BealConjecture) : ResidualMdcAteDois :=
  fun x y z hx hy hz _ => beal_iff_forall_bealFor.mp h x y z hx hy hz

/-- O `mdc` de expoentes maiores que 2 nunca é 0: o resíduo é `mdc ∈ {1, 2}`. -/
theorem mdc_pos {x y z : ℕ} (hx : 2 < x) : 0 < Nat.gcd x (Nat.gcd y z) :=
  Nat.gcd_pos_of_pos_left _ (by omega)

end ATK.BealFermat

#print axioms ATK.BealFermat.beal_iff_forall_bealFor
#print axioms ATK.BealFermat.sem_solucao_de_divisor
#print axioms ATK.BealFermat.sem_solucao_mdc
#print axioms ATK.BealFermat.beal_de_mdc_ge_tres
#print axioms ATK.BealFermat.beal_iff_residual
#print axioms ATK.BealFermat.residual_de_beal
#print axioms ATK.BealFermat.mdc_pos
