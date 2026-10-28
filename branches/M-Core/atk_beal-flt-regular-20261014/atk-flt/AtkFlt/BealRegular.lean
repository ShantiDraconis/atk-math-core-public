import FltRegular.FltRegular
import FltRegular.SmallNumbers.Five.FLT5
import FltRegular.SmallNumbers.Seven.FLT7
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# ATK — Beal quando o mdc dos expoentes tem um primo regular (via `flt-regular`)

O projeto [`flt-regular`](https://github.com/leanprover-community/flt-regular) (Brasca, Best,
Birkbeck, Rodriguez, Van de Velde, Yang; formalização completa publicada em *Annals of
Formalized Mathematics*) prova o Último Teorema de Fermat para todo primo ímpar **regular**
(`flt_regular`) e que 5 e 7 são regulares (`fermatLastTheoremFive`, `fermatLastTheoremSeven`).

Daqui, sem nenhuma hipótese:

* `beal_mdc_cinco`, `beal_mdc_sete`: Beal vale para todo triplo `(x, y, z)` com `5 ∣ mdc` ou
  `7 ∣ mdc` (junto com `3 ∣ mdc` e `4 ∣ mdc`, da Mathlib);
* `beal_iff_residual3457`: `BealConjecture ⟺` Beal nos triplos com `mdc` não divisível por
  `3`, `4`, `5` nem `7`;
* `beal_de_primo_regular`: Beal vale quando um primo ímpar regular divide o `mdc`;
* `beal_iff_residualRegular`: `BealConjecture ⟺` Beal nos triplos cujo `mdc` não é divisível por
  `3`, `4` nem por nenhum primo ímpar regular.

`BealConjecture` aqui é **o mesmo texto** de `ATK.Conditional.Beal.BealConjecture` (no
`atk-kernel`, que ainda está na Mathlib v4.34.1 e não pode importar este arquivo).

**O que isto NÃO muda.** A obrigação O2 é o caso `mdc(x, y, z) ≤ 2`; nada aqui o toca. O que
diminui é a dependência da ponte B2 (FLT geral): ela agora só é necessária quando os primos
ímpares do `mdc` são todos irregulares (37, 59, 67, …) e o mdc não é múltiplo de 4.
-/

namespace ATK.BealRegular

/-- Enunciado oficial (mesmo texto de `ATK.Conditional.Beal.BealConjecture`). -/
def BealConjecture : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    a ^ x + b ^ y = c ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

/-- Beal para um triplo fixo de expoentes. -/
def BealFor (x y z : ℕ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    a ^ x + b ^ y = c ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

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

/-- Forma via `mdc(x, y, z)`. -/
theorem sem_solucao_mdc {d a b c x y z : ℕ} (hF : FermatLastTheoremFor d)
    (h : d ∣ Nat.gcd x (Nat.gcd y z)) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ x + b ^ y ≠ c ^ z :=
  sem_solucao_de_flt_divisor hF (h.trans (Nat.gcd_dvd_left _ _))
    (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)))
    (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))) ha hb hc

/-- FLT(d) e `d ∣ mdc(x, y, z)` dão Beal para `(x, y, z)` (por vacuidade: não há soluções). -/
theorem beal_de_flt_mdc {d x y z : ℕ} (hF : FermatLastTheoremFor d)
    (h : d ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  fun _ _ _ ha hb hc heq => absurd heq (sem_solucao_mdc hF h ha hb hc)

/-- **Incondicional**: Beal quando `3 ∣ mdc(x, y, z)` (FLT(3), Mathlib). -/
theorem beal_mdc_tres {x y z : ℕ} (h : 3 ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  beal_de_flt_mdc fermatLastTheoremThree h

/-- **Incondicional**: Beal quando `4 ∣ mdc(x, y, z)` (FLT(4), Mathlib). -/
theorem beal_mdc_quatro {x y z : ℕ} (h : 4 ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  beal_de_flt_mdc fermatLastTheoremFour h

/-- **Incondicional**: Beal quando `5 ∣ mdc(x, y, z)` (FLT(5), `flt-regular`). -/
theorem beal_mdc_cinco {x y z : ℕ} (h : 5 ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  beal_de_flt_mdc fermatLastTheoremFive h

/-- **Incondicional**: Beal quando `7 ∣ mdc(x, y, z)` (FLT(7), `flt-regular`). -/
theorem beal_mdc_sete {x y z : ℕ} (h : 7 ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  beal_de_flt_mdc fermatLastTheoremSeven h

/-- **Beal quando um primo ímpar regular divide `mdc(x, y, z)`.** -/
theorem beal_de_primo_regular {p x y z : ℕ} (hp : p.Prime) (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) (h : p ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  haveI := Fact.mk hp
  beal_de_flt_mdc (flt_regular hreg hodd) h

/-- Beal ⟺ Beal para cada triplo de expoentes maiores que 2. -/
theorem beal_iff_forall_bealFor :
    BealConjecture ↔ ∀ x y z : ℕ, 2 < x → 2 < y → 2 < z → BealFor x y z :=
  ⟨fun h x y z hx hy hz a b c ha hb hc heq => h a b c x y z ha hb hc hx hy hz heq,
    fun h a b c x y z ha hb hc hx hy hz heq => h x y z hx hy hz a b c ha hb hc heq⟩

/-- Residual: triplos cujo `mdc` não é divisível por `3`, `4`, `5` nem `7`. -/
def ExclusaoResidual3457 : Prop :=
  ∀ x y z : ℕ, 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ 5 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 7 ∣ Nat.gcd x (Nat.gcd y z) → BealFor x y z

/-- **Beal ⟺ residual sem `3, 4, 5, 7` no mdc** (incondicional, sem pontes). -/
theorem beal_iff_residual3457 : BealConjecture ↔ ExclusaoResidual3457 := by
  rw [beal_iff_forall_bealFor]
  constructor
  · intro h x y z hx hy hz _ _ _ _
    exact h x y z hx hy hz
  · intro h x y z hx hy hz
    by_cases h3 : 3 ∣ Nat.gcd x (Nat.gcd y z)
    · exact beal_mdc_tres h3
    by_cases h4 : 4 ∣ Nat.gcd x (Nat.gcd y z)
    · exact beal_mdc_quatro h4
    by_cases h5 : 5 ∣ Nat.gcd x (Nat.gcd y z)
    · exact beal_mdc_cinco h5
    by_cases h7 : 7 ∣ Nat.gcd x (Nat.gcd y z)
    · exact beal_mdc_sete h7
    exact h x y z hx hy hz h3 h4 h5 h7

/-- Residual: triplos cujo `mdc` não é divisível por `3`, `4` nem por primo ímpar regular. -/
def ExclusaoResidualRegular : Prop :=
  ∀ x y z : ℕ, 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    (∀ p : ℕ, p.Prime → IsRegularPrime p → p ≠ 2 → ¬ p ∣ Nat.gcd x (Nat.gcd y z)) →
    BealFor x y z

/-- **Beal ⟺ residual sem `3`, `4` nem primos ímpares regulares no mdc.** -/
theorem beal_iff_residualRegular : BealConjecture ↔ ExclusaoResidualRegular := by
  rw [beal_iff_forall_bealFor]
  constructor
  · intro h x y z hx hy hz _ _ _
    exact h x y z hx hy hz
  · intro h x y z hx hy hz
    by_cases h3 : 3 ∣ Nat.gcd x (Nat.gcd y z)
    · exact beal_mdc_tres h3
    by_cases h4 : 4 ∣ Nat.gcd x (Nat.gcd y z)
    · exact beal_mdc_quatro h4
    by_cases hr : ∃ p : ℕ, p.Prime ∧ IsRegularPrime p ∧ p ≠ 2 ∧ p ∣ Nat.gcd x (Nat.gcd y z)
    · obtain ⟨p, hp, hreg, hodd, hdvd⟩ := hr
      exact beal_de_primo_regular hp hreg hodd hdvd
    · refine h x y z hx hy hz h3 h4 fun p hp hreg hodd hdvd => hr ⟨p, hp, hreg, hodd, hdvd⟩

/-- Instâncias novas (fora de `3 ∣ mdc`, `4 ∣ mdc`): `(5, 10, 15)`, `(10, 15, 20)`,
`(7, 14, 21)`, `(35, 70, 14)`. -/
theorem exemplos : BealFor 5 10 15 ∧ BealFor 10 15 20 ∧ BealFor 7 14 21 ∧ BealFor 35 70 14 :=
  ⟨beal_mdc_cinco (by decide), beal_mdc_cinco (by decide), beal_mdc_sete (by decide),
    beal_mdc_sete (by decide)⟩

/-- Esses triplos não eram cobertos por `3 ∣ mdc` nem `4 ∣ mdc`. -/
theorem exemplos_novos :
    ¬ 3 ∣ Nat.gcd 5 (Nat.gcd 10 15) ∧ ¬ 4 ∣ Nat.gcd 5 (Nat.gcd 10 15) ∧
    ¬ 3 ∣ Nat.gcd 10 (Nat.gcd 15 20) ∧ ¬ 4 ∣ Nat.gcd 10 (Nat.gcd 15 20) ∧
    ¬ 3 ∣ Nat.gcd 7 (Nat.gcd 14 21) ∧ ¬ 4 ∣ Nat.gcd 7 (Nat.gcd 14 21) ∧
    ¬ 3 ∣ Nat.gcd 35 (Nat.gcd 70 14) ∧ ¬ 4 ∣ Nat.gcd 35 (Nat.gcd 70 14) := by
  decide

end ATK.BealRegular

#print axioms ATK.BealRegular.sem_solucao_de_flt_divisor
#print axioms ATK.BealRegular.sem_solucao_mdc
#print axioms ATK.BealRegular.beal_de_flt_mdc
#print axioms ATK.BealRegular.beal_mdc_tres
#print axioms ATK.BealRegular.beal_mdc_quatro
#print axioms ATK.BealRegular.beal_mdc_cinco
#print axioms ATK.BealRegular.beal_mdc_sete
#print axioms ATK.BealRegular.beal_de_primo_regular
#print axioms ATK.BealRegular.beal_iff_forall_bealFor
#print axioms ATK.BealRegular.beal_iff_residual3457
#print axioms ATK.BealRegular.beal_iff_residualRegular
#print axioms ATK.BealRegular.exemplos
#print axioms ATK.BealRegular.exemplos_novos
