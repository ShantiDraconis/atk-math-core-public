import ATK.BealResidual

/-!
# ATK — Beal na assinatura `(4k, 4l, 2m)`, incondicionalmente (redução do residual de O2)

A Mathlib prova (descida infinita de Fermat) que `a⁴ + b⁴ = c²` não tem solução com
`a, b ≠ 0` (`not_fermat_42`, em `Mathlib.NumberTheory.FLT.Four`). Daí:

* `sem_solucao_442`: se `4 ∣ x`, `4 ∣ y` e `2 ∣ z`, então `aˣ + bʸ = cᶻ` **não tem solução**
  com `a, b > 0` — escrevendo `aˣ = (aʳ)⁴`, `bʸ = (bˢ)⁴`, `cᶻ = (cᵗ)²`;
* `beal_442`: Beal vale para todo triplo de expoentes desse tipo.

Isso cobre triplos **fora** do caso já certificado `3 ∣ mdc(x,y,z)` ou `4 ∣ mdc(x,y,z)`
(`ATK.BealPartial.beal_mdc_expoentes`): p.ex. `(4, 4, 6)`, `(8, 4, 10)`, `(4, 12, 14)`, com
`mdc = 2`. O residual de `ATK.BealResidual` encolhe para `ExclusaoResidual442`, e o kernel prova
`BealConjecture ↔ ExclusaoResidual442` sem pontes.

Status matemático: o fato `x⁴ + y⁴ ≠ z²` é clássico (Fermat); a consequência para Beal é
folclore. O que é novo aqui é só a formalização no atk-kernel. **O2 continua aberta.**
-/

namespace ATK.BealFourFourTwo

open ATK.Conditional.Beal ATK.BealPartial ATK.BealResidual

/-- **Sem solução** quando `4 ∣ x`, `4 ∣ y`, `2 ∣ z` (via `not_fermat_42` da Mathlib). -/
theorem sem_solucao_442 {a b c x y z : ℕ} (hx : 4 ∣ x) (hy : 4 ∣ y) (hz : 2 ∣ z)
    (ha : 0 < a) (hb : 0 < b) : a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := hz
  intro heq
  have hA : ((a : ℤ) ^ r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast ha.ne')
  have hB : ((b : ℤ) ^ s) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb.ne')
  have hZ : (a : ℤ) ^ (4 * r) + (b : ℤ) ^ (4 * s) = (c : ℤ) ^ (2 * t) := by
    exact_mod_cast heq
  have e1 : ((a : ℤ) ^ r) ^ 4 = (a : ℤ) ^ (4 * r) := by rw [← pow_mul, mul_comm r 4]
  have e2 : ((b : ℤ) ^ s) ^ 4 = (b : ℤ) ^ (4 * s) := by rw [← pow_mul, mul_comm s 4]
  have e3 : ((c : ℤ) ^ t) ^ 2 = (c : ℤ) ^ (2 * t) := by rw [← pow_mul, mul_comm t 2]
  exact not_fermat_42 (c := (c : ℤ) ^ t) hA hB (by rw [e1, e2, e3]; exact hZ)

/-- **Incondicional**: Beal para todo triplo `(x, y, z)` com `4 ∣ x`, `4 ∣ y`, `2 ∣ z`. -/
theorem beal_442 {x y z : ℕ} (hx : 4 ∣ x) (hy : 4 ∣ y) (hz : 2 ∣ z) : BealFor x y z :=
  fun _ _ _ ha hb _ heq => absurd heq (sem_solucao_442 hx hy hz ha hb)

/-- Residual reduzido: além de `3 ∤ g` e `4 ∤ g`, exclui a assinatura `(4k, 4l, 2m)`. -/
def ExclusaoResidual442 : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

theorem residual_iff_residual442 : ExclusaoResidual ↔ ExclusaoResidual442 := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 _ hab
    exact h a b c x y z ha hb hc hx hy hz h3 h4 hab
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 hab
    by_cases h442 : 4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z
    · exact sem_solucao_442 h442.1 h442.2.1 h442.2.2 ha hb
    · exact h a b c x y z ha hb hc hx hy hz h3 h4 h442 hab

/-- **Beal ⟺ residual reduzido** (incondicional, sem pontes). -/
theorem beal_iff_residual442 : BealConjecture ↔ ExclusaoResidual442 :=
  beal_iff_residual.trans residual_iff_residual442

/-- Instâncias: `(4,4,6)`, `(8,4,10)`, `(4,12,14)`. -/
theorem exemplos_442 : BealFor 4 4 6 ∧ BealFor 8 4 10 ∧ BealFor 4 12 14 :=
  ⟨beal_442 (dvd_refl 4) (dvd_refl 4) ⟨3, rfl⟩,
    beal_442 ⟨2, rfl⟩ (dvd_refl 4) ⟨5, rfl⟩,
    beal_442 (dvd_refl 4) ⟨3, rfl⟩ ⟨7, rfl⟩⟩

/-- Esses triplos têm `mdc = 2`: **não** eram cobertos por `beal_mdc_expoentes`. -/
theorem exemplos_442_fora_do_caso_mdc :
    ¬ 3 ∣ Nat.gcd 4 (Nat.gcd 4 6) ∧ ¬ 4 ∣ Nat.gcd 4 (Nat.gcd 4 6) ∧
    ¬ 3 ∣ Nat.gcd 8 (Nat.gcd 4 10) ∧ ¬ 4 ∣ Nat.gcd 8 (Nat.gcd 4 10) ∧
    ¬ 3 ∣ Nat.gcd 4 (Nat.gcd 12 14) ∧ ¬ 4 ∣ Nat.gcd 4 (Nat.gcd 12 14) := by
  decide

end ATK.BealFourFourTwo

#print axioms ATK.BealFourFourTwo.sem_solucao_442
#print axioms ATK.BealFourFourTwo.beal_442
#print axioms ATK.BealFourFourTwo.residual_iff_residual442
#print axioms ATK.BealFourFourTwo.beal_iff_residual442
#print axioms ATK.BealFourFourTwo.exemplos_442
#print axioms ATK.BealFourFourTwo.exemplos_442_fora_do_caso_mdc
