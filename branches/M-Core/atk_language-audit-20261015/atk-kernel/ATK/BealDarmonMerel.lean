import ATK.BealFermatDescent

/-!
# ATK — Redução **condicional** de O2 pela ponte de Darmon–Merel

As reduções incondicionais de O2 com o que existe na Mathlib estão esgotadas: FLT(3), FLT(4),
`x⁴ + y⁴ ≠ z²` e `x⁴ − y⁴ ≠ z²` cobrem as famílias `3 ∣ mdc`, `4 ∣ mdc`, `(4,4,2)`, `(4,2,4)`,
`(2,4,4)` — 4,82% do domínio residual (expoentes 3..200, `mdc ≤ 2`).

O próximo corte vem de um teorema **publicado e não formalizado**, usado aqui como hipótese
explícita (`DarmonMerel`), nunca como axioma:

* `Aⁿ + Bⁿ = C²` não tem solução primitiva não trivial para `n ≥ 4`
  (Darmon–Merel 1997; `n = 4` Fermat; `n = 5, 6, 9` Poonen 1998);
* `Aⁿ + Bⁿ = C³` não tem solução primitiva não trivial para `n ≥ 3`
  (Darmon–Merel 1997, condicional à modularidade, hoje teorema por Breuil–Conrad–Diamond–Taylor 2001;
  `n = 3` Euler, `n = 4` Lucas, `n = 5` Poonen).

As hipóteses abaixo são as formas **mais fracas** desses teoremas (só inteiros positivos com
`A, B` coprimos), que são consequência direta deles.

Com elas o kernel prova:
* `sem_solucao_dm_sq`: `n ≥ 4`, `n ∣ x`, `n ∣ y`, `2 ∣ z` ⇒ sem solução coprima;
* `sem_solucao_dm_cube`: `n ≥ 3`, `n ∣ x`, `n ∣ y`, `3 ∣ z` ⇒ sem solução coprima;
* `beal_iff_residual_dm`: `DarmonMerel → (BealConjecture ↔ ExclusaoResidualDM)`, em que o residual
  exclui também `mdc(x, y) ≥ 4 ∧ 2 ∣ z` e `mdc(x, y) ≥ 3 ∧ 3 ∣ z`.

Cobertura do domínio residual (expoentes 3..200, `mdc ≤ 2`): de 4,82% (incondicional) para
**11,03%** (800.982 de 7.260.078 triplos) sob `DarmonMerel`. Exemplos novos: `(4,4,3)`, `(5,5,4)`,
`(7,14,6)`.

**Status.** É uma redução condicional: vale só se a ponte `DarmonMerel` for provada (a prova
publicada usa modularidade, ausente da Mathlib). O2 continua aberta; `CLOSED_MATH = false`.
-/

namespace ATK.BealDarmonMerel

open ATK.Conditional.Beal ATK.BealFermatDescent

/-- Ponte publicada (Darmon–Merel 1997; Poonen 1998), forma fraca: `Aⁿ + Bⁿ ≠ C²` para `n ≥ 4`,
`A, B > 0` coprimos. -/
def DarmonMerelSq : Prop :=
  ∀ n A B C : ℕ, 4 ≤ n → 0 < A → 0 < B → Nat.Coprime A B → A ^ n + B ^ n ≠ C ^ 2

/-- Ponte publicada (Darmon–Merel 1997 + BCDT 2001; Euler, Lucas, Poonen), forma fraca:
`Aⁿ + Bⁿ ≠ C³` para `n ≥ 3`, `A, B > 0` coprimos. -/
def DarmonMerelCube : Prop :=
  ∀ n A B C : ℕ, 3 ≤ n → 0 < A → 0 < B → Nat.Coprime A B → A ^ n + B ^ n ≠ C ^ 3

/-- A ponte completa usada nesta redução. -/
def DarmonMerel : Prop :=
  DarmonMerelSq ∧ DarmonMerelCube

/-- Sob `DarmonMerelSq`: `n ≥ 4`, `n ∣ x`, `n ∣ y`, `2 ∣ z` ⇒ sem solução com `a, b` coprimos. -/
theorem sem_solucao_dm_sq (hDM : DarmonMerelSq) {a b c x y z n : ℕ} (hn : 4 ≤ n)
    (hx : n ∣ x) (hy : n ∣ y) (hz : 2 ∣ z) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := hz
  intro heq
  exact hDM n (a ^ r) (b ^ s) (c ^ t) hn (pow_pos ha r) (pow_pos hb s) (Nat.Coprime.pow r s hab)
    (by rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm r n, mul_comm s n, mul_comm t 2]; exact heq)

/-- Sob `DarmonMerelCube`: `n ≥ 3`, `n ∣ x`, `n ∣ y`, `3 ∣ z` ⇒ sem solução com `a, b` coprimos. -/
theorem sem_solucao_dm_cube (hDM : DarmonMerelCube) {a b c x y z n : ℕ} (hn : 3 ≤ n)
    (hx : n ∣ x) (hy : n ∣ y) (hz : 3 ∣ z) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := hz
  intro heq
  exact hDM n (a ^ r) (b ^ s) (c ^ t) hn (pow_pos ha r) (pow_pos hb s) (Nat.Coprime.pow r s hab)
    (by rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm r n, mul_comm s n, mul_comm t 3]; exact heq)

/-- Residual após as reduções incondicionais **e** as duas famílias de Darmon–Merel. -/
def ExclusaoResidualDM : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) → ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) → ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) →
    ¬ (4 ≤ Nat.gcd x y ∧ 2 ∣ z) → ¬ (3 ≤ Nat.gcd x y ∧ 3 ∣ z) →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

/-- Sob `DarmonMerel`, o residual da descida equivale ao residual reduzido. -/
theorem descida_iff_dm (hDM : DarmonMerel) : ExclusaoResidualDescida ↔ ExclusaoResidualDM := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 _ _ hab
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab
    by_cases hsq : 4 ≤ Nat.gcd x y ∧ 2 ∣ z
    · exact sem_solucao_dm_sq hDM.1 hsq.1 (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y) hsq.2
        ha hb hab
    by_cases hcu : 3 ≤ Nat.gcd x y ∧ 3 ∣ z
    · exact sem_solucao_dm_cube hDM.2 hcu.1 (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y) hcu.2
        ha hb hab
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hsq hcu hab

/-- **Redução condicional de O2**: `DarmonMerel → (BealConjecture ↔ ExclusaoResidualDM)`. -/
theorem beal_iff_residual_dm (hDM : DarmonMerel) : BealConjecture ↔ ExclusaoResidualDM :=
  beal_iff_residual_descida.trans (descida_iff_dm hDM)

/-- Instâncias sob a ponte: `(4,4,3)`, `(5,5,4)`, `(7,14,6)` sem solução coprima. -/
theorem exemplos_dm (hDM : DarmonMerel) {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    a ^ 4 + b ^ 4 ≠ c ^ 3 ∧ a ^ 5 + b ^ 5 ≠ c ^ 4 ∧ a ^ 7 + b ^ 14 ≠ c ^ 6 :=
  ⟨sem_solucao_dm_cube hDM.2 (n := 4) (by norm_num) (dvd_refl 4) (dvd_refl 4) (dvd_refl 3)
      ha hb hab,
    sem_solucao_dm_sq hDM.1 (n := 5) (by norm_num) (dvd_refl 5) (dvd_refl 5) ⟨2, rfl⟩ ha hb hab,
    sem_solucao_dm_sq hDM.1 (n := 7) (by norm_num) (dvd_refl 7) ⟨2, rfl⟩ ⟨3, rfl⟩ ha hb hab⟩

/-- Esses triplos estão fora de todos os casos incondicionais anteriores. -/
theorem exemplos_dm_novos :
    (¬ 3 ∣ Nat.gcd 4 (Nat.gcd 4 3) ∧ ¬ 4 ∣ Nat.gcd 4 (Nat.gcd 4 3) ∧
      ¬ (4 ∣ 4 ∧ 4 ∣ 4 ∧ 2 ∣ 3) ∧ ¬ (4 ∣ 4 ∧ 2 ∣ 4 ∧ 4 ∣ 3) ∧ ¬ (2 ∣ 4 ∧ 4 ∣ 4 ∧ 4 ∣ 3)) ∧
    (¬ 3 ∣ Nat.gcd 5 (Nat.gcd 5 4) ∧ ¬ 4 ∣ Nat.gcd 5 (Nat.gcd 5 4) ∧
      ¬ (4 ∣ 5 ∧ 4 ∣ 5 ∧ 2 ∣ 4) ∧ ¬ (4 ∣ 5 ∧ 2 ∣ 5 ∧ 4 ∣ 4) ∧ ¬ (2 ∣ 5 ∧ 4 ∣ 5 ∧ 4 ∣ 4)) ∧
    (¬ 3 ∣ Nat.gcd 7 (Nat.gcd 14 6) ∧ ¬ 4 ∣ Nat.gcd 7 (Nat.gcd 14 6) ∧
      ¬ (4 ∣ 7 ∧ 4 ∣ 14 ∧ 2 ∣ 6) ∧ ¬ (4 ∣ 7 ∧ 2 ∣ 14 ∧ 4 ∣ 6) ∧ ¬ (2 ∣ 7 ∧ 4 ∣ 14 ∧ 4 ∣ 6)) := by
  decide

end ATK.BealDarmonMerel

#print axioms ATK.BealDarmonMerel.sem_solucao_dm_sq
#print axioms ATK.BealDarmonMerel.sem_solucao_dm_cube
#print axioms ATK.BealDarmonMerel.descida_iff_dm
#print axioms ATK.BealDarmonMerel.beal_iff_residual_dm
#print axioms ATK.BealDarmonMerel.exemplos_dm
#print axioms ATK.BealDarmonMerel.exemplos_dm_novos
