import ATK.BealFourFourTwo
import ATK.FermatRightTriangle

/-!
# ATK — Beal nas assinaturas `(4k, 2l, 4m)` e `(2k, 4l, 4m)` (redução do residual de O2)

Com `ATK.FermatRightTriangle.not_fourth_add_sq_eq_fourth` (`x⁴ + y² ≠ z⁴`, consequência de
`x⁴ − y⁴ ≠ z²`, provada aqui por descida), o kernel prova:

* `sem_solucao_424`: `4 ∣ x`, `2 ∣ y`, `4 ∣ z` ⇒ `aˣ + bʸ = cᶻ` sem solução (`a, b > 0`);
* `sem_solucao_244`: o caso simétrico `2 ∣ x`, `4 ∣ y`, `4 ∣ z`;
* `beal_iff_residual_descida`: `BealConjecture ↔ ExclusaoResidualDescida`, sem pontes.

Junto com `(4k, 4l, 2m)` (`ATK.BealFourFourTwo`, via `not_fermat_42` da Mathlib), as três posições
do expoente "2" ficam cobertas. Exemplos novos (mdc dos expoentes = 2, fora de todos os casos
anteriores): `(4, 6, 4)`, `(8, 10, 4)`, `(6, 4, 4)`, `(10, 4, 8)`.

Status: matemática clássica (Fermat); nova só a formalização. **O2 continua aberta.**
-/

namespace ATK.BealFermatDescent

open ATK.Conditional.Beal ATK.BealReduction ATK.BealPartial ATK.BealResidual
  ATK.BealFourFourTwo ATK.FermatRightTriangle

/-- **Sem solução** quando `4 ∣ x`, `2 ∣ y`, `4 ∣ z`. -/
theorem sem_solucao_424 {a b c x y z : ℕ} (hx : 4 ∣ x) (hy : 2 ∣ y) (hz : 4 ∣ z)
    (ha : 0 < a) (hb : 0 < b) : a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := hz
  intro heq
  have hA : ((a : ℤ) ^ r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast ha.ne')
  have hB : ((b : ℤ) ^ s) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb.ne')
  have hZ : (a : ℤ) ^ (4 * r) + (b : ℤ) ^ (2 * s) = (c : ℤ) ^ (4 * t) := by
    exact_mod_cast heq
  have e1 : ((a : ℤ) ^ r) ^ 4 = (a : ℤ) ^ (4 * r) := by rw [← pow_mul, mul_comm r 4]
  have e2 : ((b : ℤ) ^ s) ^ 2 = (b : ℤ) ^ (2 * s) := by rw [← pow_mul, mul_comm s 2]
  have e3 : ((c : ℤ) ^ t) ^ 4 = (c : ℤ) ^ (4 * t) := by rw [← pow_mul, mul_comm t 4]
  exact not_fourth_add_sq_eq_fourth (z := (c : ℤ) ^ t) hA hB (by rw [e1, e2, e3]; exact hZ)

/-- **Sem solução** quando `2 ∣ x`, `4 ∣ y`, `4 ∣ z` (simétrico). -/
theorem sem_solucao_244 {a b c x y z : ℕ} (hx : 2 ∣ x) (hy : 4 ∣ y) (hz : 4 ∣ z)
    (ha : 0 < a) (hb : 0 < b) : a ^ x + b ^ y ≠ c ^ z := by
  intro heq
  exact sem_solucao_424 hy hx hz hb ha (by rw [add_comm]; exact heq)

/-- **Incondicional**: Beal para todo triplo com `4 ∣ x`, `2 ∣ y`, `4 ∣ z`. -/
theorem beal_424 {x y z : ℕ} (hx : 4 ∣ x) (hy : 2 ∣ y) (hz : 4 ∣ z) : BealFor x y z :=
  fun _ _ _ ha hb _ heq => absurd heq (sem_solucao_424 hx hy hz ha hb)

/-- **Incondicional**: Beal para todo triplo com `2 ∣ x`, `4 ∣ y`, `4 ∣ z`. -/
theorem beal_244 {x y z : ℕ} (hx : 2 ∣ x) (hy : 4 ∣ y) (hz : 4 ∣ z) : BealFor x y z :=
  fun _ _ _ ha hb _ heq => absurd heq (sem_solucao_244 hx hy hz ha hb)

/-- Residual após FLT(3), FLT(4), `(4,4,2)`, `(4,2,4)` e `(2,4,4)`. -/
def ExclusaoResidualDescida : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) → ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) → ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

theorem residual442_iff_descida : ExclusaoResidual442 ↔ ExclusaoResidualDescida := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h442 _ _ hab
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h442 hab
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h442 hab
    by_cases h424 : 4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z
    · exact sem_solucao_424 h424.1 h424.2.1 h424.2.2 ha hb
    by_cases h244 : 2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z
    · exact sem_solucao_244 h244.1 h244.2.1 h244.2.2 ha hb
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h442 h424 h244 hab

/-- **Beal ⟺ residual reduzido** (incondicional, sem pontes). -/
theorem beal_iff_residual_descida : BealConjecture ↔ ExclusaoResidualDescida :=
  beal_iff_residual442.trans residual442_iff_descida

/-- Forma dois a dois coprima do residual reduzido. -/
def ExclusaoResidualDescidaPairwise : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) → ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) → ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) →
    Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c → a ^ x + b ^ y ≠ c ^ z

theorem descida_iff_pairwise : ExclusaoResidualDescida ↔ ExclusaoResidualDescidaPairwise := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab _ _
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab heq
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab
      (coprime_ac_de_ab (by omega) (by omega) heq hab)
      (coprime_bc_de_ab (by omega) (by omega) heq hab) heq

/-- **Beal ⟺ nenhuma solução dois a dois coprima no residual reduzido.** -/
theorem beal_iff_residual_descida_pairwise : BealConjecture ↔ ExclusaoResidualDescidaPairwise :=
  beal_iff_residual_descida.trans descida_iff_pairwise

/-- Instâncias: `(4, 6, 4)`, `(8, 10, 4)`, `(6, 4, 4)`, `(10, 4, 8)`. -/
theorem exemplos_descida :
    BealFor 4 6 4 ∧ BealFor 8 10 4 ∧ BealFor 6 4 4 ∧ BealFor 10 4 8 :=
  ⟨beal_424 (dvd_refl 4) ⟨3, rfl⟩ (dvd_refl 4),
    beal_424 ⟨2, rfl⟩ ⟨5, rfl⟩ (dvd_refl 4),
    beal_244 ⟨3, rfl⟩ (dvd_refl 4) (dvd_refl 4),
    beal_244 ⟨5, rfl⟩ (dvd_refl 4) ⟨2, rfl⟩⟩

/-- Esses triplos **não** eram cobertos por nenhum caso anterior (mdc = 2 e fora de `(4,4,2)`). -/
theorem exemplos_descida_novos :
    (¬ 3 ∣ Nat.gcd 4 (Nat.gcd 6 4) ∧ ¬ 4 ∣ Nat.gcd 4 (Nat.gcd 6 4) ∧
      ¬ (4 ∣ 4 ∧ 4 ∣ 6 ∧ 2 ∣ 4)) ∧
    (¬ 3 ∣ Nat.gcd 8 (Nat.gcd 10 4) ∧ ¬ 4 ∣ Nat.gcd 8 (Nat.gcd 10 4) ∧
      ¬ (4 ∣ 8 ∧ 4 ∣ 10 ∧ 2 ∣ 4)) ∧
    (¬ 3 ∣ Nat.gcd 6 (Nat.gcd 4 4) ∧ ¬ 4 ∣ Nat.gcd 6 (Nat.gcd 4 4) ∧
      ¬ (4 ∣ 6 ∧ 4 ∣ 4 ∧ 2 ∣ 4)) ∧
    (¬ 3 ∣ Nat.gcd 10 (Nat.gcd 4 8) ∧ ¬ 4 ∣ Nat.gcd 10 (Nat.gcd 4 8) ∧
      ¬ (4 ∣ 10 ∧ 4 ∣ 4 ∧ 2 ∣ 8)) := by
  decide

end ATK.BealFermatDescent

#print axioms ATK.BealFermatDescent.sem_solucao_424
#print axioms ATK.BealFermatDescent.sem_solucao_244
#print axioms ATK.BealFermatDescent.beal_424
#print axioms ATK.BealFermatDescent.beal_244
#print axioms ATK.BealFermatDescent.residual442_iff_descida
#print axioms ATK.BealFermatDescent.beal_iff_residual_descida
#print axioms ATK.BealFermatDescent.descida_iff_pairwise
#print axioms ATK.BealFermatDescent.beal_iff_residual_descida_pairwise
#print axioms ATK.BealFermatDescent.exemplos_descida
#print axioms ATK.BealFermatDescent.exemplos_descida_novos
