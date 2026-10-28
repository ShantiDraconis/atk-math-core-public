import ATK.BealFermatDescent
import ATK.DarmonMerelSeis

/-!
# ATK — Beal na assinatura `(6k, 6l, 2m)`, incondicionalmente (redução do residual de O2)

`ATK.DarmonMerelSeis.dmSq_seis` prova `A⁶ + B⁶ ≠ C²` para `A, B > 0` coprimos (Euler, via FLT(3)
da Mathlib). Daí:

* `sem_solucao_662`: se `6 ∣ x`, `6 ∣ y` e `2 ∣ z`, `aˣ + bʸ = cᶻ` não tem solução com `a, b > 0`
  coprimos — escrevendo `aˣ = (aʳ)⁶`, `bʸ = (bˢ)⁶`, `cᶻ = (cᵗ)²`;
* `beal_662`: Beal vale para todo triplo de expoentes desse tipo (se `a, b` não são coprimos, um
  primo comum divide `c`);
* `beal_iff_residual_seis`: **`BealConjecture ↔ ExclusaoResidualSeis`**, sem pontes — o residual
  incondicional de `ATK.BealFermatDescent` perde a família `(6k, 6l, 2m)`.

Isso cobre triplos com `mdc(x, y, z) = 2` fora de todas as famílias já certificadas
(`3 ∣ mdc`, `4 ∣ mdc`, `(4,4,2)`, `(4,2,4)`, `(2,4,4)`): p.ex. `(6, 6, 4)`, `(6, 12, 10)`,
`(18, 6, 14)`. Nos triplos com expoentes em `3..200` (7.762.392), a cobertura incondicional passa de
762.844 (9,83%) para **799.326 (10,30%)**.

Status: sob a ponte B8 (Darmon–Merel) essa família já estava coberta; o que muda é que agora ela é
incondicional. **O2 continua aberta.**
-/

namespace ATK.BealSeisSeisDois

open ATK.Conditional.Beal ATK.BealPartial ATK.BealReduction ATK.BealFermatDescent
  ATK.DarmonMerelSeis

/-- **Sem solução coprima** quando `6 ∣ x`, `6 ∣ y`, `2 ∣ z` (via `dmSq_seis`). -/
theorem sem_solucao_662 {a b c x y z : ℕ} (hx : 6 ∣ x) (hy : 6 ∣ y) (hz : 2 ∣ z)
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) : a ^ x + b ^ y ≠ c ^ z := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := hz
  intro heq
  refine dmSq_seis (a ^ r) (b ^ s) (c ^ t) (pow_pos ha r) (pow_pos hb s)
    (Nat.Coprime.pow r s hab) ?_
  rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm r 6, mul_comm s 6, mul_comm t 2]
  exact heq

/-- **Incondicional**: Beal para todo triplo com `6 ∣ x`, `6 ∣ y`, `2 ∣ z` (`x, y > 0`). -/
theorem beal_662 {x y z : ℕ} (hx : 6 ∣ x) (hy : 6 ∣ y) (hz : 2 ∣ z) (hx0 : 0 < x)
    (hy0 : 0 < y) : BealFor x y z := by
  intro a b c ha hb _ heq
  by_cases hab : Nat.Coprime a b
  · exact absurd heq (sem_solucao_662 hx hy hz ha hb hab)
  · obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
    exact ⟨p, hp, hpa, hpb, primo_ab_divide_c hp hx0 hy0 heq hpa hpb⟩

/-- Residual incondicional após FLT(3), FLT(4), `(4,4,2)`, `(4,2,4)`, `(2,4,4)` e `(6,6,2)`. -/
def ExclusaoResidualSeis : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) → ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) → ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) →
    ¬ (6 ∣ x ∧ 6 ∣ y ∧ 2 ∣ z) →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

theorem descida_iff_seis : ExclusaoResidualDescida ↔ ExclusaoResidualSeis := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 _ hab
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 hab
    by_cases h662 : 6 ∣ x ∧ 6 ∣ y ∧ 2 ∣ z
    · exact sem_solucao_662 h662.1 h662.2.1 h662.2.2 ha hb hab
    · exact h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 h662 hab

/-- **Beal ⟺ residual reduzido** (incondicional, sem pontes). -/
theorem beal_iff_residual_seis : BealConjecture ↔ ExclusaoResidualSeis :=
  beal_iff_residual_descida.trans descida_iff_seis

/-- Instâncias: `(6, 6, 4)`, `(6, 12, 10)`, `(18, 6, 14)`. -/
theorem exemplos_662 : BealFor 6 6 4 ∧ BealFor 6 12 10 ∧ BealFor 18 6 14 :=
  ⟨beal_662 (dvd_refl 6) (dvd_refl 6) ⟨2, rfl⟩ (by norm_num) (by norm_num),
    beal_662 (dvd_refl 6) ⟨2, rfl⟩ ⟨5, rfl⟩ (by norm_num) (by norm_num),
    beal_662 ⟨3, rfl⟩ (dvd_refl 6) ⟨7, rfl⟩ (by norm_num) (by norm_num)⟩

/-- Esses triplos têm `mdc = 2` e estão fora de todas as famílias incondicionais anteriores. -/
theorem exemplos_662_novos :
    (¬ 3 ∣ Nat.gcd 6 (Nat.gcd 6 4) ∧ ¬ 4 ∣ Nat.gcd 6 (Nat.gcd 6 4) ∧
      ¬ (4 ∣ 6 ∧ 4 ∣ 6 ∧ 2 ∣ 4) ∧ ¬ (4 ∣ 6 ∧ 2 ∣ 6 ∧ 4 ∣ 4) ∧ ¬ (2 ∣ 6 ∧ 4 ∣ 6 ∧ 4 ∣ 4)) ∧
    (¬ 3 ∣ Nat.gcd 6 (Nat.gcd 12 10) ∧ ¬ 4 ∣ Nat.gcd 6 (Nat.gcd 12 10) ∧
      ¬ (4 ∣ 6 ∧ 4 ∣ 12 ∧ 2 ∣ 10) ∧ ¬ (4 ∣ 6 ∧ 2 ∣ 12 ∧ 4 ∣ 10) ∧
      ¬ (2 ∣ 6 ∧ 4 ∣ 12 ∧ 4 ∣ 10)) ∧
    (¬ 3 ∣ Nat.gcd 18 (Nat.gcd 6 14) ∧ ¬ 4 ∣ Nat.gcd 18 (Nat.gcd 6 14) ∧
      ¬ (4 ∣ 18 ∧ 4 ∣ 6 ∧ 2 ∣ 14) ∧ ¬ (4 ∣ 18 ∧ 2 ∣ 6 ∧ 4 ∣ 14) ∧
      ¬ (2 ∣ 18 ∧ 4 ∣ 6 ∧ 4 ∣ 14)) := by
  decide

end ATK.BealSeisSeisDois

#print axioms ATK.BealSeisSeisDois.sem_solucao_662
#print axioms ATK.BealSeisSeisDois.beal_662
#print axioms ATK.BealSeisSeisDois.descida_iff_seis
#print axioms ATK.BealSeisSeisDois.beal_iff_residual_seis
#print axioms ATK.BealSeisSeisDois.exemplos_662
#print axioms ATK.BealSeisSeisDois.exemplos_662_novos
