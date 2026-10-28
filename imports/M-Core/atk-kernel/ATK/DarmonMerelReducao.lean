import ATK.BealDarmonMerel
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# ATK — Ponte B8 (Darmon–Merel): redução a expoentes primos

A ponte `ATK.BealDarmonMerel.DarmonMerel` (Darmon–Merel 1997, publicada, não formalizada) pede

* `Aⁿ + Bⁿ ≠ C²` para todo `n ≥ 4` (`A, B > 0` coprimos), e
* `Aⁿ + Bⁿ ≠ C³` para todo `n ≥ 3`.

Como `Aⁿ = (A^{n/d})^d` para `d ∣ n`, cada expoente herda o resultado de qualquer divisor. Este
arquivo prova, só com a Mathlib:

* `dmSq_four`: `n = 4` no caso `C²` (Fermat, `not_fermat_42` da Mathlib);
* `dmCube_three`: `n = 3` no caso `C³` (Euler, `fermatLastTheoremThree` da Mathlib);
* `divisor_sq` / `divisor_cube`: todo `n ≥ 4` tem um divisor em `{4, 6, 9}` ou primo `≥ 5`; todo
  `n ≥ 3` tem um divisor em `{3, 4}` ou primo `≥ 5`;
* `darmonMerel_iff`: **a ponte B8 equivale a** `C²` para `n ∈ {6, 9}` e `n` primo `≥ 5`, mais `C³`
  para `n = 4` e `n` primo `≥ 5`. O resto da ponte (todos os compostos e os casos `4 ∣ n` em `C²`,
  `3 ∣ n` em `C³`) está provado.

B8 continua `PUBLICADA_NAO_FORMALIZADA`: os casos primos são o conteúdo de Darmon–Merel
(modularidade), ausente da Mathlib.
-/

namespace ATK.DarmonMerelReducao

open ATK.BealDarmonMerel

/-- `Aⁿ + Bⁿ ≠ C²` para `A, B > 0` coprimos (expoente `n` fixo). -/
def DMSq (n : ℕ) : Prop :=
  ∀ A B C : ℕ, 0 < A → 0 < B → Nat.Coprime A B → A ^ n + B ^ n ≠ C ^ 2

/-- `Aⁿ + Bⁿ ≠ C³` para `A, B > 0` coprimos (expoente `n` fixo). -/
def DMCube (n : ℕ) : Prop :=
  ∀ A B C : ℕ, 0 < A → 0 < B → Nat.Coprime A B → A ^ n + B ^ n ≠ C ^ 3

theorem dmSq_of_dvd {d n : ℕ} (hd : d ∣ n) (h : DMSq d) : DMSq n := by
  obtain ⟨k, rfl⟩ := hd
  intro A B C hA hB hAB heq
  refine h (A ^ k) (B ^ k) C (pow_pos hA k) (pow_pos hB k) (Nat.Coprime.pow k k hAB) ?_
  rw [← pow_mul, ← pow_mul, mul_comm k d]
  exact heq

theorem dmCube_of_dvd {d n : ℕ} (hd : d ∣ n) (h : DMCube d) : DMCube n := by
  obtain ⟨k, rfl⟩ := hd
  intro A B C hA hB hAB heq
  refine h (A ^ k) (B ^ k) C (pow_pos hA k) (pow_pos hB k) (Nat.Coprime.pow k k hAB) ?_
  rw [← pow_mul, ← pow_mul, mul_comm k d]
  exact heq

/-- `n = 4`, `C²`: Fermat (`not_fermat_42` da Mathlib). -/
theorem dmSq_four : DMSq 4 := by
  intro A B C hA hB _ heq
  have h := not_fermat_42 (a := (A : ℤ)) (b := (B : ℤ)) (c := (C : ℤ)) (by exact_mod_cast hA.ne')
    (by exact_mod_cast hB.ne')
  exact h (by exact_mod_cast heq)

/-- `n = 3`, `C³`: Euler (`fermatLastTheoremThree` da Mathlib). -/
theorem dmCube_three : DMCube 3 := by
  intro A B C hA hB _ heq
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · have : 0 < A ^ 3 + B ^ 3 := by positivity
    rw [heq] at this
    norm_num at this
  · exact fermatLastTheoremThree A B C hA.ne' hB.ne' hC.ne' heq

/-- Todo `n ≥ 4` tem um divisor em `{4, 6, 9}` ou primo `≥ 5`. -/
theorem divisor_sq {n : ℕ} (hn : 4 ≤ n) :
    4 ∣ n ∨ 6 ∣ n ∨ 9 ∣ n ∨ ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ n := by
  have hr := Nat.minFac_prime (show n ≠ 1 by omega)
  have hrd := Nat.minFac_dvd n
  have hr2 := hr.two_le
  by_cases h5 : 5 ≤ n.minFac
  · exact Or.inr (Or.inr (Or.inr ⟨_, hr, h5, hrd⟩))
  have h23 : n.minFac = 2 ∨ n.minFac = 3 := by
    have : n.minFac ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hr)
    omega
  obtain ⟨k, hk⟩ := hrd
  rcases h23 with h2 | h3
  · rw [h2] at hk
    by_cases hk2 : 2 ∣ k
    · obtain ⟨j, rfl⟩ := hk2; exact Or.inl ⟨j, by omega⟩
    by_cases hk3 : 3 ∣ k
    · obtain ⟨j, rfl⟩ := hk3; exact Or.inr (Or.inl ⟨j, by omega⟩)
    have hk1 : k ≠ 1 := by omega
    have hq := Nat.minFac_prime hk1
    have hq2 : k.minFac ≠ 2 := fun h => hk2 (h ▸ Nat.minFac_dvd k)
    have hq3 : k.minFac ≠ 3 := fun h => hk3 (h ▸ Nat.minFac_dvd k)
    have hq4 : k.minFac ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hq)
    refine Or.inr (Or.inr (Or.inr ⟨k.minFac, hq, by have := hq.two_le; omega, ?_⟩))
    exact (Nat.minFac_dvd k).trans ⟨2, by rw [hk]; ring⟩
  · rw [h3] at hk
    have hn2 : ¬ 2 ∣ n := fun h => by
      have := Nat.minFac_le_of_dvd (le_refl 2) h; omega
    by_cases hk3 : 3 ∣ k
    · obtain ⟨j, rfl⟩ := hk3; exact Or.inr (Or.inr (Or.inl ⟨j, by omega⟩))
    have hk2 : ¬ 2 ∣ k := fun h => hn2 (h.trans ⟨3, by rw [hk]; ring⟩)
    have hk1 : k ≠ 1 := by omega
    have hq := Nat.minFac_prime hk1
    have hq2 : k.minFac ≠ 2 := fun h => hk2 (h ▸ Nat.minFac_dvd k)
    have hq3 : k.minFac ≠ 3 := fun h => hk3 (h ▸ Nat.minFac_dvd k)
    have hq4 : k.minFac ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hq)
    refine Or.inr (Or.inr (Or.inr ⟨k.minFac, hq, by have := hq.two_le; omega, ?_⟩))
    exact (Nat.minFac_dvd k).trans ⟨3, by rw [hk]; ring⟩

/-- Todo `n ≥ 3` tem um divisor em `{3, 4}` ou primo `≥ 5`. -/
theorem divisor_cube {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ n ∨ 4 ∣ n ∨ ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ n := by
  have hr := Nat.minFac_prime (show n ≠ 1 by omega)
  have hrd := Nat.minFac_dvd n
  have hr2 := hr.two_le
  by_cases h5 : 5 ≤ n.minFac
  · exact Or.inr (Or.inr ⟨_, hr, h5, hrd⟩)
  have h23 : n.minFac = 2 ∨ n.minFac = 3 := by
    have : n.minFac ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hr)
    omega
  rcases h23 with h2 | h3
  · obtain ⟨k, hk⟩ := hrd
    rw [h2] at hk
    by_cases hk2 : 2 ∣ k
    · obtain ⟨j, rfl⟩ := hk2; exact Or.inr (Or.inl ⟨j, by omega⟩)
    by_cases hk3 : 3 ∣ k
    · exact Or.inl (hk3.trans ⟨2, by rw [hk]; ring⟩)
    have hk1 : k ≠ 1 := by omega
    have hq := Nat.minFac_prime hk1
    have hq2 : k.minFac ≠ 2 := fun h => hk2 (h ▸ Nat.minFac_dvd k)
    have hq3 : k.minFac ≠ 3 := fun h => hk3 (h ▸ Nat.minFac_dvd k)
    have hq4 : k.minFac ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hq)
    refine Or.inr (Or.inr ⟨k.minFac, hq, by have := hq.two_le; omega, ?_⟩)
    exact (Nat.minFac_dvd k).trans ⟨2, by rw [hk]; ring⟩
  · exact Or.inl (h3 ▸ hrd)

/-- **Redução da ponte B8, caso `C²`**: basta `n ∈ {6, 9}` e `n` primo `≥ 5`. -/
theorem darmonMerelSq_iff :
    DarmonMerelSq ↔ DMSq 6 ∧ DMSq 9 ∧ ∀ p, p.Prime → 5 ≤ p → DMSq p := by
  constructor
  · intro h
    refine ⟨fun A B C => h 6 A B C (by norm_num), fun A B C => h 9 A B C (by norm_num),
      fun p _ hp A B C => h p A B C (by omega)⟩
  · rintro ⟨h6, h9, hp⟩ n A B C hn
    rcases divisor_sq hn with h4 | h6' | h9' | ⟨p, hpp, hp5, hpn⟩
    · exact dmSq_of_dvd h4 dmSq_four A B C
    · exact dmSq_of_dvd h6' h6 A B C
    · exact dmSq_of_dvd h9' h9 A B C
    · exact dmSq_of_dvd hpn (hp p hpp hp5) A B C

/-- **Redução da ponte B8, caso `C³`**: basta `n = 4` e `n` primo `≥ 5`. -/
theorem darmonMerelCube_iff :
    DarmonMerelCube ↔ DMCube 4 ∧ ∀ p, p.Prime → 5 ≤ p → DMCube p := by
  constructor
  · intro h
    exact ⟨fun A B C => h 4 A B C (by norm_num), fun p _ hp A B C => h p A B C (by omega)⟩
  · rintro ⟨h4, hp⟩ n A B C hn
    rcases divisor_cube hn with h3 | h4' | ⟨p, hpp, hp5, hpn⟩
    · exact dmCube_of_dvd h3 dmCube_three A B C
    · exact dmCube_of_dvd h4' h4 A B C
    · exact dmCube_of_dvd hpn (hp p hpp hp5) A B C

/-- **A ponte B8 reduzida**: `DarmonMerel` equivale aos casos `C²` com `n ∈ {6, 9}` ou primo `≥ 5`
e `C³` com `n = 4` ou primo `≥ 5`. -/
theorem darmonMerel_iff :
    DarmonMerel ↔ (DMSq 6 ∧ DMSq 9 ∧ ∀ p, p.Prime → 5 ≤ p → DMSq p) ∧
      (DMCube 4 ∧ ∀ p, p.Prime → 5 ≤ p → DMCube p) :=
  and_congr darmonMerelSq_iff darmonMerelCube_iff

end ATK.DarmonMerelReducao

#print axioms ATK.DarmonMerelReducao.dmSq_of_dvd
#print axioms ATK.DarmonMerelReducao.dmCube_of_dvd
#print axioms ATK.DarmonMerelReducao.dmSq_four
#print axioms ATK.DarmonMerelReducao.dmCube_three
#print axioms ATK.DarmonMerelReducao.divisor_sq
#print axioms ATK.DarmonMerelReducao.divisor_cube
#print axioms ATK.DarmonMerelReducao.darmonMerelSq_iff
#print axioms ATK.DarmonMerelReducao.darmonMerelCube_iff
#print axioms ATK.DarmonMerelReducao.darmonMerel_iff
