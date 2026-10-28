/-
ATK — As partes refutáveis em volta de Beal, como contraexemplos certificados.

Beal (`ATK.Conditional.Beal.BealConjecture`) exige **duas** hipóteses: expoentes `> 2` e a
conclusão "fator primo comum".  Cada uma delas é necessária, e algumas generalizações
naturais de Fermat são falsas.  Aqui o kernel verifica, por cálculo exato:

* **Fermat–Catalan**: as dez soluções coprimas conhecidas de `aˣ + bʸ = cᶻ` com
  `1/x + 1/y + 1/z < 1` (todas com um expoente 2); logo **Beal com expoentes `≥ 2` é falso**
  (`bealExpoenteDois_falso`, testemunha `2⁵ + 7² = 3⁴`);
* **o fator comum é necessário**: "nenhuma solução com x, y, z > 2" é falso
  (`2³ + 2³ = 2⁴`, `3³ + 6³ = 3⁵`, `7⁶ + 7⁷ = 98³` e a família infinita `2ⁿ + 2ⁿ = 2ⁿ⁺¹`);
  todos esses exemplos **respeitam** Beal (têm primo comum);
* **conjectura de Euler das somas de potências** (generalização de Fermat) é falsa:
  `27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵` (Lander–Parkin 1966) e
  `95800⁴ + 217519⁴ + 414560⁴ = 422481⁴` (Frye 1988).

Nada aqui refuta Beal: nenhum desses exemplos tem os três expoentes > 2 e bases coprimas.
-/
import ATK.Conditional.Beal
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime

namespace ATK.RefutacoesBeal

open ATK.Conditional.Beal

/-! ### As dez soluções de Fermat–Catalan -/

theorem fc1 : 1 ^ 7 + 2 ^ 3 = 3 ^ 2 := by norm_num
theorem fc2 : 2 ^ 5 + 7 ^ 2 = 3 ^ 4 := by norm_num
theorem fc3 : 7 ^ 3 + 13 ^ 2 = 2 ^ 9 := by norm_num
theorem fc4 : 2 ^ 7 + 17 ^ 3 = 71 ^ 2 := by norm_num
theorem fc5 : 3 ^ 5 + 11 ^ 4 = 122 ^ 2 := by norm_num
theorem fc6 : 33 ^ 8 + 1549034 ^ 2 = 15613 ^ 3 := by norm_num
theorem fc7 : 1414 ^ 3 + 2213459 ^ 2 = 65 ^ 7 := by norm_num
theorem fc8 : 9262 ^ 3 + 15312283 ^ 2 = 113 ^ 7 := by norm_num
theorem fc9 : 17 ^ 7 + 76271 ^ 3 = 21063928 ^ 2 := by norm_num
theorem fc10 : 43 ^ 8 + 96222 ^ 3 = 30042907 ^ 2 := by norm_num

/-- As bases são coprimas duas a duas (basta `mdc(a, b) = 1`, com a equação). -/
theorem fc_coprimos :
    Nat.Coprime 1 2 ∧ Nat.Coprime 2 7 ∧ Nat.Coprime 7 13 ∧ Nat.Coprime 2 17 ∧
      Nat.Coprime 3 11 ∧ Nat.Coprime 33 1549034 ∧ Nat.Coprime 1414 2213459 ∧
      Nat.Coprime 9262 15312283 ∧ Nat.Coprime 17 76271 ∧ Nat.Coprime 43 96222 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- As dez assinaturas `(x, y, z)`, na ordem de `fc1` … `fc10`. -/
def assinaturasFC : List (ℕ × ℕ × ℕ) :=
  [(7, 3, 2), (5, 2, 4), (3, 2, 9), (7, 3, 2), (5, 4, 2), (8, 2, 3), (3, 2, 7), (3, 2, 7),
    (7, 3, 2), (8, 3, 2)]

/-- Todas são hiperbólicas: `xy + yz + zx < xyz`, isto é, `1/x + 1/y + 1/z < 1`. -/
theorem fc_hiperbolicas :
    ∀ s ∈ assinaturasFC, s.1 * s.2.1 + s.2.1 * s.2.2 + s.2.2 * s.1 < s.1 * s.2.1 * s.2.2 := by
  decide

/-! ### Beal com expoentes ≥ 2 é falso -/

/-- A variante com `x, y, z ≥ 2`. -/
def BealExpoenteDois : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 ≤ x → 2 ≤ y → 2 ≤ z →
    a ^ x + b ^ y = c ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

/-- **Refutada** por `2⁵ + 7² = 3⁴`. -/
theorem bealExpoenteDois_falso : ¬ BealExpoenteDois := by
  intro h
  obtain ⟨p, hp, ha, hb, -⟩ :=
    h 2 7 3 5 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) fc2
  have h1 : p ∣ Nat.gcd 2 7 := Nat.dvd_gcd ha hb
  have h2 : Nat.gcd 2 7 = 1 := by norm_num
  rw [h2] at h1
  exact hp.ne_one (Nat.dvd_one.mp h1)

/-- Cada solução de Fermat–Catalan tem um expoente `≤ 2`: nenhuma está no domínio de
`BealConjecture` (que exige os três expoentes `> 2`). -/
theorem fc_fora_de_beal : ∀ s ∈ assinaturasFC, ¬ (2 < s.1 ∧ 2 < s.2.1 ∧ 2 < s.2.2) := by
  decide

/-! ### O fator comum é necessário -/

/-- "Não há solução nenhuma com x, y, z > 2" (Beal sem a conclusão do fator comum). -/
def SemSolucoes : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z → a ^ x + b ^ y ≠ c ^ z

theorem exemplos_fator_comum : 2 ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ 3 ^ 3 + 6 ^ 3 = 3 ^ 5 ∧
    7 ^ 6 + 7 ^ 7 = 98 ^ 3 := by
  norm_num

/-- **Refutada** por `2³ + 2³ = 2⁴`. -/
theorem semSolucoes_falso : ¬ SemSolucoes := fun h =>
  h 2 2 2 3 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Família infinita: `2ⁿ + 2ⁿ = 2ⁿ⁺¹`, com expoentes `> 2` para `n ≥ 3`. -/
theorem familia_infinita (n : ℕ) : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
  rw [pow_succ]; ring

/-- Esses exemplos **respeitam** Beal: há primo comum. -/
theorem exemplos_respeitam_beal :
    (Nat.Prime 2 ∧ 2 ∣ 2 ∧ 2 ∣ 2 ∧ 2 ∣ 2) ∧ (Nat.Prime 3 ∧ 3 ∣ 3 ∧ 3 ∣ 6 ∧ 3 ∣ 3) ∧
      (Nat.Prime 7 ∧ 7 ∣ 7 ∧ 7 ∣ 7 ∧ 7 ∣ 98) := by
  norm_num

/-! ### Conjectura de Euler das somas de potências -/

/-- Euler (k = 5): quatro quintas potências positivas nunca somam uma quinta potência. -/
def Euler5 : Prop :=
  ∀ a b c d e : ℕ, 0 < a → 0 < b → 0 < c → 0 < d → a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 ≠ e ^ 5

/-- Euler (k = 4): três quartas potências positivas nunca somam uma quarta potência. -/
def Euler4 : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → a ^ 4 + b ^ 4 + c ^ 4 ≠ d ^ 4

theorem lander_parkin : 27 ^ 5 + 84 ^ 5 + 110 ^ 5 + 133 ^ 5 = 144 ^ 5 := by norm_num

theorem frye : 95800 ^ 4 + 217519 ^ 4 + 414560 ^ 4 = 422481 ^ 4 := by norm_num

theorem euler5_falso : ¬ Euler5 := fun h =>
  h 27 84 110 133 144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) lander_parkin

theorem euler4_falso : ¬ Euler4 := fun h =>
  h 95800 217519 414560 422481 (by norm_num) (by norm_num) (by norm_num) frye

end ATK.RefutacoesBeal

#print axioms ATK.RefutacoesBeal.fc1
#print axioms ATK.RefutacoesBeal.fc2
#print axioms ATK.RefutacoesBeal.fc3
#print axioms ATK.RefutacoesBeal.fc4
#print axioms ATK.RefutacoesBeal.fc5
#print axioms ATK.RefutacoesBeal.fc6
#print axioms ATK.RefutacoesBeal.fc7
#print axioms ATK.RefutacoesBeal.fc8
#print axioms ATK.RefutacoesBeal.fc9
#print axioms ATK.RefutacoesBeal.fc10
#print axioms ATK.RefutacoesBeal.fc_coprimos
#print axioms ATK.RefutacoesBeal.fc_hiperbolicas
#print axioms ATK.RefutacoesBeal.bealExpoenteDois_falso
#print axioms ATK.RefutacoesBeal.fc_fora_de_beal
#print axioms ATK.RefutacoesBeal.exemplos_fator_comum
#print axioms ATK.RefutacoesBeal.semSolucoes_falso
#print axioms ATK.RefutacoesBeal.familia_infinita
#print axioms ATK.RefutacoesBeal.exemplos_respeitam_beal
#print axioms ATK.RefutacoesBeal.lander_parkin
#print axioms ATK.RefutacoesBeal.frye
#print axioms ATK.RefutacoesBeal.euler5_falso
#print axioms ATK.RefutacoesBeal.euler4_falso
