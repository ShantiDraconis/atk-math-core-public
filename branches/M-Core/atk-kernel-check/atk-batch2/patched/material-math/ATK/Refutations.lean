import Mathlib

/-!
# Refutações (auditoria ATK, 12/10/2026)

Dois enunciados do pacote ATK_MATERIAL_MATH_20261012, **como escritos**, são falsos.
Aqui o kernel verifica contraexemplos explícitos. As versões corrigidas estão em
`ATK/ConcreteAnalytic.lean` e `ATK/ConcreteArithmetic.lean` desta pasta `patched/`.
-/

namespace ATK.Refutations

/-- `common_prime_divides_third` como escrito (sem `0 < x`, `0 < y`) é falso:
`a = b = 2, x = 0, y = 1, c = 3, z = 1`: `2^0 + 2^1 = 3^1`, `2 ∣ 2`, `2 ∣ 2`, mas `¬ 2 ∣ 3`. -/
theorem common_prime_divides_third_as_written_false :
    ¬ (∀ {a b c x y z : ℕ}, 0 < z → a ^ x + b ^ y = c ^ z →
        ∀ {p : ℕ}, Nat.Prime p → p ∣ a → p ∣ b → p ∣ c) := by
  intro h
  have h3 : (2 : ℕ) ∣ 3 :=
    @h 2 2 3 0 1 1 (by norm_num) (by norm_num) 2 Nat.prime_two (dvd_refl 2) (dvd_refl 2)
  exact absurd h3 (by norm_num)

/-- `infimum_antitone` como escrito (limitação inferior exigida de `cost '' A`, o conjunto
MENOR) é falso: `cost = id`, `A = {-1}`, `B = univ`; `sInf (univ : Set ℝ) = 0` pela convenção
de Mathlib para conjuntos não limitados, `sInf {-1} = -1`, e `0 ≤ -1` é falso. -/
theorem infimum_antitone_as_written_false :
    ¬ (∀ (cost : ℝ → ℝ) (A B : Set ℝ), A ⊆ B → BddBelow (cost '' A) →
        (cost '' A).Nonempty → sInf (cost '' B) ≤ sInf (cost '' A)) := by
  intro h
  have h0 := h id {-1} Set.univ (Set.subset_univ _) (by simp) (by simp)
  simp only [Set.image_id, Real.sInf_univ, csInf_singleton] at h0
  norm_num at h0

end ATK.Refutations
