import MCore.YangMills.A1.RegulatedConstruction
import MCore.PhysicalGapScaling

namespace MCore.YangMills.A1

/-- Abstract two-parameter positivity system used only for adversarial tests. -/
structure TwoParameterPositiveSystem where
  value : ℝ → ℕ → ℝ

/-- Explicit adversarial family: every positive cutoff/finite volume value is
positive, but no positive lower bound is uniform in cutoff and volume. -/
theorem pointwise_cutoff_volume_positive_not_uniform :
    ∃ S : TwoParameterPositiveSystem,
      (∀ a : ℝ, ∀ L : ℕ, 0 < a → 0 < S.value a L) ∧
      ¬ ∃ c : ℝ, 0 < c ∧
        ∀ a : ℝ, ∀ L : ℕ, 0 < a → a < 1 → c ≤ S.value a L := by
  refine ⟨⟨fun a L => a / (L + 1 : ℝ)⟩, ?_, ?_⟩
  · intro a L ha
    positivity
  · rintro ⟨c, hc, hbound⟩
    let a : ℝ := min (1 / 2) (c / 2)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have ha1 : a < 1 := by
      dsimp [a]
      exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hac : a < c := by
      dsimp [a]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hc)
    have h := hbound a 0 ha ha1
    norm_num at h
    exact (not_lt_of_ge h) hac

/-- Existing physical-cutoff firewall remains reusable and is not reproved as
scientific YM content. -/
theorem positive_cutoff_gap_firewall :
    ∃ gamma : ℝ → ℝ,
      (∀ a : ℝ, 0 < a → 0 < gamma a) ∧
      ¬ ∃ m0 : ℝ, 0 < m0 ∧
        ∀ a : ℝ, 0 < a → a < 1 → m0 ≤ gamma a / a :=
  positive_cutoff_gap_not_physical_uniform

/-- Existing finite-volume firewall remains reusable. -/
theorem finite_volume_gap_firewall :
    ∃ gamma : ℕ → ℝ,
      (∀ L, 0 < gamma L) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ L, c ≤ gamma L :=
  finite_volume_gap_not_uniform

end MCore.YangMills.A1
