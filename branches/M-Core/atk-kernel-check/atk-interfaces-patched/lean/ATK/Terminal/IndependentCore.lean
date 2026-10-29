import Mathlib

/-! Independent, reusable deductions. None proves an open conjecture. -/
namespace ATK.Terminal

/-- A nonnegative antitone real sequence converges to its infimum. -/
theorem nonnegative_antitone_has_limit (D : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ D n) (hmono : Antitone D) :
    ∃ l : ℝ, 0 ≤ l ∧ Filter.Tendsto D Filter.atTop (nhds l) := by
  have hb : BddBelow (Set.range D) := ⟨0, by rintro x ⟨n, rfl⟩; exact h0 n⟩
  refine ⟨sInf (Set.range D), ?_, ?_⟩
  · exact le_csInf (Set.range_nonempty D) (by rintro x ⟨n, rfl⟩; exact h0 n)
  · exact tendsto_atTop_ciInf hmono hb

/-- Strict descent on naturals excludes any inhabitant. -/
theorem no_inhabitant_of_strict_descent (S : Type*) (m : S → ℕ)
    (step : S → S) (decreases : ∀ s, m (step s) < m s) : IsEmpty S := by
  classical
  constructor
  intro s
  let n := Nat.find (show ∃ n : ℕ, ∃ t : S, m t = n from ⟨m s, s, rfl⟩)
  obtain ⟨t, ht⟩ := Nat.find_spec (show ∃ n : ℕ, ∃ t : S, m t = n from ⟨m s, s, rfl⟩)
  have hs : ∃ t' : S, m t' = m (step t) := ⟨step t, rfl⟩
  -- PATCH (ATK-kernel): `ht ▸ decreases t` não elabora no Lean 4.34.1; reescrita explícita.
  have hlt : m (step t) < m t := decreases t
  rw [ht] at hlt
  exact (Nat.find_min (show ∃ n : ℕ, ∃ t : S, m t = n from ⟨m s, s, rfl⟩) hlt) hs

/-- The identity witnesses that a finite group has positive cardinality. -/
theorem finite_group_nonempty (G : Type*) [Group G] [Fintype G] :
    0 < Fintype.card G := by
  exact Fintype.card_pos_iff.mpr ⟨1⟩

/-- A true material lemma and a proved bridge produce the terminal conclusion. -/
theorem independent_terminal {Material Terminal : Prop}
    (material_proof : Material) (bridge_proof : Material → Terminal) : Terminal :=
  bridge_proof material_proof

end ATK.Terminal
