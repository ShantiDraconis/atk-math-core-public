import Mathlib

/-! ATK material laws: actual logical and algebraic facts; no terminal conjecture claimed. -/
namespace ATK.FinalRoot

/-- A nonnegative Schur decrement gives monotonicity. -/
theorem schur_decrease (d u s : ℝ) (hs : 0 < s) :
    d - u ^ 2 / s ≤ d := by
  have h : 0 ≤ u ^ 2 / s := div_nonneg (sq_nonneg u) hs.le
  linarith

/-- Positivity of a finite torsion group, conditional only on its group structure. -/
theorem torsion_card_positive (G : Type*) [Group G] [Fintype G] :
    0 < Fintype.card G := by
  exact Fintype.card_pos_iff.mpr ⟨1⟩

/-- Strictly decreasing a natural-valued measure on every state is impossible. -/
theorem no_global_descent (S : Type*) (m : S → ℕ)
    (step : S → S) (h : ∀ s, m (step s) < m s) : IsEmpty S := by
  classical
  constructor
  intro s
  let P : ℕ → Prop := fun n => ∃ t : S, m t = n
  have hex : ∃ n, P n := ⟨m s, s, rfl⟩
  let n := Nat.find hex
  obtain ⟨t, ht⟩ := Nat.find_spec hex
  -- PATCH (ATK-kernel): `ht ▸ h t` não elabora no Lean 4.34.1; reescrita explícita.
  have hlt : m (step t) < m t := h t
  rw [ht] at hlt
  exact (Nat.find_min hex hlt) ⟨step t, rfl⟩

/-- Material production and a verified implication close an endpoint. -/
theorem terminal_from_independent_producer {M C : Prop}
    (material : M) (bridge : M → C) : C := bridge material

#print axioms ATK.FinalRoot.schur_decrease
#print axioms ATK.FinalRoot.torsion_card_positive
#print axioms ATK.FinalRoot.no_global_descent
#print axioms ATK.FinalRoot.terminal_from_independent_producer
end ATK.FinalRoot
