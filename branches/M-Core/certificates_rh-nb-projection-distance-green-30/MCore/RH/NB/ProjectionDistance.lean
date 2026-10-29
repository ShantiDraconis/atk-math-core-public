import Mathlib
import MCore.RH.NB.Distance

namespace MCore.RH.NB

/-- A coherent infinite generator family. Finite approximation spaces are obtained by
restricting this one family to the first `N` generators, so nesting is structural. -/
structure NestedApproximationSpaces (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  target : E
  generator : ℕ → E

namespace NestedApproximationSpaces

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restriction of the global generator family to the first `N` indices. -/
def gammaFamily (S : NestedApproximationSpaces E) (N : ℕ) : Fin N → E :=
  fun i => S.generator i.val

/-- Primary finite approximation space. This definition is independent of Gram
invertibility and remains meaningful for redundant generators. -/
def V (S : NestedApproximationSpaces E) (N : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (S.gammaFamily N))

/-- The finite approximation spaces are nested. -/
theorem V_mono (S : NestedApproximationSpaces E) : Monotone S.V := by
  intro a b hab
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨i, rfl⟩
  refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hab⟩, ?_⟩
  rfl

/-- Primary squared distance to the finite approximation space. No determinant or
matrix inverse occurs in this definition. -/
noncomputable def D (S : NestedApproximationSpaces E) (N : ℕ) : ℝ :=
  (Metric.infDist S.target (S.V N : Set E)) ^ 2

/-- Squared projection distance is nonnegative. -/
theorem D_nonneg (S : NestedApproximationSpaces E) (N : ℕ) : 0 ≤ S.D N := by
  exact sq_nonneg _

/-- Enlarging the approximation space cannot increase the primary distance. -/
theorem D_antitone (S : NestedApproximationSpaces E) : Antitone S.D := by
  intro a b hab
  have hV : (S.V a : Set E) ⊆ (S.V b : Set E) := S.V_mono hab
  have hne : (S.V a : Set E).Nonempty := ⟨0, (S.V a).zero_mem⟩
  have hdist : Metric.infDist S.target (S.V b : Set E) ≤
      Metric.infDist S.target (S.V a : Set E) :=
    Metric.infDist_le_infDist_of_subset hV hne
  have h0a : 0 ≤ Metric.infDist S.target (S.V a : Set E) := Metric.infDist_nonneg
  have h0b : 0 ≤ Metric.infDist S.target (S.V b : Set E) := Metric.infDist_nonneg
  dsimp [D]
  nlinarith

/-- Successor form used by the audit DAG. -/
theorem D_succ_le (S : NestedApproximationSpaces E) (N : ℕ) :
    S.D (N + 1) ≤ S.D N :=
  S.D_antitone (Nat.le_succ N)

end NestedApproximationSpaces

/-- Generic diagonal closure principle. For a nonnegative antitone sequence, convergence
to zero along any index sequence already forces full convergence; the explicit cofinality
hypothesis records the intended approximation-diagonal semantics and prevents a later
specialization from silently using a bounded index schedule. -/
theorem tendsto_zero_of_antitone_subsequence
    {D : ℕ → ℝ} (h0 : ∀ n, 0 ≤ D n) (hAnti : Antitone D)
    (Nk : ℕ → ℕ) (_hCof : Filter.Tendsto Nk Filter.atTop Filter.atTop)
    (hSub : Filter.Tendsto (D ∘ Nk) Filter.atTop (nhds 0)) :
    Filter.Tendsto D Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hball : Metric.ball (0 : ℝ) ε ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  have hEv : ∀ᶠ k in Filter.atTop, D (Nk k) ∈ Metric.ball (0 : ℝ) ε :=
    hSub.eventually hball
  rw [Filter.eventually_atTop] at hEv
  obtain ⟨K, hK⟩ := hEv
  refine ⟨Nk K, ?_⟩
  intro n hn
  have hsample : D (Nk K) ∈ Metric.ball (0 : ℝ) ε := hK K le_rfl
  have hsample_lt : D (Nk K) < ε := by
    rw [Metric.mem_ball, Real.dist_eq] at hsample
    simpa [abs_of_nonneg (h0 (Nk K))] using hsample
  have hle : D n ≤ D (Nk K) := hAnti hn
  have hnlt : D n < ε := lt_of_le_of_lt hle hsample_lt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h0 n)]
  exact hnlt

/-- Specialization of the generic diagonal closure principle to direct approximation
spaces. This contains no RH criterion and no Gram inverse. -/
theorem projectionDistance_tendsto_zero_of_subsequence
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : NestedApproximationSpaces E) (Nk : ℕ → ℕ)
    (hCof : Filter.Tendsto Nk Filter.atTop Filter.atTop)
    (hSub : Filter.Tendsto (S.D ∘ Nk) Filter.atTop (nhds 0)) :
    Filter.Tendsto S.D Filter.atTop (nhds 0) :=
  tendsto_zero_of_antitone_subsequence S.D_nonneg S.D_antitone Nk hCof hSub

end MCore.RH.NB
