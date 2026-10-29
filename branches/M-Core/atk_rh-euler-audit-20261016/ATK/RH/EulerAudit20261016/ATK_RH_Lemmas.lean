import Mathlib

/-!
# ATK — Tail and error lemmas

The elementary statements below are unconditional. The actual
Nyman–Beurling density obligation is NOT asserted as a theorem.
No `sorry`, `admit`, or new axioms are introduced.

This file has not been kernel-checked in this environment.
-/

namespace ATK

section Tail

/-- An observable projection and its residual tail. -/
def tail (P : ℝ → ℝ) (x : ℝ) : ℝ := x - P x

theorem projection_add_tail (P : ℝ → ℝ) (x : ℝ) :
    P x + tail P x = x := by
  unfold tail
  ring

theorem exact_lt_iff (P : ℝ → ℝ) (a b : ℝ) :
    a < b ↔ P a - P b < tail P b - tail P a := by
  unfold tail
  constructor <;> intro h <;> linarith

theorem equal_projection_comparison (P : ℝ → ℝ) (a b : ℝ)
    (h : P a = P b) :
    a < b ↔ tail P a < tail P b := by
  rw [exact_lt_iff]
  rw [h]
  simp only [sub_self, zero_lt_sub_iff]

end Tail

section Error

/-- Squared error in a real inner product space. -/
def squaredError {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (target candidate : H) : ℝ := ‖target - candidate‖ ^ 2

theorem squaredError_nonneg {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (target candidate : H) :
    0 ≤ squaredError target candidate := by
  unfold squaredError
  positivity

theorem squaredError_self {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (target : H) : squaredError target target = 0 := by
  simp [squaredError]

/-- Algebraic expansion of the finite-dimensional Gram objective. -/
theorem quadratic_error_complete_square
    (G b c : ℝ) (hG : G ≠ 0) :
    1 - 2 * c * b + G * c ^ 2 =
      1 - b ^ 2 / G + G * (c - b / G) ^ 2 := by
  field_simp
  ring

/-- Exact one-dimensional minimization when the Gram entry is positive. -/
theorem quadratic_error_lower_bound
    (G b c : ℝ) (hG : 0 < G) :
    1 - b ^ 2 / G ≤ 1 - 2 * c * b + G * c ^ 2 := by
  rw [quadratic_error_complete_square G b c (ne_of_gt hG)]
  have hs : 0 ≤ G * (c - b / G) ^ 2 :=
    mul_nonneg (le_of_lt hG) (sq_nonneg _)
  linarith

end Error

section Defect

/-- Improvement between consecutive defect values. -/
def improvement (D : ℕ → ℝ) (n : ℕ) : ℝ := D n - D (n + 1)

theorem improvement_nonneg (D : ℕ → ℝ)
    (hmono : ∀ n, D (n + 1) ≤ D n) (n : ℕ) :
    0 ≤ improvement D n := by
  unfold improvement
  linarith [hmono n]

/-- Exact telescoping identity: finite gains plus the residual. -/
theorem telescoping_improvements (D : ℕ → ℝ) (N M : ℕ)
    (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ico N M, improvement D n) = D N - D M := by
  simp only [improvement]
  exact Finset.sum_Ico_sub D hNM

/-- A gain estimate produces a one-step contraction. -/
theorem gain_implies_contraction (D : ℕ → ℝ) (n : ℕ)
    (alpha : ℝ)
    (hgain : alpha * D n ≤ improvement D n) :
    D (n + 1) ≤ (1 - alpha) * D n := by
  unfold improvement at hgain
  nlinarith

/-- If every tolerance is eventually beaten, the residual is zero
    whenever a nonnegative real limit is known to exist. -/
theorem zero_of_arbitrarily_small
    (d : ℝ) (hd : 0 ≤ d)
    (hsmall : ∀ ε : ℝ, 0 < ε → d < ε) : d = 0 := by
  by_contra hne
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hne)
  exact (lt_irrefl d) (hsmall d hdpos)

/-- Finite improvement alone does not force a zero limit. -/
theorem constant_positive_defect_example :
    (∀ n : ℕ, (1 / 4 : ℝ) - (1 / 4 : ℝ) = 0) ∧
    (0 < (1 / 4 : ℝ)) := by
  constructor
  · intro n
    ring
  · norm_num

end Defect

/-!
## Unproved original mathematical obligation

To prove RH by the appropriate Nyman–Beurling criterion, one must
construct admissible approximants f_m to the target in L² with
squared error < 10^(-m) for every m. This is intentionally not
postulated, proved, or replaced by an artificial numeric sequence.

The hyperreal interpretation of an infinitesimal tail also requires
an explicit non-Archimedean model; it is not identified with the
ordinary real number zero.
-/

end ATK