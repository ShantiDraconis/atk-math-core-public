import MCore.MaterialMath.TriState.Spectral

namespace MCore.MaterialMath

/-- F1-style vanishing: an explicit epsilon/N formulation over a real sequence. -/
def VanishesAtInfinity (a : Nat → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : Nat, ∀ n ≥ N, |a n| ≤ ε

theorem vanishing_zero :
    VanishesAtInfinity (fun _ => 0) := by
  intro ε hε
  exact ⟨0, by intro n hn; simp [le_of_lt hε]⟩

theorem vanishing_add
    {a b : Nat → ℝ}
    (ha : VanishesAtInfinity a)
    (hb : VanishesAtInfinity b) :
    VanishesAtInfinity (fun n => a n + b n) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases ha (ε / 2) hhalf with ⟨Na, hNa⟩
  rcases hb (ε / 2) hhalf with ⟨Nb, hNb⟩
  refine ⟨max Na Nb, ?_⟩
  intro n hn
  have hna : Na ≤ n := le_trans (le_max_left Na Nb) hn
  have hnb : Nb ≤ n := le_trans (le_max_right Na Nb) hn
  calc
    |a n + b n| ≤ |a n| + |b n| := abs_add _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hNa n hna) (hNb n hnb)
    _ = ε := by ring

/-- F2-style gap: a quantity is uniformly bounded away from zero. -/
def PositiveGap {X : Type*} (f : X → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ f x

theorem positiveGap_of_one_lower_bound
    {X : Type*} {f : X → ℝ}
    (h : ∀ x, 1 ≤ f x) :
    PositiveGap f := by
  exact ⟨1, by norm_num, h⟩

/-- F4-style realization. -/
def UniversalRealization
    {A B : Type*}
    (R : A → B → Prop) : Prop :=
  ∀ a, ∃ b, R a b

/-- F5-style pointwise equality. -/
def UniversalEquality
    {X Y : Type*}
    (f g : X → Y) : Prop :=
  ∀ x, f x = g x

/-- F6-style exclusion. -/
def UniversalExclusion
    {X : Type*}
    (Bad : X → Prop) : Prop :=
  ∀ x, ¬ Bad x

/-- F7-style strict budget: every admissible state has a contraction factor
strictly below one together with a certified bound. -/
def StrictBudget
    {X : Type*}
    (Cost Bound : X → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
    ∀ x, Cost x ≤ c * Bound x

/-- F8-style fixed point. -/
def HasFixedPoint {X : Type*} (f : X → X) : Prop :=
  ∃ x, f x = x

/-- One-step phase rotation has no fixed point. -/
theorem rotate_has_no_fixedPoint :
    ¬ HasFixedPoint Phase3.rotate := by
  rintro ⟨p, hp⟩
  exact Phase3.rotate_ne_self p hp

/-- Three-step phase rotation fixes every phase. -/
theorem rotate_three_fixes_all :
    ∀ p : Phase3,
      Phase3.rotate (Phase3.rotate (Phase3.rotate p)) = p :=
  Phase3.rotate_three

/-- Distinct phases possess an exact discrete gap of one. -/
theorem distinct_phases_have_unit_gap
    {p q : Phase3}
    (h : p ≠ q) :
    Phase3.cyclicDistance p q = 1 :=
  Phase3.cyclicDistance_eq_one h

/-- The balanced tri-state sector carries an exact spectral gap magnitude 3:
the Laplacian acts as -3 times identity there. -/
theorem balanced_sector_exact_spectral_gap
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {x : TriNumber α}
    (h : TriNumber.Balanced x) :
    TriNumber.laplacian x =
      fun p => (-3 : α) * x p :=
  TriSpectral.laplacian_eq_neg_three_of_balanced h

end MCore.MaterialMath
