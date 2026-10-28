namespace MCore

structure BealData where
  a : Nat
  b : Nat
  c : Nat
  x : Nat
  y : Nat
  z : Nat
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  x_gt_two : 2 < x
  y_gt_two : 2 < y
  z_gt_two : 2 < z
  equation : a ^ x + b ^ y = c ^ z

def CommonDivisor (d a b c : Nat) : Prop :=
  1 < d ∧ d ∣ a ∧ d ∣ b ∧ d ∣ c

/-- Prime in the elementary divisor sense; local definition keeps the kernel dependency-free. -/
def IsPrime (p : Nat) : Prop :=
  1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def CommonPrime (a b c : Nat) : Prop :=
  ∃ p : Nat, IsPrime p ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c

def BealConjecture : Prop :=
  ∀ d : BealData, CommonPrime d.a d.b d.c

def BealCounterexample (d : BealData) : Prop :=
  ¬ CommonPrime d.a d.b d.c

theorem counterexample_refutes (d : BealData) (h : BealCounterexample d) : ¬ BealConjecture := by
  intro hBeal
  exact h (hBeal d)

theorem conjecture_excludes_counterexamples (h : BealConjecture) (d : BealData) :
    ¬ BealCounterexample d := by
  intro hd
  exact hd (h d)

end MCore
