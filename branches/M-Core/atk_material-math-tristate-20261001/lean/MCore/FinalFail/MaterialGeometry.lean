import MCore.FinalFail.MaterialDerived

namespace MCore.FinalFail.MaterialGeometry

abbrev TState := MCore.FinalFail.MaterialAlgebra.TriState
abbrev LaneVector := MCore.FinalFail.MaterialAlgebra.SevenLaneVector
abbrev EState := MCore.FinalFail.MaterialCalculus.EvidenceState

/-!
# Discrete material geometry

This module derives geometry and higher discrete calculus from the already
kernel-checked three-state algebra and seven-lane vector carrier.

It is internal mathematics of the ATK material calculus. It does not assert
or manufacture an inhabitant of any external open problem.
-/

namespace TriState

abbrev zeroPhase : TState := .seed
abbrev unitPhase : TState := .transit
abbrev conjugatePhase : TState := .manifest

def rho (x : TState) : TState := x.rotate

@[simp] theorem rho_three (x : TState) :
    rho (rho (rho x)) = x := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.rotate_three x

theorem rho_ne_self (x : TState) :
    rho x ≠ x := by
  cases x <;> decide

theorem rho_injective : Function.Injective rho := by
  intro x y h
  cases x <;> cases y <;> simp [rho, MCore.FinalFail.MaterialAlgebra.TriState.rotate] at h ⊢

theorem rho_surjective : Function.Surjective rho := by
  intro y
  refine ⟨rho (rho y), ?_⟩
  exact rho_three y

def delta (x y : TState) : TState := x + (-y)

@[simp] theorem delta_self (x : TState) :
    delta x x = 0 := by
  exact MCore.FinalFail.MaterialAlgebra.TriState.add_neg x

theorem delta_eq_zero_iff (x y : TState) :
    delta x y = 0 ↔ x = y := by
  cases x <;> cases y <;> decide

def support : TState → Nat
  | .seed => 0
  | .transit => 1
  | .manifest => 1

theorem support_le_one (x : TState) :
    support x ≤ 1 := by
  cases x <;> decide

theorem support_eq_zero_iff (x : TState) :
    support x = 0 ↔ x = 0 := by
  cases x <;> decide

theorem support_delta_eq_zero_iff (x y : TState) :
    support (delta x y) = 0 ↔ x = y := by
  rw [support_eq_zero_iff, delta_eq_zero_iff]

end TriState

namespace SevenLaneVector

def rotate (x : LaneVector) : LaneVector where
  riemann := TriState.rho x.riemann
  beal := TriState.rho x.beal
  pvsnp := TriState.rho x.pvsnp
  navierStokes := TriState.rho x.navierStokes
  hodge := TriState.rho x.hodge
  bsd := TriState.rho x.bsd
  yangMills := TriState.rho x.yangMills

@[simp] theorem rotate_three (x : LaneVector) :
    rotate (rotate (rotate x)) = x := by
  apply MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality
  · exact TriState.rho_three x.riemann
  · exact TriState.rho_three x.beal
  · exact TriState.rho_three x.pvsnp
  · exact TriState.rho_three x.navierStokes
  · exact TriState.rho_three x.hodge
  · exact TriState.rho_three x.bsd
  · exact TriState.rho_three x.yangMills

def supportCount (x : LaneVector) : Nat :=
  TriState.support x.riemann +
  TriState.support x.beal +
  TriState.support x.pvsnp +
  TriState.support x.navierStokes +
  TriState.support x.hodge +
  TriState.support x.bsd +
  TriState.support x.yangMills

theorem supportCount_le_seven (x : LaneVector) :
    supportCount x ≤ 7 := by
  have hR := TriState.support_le_one x.riemann
  have hB := TriState.support_le_one x.beal
  have hP := TriState.support_le_one x.pvsnp
  have hN := TriState.support_le_one x.navierStokes
  have hH := TriState.support_le_one x.hodge
  have hD := TriState.support_le_one x.bsd
  have hY := TriState.support_le_one x.yangMills
  unfold supportCount
  omega

@[simp] theorem supportCount_zero :
    supportCount MCore.FinalFail.MaterialAlgebra.SevenLaneVector.zero = 0 := by
  rfl

def hamming (x y : LaneVector) : Nat :=
  (if x.riemann = y.riemann then 0 else 1) +
  (if x.beal = y.beal then 0 else 1) +
  (if x.pvsnp = y.pvsnp then 0 else 1) +
  (if x.navierStokes = y.navierStokes then 0 else 1) +
  (if x.hodge = y.hodge then 0 else 1) +
  (if x.bsd = y.bsd then 0 else 1) +
  (if x.yangMills = y.yangMills then 0 else 1)

@[simp] theorem hamming_self (x : LaneVector) :
    hamming x x = 0 := by
  simp [hamming]

theorem hamming_comm (x y : LaneVector) :
    hamming x y = hamming y x := by
  simp [hamming, eq_comm]

theorem hamming_le_seven (x y : LaneVector) :
    hamming x y ≤ 7 := by
  unfold hamming
  split <;> split <;> split <;> split <;> split <;> split <;> split <;> decide

theorem hamming_eq_zero_iff (x y : LaneVector) :
    hamming x y = 0 ↔ x = y := by
  constructor
  · intro h
    unfold hamming at h
    have hr : x.riemann = y.riemann := by
      by_contra hne
      simp [hne] at h
    have hb : x.beal = y.beal := by
      by_contra hne
      simp [hr, hne] at h
    have hp : x.pvsnp = y.pvsnp := by
      by_contra hne
      simp [hr, hb, hne] at h
    have hn : x.navierStokes = y.navierStokes := by
      by_contra hne
      simp [hr, hb, hp, hne] at h
    have hh : x.hodge = y.hodge := by
      by_contra hne
      simp [hr, hb, hp, hn, hne] at h
    have hd : x.bsd = y.bsd := by
      by_contra hne
      simp [hr, hb, hp, hn, hh, hne] at h
    have hy : x.yangMills = y.yangMills := by
      by_contra hne
      simp [hr, hb, hp, hn, hh, hd, hne] at h
    exact MCore.FinalFail.MaterialAlgebra.SevenLaneVector.extensionality hr hb hp hn hh hd hy
  · intro h
    subst y
    exact hamming_self x

theorem hamming_rotate (x y : LaneVector) :
    hamming (rotate x) (rotate y) = hamming x y := by
  have hiff : ∀ a b : TState, TriState.rho a = TriState.rho b ↔ a = b := by
    intro a b
    cases a <;> cases b <;> decide
  unfold hamming rotate
  simp [hiff]

end SevenLaneVector

namespace EvidenceState

def secondDerivative (f : Nat → EState) (n : Nat) : Int :=
  MCore.FinalFail.MaterialCalculus.EvidenceState.derivative f (n + 1) -
    MCore.FinalFail.MaterialCalculus.EvidenceState.derivative f n

theorem secondDerivative_bounds
    (f : Nat → EState) (n : Nat) :
    -4 ≤ secondDerivative f n ∧ secondDerivative f n ≤ 4 := by
  have h1 := MCore.FinalFail.MaterialCalculus.EvidenceState.derivative_bounds f (n + 1)
  have h0 := MCore.FinalFail.MaterialCalculus.EvidenceState.derivative_bounds f n
  unfold secondDerivative
  omega

theorem secondDerivative_eq_zero_of_local_constant
    (f : Nat → EState) (n : Nat)
    (h01 : f (n + 1) = f n)
    (h12 : f (n + 2) = f (n + 1)) :
    secondDerivative f n = 0 := by
  have h0 : MCore.FinalFail.MaterialCalculus.EvidenceState.derivative f n = 0 :=
    (MCore.FinalFail.MaterialCalculus.EvidenceState.derivative_eq_zero_iff_state_stable f n).2 h01
  have h1 : MCore.FinalFail.MaterialCalculus.EvidenceState.derivative f (n + 1) = 0 := by
    apply (MCore.FinalFail.MaterialCalculus.EvidenceState.derivative_eq_zero_iff_state_stable f (n + 1)).2
    simpa [Nat.add_assoc] using h12
  unfold secondDerivative
  rw [h0, h1]
  simp

def jumpMagnitude (f : Nat → EState) (n : Nat) : Nat :=
  Int.natAbs (MCore.FinalFail.MaterialCalculus.EvidenceState.derivative f n)

theorem jumpMagnitude_le_two
    (f : Nat → EState) (n : Nat) :
    jumpMagnitude f n ≤ 2 := by
  unfold jumpMagnitude MCore.FinalFail.MaterialCalculus.EvidenceState.derivative
  cases h0 : f n <;>
    cases h1 : f (n + 1) <;>
    norm_num [MCore.FinalFail.MaterialCalculus.EvidenceState.code, h0, h1]

end EvidenceState

#print axioms MCore.FinalFail.MaterialGeometry.TriState.rho_three
#print axioms MCore.FinalFail.MaterialGeometry.TriState.delta_eq_zero_iff
#print axioms MCore.FinalFail.MaterialGeometry.SevenLaneVector.supportCount_le_seven
#print axioms MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming_eq_zero_iff
#print axioms MCore.FinalFail.MaterialGeometry.SevenLaneVector.hamming_rotate
#print axioms MCore.FinalFail.MaterialGeometry.EvidenceState.secondDerivative_bounds

end MCore.FinalFail.MaterialGeometry
