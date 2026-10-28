import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace MCore.OpenMath.I3

/-- Algebraic carrier for a primitive cube-root three-cycle. -/
structure TristableRoot where
  omega : ℂ
  cube_eq_one : omega ^ 3 = 1
  nontrivial : omega ≠ 1
  equilibrium : 1 + omega + omega ^ 2 = 0

inductive IState
  | manifesto
  | travessia
  | semente
  deriving DecidableEq, Repr

def next : IState → IState
  | .manifesto => .travessia
  | .travessia => .semente
  | .semente => .manifesto

@[simp] theorem next_three (s : IState) : next (next (next s)) = s := by
  cases s <;> rfl

theorem states_pairwise_distinct :
    IState.manifesto ≠ IState.travessia ∧
    IState.travessia ≠ IState.semente ∧
    IState.semente ≠ IState.manifesto := by
  decide

/-- An explicit primitive cube root, defined algebraically. -/
noncomputable def omega : ℂ :=
  (-1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I

lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  norm_num

theorem omega_sq :
    omega ^ 2 = (-1 / 2 : ℂ) - (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  rw [omega]
  have hs : (Real.sqrt 3) ^ 2 = 3 := sqrt_three_sq
  apply Complex.ext <;> simp [pow_two] <;> nlinarith

theorem omega_equilibrium : 1 + omega + omega ^ 2 = 0 := by
  rw [omega_sq, omega]
  ring

theorem omega_cube : omega ^ 3 = 1 := by
  have h : omega * (omega ^ 2 + omega + 1) = 0 := by
    rw [show omega ^ 2 + omega + 1 = 0 by
      have := omega_equilibrium
      linear_combination this]
    simp
  have hpoly : omega ^ 3 - 1 = 0 := by
    calc
      omega ^ 3 - 1 = (omega - 1) * (omega ^ 2 + omega + 1) := by ring
      _ = 0 := by
        rw [show omega ^ 2 + omega + 1 = 0 by
          have := omega_equilibrium
          linear_combination this]
        ring
  linear_combination hpoly

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have he := omega_equilibrium
  rw [h] at he
  norm_num at he

noncomputable def certifiedRoot : TristableRoot where
  omega := omega
  cube_eq_one := omega_cube
  nontrivial := omega_ne_one
  equilibrium := omega_equilibrium

theorem i3_final_theorem :
    ∃ r : TristableRoot,
      r.omega ^ 3 = 1 ∧
      r.omega ≠ 1 ∧
      1 + r.omega + r.omega ^ 2 = 0 := by
  refine ⟨certifiedRoot, ?_⟩
  exact ⟨certifiedRoot.cube_eq_one,
    certifiedRoot.nontrivial,
    certifiedRoot.equilibrium⟩

end MCore.OpenMath.I3
