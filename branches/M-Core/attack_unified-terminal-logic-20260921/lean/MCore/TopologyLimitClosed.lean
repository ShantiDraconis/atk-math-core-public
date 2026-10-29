import Mathlib

namespace MCore.LimitClosed

noncomputable def rho (r : ℝ) : ℝ := r / (1 + r)
noncomputable def epsilon (r : ℝ) : ℝ := 1 / (1 + r)

theorem rho_epsilon {r : ℝ} (hr : r ≠ -1) :
    rho r + epsilon r = 1 := by
  unfold rho epsilon
  have hden : (1 + r : ℝ) ≠ 0 := by
    intro h
    apply hr
    linarith
  field_simp [hden]
  ring

inductive Phase
  | approach | crossing | indeterminate (e : String) | collapse
  deriving Repr

def kerC : Phase → String
  | .collapse => "ker non-trivial - information loss"
  | _ => "ker trivial - expression preserved"

def TendstoRhoTarget : Prop :=
  Filter.Tendsto rho Filter.atTop (nhdsWithin 1 (Set.Iio 1))

def TendstoEpsilonTarget : Prop :=
  Filter.Tendsto epsilon Filter.atTop (nhdsWithin 0 (Set.Ioi 0))

def limitStatus : String := "OPEN_FORMALIZATION"

end MCore.LimitClosed
