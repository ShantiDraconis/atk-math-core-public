import MCore.MaterialMath.TriCyclicCalculus

namespace MCore.MaterialMath

namespace TriNumber

/-- Mean phase coordinate of a real tri-number. -/
noncomputable def mean (x : TriNumber ℝ) : ℝ :=
  total x / 3

/-- Projection onto the one-dimensional balanced mode. -/
noncomputable def balancedProjection (x : TriNumber ℝ) : TriNumber ℝ where
  manifest := mean x
  crossing := mean x
  seed := mean x

/-- Zero-sum fluctuation around the balanced mode. -/
noncomputable def fluctuation (x : TriNumber ℝ) : TriNumber ℝ where
  manifest := x.manifest - mean x
  crossing := x.crossing - mean x
  seed := x.seed - mean x

theorem balancedProjection_is_balanced (x : TriNumber ℝ) :
    Balanced (balancedProjection x) := by
  simp [Balanced, balancedProjection]

theorem total_balancedProjection (x : TriNumber ℝ) :
    total (balancedProjection x) = total x := by
  simp [total, balancedProjection, mean]
  ring

theorem fluctuation_zeroSum (x : TriNumber ℝ) :
    ZeroSum (fluctuation x) := by
  simp [ZeroSum, total, fluctuation, mean]
  ring

/-- Canonical direct-sum decomposition x = balanced + zero-sum fluctuation. -/
theorem balanced_add_fluctuation (x : TriNumber ℝ) :
    add (balancedProjection x) (fluctuation x) = x := by
  apply TriNumber.ext <;> simp [add, balancedProjection, fluctuation, mean]

/-- Removing the mean does not change phase spread. -/
theorem spread_fluctuation (x : TriNumber ℝ) :
    spread (fluctuation x) = spread x := by
  simp [spread, fluctuation, mean]

/-- Balanced projection has zero spread. -/
theorem spread_balancedProjection (x : TriNumber ℝ) :
    spread (balancedProjection x) = 0 := by
  exact (spread_eq_zero_iff_balanced (balancedProjection x)).2
    (balancedProjection_is_balanced x)

/-- The fluctuation vanishes exactly for balanced states. -/
theorem fluctuation_eq_zero_iff_balanced (x : TriNumber ℝ) :
    fluctuation x = { manifest := 0, crossing := 0, seed := 0 } ↔ Balanced x := by
  constructor
  · intro h
    have hm := congrArg TriNumber.manifest h
    have hc := congrArg TriNumber.crossing h
    have hs := congrArg TriNumber.seed h
    simp [fluctuation] at hm hc hs
    constructor <;> linarith
  · intro h
    rcases x with ⟨m, c, s⟩
    rcases h with ⟨hmc, hcs⟩
    change m = c at hmc
    change c = s at hcs
    subst c
    subst s
    apply TriNumber.ext <;>
      simp [fluctuation, mean, total] <;>
      ring

/-- Rotation commutes with the balanced projection. -/
theorem balancedProjection_rotate (x : TriNumber ℝ) :
    balancedProjection (rotate x) = rotate (balancedProjection x) := by
  apply TriNumber.ext <;> simp [balancedProjection, mean, total, rotate]
  all_goals ring

/-- Rotation commutes with zero-sum fluctuation. -/
theorem fluctuation_rotate (x : TriNumber ℝ) :
    fluctuation (rotate x) = rotate (fluctuation x) := by
  apply TriNumber.ext <;> simp [fluctuation, mean, total, rotate]
  all_goals ring


/-- The balanced and transverse subspaces intersect only at zero. -/
theorem balanced_and_zeroSum_eq_zero
    (x : TriNumber ℝ)
    (hb : Balanced x)
    (hz : ZeroSum x) :
    x = { manifest := 0, crossing := 0, seed := 0 } := by
  rcases x with ⟨m, c, s⟩
  rcases hb with ⟨hmc, hcs⟩
  change m = c at hmc
  change c = s at hcs
  subst c
  subst s
  simp [ZeroSum, total] at hz
  have hm : m = 0 := by linarith
  subst m
  rfl

/-- The canonical decomposition is unique among balanced + zero-sum splits. -/
theorem balanced_transverse_decomposition_unique
    (x b t : TriNumber ℝ)
    (hb : Balanced b)
    (ht : ZeroSum t)
    (hdecomp : add b t = x) :
    b = balancedProjection x ∧ t = fluctuation x := by
  rcases x with ⟨xm, xc, xs⟩
  rcases b with ⟨bm, bc, bs⟩
  rcases t with ⟨tm, tc, ts⟩
  change bm = bc ∧ bc = bs at hb
  rcases hb with ⟨hbc, hcs⟩
  subst bc
  subst bs
  change tm + tc + ts = 0 at ht
  have hm := congrArg TriNumber.manifest hdecomp
  have hc := congrArg TriNumber.crossing hdecomp
  have hs := congrArg TriNumber.seed hdecomp
  simp [add] at hm hc hs
  have hbm : bm = (xm + xc + xs) / 3 := by
    linarith
  constructor
  · apply TriNumber.ext <;>
      simp [balancedProjection, mean, total, hbm]
  · apply TriNumber.ext <;>
      simp [fluctuation, mean, total] <;>
      linarith

/-- Equilibrium mode: the balanced one-dimensional part. -/
def EquilibriumMode (x : TriNumber ℝ) : Prop :=
  Balanced x

/-- Transverse mode: the two-dimensional zero-sum phase plane. -/
def TransverseMode (x : TriNumber ℝ) : Prop :=
  ZeroSum x

end TriNumber

/-- Resolution fiber for the formal singular ratio I = 0/0.
It records tri-states in the transverse zero-sum plane rather than assigning
an ordinary scalar value to division by zero. -/
structure SingularResolution where
  state : TriNumber ℝ
  transverse : TriNumber.ZeroSum state

namespace SingularResolution

/-- Every real tri-state has a canonical singular-resolution representative:
its zero-sum fluctuation. -/
noncomputable def ofTriNumber (x : TriNumber ℝ) : SingularResolution where
  state := TriNumber.fluctuation x
  transverse := TriNumber.fluctuation_zeroSum x

/-- Cyclic phase rotation acts on the singular-resolution fiber. -/
def rotate (r : SingularResolution) : SingularResolution where
  state := TriNumber.rotate r.state
  transverse :=
    (TriNumber.zeroSum_rotate_iff r.state).2 r.transverse

theorem rotate_three (r : SingularResolution) :
    rotate (rotate (rotate r)) = r := by
  cases r with
  | mk state h =>
      simp [rotate, TriNumber.rotate_three]

end SingularResolution

end MCore.MaterialMath
