import MCore.FinalFail.BoundaryAtoms

namespace MCore.FinalFail.Semantic

/-- Concrete admissible Beal datum, with the Diophantine equation stored as
evidence rather than as an ambient hypothesis. -/
structure BealEquationData where
  a : ℕ
  b : ℕ
  c : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  x_gt_two : 2 < x
  y_gt_two : 2 < y
  z_gt_two : 2 < z
  equation : a ^ x + b ^ y = c ^ z

/-- Positive Beal orientation used by the current canonical HARD: every
admissible equation datum has a nontrivial common gcd. -/
structure BealUniversalGCDTarget where
  commonGCD : ∀ d : BealEquationData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)

abbrev BealInterpretation :=
  BoundaryInterpretation .beal BealUniversalGCDTarget

theorem beal_interpretation_iff_target :
    Nonempty BealInterpretation ↔ Nonempty BealUniversalGCDTarget :=
  nonempty_boundaryInterpretation_iff_nonempty_target

end MCore.FinalFail.Semantic
