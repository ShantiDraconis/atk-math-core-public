import MCore.FinalFail.BoundaryAtoms
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace MCore.FinalFail.Semantic

/-- The exact counterexample object selected for the RH lane. -/
structure RiemannOffCriticalZero where
  s : ℂ
  zero : riemannZeta s = 0
  nontrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1)
  notPole : s ≠ 1
  offCriticalLine : s.re ≠ 1 / 2

abbrev RiemannInterpretation :=
  BoundaryInterpretation .riemann RiemannOffCriticalZero

theorem riemann_interpretation_iff_target :
    Nonempty RiemannInterpretation ↔ Nonempty RiemannOffCriticalZero :=
  nonempty_boundaryInterpretation_iff_nonempty_target

/-- Any inhabitant of the selected semantic target really refutes Mathlib's RH
statement; it is not merely an audit label. -/
theorem offCriticalZero_refutes_RH
    (w : RiemannOffCriticalZero) : ¬ RiemannHypothesis := by
  intro h
  exact w.offCriticalLine (h w.s w.zero w.nontrivial w.notPole)

/-- Every selected off-critical zero lies strictly to the left of Re(s)=1,
because zeta is nonzero on the closed half-plane Re(s) >= 1. -/
theorem RiemannOffCriticalZero.re_lt_one
    (w : RiemannOffCriticalZero) : w.s.re < 1 := by
  apply lt_of_not_ge
  intro h
  exact (riemannZeta_ne_zero_of_one_le_re h) w.zero


/-- Exact logical extraction: because Mathlib defines RH as a universal
statement over all nontrivial zeros, its negation is equivalent (classically)
to the existence of a concrete nontrivial zero off the critical line. -/
theorem not_riemannHypothesis_iff_nonempty_offCriticalZero :
    (¬ RiemannHypothesis) ↔ Nonempty RiemannOffCriticalZero := by
  constructor
  · intro hNotRH
    classical
    by_contra hNoWitness
    apply hNotRH
    intro s hZero hNontrivial hNotPole
    by_contra hOff
    exact hNoWitness ⟨{
      s := s
      zero := hZero
      nontrivial := hNontrivial
      notPole := hNotPole
      offCriticalLine := hOff
    }⟩
  · rintro ⟨w⟩
    exact offCriticalZero_refutes_RH w

/-- In the accepted-hypothesis world used by the ATK programme, an explicit
accepted negation of RH therefore yields the exact semantic target, not merely
a syntactic boundary atom.  This theorem remains conditional on hNotRH. -/
theorem accepted_not_RH_produces_semantic_inhabitant
    (hNotRH : ¬ RiemannHypothesis) :
    Nonempty RiemannOffCriticalZero :=
  not_riemannHypothesis_iff_nonempty_offCriticalZero.mp hNotRH

end MCore.FinalFail.Semantic
