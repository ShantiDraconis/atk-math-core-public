import MCore.FinalFail.Semantic.Riemann
import MCore.FinalFail.RPAConfirmation

/-!
# Riemann lane — dual orientation (prove / refute) and the exact boundary

The lane keeps **both** orientations as separate terminal obligations:

* prove side  `RiemannProveTarget  := RiemannHypothesis` (Mathlib's statement);
  the source repository's producer is the Nyman–Beurling / Báez-Duarte criterion
  `FiniteSpanApproximatesChi` (`m-core-riemann`);
* refute side `RiemannRefuteTarget := Nonempty RiemannOffCriticalZero`.

Exactly one side can ever be inhabited (`riemann_not_both`,
`riemann_prove_iff_not_refute`).  The classical dichotomy `RH ∨ ¬RH` is *not* a
terminal: the lane closes only with an explicit inhabitant of one side.

## Where the proof turns into a refutation

Using Mathlib's functional equation `riemannZeta_one_sub` this file proves:

* every nontrivial zero has `0 < re s` (`nontrivial_zero_re_pos`);
* in the open critical strip, zeros are symmetric under `s ↦ 1 - s`
  (`riemannZeta_one_sub_eq_zero`), so off-critical zeros come in pairs
  (`RiemannOffCriticalZero.reflect`) and the critical line is the fixed locus;
* hence the whole question lives in the open half-strip `1/2 < re s < 1`:
  `riemann_refute_iff_zero_in_right_strip` and
  `riemann_prove_iff_no_zero_in_right_strip`.

These are classical facts, formalized here; they are reductions, not progress on
either side of the conjecture.  No axiom, `sorry`, or hypothesis is introduced.
-/

namespace MCore.FinalFail.Semantic

/-- Prove side of the Riemann lane: Mathlib's official statement. -/
abbrev RiemannProveTarget : Prop := RiemannHypothesis

/-- Refute side of the Riemann lane: an explicit off-critical nontrivial zero. -/
abbrev RiemannRefuteTarget : Prop := Nonempty RiemannOffCriticalZero

theorem riemann_prove_iff_not_refute :
    RiemannProveTarget ↔ ¬ RiemannRefuteTarget := by
  show RiemannHypothesis ↔ ¬ Nonempty RiemannOffCriticalZero
  constructor
  · intro h hw
    exact (not_riemannHypothesis_iff_nonempty_offCriticalZero.mpr hw) h
  · intro h
    by_contra hRH
    exact h (not_riemannHypothesis_iff_nonempty_offCriticalZero.mp hRH)

/-- The two orientations exclude each other. -/
theorem riemann_not_both : ¬ (RiemannProveTarget ∧ RiemannRefuteTarget) :=
  fun ⟨hp, hr⟩ => (riemann_prove_iff_not_refute.mp hp) hr

/-- The dual lane as an M-Core RPA frame: the prove endpoint and the negated
refute endpoint carry the same identity. -/
theorem riemann_dual_frame :
    RPA.RPAFrame RiemannProveTarget (¬ RiemannRefuteTarget) :=
  ⟨riemann_prove_iff_not_refute⟩

/-- In the open critical strip, zeros of ζ are symmetric under `s ↦ 1 - s`. -/
theorem riemannZeta_one_sub_eq_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have hre : s.re = -(n : ℝ) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  rw [riemannZeta_one_sub hs hs', hz, mul_zero]

/-- Every nontrivial zero of ζ satisfies `0 < re s`. -/
theorem nontrivial_zero_re_pos {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬ ∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra hle
  push_neg at hle
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hz
    norm_num at hz
  set t : ℂ := 1 - s with ht
  have hst : s = 1 - t := by rw [ht]; ring
  have htre : 1 ≤ t.re := by
    rw [ht]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have htn : ∀ n : ℕ, t ≠ -n := by
    intro n hn
    have hre : t.re = -(n : ℝ) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have ht1 : t ≠ 1 := by
    intro h
    apply hs0
    have h' : s = 1 - 1 := by rw [hst, h]
    simpa using h'
  have hfe := riemannZeta_one_sub htn ht1
  rw [← hst, hz] at hfe
  have hzt : riemannZeta t ≠ 0 := riemannZeta_ne_zero_of_one_le_re htre
  have hG : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2pi : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hpi
  have hpow : ((2 : ℂ) * Real.pi) ^ (-t) ≠ 0 := by
    intro h
    exact h2pi ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hcos : Complex.cos (Real.pi * t / 2) = 0 := by
    rcases mul_eq_zero.mp hfe.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact absurd h hpow
        · exact absurd h hG
      · exact h
    · exact absurd h hzt
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have htk : t = 2 * (k : ℂ) + 1 := by
    apply mul_left_cancel₀ hpi
    linear_combination 2 * hk
  have hsk : s = -2 * (k : ℂ) := by
    rw [hst, htk]
    ring
  have hkre : s.re = -2 * (k : ℝ) := by
    rw [hsk]
    simp
  have hk1 : 1 ≤ k := by
    by_contra hk1
    have hk0 : k ≤ 0 := by omega
    rcases lt_or_eq_of_le hk0 with hlt | heq
    · have hkr : (k : ℝ) < 0 := by exact_mod_cast hlt
      linarith
    · apply hs0
      rw [hsk, heq]
      simp
  apply hnt
  refine ⟨(k - 1).toNat, ?_⟩
  have hnat : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by exact_mod_cast hnat
  rw [hsk, hc]
  ring

theorem RiemannOffCriticalZero.re_pos (w : RiemannOffCriticalZero) : 0 < w.s.re :=
  nontrivial_zero_re_pos w.zero w.nontrivial

/-- Off-critical zeros come in pairs `s ↔ 1 - s`; the critical line `re s = 1/2`
is exactly the fixed locus of this reflection. -/
noncomputable def RiemannOffCriticalZero.reflect (w : RiemannOffCriticalZero) :
    RiemannOffCriticalZero where
  s := 1 - w.s
  zero := riemannZeta_one_sub_eq_zero w.re_pos w.re_lt_one w.zero
  nontrivial := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have h1 := w.re_lt_one
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [Complex.sub_re, Complex.one_re] at hre
    have hrhs : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    linarith
  notPole := by
    intro h
    have hre := congrArg Complex.re h
    have h0 := w.re_pos
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  offCriticalLine := by
    have hoff := w.offCriticalLine
    simp only [Complex.sub_re, Complex.one_re]
    intro h
    apply hoff
    linarith

theorem RiemannOffCriticalZero.reflect_re (w : RiemannOffCriticalZero) :
    w.reflect.s.re = 1 - w.s.re := by
  show (1 - w.s).re = 1 - w.s.re
  simp

/-- **Exact boundary (refute side).**  A refutation of RH exists iff ζ has a zero
in the open half-strip `1/2 < re s < 1`. -/
theorem riemann_refute_iff_zero_in_right_strip :
    RiemannRefuteTarget ↔ ∃ s : ℂ, riemannZeta s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1 := by
  constructor
  · rintro ⟨w⟩
    have h0 := w.re_pos
    have h1 := w.re_lt_one
    rcases lt_or_gt_of_ne w.offCriticalLine with hlt | hgt
    · refine ⟨1 - w.s, riemannZeta_one_sub_eq_zero h0 h1 w.zero, ?_, ?_⟩
      · simp only [Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.sub_re, Complex.one_re]
        linarith
    · exact ⟨w.s, w.zero, hgt, h1⟩
  · rintro ⟨s, hz, hhalf, h1⟩
    refine ⟨{ s := s, zero := hz, nontrivial := ?_, notPole := ?_,
              offCriticalLine := hhalf.ne' }⟩
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      have hrhs : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h
      rw [h] at h1
      simp at h1

/-- **Exact boundary (prove side).**  RH holds iff ζ has no zero with
`1/2 < re s < 1`. -/
theorem riemann_prove_iff_no_zero_in_right_strip :
    RiemannProveTarget ↔ ∀ s : ℂ, riemannZeta s = 0 → 1 / 2 < s.re → 1 ≤ s.re := by
  rw [riemann_prove_iff_not_refute, riemann_refute_iff_zero_in_right_strip]
  constructor
  · intro h s hz hh
    by_contra hlt
    push_neg at hlt
    exact h ⟨s, hz, hh, hlt⟩
  · rintro h ⟨s, hz, hh, hlt⟩
    exact absurd (h s hz hh) (not_le.mpr hlt)

#print axioms MCore.FinalFail.Semantic.riemann_prove_iff_not_refute
#print axioms MCore.FinalFail.Semantic.riemann_not_both
#print axioms MCore.FinalFail.Semantic.riemann_dual_frame
#print axioms MCore.FinalFail.Semantic.riemannZeta_one_sub_eq_zero
#print axioms MCore.FinalFail.Semantic.nontrivial_zero_re_pos
#print axioms MCore.FinalFail.Semantic.riemann_refute_iff_zero_in_right_strip
#print axioms MCore.FinalFail.Semantic.riemann_prove_iff_no_zero_in_right_strip

end MCore.FinalFail.Semantic
