/-
Copyright (c) 2026 Tiago Paschoalatto Fagliari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiago Paschoalatto Fagliari
-/
import Mathlib.NumberTheory.Height.EllipticCurve

/-!
# The canonical (Néron–Tate) height on an elliptic curve

Let `W` be an elliptic curve over a field `F` with a theory of heights
(`[Height.AdmissibleAbsValues F]`). Using the approximate parallelogram law for the naïve height
(`WeierstrassCurve.Affine.approx_parallelogram_law`), we define the canonical height
`ĥ(P) = lim_{n → ∞} h(2ⁿ P) / 4ⁿ` and prove its basic properties.

## Main definitions

* `WeierstrassCurve.Affine.Point.canonicalHeight`: the canonical height `ĥ`.
* `WeierstrassCurve.Affine.Point.neronTatePairing`: `⟨P, Q⟩ = (ĥ(P + Q) − ĥ(P) − ĥ(Q)) / 2`.

## Main statements

* `tendsto_canonicalHeight`: the limit defining `ĥ` exists (Tate's telescoping argument).
* `abs_canonicalHeight_sub_naiveHeight_le`: `ĥ − h` is bounded.
* `canonicalHeight_add_add_canonicalHeight_sub`: the exact parallelogram law.
* `canonicalHeight_nsmul`: `ĥ(n • P) = n² ĥ(P)`.
* `canonicalHeight_eq_zero_iff` (with the Northcott property): `ĥ(P) = 0 ↔ P` is torsion.
* `neronTatePairing_add_left`: the Néron–Tate pairing is additive.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*, VIII.9][silverman2009]
-/

open Filter Topology Height

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F] {W : Affine F}

/-- The canonical (Néron–Tate) height `ĥ(P) = lim h(2ⁿ P) / 4ⁿ`. -/
noncomputable def canonicalHeight (P : W.Point) : ℝ :=
  limUnder atTop fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / 4 ^ n

variable [W.IsElliptic]

theorem exists_abs_naiveHeight_two_nsmul_sub_le :
    ∃ C, ∀ Q : W.Point, |(2 • Q).naiveHeight - 4 * Q.naiveHeight| ≤ C := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  refine ⟨C + |(0 : W.Point).naiveHeight|, fun Q ↦ ?_⟩
  have := hC Q Q
  rw [sub_self, ← two_nsmul] at this
  calc |(2 • Q).naiveHeight - 4 * Q.naiveHeight|
      = |((2 • Q).naiveHeight + (0 : W.Point).naiveHeight
            - 2 * (Q.naiveHeight + Q.naiveHeight)) - (0 : W.Point).naiveHeight| := by ring_nf
    _ ≤ |(2 • Q).naiveHeight + (0 : W.Point).naiveHeight
            - 2 * (Q.naiveHeight + Q.naiveHeight)| + |(0 : W.Point).naiveHeight| := abs_sub _ _
    _ ≤ C + |(0 : W.Point).naiveHeight| := by linarith

omit [W.IsElliptic] in
theorem dist_naiveHeight_div_le {C : ℝ}
    (hC : ∀ Q : W.Point, |(2 • Q).naiveHeight - 4 * Q.naiveHeight| ≤ C) (P : W.Point) (n : ℕ) :
    dist (((2 ^ n) • P).naiveHeight / 4 ^ n) (((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1)) ≤
      C / 4 * (1 / 4) ^ n := by
  rw [Real.dist_eq]
  have hq := hC ((2 ^ n) • P)
  rw [← mul_nsmul', ← pow_succ'] at hq
  have e : ((2 ^ n) • P).naiveHeight / 4 ^ n - ((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1) =
      -(((2 ^ (n + 1)) • P).naiveHeight - 4 * ((2 ^ n) • P).naiveHeight) / 4 ^ (n + 1) := by
    field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (n + 1)),
    div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ (n + 1))]
  calc |((2 ^ (n + 1)) • P).naiveHeight - 4 * ((2 ^ n) • P).naiveHeight| ≤ C := hq
    _ = C / 4 * (1 / 4) ^ n * 4 ^ (n + 1) := by rw [one_div_pow, pow_succ]; field_simp

theorem tendsto_canonicalHeight (P : W.Point) :
    Tendsto (fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / 4 ^ n) atTop (𝓝 P.canonicalHeight) := by
  obtain ⟨C, hC⟩ := exists_abs_naiveHeight_two_nsmul_sub_le (W := W)
  exact (cauchySeq_of_le_geometric (1 / 4) (C / 4) (by norm_num)
    (dist_naiveHeight_div_le hC P)).tendsto_limUnder

theorem abs_canonicalHeight_sub_naiveHeight_le :
    ∃ C, ∀ P : W.Point, |P.canonicalHeight - P.naiveHeight| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_naiveHeight_two_nsmul_sub_le (W := W)
  refine ⟨C / 4 / (1 - 1 / 4), fun P ↦ ?_⟩
  have := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (C / 4) (by norm_num)
    (dist_naiveHeight_div_le hC P) (tendsto_canonicalHeight P)
  rw [Real.dist_eq] at this
  simpa [abs_sub_comm] using this

theorem canonicalHeight_nonneg (P : W.Point) : 0 ≤ P.canonicalHeight :=
  ge_of_tendsto' (tendsto_canonicalHeight P) fun _ ↦
    div_nonneg (logHeight_nonneg _) (by positivity)

/-- The exact parallelogram law for the canonical height. -/
theorem canonicalHeight_add_add_canonicalHeight_sub (P Q : W.Point) :
    (P + Q).canonicalHeight + (P - Q).canonicalHeight =
      2 * (P.canonicalHeight + Q.canonicalHeight) := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  set a : W.Point → ℕ → ℝ := fun X n ↦ ((2 ^ n) • X).naiveHeight / 4 ^ n with ha
  have hlim : Tendsto (fun n ↦ a (P + Q) n + a (P - Q) n - 2 * (a P n + a Q n)) atTop
      (𝓝 ((P + Q).canonicalHeight + (P - Q).canonicalHeight -
        2 * (P.canonicalHeight + Q.canonicalHeight))) :=
    (((tendsto_canonicalHeight _).add (tendsto_canonicalHeight _)).sub
      (((tendsto_canonicalHeight _).add (tendsto_canonicalHeight _)).const_mul 2))
  have hzero : Tendsto (fun n ↦ a (P + Q) n + a (P - Q) n - 2 * (a P n + a Q n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ ↦ C * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul C
    refine squeeze_zero_norm (fun n ↦ ?_) hg
    have hb := hC ((2 ^ n) • P) ((2 ^ n) • Q)
    rw [← smul_add, ← smul_sub] at hb
    have e : a (P + Q) n + a (P - Q) n - 2 * (a P n + a Q n) =
        (((2 ^ n) • (P + Q)).naiveHeight + ((2 ^ n) • (P - Q)).naiveHeight -
          2 * (((2 ^ n) • P).naiveHeight + ((2 ^ n) • Q).naiveHeight)) / 4 ^ n := by
      simp only [ha]; field_simp
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n),
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)]
    calc _ ≤ C := hb
      _ = C * (1 / 4) ^ n * 4 ^ n := by rw [one_div_pow]; field_simp
  have := tendsto_nhds_unique hlim hzero
  linarith

@[simp]
theorem canonicalHeight_zero : (0 : W.Point).canonicalHeight = 0 := by
  have := canonicalHeight_add_add_canonicalHeight_sub (0 : W.Point) 0
  simp only [add_zero, sub_zero] at this
  linarith

@[simp]
theorem canonicalHeight_neg (P : W.Point) : (-P).canonicalHeight = P.canonicalHeight := by
  have := canonicalHeight_add_add_canonicalHeight_sub (0 : W.Point) P
  simp only [zero_add, zero_sub, canonicalHeight_zero] at this
  linarith

theorem canonicalHeight_nsmul (P : W.Point) (n : ℕ) :
    (n • P).canonicalHeight = (n : ℝ) ^ 2 * P.canonicalHeight := by
  suffices h : ∀ n : ℕ, (n • P).canonicalHeight = (n : ℝ) ^ 2 * P.canonicalHeight ∧
      ((n + 1) • P).canonicalHeight = ((n + 1 : ℕ) : ℝ) ^ 2 * P.canonicalHeight from (h n).1
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hp := canonicalHeight_add_add_canonicalHeight_sub ((k + 1) • P) P
    rw [← succ_nsmul, show (k + 1) • P - P = k • P by rw [succ_nsmul, add_sub_cancel_right],
      ih.1, ih.2] at hp
    push_cast at hp ⊢
    linarith

/-- With the Northcott property, the canonical height vanishes exactly on torsion points. -/
theorem canonicalHeight_eq_zero_iff [Northcott (logHeight₁ (K := F))] (P : W.Point) :
    P.canonicalHeight = 0 ↔ IsOfFinAddOrder P := by
  constructor
  · intro h0
    obtain ⟨C, hC⟩ := abs_canonicalHeight_sub_naiveHeight_le (W := W)
    have hb : ∀ n : ℕ, n • P ∈ {Q : W.Point | Q.naiveHeight ≤ C} := by
      intro n
      have h1 := hC (n • P)
      rw [canonicalHeight_nsmul, h0, mul_zero, zero_sub, abs_neg] at h1
      exact (le_abs_self _).trans h1
    have := (finite_naiveHeight_le W C).to_subtype
    obtain ⟨m, n, hmn, he⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ ↦ (⟨n • P, hb n⟩ : {Q : W.Point | Q.naiveHeight ≤ C}))
    have he' : m • P = n • P := congrArg Subtype.val he
    rcases lt_or_gt_of_ne hmn with h | h
    · refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n - m, by omega, ?_⟩
      rw [show n • P = (n - m) • P + m • P by rw [← add_nsmul, Nat.sub_add_cancel h.le]] at he'
      simpa using (congrArg (· - m • P) he').symm
    · refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m - n, by omega, ?_⟩
      rw [show m • P = (m - n) • P + n • P by rw [← add_nsmul, Nat.sub_add_cancel h.le]] at he'
      simpa using congrArg (· - n • P) he'
  · intro h
    obtain ⟨n, hn, hP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
    have := canonicalHeight_nsmul P n
    rw [hP, canonicalHeight_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (by positivity)

/-- The Néron–Tate pairing `⟨P, Q⟩ = (ĥ(P + Q) − ĥ(P) − ĥ(Q)) / 2`. -/
noncomputable def neronTatePairing (P Q : W.Point) : ℝ :=
  ((P + Q).canonicalHeight - P.canonicalHeight - Q.canonicalHeight) / 2

omit [W.IsElliptic] in
theorem neronTatePairing_comm (P Q : W.Point) : neronTatePairing P Q = neronTatePairing Q P := by
  simp only [neronTatePairing, add_comm P Q]; ring

theorem neronTatePairing_self (P : W.Point) : neronTatePairing P P = P.canonicalHeight := by
  have := canonicalHeight_nsmul P 2
  rw [two_nsmul] at this
  simp only [neronTatePairing, this]; push_cast; ring

theorem neronTatePairing_add_left (P P' Q : W.Point) :
    neronTatePairing (P + P') Q = neronTatePairing P Q + neronTatePairing P' Q := by
  have h1 := canonicalHeight_add_add_canonicalHeight_sub (P + Q) P'
  have h2 := canonicalHeight_add_add_canonicalHeight_sub (P' + Q) P
  have h3 := canonicalHeight_add_add_canonicalHeight_sub Q (P - P')
  have h4 := canonicalHeight_add_add_canonicalHeight_sub P P'
  rw [show P + Q + P' = P + P' + Q by abel, show P + Q - P' = Q + (P - P') by abel] at h1
  rw [show P' + Q + P = P + P' + Q by abel, show P' + Q - P = Q - (P - P') by abel] at h2
  simp only [neronTatePairing]
  linarith

end WeierstrassCurve.Affine.Point
