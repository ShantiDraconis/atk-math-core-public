import MCore.MaterialMath.TransverseContraction

namespace MCore.MaterialMath

noncomputable section

namespace TriNumber

/--
Canonical zero-sum embedding of one real scalar defect into the transverse
three-phase plane.
-/
def scalarDefectEmbedding (d : ℝ) : TriNumber ℝ where
  manifest := d
  crossing := -d
  seed := 0

theorem scalarDefectEmbedding_zeroSum (d : ℝ) :
    ZeroSum (scalarDefectEmbedding d) := by
  simp [ZeroSum, total, scalarDefectEmbedding]

/--
Exact energy identity for the scalar embedding:
phaseEnergy(d,-d,0) = 6 d^2.
-/
theorem phaseEnergy_scalarDefectEmbedding (d : ℝ) :
    phaseEnergy (scalarDefectEmbedding d) = 6 * d^2 := by
  simp [phaseEnergy, spread, scalarDefectEmbedding]
  ring

/-- The scalar embedding is balanced exactly when the original defect is zero. -/
theorem scalarDefectEmbedding_balanced_iff (d : ℝ) :
    Balanced (scalarDefectEmbedding d) ↔ d = 0 := by
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    simp [scalarDefectEmbedding] at h1 h2
    linarith
  · intro h
    subst d
    simp [Balanced, scalarDefectEmbedding]

/--
Vanishing of a scalar defect implies vanishing of the associated tri-state
phase energy.
-/
theorem phaseEnergy_scalarDefectEmbedding_tendsto_zero
    (d : Nat → ℝ)
    (hd : Filter.Tendsto d Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => phaseEnergy (scalarDefectEmbedding (d n)))
      Filter.atTop (nhds 0) := by
  have hsq :
      Filter.Tendsto
        (fun n => (d n)^2)
        Filter.atTop (nhds (0^2 : ℝ)) :=
    hd.pow 2
  have hmul :
      Filter.Tendsto
        (fun n => 6 * (d n)^2)
        Filter.atTop (nhds (6 * (0^2 : ℝ))) :=
    tendsto_const_nhds.mul hsq
  simpa [phaseEnergy_scalarDefectEmbedding] using hmul

/--
The embedded phase energy vanishes pointwise exactly when the original scalar
defect vanishes.
-/
theorem phaseEnergy_scalarDefectEmbedding_eq_zero_iff (d : ℝ) :
    phaseEnergy (scalarDefectEmbedding d) = 0 ↔ d = 0 := by
  rw [phaseEnergy_scalarDefectEmbedding]
  constructor
  · intro h
    have : d^2 = 0 := by nlinarith
    exact sq_eq_zero_iff.mp this
  · intro h
    subst d
    norm_num

/--
Thus every scalar F1 problem has a canonical faithful tri-state presentation:
the tri-state energy vanishes iff the original scalar defect vanishes.
-/
def scalarDefectVanishingLaw
    (d : Nat → ℝ)
    (hd : Filter.Tendsto d Filter.atTop (nhds 0)) :
    VanishingLaw
      (fun n => phaseEnergy (scalarDefectEmbedding (d n))) where
  nonneg := fun n => spread_nonneg _
  tendsToZero := phaseEnergy_scalarDefectEmbedding_tendsto_zero d hd

#print axioms MCore.MaterialMath.TriNumber.phaseEnergy_scalarDefectEmbedding
#print axioms MCore.MaterialMath.TriNumber.phaseEnergy_scalarDefectEmbedding_eq_zero_iff

end TriNumber

end

end MCore.MaterialMath
