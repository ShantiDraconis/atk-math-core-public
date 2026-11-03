import MCore.MaterialMath.TriCyclicGeometry
import MCore.MaterialMath.OperatorLaws

namespace MCore.MaterialMath

noncomputable section

namespace TriNumber

/-- The intrinsic transverse eigenvalue magnitude of the three-phase Laplacian. -/
def phaseSpectralGap : ℝ := 3

theorem phaseSpectralGap_pos :
    0 < phaseSpectralGap := by
  norm_num [phaseSpectralGap]

/-- On the zero-sum plane, the cyclic Laplacian acts as multiplication by -3. -/
theorem phaseLaplacian_zeroSum_eigen
    (x : TriNumber ℝ)
    (h : ZeroSum x) :
    phaseLaplacian x = smul (-3 : ℝ) x := by
  rcases x with ⟨m, c, s⟩
  simp [ZeroSum, total] at h
  apply TriNumber.ext <;>
    simp [phaseLaplacian, smul] <;>
    linarith

/-- For every state, the Laplacian sees only the transverse fluctuation. -/
theorem phaseLaplacian_eq_neg_three_fluctuation
    (x : TriNumber ℝ) :
    phaseLaplacian x = smul (-3 : ℝ) (fluctuation x) := by
  apply TriNumber.ext <;>
    simp [phaseLaplacian, smul, fluctuation, mean, total] <;>
    ring

/-- Balanced states form the zero eigenspace. -/
theorem phaseLaplacian_eq_zero_iff_balanced
    (x : TriNumber ℝ) :
    phaseLaplacian x = { manifest := 0, crossing := 0, seed := 0 } ↔
      Balanced x := by
  constructor
  · intro h
    have hf :
        smul (-3 : ℝ) (fluctuation x) =
          { manifest := 0, crossing := 0, seed := 0 } := by
      rw [← phaseLaplacian_eq_neg_three_fluctuation x]
      exact h
    have hm := congrArg TriNumber.manifest hf
    have hc := congrArg TriNumber.crossing hf
    have hs := congrArg TriNumber.seed hf
    simp [smul] at hm hc hs
    have hz :
        fluctuation x =
          { manifest := 0, crossing := 0, seed := 0 } := by
      apply TriNumber.ext <;> assumption
    exact (fluctuation_eq_zero_iff_balanced x).1 hz
  · exact phaseLaplacian_of_balanced

/-- Squared Laplacian energy. -/
def phaseLaplacianEnergy (x : TriNumber ℝ) : ℝ :=
  euclideanSquare (phaseLaplacian x)

/-- Scaling a tri-state by -3 multiplies its Euclidean square by 9. -/
theorem euclideanSquare_smul_neg_three
    (x : TriNumber ℝ) :
    euclideanSquare (smul (-3 : ℝ) x) = 9 * euclideanSquare x := by
  rcases x with ⟨m, c, s⟩
  simp [euclideanSquare, smul]
  ring

/-- Exact transverse spectral-energy law. -/
theorem phaseLaplacianEnergy_of_zeroSum
    (x : TriNumber ℝ)
    (h : ZeroSum x) :
    phaseLaplacianEnergy x = 9 * euclideanSquare x := by
  unfold phaseLaplacianEnergy
  rw [phaseLaplacian_zeroSum_eigen x h]
  exact euclideanSquare_smul_neg_three x

/-- Normalized transverse states have exact Laplacian energy 9. -/
theorem normalized_transverse_energy
    (x : TriNumber ℝ)
    (hz : ZeroSum x)
    (hn : euclideanSquare x = 1) :
    phaseLaplacianEnergy x = 9 := by
  rw [phaseLaplacianEnergy_of_zeroSum x hz, hn]
  norm_num

/-- A genuine internal F2 gap law of the tri-cyclic material kernel.
This concerns only normalized transverse material states. -/
def normalizedTransverseGapLaw :
    GapLaw
      (TriNumber ℝ)
      (fun x => ZeroSum x ∧ euclideanSquare x = 1)
      phaseLaplacianEnergy where
  gap := 9
  gap_pos := by norm_num
  lower := by
    intro x hx
    rcases hx with ⟨hz, hn⟩
    rw [normalized_transverse_energy x hz hn]

/-- Exact operator polynomial relation L = D² + 3D. -/
theorem phaseLaplacian_eq_secondDerivative_plus_three_first
    (x : TriNumber ℝ) :
    phaseLaplacian x =
      add
        (phaseDerivative (phaseDerivative x))
        (smul (3 : ℝ) (phaseDerivative x)) := by
  apply TriNumber.ext <;>
    simp [phaseLaplacian, phaseDerivative, add, smul] <;>
    ring

/-- Cubic closure forced by R³ = I:
D³ + 3D² + 3D = 0. -/
theorem phaseDerivative_cubic_closure
    (x : TriNumber ℝ) :
    add
      (phaseDerivative (phaseDerivative (phaseDerivative x)))
      (add
        (smul (3 : ℝ) (phaseDerivative (phaseDerivative x)))
        (smul (3 : ℝ) (phaseDerivative x))) =
      { manifest := 0, crossing := 0, seed := 0 } := by
  apply TriNumber.ext <;>
    simp [phaseDerivative, add, smul] <;>
    ring

end TriNumber

end

end MCore.MaterialMath
