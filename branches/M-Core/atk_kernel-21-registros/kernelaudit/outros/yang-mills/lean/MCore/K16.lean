import MCore.K15

namespace MCore

/-- K16 refines the scientific program into typed, non-circular obligations.
    The fields are propositions to be established by a YM4 realization; their
    presence in this structure is not evidence that they hold. -/
structure K16ScientificObligations where
  RGControl : Prop
  IRStability : Prop
  ConnectedDecay : Prop
  UVUniformity : Prop
  IRVolumeUniformity : Prop

/-- Explicit conjunction of the five independent scientific obligations. -/
def K16ObligationsHold (O : K16ScientificObligations) : Prop :=
  O.RGControl ∧ O.IRStability ∧ O.ConnectedDecay ∧
  O.UVUniformity ∧ O.IRVolumeUniformity

/-- Mapping K16 obligations into the K15 vocabulary is itself explicit data.
    This prevents the desired clustering conclusion from being hidden in the
    definitions of RG or infrared stability. -/
def K16RefinesK15
    (O : K16ScientificObligations)
    (P : K15ClusteringProgram) : Prop :=
  (O.RGControl → P.NonperturbativeRG) ∧
  (O.IRStability → P.InfraredStability) ∧
  (O.ConnectedDecay → P.ClusterExpansion) ∧
  (O.UVUniformity → P.CutoffUniformity) ∧
  (O.IRVolumeUniformity → P.VolumeUniformity)

/-- Mechanical assembly only: if all K16 obligations hold and each refines its
    corresponding K15 node, the K15 program is complete. -/
theorem k16_refinement_completes_k15
    {O : K16ScientificObligations}
    {P : K15ClusteringProgram}
    (hO : K16ObligationsHold O)
    (hR : K16RefinesK15 O P) :
    K15ProgramComplete P := by
  rcases hO with ⟨hRG, hIR, hDecay, hUV, hVol⟩
  rcases hR with ⟨rRG, rIR, rDecay, rUV, rVol⟩
  exact ⟨rRG hRG, rIR hIR, rDecay hDecay, rUV hUV, rVol hVol⟩

/-- Full downstream composition remains conditional on the scientific
    obligations and both previously exposed bridges. -/
theorem k16_obligations_imply_mass_gap
    {O : K16ScientificObligations}
    {P : K15ClusteringProgram}
    {C : K14UniformExpClusteringData}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {S : K14GapScale D}
    (hO : K16ObligationsHold O)
    (hR : K16RefinesK15 O P)
    (toClustering : K15ProgramToClusteringBridge P C)
    (toGap : K14ClusteringToMassGapBridge C D H S) :
    ∃ delta : D.Scale, K14MassGap D H S delta :=
  k15_complete_program_implies_mass_gap toClustering toGap
    (k16_refinement_completes_k15 hO hR)

theorem k16_target_still_open :
    k6_dependency.target.status = .openBridge :=
  k15_target_still_open

theorem k16_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k15_no_promotion

end MCore
