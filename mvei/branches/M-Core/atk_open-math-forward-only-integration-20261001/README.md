# M-Core — branch `atk/open-math-forward-only-integration-20261001`

Lean sources from the branch `atk/open-math-forward-only-integration-20261001` of the private repository `ShantiDraconis/M-Core`, commit `d4cc8e5b79b9f3978d4ef5789da227ced0613488` (2026-10-01T20:20:56+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 114 — closed 20, conditional 0, open 0, proof error 2, not reached 92, no result 0.
* History: 125 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `6cf01a34461ae4b0ae264b9a38cb6371ad428797ef1ed29e8be51de977c9c700`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_open-math-forward-only-integration-20261001/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.FinalFail.Semantic.ns_resolution_of_breakdown` | `lean/MCore/FinalFail/Semantic/NavierStokes.lean`:67 | erro |
| `MCore.FinalFail.Semantic.ns_resolution_of_stabilization` | `lean/MCore/FinalFail/Semantic/NavierStokes.lean`:55 | erro |
| `MCore.MaterialMath.BilateralOpenMathProblem.both_is_inconsistent` | `lean/MCore/MaterialMath/GlobalOpenMathLogic.lean`:80 | nao_alcancado |
| `MCore.MaterialMath.BilateralOpenMathProblem.negative_outcome` | `lean/MCore/MaterialMath/GlobalOpenMathLogic.lean`:74 | nao_alcancado |
| `MCore.MaterialMath.BilateralOpenMathProblem.positive_outcome` | `lean/MCore/MaterialMath/GlobalOpenMathLogic.lean`:68 | nao_alcancado |
| `MCore.MaterialMath.FormalRatio.zeroOverZero_not_evaluable` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:231 | fechado |
| `MCore.MaterialMath.SingularResolution.rotate_three` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:162 | nao_alcancado |
| `MCore.MaterialMath.TerminalMaterialAdapters.toGlobalPositiveRoot` | `lean/MCore/MaterialMath/OperatorLaws.lean`:226 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.D_cubic_polynomial` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:81 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.L_polynomial_in_D` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:91 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.L_sector_law` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:96 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.Peq_add_Ptr` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:63 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.Peq_idempotent` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:48 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.Ptr_idempotent` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:55 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.R_cubic_identity` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:76 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.balancedProjection_is_balanced` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:22 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.balancedProjection_rotate` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:73 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.balanced_add_fluctuation` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:36 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.balanced_and_zeroSum_eq_zero` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:85 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.balanced_rotate_iff` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:171 | fechado |
| `MCore.MaterialMath.TriNumber.balanced_transverse_decomposition_unique` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:103 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.basis_cycle` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:196 | fechado |
| `MCore.MaterialMath.TriNumber.canonicalMaterialConstants_values` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:27 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.continuous_fromProduct` | `lean/MCore/MaterialMath/TriCyclicTopology.lean`:36 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.continuous_toProduct` | `lean/MCore/MaterialMath/TriCyclicTopology.lean`:31 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.cyclicMul_add_left` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:103 | fechado |
| `MCore.MaterialMath.TriNumber.cyclicMul_assoc` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:99 | fechado |
| `MCore.MaterialMath.TriNumber.cyclicMul_comm` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:95 | fechado |
| `MCore.MaterialMath.TriNumber.cyclicMul_one` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:85 | fechado |
| `MCore.MaterialMath.TriNumber.equilibrium_transverse_intersection_zero` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:68 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.euclideanSquare_nonneg` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:29 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.euclideanSquare_smul_neg_three` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:62 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.ext` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:23 | fechado |
| `MCore.MaterialMath.TriNumber.fluctuation_eq_zero_iff_balanced` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:52 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.fluctuation_rotate` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:79 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.fluctuation_zeroSum` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:31 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.fromProduct_toProduct` | `lean/MCore/MaterialMath/TriCyclicTopology.lean`:14 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.geometricTransverseTrajectory_balancedProjection` | `lean/MCore/MaterialMath/TransverseContraction.lean`:19 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_kernel_rejects_both` | `lean/MCore/MaterialMath/GlobalMaterialTheoremV2.lean`:82 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_kernel_with_bilateral_negative` | `lean/MCore/MaterialMath/GlobalMaterialTheoremV2.lean`:75 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_kernel_with_bilateral_positive` | `lean/MCore/MaterialMath/GlobalMaterialTheoremV2.lean`:64 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_normalized_gap_constant` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:108 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_profile_energy_law` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:134 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_scalar_defect_energy` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:116 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_scalar_vanishing_transport` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:122 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.global_spread_radius_law` | `lean/MCore/MaterialMath/GlobalMaterialTheorem.lean`:102 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.normalized_transverse_energy` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:79 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.one_cyclicMul` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:90 | fechado |
| `MCore.MaterialMath.TriNumber.phaseDerivative_cubic_closure` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:113 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseDerivative_eq_zero_iff_balanced` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:41 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseDerivative_rotate` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:20 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_geometricTransverseTrajectory` | `lean/MCore/MaterialMath/TransverseContraction.lean`:52 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_geometricTransverseTrajectory_tendsto_zero` | `lean/MCore/MaterialMath/TransverseContraction.lean`:69 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_profiledTransverseTrajectory` | `lean/MCore/MaterialMath/ProfiledTransverseDecay.lean`:20 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_profiledTransverseTrajectory_tendsto_zero` | `lean/MCore/MaterialMath/ProfiledTransverseDecay.lean`:35 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_rotate` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:116 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_scalarDefectEmbedding` | `lean/MCore/MaterialMath/ScalarDefectEmbedding.lean`:21 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_scalarDefectEmbedding_eq_zero_iff` | `lean/MCore/MaterialMath/ScalarDefectEmbedding.lean`:64 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseEnergy_scalarDefectEmbedding_tendsto_zero` | `lean/MCore/MaterialMath/ScalarDefectEmbedding.lean`:42 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseLaplacianEnergy_of_zeroSum` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:70 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseLaplacian_eq_neg_three_fluctuation` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:27 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseLaplacian_eq_secondDerivative_plus_three_first` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:102 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseLaplacian_eq_zero_iff_balanced` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:35 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseLaplacian_of_balanced` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:56 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseLaplacian_rotate` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:25 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseLaplacian_zeroSum_eigen` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:16 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.phaseSpectralGap_pos` | `lean/MCore/MaterialMath/TriCyclicSpectral.lean`:12 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.positive_spread_implies_not_balanced` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:104 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.rotate_cyclicMul` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:107 | fechado |
| `MCore.MaterialMath.TriNumber.scalarDefectEmbedding_balanced_iff` | `lean/MCore/MaterialMath/ScalarDefectEmbedding.lean`:30 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.scalarDefectEmbedding_zeroSum` | `lean/MCore/MaterialMath/ScalarDefectEmbedding.lean`:17 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_add_balanced_left` | `lean/MCore/MaterialMath/TransverseContraction.lean`:37 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_balancedProjection` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:46 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_eq_three_transverseRadiusSq` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:79 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_eq_zero_iff_balanced` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:74 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_fluctuation` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:41 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_identity` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:12 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_nonneg` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:68 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_of_zeroSum` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:19 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_product_eq_torsion_plus_transverseInner` | `lean/MCore/MaterialMath/TorsionEnergyLaw.lean`:14 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.spread_rotate` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:161 | fechado |
| `MCore.MaterialMath.TriNumber.spread_smul` | `lean/MCore/MaterialMath/TransverseContraction.lean`:29 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.three_torsion_sq_eq_spread_product_iff` | `lean/MCore/MaterialMath/TorsionEnergyLaw.lean`:37 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.three_torsion_sq_le_spread_product` | `lean/MCore/MaterialMath/TorsionEnergyLaw.lean`:30 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.toProduct_fromProduct` | `lean/MCore/MaterialMath/TriCyclicTopology.lean`:19 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.torsion_balanced_left` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:45 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.torsion_balanced_right` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:59 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.torsion_fluctuation` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:68 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.torsion_rotate_both` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:148 | fechado |
| `MCore.MaterialMath.TriNumber.torsion_self` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:138 | fechado |
| `MCore.MaterialMath.TriNumber.torsion_skew` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:143 | fechado |
| `MCore.MaterialMath.TriNumber.torsion_sq_le_one_of_spread_three` | `lean/MCore/MaterialMath/TorsionEnergyLaw.lean`:54 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.total_balancedProjection` | `lean/MCore/MaterialMath/TriCyclicDecomposition.lean`:26 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.total_phaseDerivative` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:30 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.total_phaseLaplacian` | `lean/MCore/MaterialMath/TriCyclicCalculus.lean`:35 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.total_rotate` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:115 | fechado |
| `MCore.MaterialMath.TriNumber.transverseRadiusSq_rotate` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:86 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.triCyclic_F1_F2_kernel` | `lean/MCore/MaterialMath/TransverseContraction.lean`:109 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.zeroSum_and_zeroSpread_eq_zero` | `lean/MCore/MaterialMath/TriCyclicGeometry.lean`:35 | nao_alcancado |
| `MCore.MaterialMath.TriNumber.zeroSum_rotate_iff` | `lean/MCore/MaterialMath/TriCyclicAlgebra.lean`:181 | fechado |
| `MCore.MaterialMath.TwoSidedMaterialResolution.both_material_routes_contradict` | `lean/MCore/MaterialMath/TwoSidedMaterialResolution.lean`:52 | fechado |
| `MCore.MaterialMath.TwoSidedMaterialResolution.close_negative` | `lean/MCore/MaterialMath/TwoSidedMaterialResolution.lean`:27 | fechado |
| `MCore.MaterialMath.TwoSidedMaterialResolution.close_positive` | `lean/MCore/MaterialMath/TwoSidedMaterialResolution.lean`:19 | fechado |
| `MCore.MaterialMath.TwoSidedMaterialResolution.materiallyResolved_elim` | `lean/MCore/MaterialMath/TwoSidedMaterialResolution.lean`:43 | fechado |
| `MCore.MaterialMath.balanced_fixed_by_rotate` | `lean/MCore/MaterialMath/OperatorLaws.lean`:78 | nao_alcancado |
| `MCore.MaterialMath.canonicalGlobalQuestionProtocol_complete` | `lean/MCore/MaterialMath/GlobalOpenMathLogic.lean`:149 | nao_alcancado |
| `MCore.MaterialMath.close_from_material_audit` | `lean/MCore/MaterialMath/GlobalOpenMathLogic.lean`:118 | nao_alcancado |
| `MCore.MaterialMath.materialKernelVersion_eq_one` | `lean/MCore/MaterialMath/MaterialKernel.lean`:23 | nao_alcancado |
| `MCore.MaterialMath.rotate_energy_preserving` | `lean/MCore/MaterialMath/OperatorLaws.lean`:72 | nao_alcancado |
| `MCore.MaterialMath.rotate_fixed_iff_balanced` | `lean/MCore/MaterialMath/OperatorLaws.lean`:90 | nao_alcancado |
| `MCore.MaterialMath.rotate_periodic3` | `lean/MCore/MaterialMath/OperatorLaws.lean`:66 | nao_alcancado |
| `MCore.MaterialMath.triState_closes_global_root` | `lean/MCore/MaterialMath/TriStateTerminalClosure.lean`:40 | nao_alcancado |
| `MCore.MaterialMath.triState_fixed_iff_balanced` | `lean/MCore/MaterialMath/TriStateTerminalClosure.lean`:91 | nao_alcancado |
| `MCore.MaterialMath.triState_three_phase_orbit` | `lean/MCore/MaterialMath/TriStateTerminalClosure.lean`:82 | nao_alcancado |
