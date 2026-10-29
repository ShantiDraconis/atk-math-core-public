# M-Core — branch `atk/seven-terminal-parameter-law`

Lean sources from the branch `atk/seven-terminal-parameter-law` of the private repository `ShantiDraconis/M-Core`, commit `6406f0adf793208ce1236b07381a9e966343c184` (2026-10-06T21:05:26+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 98 — closed 41, conditional 0, open 0, proof error 0, not reached 57, no result 0.
* History: 18 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `a02ffbf2b721bae7e55f0de4afe8a1b71d831684964f6274a37a5abd1bedffbf`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_seven-terminal-parameter-law/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.FinalFail.RPA.COC_ne_CCO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:292 | nao_alcancado |
| `MCore.FinalFail.RPA.OCC_ne_COC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:291 | nao_alcancado |
| `MCore.FinalFail.RPA.OCO_ne_COO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:290 | nao_alcancado |
| `MCore.FinalFail.RPA.OOC_ne_OCO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:287 | nao_alcancado |
| `MCore.FinalFail.RPA.bridge_eq_math` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:63 | fechado |
| `MCore.FinalFail.RPA.cannot_confirm_from_closed_alone` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:50 | fechado |
| `MCore.FinalFail.RPA.cannot_confirm_from_open_alone` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:42 | fechado |
| `MCore.FinalFail.RPA.confirmed_projects_closed` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:93 | fechado |
| `MCore.FinalFail.RPA.confirmed_projects_open` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:86 | fechado |
| `MCore.FinalFail.RPA.dualEndpointState_iff_both_and_identity` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:145 | fechado |
| `MCore.FinalFail.RPA.dualEndpointState_iff_transition` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:135 | fechado |
| `MCore.FinalFail.RPA.dual_endpoint_eq_global_external` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:196 | fechado |
| `MCore.FinalFail.RPA.dual_endpoint_full_chain` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:177 | fechado |
| `MCore.FinalFail.RPA.dual_state_projects_closed` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:170 | fechado |
| `MCore.FinalFail.RPA.dual_state_projects_open` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:163 | fechado |
| `MCore.FinalFail.RPA.eval_C` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:235 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_CC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:247 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_CCC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:253 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_CCO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:271 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_CO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:244 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_COC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:268 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_COO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:262 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_O` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:232 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_OC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:241 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_OCC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:265 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_OCO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:259 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_OO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:238 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_OOC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:256 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_OOCC` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:274 | nao_alcancado |
| `MCore.FinalFail.RPA.eval_OOO` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:250 | nao_alcancado |
| `MCore.FinalFail.RPA.finalRoot_eq_globalExternalCertificate` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:73 | fechado |
| `MCore.FinalFail.RPA.free_closed_plus_closed` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:45 | nao_alcancado |
| `MCore.FinalFail.RPA.free_open_closed_closed` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:53 | nao_alcancado |
| `MCore.FinalFail.RPA.free_open_open_closed` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:49 | nao_alcancado |
| `MCore.FinalFail.RPA.free_open_plus_closed` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:37 | nao_alcancado |
| `MCore.FinalFail.RPA.free_open_plus_open` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:41 | nao_alcancado |
| `MCore.FinalFail.RPA.free_two_two_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:57 | nao_alcancado |
| `MCore.FinalFail.RPA.full_eq_dualEndpointState` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:152 | nao_alcancado |
| `MCore.FinalFail.RPA.full_eq_finalRoot` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:164 | nao_alcancado |
| `MCore.FinalFail.RPA.full_eq_globalExternalCertificate` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:170 | nao_alcancado |
| `MCore.FinalFail.RPA.full_eq_math` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:158 | nao_alcancado |
| `MCore.FinalFail.RPA.full_maximal_chain` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:176 | nao_alcancado |
| `MCore.FinalFail.RPA.global_certificate_contains_both_endpoints` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:202 | fechado |
| `MCore.FinalFail.RPA.global_external_no_escape` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:99 | fechado |
| `MCore.FinalFail.RPA.join_closed_idempotent` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:128 | nao_alcancado |
| `MCore.FinalFail.RPA.join_closed_open_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:136 | nao_alcancado |
| `MCore.FinalFail.RPA.join_full_absorbing_left` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:140 | nao_alcancado |
| `MCore.FinalFail.RPA.join_full_absorbing_right` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:144 | nao_alcancado |
| `MCore.FinalFail.RPA.join_open_closed_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:132 | nao_alcancado |
| `MCore.FinalFail.RPA.join_open_idempotent` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:124 | nao_alcancado |
| `MCore.FinalFail.RPA.math_eq_finalRoot` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:68 | fechado |
| `MCore.FinalFail.RPA.normalize_CCC_closed` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:321 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_CCO_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:316 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_COC_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:314 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_COO_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:310 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_OCC_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:312 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_OCO_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:308 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_OOC_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:304 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_OOO_open` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:318 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_closed_sq` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:96 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_dual` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:88 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_empty` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:76 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_open_closed_closed` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:104 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_open_open_closed` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:100 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_open_sq` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:92 | nao_alcancado |
| `MCore.FinalFail.RPA.normalize_two_two_full` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:108 | nao_alcancado |
| `MCore.FinalFail.RPA.openEndpointSide_ne_closedEndpointSide` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:122 | fechado |
| `MCore.FinalFail.RPA.open_and_closed_coexist` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:155 | fechado |
| `MCore.FinalFail.RPA.open_closed_eq_bridge` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:58 | fechado |
| `MCore.FinalFail.RPA.ordered_FULL_eq_globalExternalCertificate` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:333 | nao_alcancado |
| `MCore.FinalFail.RPA.ordered_OOCC_is_freeFull22` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:324 | nao_alcancado |
| `MCore.FinalFail.RPA.ordered_OOCC_normalizes_FULL` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:329 | nao_alcancado |
| `MCore.FinalFail.RPA.three_closed_one_two_same_multiplicity` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:299 | nao_alcancado |
| `MCore.FinalFail.RPA.three_open_two_one_same_multiplicity` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:293 | nao_alcancado |
| `MCore.FinalFail.RPA.transition_iff_source_target_identity` | `lean/MCore/FinalFail/RPATransitionDuality.lean`:32 | fechado |
| `MCore.FinalFail.RPA.wordsUpToThree_count` | `lean/MCore/FinalFail/RPAEndpointLattice.lean`:283 | nao_alcancado |
| `MCore.FinalFail.SevenTerminalParameterLaw.beal_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:265 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.bsd_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:216 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.bsd_rank_defect_zero_iff` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:194 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.global_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:350 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.global_projects_all` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:339 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.hodge_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:171 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.navierStokes_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:147 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_bealCertifies_iff_bealRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:260 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_bsdCertifies_iff_bsdRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:199 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_certifies_iff_refutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:61 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_globalCertifies_iff_globalRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:299 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_hodgeCertifies_iff_hodgeRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:166 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_navierStokesCertifies_iff_navierStokesRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:141 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_pVsNPCertifies_iff_pVsNPRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:234 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_riemannCertifies_iff_riemannRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:90 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.not_yangMillsCertifies_iff_yangMillsRefutes` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:117 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.pVsNP_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:239 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.refutes_not_certifies` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:54 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.riemann_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:95 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.riemann_defect_zero_iff_critical_line` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:84 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.terminalMode_total` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:40 | fechado |
| `MCore.FinalFail.SevenTerminalParameterLaw.yangMills_cert_refute_disjoint` | `lean/MCore/FinalFail/SevenTerminalParameterLaw.lean`:122 | fechado |
