# M-Core — branch `work/kernel-truncation-closure-20261005`

Lean sources from the branch `work/kernel-truncation-closure-20261005` of the private repository `ShantiDraconis/M-Core`, commit `a3c0a60083a01e6d2ecf93a87b68763f0c7f47cd` (2026-10-05T16:03:28+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 39 — closed 29, conditional 0, open 0, proof error 3, not reached 7, no result 0.
* History: 41 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `017dc036c997ad4da4a4c60dee70085bdb51dd5973ec819e34b2efa3903b5b5b`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/work_kernel-truncation-closure-20261005/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.ATKThreeRuleClosure.closureWitness_proves_target` | `lean/MCore/ATKThreeRuleClosure.lean`:138 | nao_alcancado |
| `MCore.ATKThreeRuleClosure.exhausted_closes` | `lean/MCore/ATKThreeRuleClosure.lean`:105 | nao_alcancado |
| `MCore.ATKThreeRuleClosure.found_closes` | `lean/MCore/ATKThreeRuleClosure.lean`:94 | nao_alcancado |
| `MCore.ATKThreeRuleClosure.loopMeasure_wellFounded` | `lean/MCore/ATKThreeRuleClosure.lean`:28 | nao_alcancado |
| `MCore.ATKThreeRuleClosure.loop_detected_closes` | `lean/MCore/ATKThreeRuleClosure.lean`:117 | nao_alcancado |
| `MCore.ATKThreeRuleClosure.materialProducer_proves_target` | `lean/MCore/ATKThreeRuleClosure.lean`:145 | nao_alcancado |
| `MCore.ATKThreeRuleClosure.open_does_not_close` | `lean/MCore/ATKThreeRuleClosure.lean`:128 | nao_alcancado |
| `MCore.Audit.green_action` | `lean/MCore/Audit/WorkQueue.lean`:30 | fechado |
| `MCore.Audit.historicalClaims_length` | `lean/MCore/Audit/HistoricalClaims.lean`:51 | fechado |
| `MCore.Audit.initialSummary_openMath` | `lean/MCore/Audit/StatusSummary.lean`:28 | fechado |
| `MCore.Audit.initialSummary_terminalSlots` | `lean/MCore/Audit/StatusSummary.lean`:24 | fechado |
| `MCore.Audit.initial_terminal_states_are_open` | `lean/MCore/Audit/MasterCertificate.lean`:24 | fechado |
| `MCore.Audit.openMath_action` | `lean/MCore/Audit/WorkQueue.lean`:26 | fechado |
| `MCore.Audit.open_math_registry_tracks_eight_frontiers` | `lean/MCore/Audit/MasterCertificate.lean`:32 | erro |
| `MCore.Audit.problem_registry_tracks_eight_slots` | `lean/MCore/Audit/MasterCertificate.lean`:28 | fechado |
| `MCore.Audit.terminalClaims_length` | `lean/MCore/Audit/MasterClaims.lean`:22 | fechado |
| `MCore.Audit.tracks_eight_terminal_producer_slots` | `lean/MCore/Audit/MasterCertificate.lean`:10 | fechado |
| `MCore.Canonical.certified_is_closed` | `lean/MCore/Canonical/Rules.lean`:14 | fechado |
| `MCore.Canonical.frozen_is_closed` | `lean/MCore/Canonical/Rules.lean`:17 | fechado |
| `MCore.Canonical.openMath_requires_material_producer` | `lean/MCore/Canonical/Rules.lean`:20 | fechado |
| `MCore.CanonicalClosure.atk_closedSearch_does_not_imply_external` | `lean/MCore/CanonicalClosureLaw.lean`:146 | fechado |
| `MCore.CanonicalClosure.exhausted_closes_material` | `lean/MCore/CanonicalClosureLaw.lean`:111 | fechado |
| `MCore.CanonicalClosure.found_closes_material` | `lean/MCore/CanonicalClosureLaw.lean`:106 | fechado |
| `MCore.CanonicalClosure.loopMeasure_wellFounded` | `lean/MCore/CanonicalClosureLaw.lean`:40 | erro |
| `MCore.CanonicalClosure.loop_closes_material` | `lean/MCore/CanonicalClosureLaw.lean`:117 | fechado |
| `MCore.ExternalPromotion.atk_status_alone_does_not_produce_external` | `lean/MCore/ExternalPromotionGuard.lean`:97 | fechado |
| `MCore.ExternalPromotion.external_certificate_gives_target` | `lean/MCore/ExternalPromotionGuard.lean`:109 | fechado |
| `MCore.ExternalPromotion.external_proved_requires_material` | `lean/MCore/ExternalPromotionGuard.lean`:77 | fechado |
| `MCore.ExternalPromotion.truncation_cannot_be_external_proved` | `lean/MCore/ExternalPromotionGuard.lean`:87 | erro |
| `MCore.KernelTruncation.target_closed_of_truncation_and_extractor` | `lean/MCore/KernelTruncationLaw.lean`:48 | fechado |
| `MCore.KernelTruncation.truncateAtMinimalBlocker_is_closed` | `lean/MCore/KernelTruncationLaw.lean`:36 | fechado |
| `MCore.KernelTruncation.truncated_certificate_terminal` | `lean/MCore/KernelTruncationLaw.lean`:61 | fechado |
| `MCore.KernelTruncation.truncation_claim_is_exactly_an_extractor` | `lean/MCore/KernelTruncationLaw.lean`:74 | fechado |
| `MCore.OpenMath.allTerminalFrontiers_length` | `lean/MCore/OpenMath/All.lean`:21 | fechado |
| `MCore.Problems.totalOpenTerminalSlots_eq_eight` | `lean/MCore/Problems/Registry.lean`:25 | fechado |
| `MCore.Reuse.iff_backward` | `lean/MCore/Reuse/Transport.lean`:16 | fechado |
| `MCore.Reuse.iff_forward` | `lean/MCore/Reuse/Transport.lean`:13 | fechado |
| `MCore.Reuse.implication_comp` | `lean/MCore/Reuse/Transport.lean`:8 | fechado |
| `MCore.Reuse.nonempty_map` | `lean/MCore/Reuse/Transport.lean`:2 | fechado |
