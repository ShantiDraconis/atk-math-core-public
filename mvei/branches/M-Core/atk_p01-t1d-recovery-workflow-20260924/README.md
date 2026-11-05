# M-Core — branch `atk/p01-t1d-recovery-workflow-20260924`

Lean sources from the branch `atk/p01-t1d-recovery-workflow-20260924` of the private repository `ShantiDraconis/M-Core`, commit `514a9500203950d2c4b46ab77aa5eab3ee461d4c` (2026-09-24T19:30:03+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 15 — closed 13, conditional 0, open 0, proof error 0, not reached 1, no result 1.
* History: 28 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `d6de1b4548de0341112ff424ee19a084781f0004463595fa1752da737670ca1b`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_p01-t1d-recovery-workflow-20260924/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.P01ComponentFailProof.all_legacy_components_are_trivially_inhabited` | `imports/pnp/cf885872/lean/MCore/Real/P01ComponentFailProof.lean`:64 | fechado |
| `MCore.Real.P01ComponentFailProof.parser_component_is_trivially_inhabited` | `imports/pnp/cf885872/lean/MCore/Real/P01ComponentFailProof.lean`:40 | fechado |
| `MCore.Real.P01ComponentFailProof.verifier_component_is_trivially_inhabited` | `imports/pnp/cf885872/lean/MCore/Real/P01ComponentFailProof.lean`:56 | fechado |
| `MCore.Real.P01ComponentFailProof.witness_guess_component_is_trivially_inhabited` | `imports/pnp/cf885872/lean/MCore/Real/P01ComponentFailProof.lean`:48 | fechado |
| `MCore.Real.P01ComponentFailProof.zero_bound_poly` | `imports/pnp/cf885872/lean/MCore/Real/P01ComponentFailProof.lean`:34 | nao_checado |
| `MCore.Real.P01FullVerifierReadWitnessLocal.physicalWitnessRead_correct` | `imports/pnp/cf885872/lean/MCore/Real/P01FullVerifierReadWitnessLocal.lean`:15 | fechado |
| `MCore.Real.P01FullVerifierReverseDecoderGap.reverse_decoder_length_from_correct` | `imports/pnp/cf885872/lean/MCore/Real/P01FullVerifierReverseDecoderGap.lean`:25 | nao_alcancado |
| `MCore.Real.P01FullVerifierShuttleReturn.execMoves_append` | `imports/pnp/cf885872/lean/MCore/Real/P01FullVerifierShuttleReturn.lean`:10 | fechado |
| `MCore.Real.P01FullVerifierShuttleReturn.witness_roundTrip_exec` | `imports/pnp/cf885872/lean/MCore/Real/P01FullVerifierShuttleReturn.lean`:19 | fechado |
| `MCore.Real.P01IntegratedNTMFrontier.construction_only_closes` | `imports/pnp/cf885872/lean/MCore/Real/P01IntegratedNTMFrontier.lean`:46 | fechado |
| `MCore.Real.P01RecursiveFiniteControlFrontier.frame_machine_has_canonical_machine_type` | `imports/pnp/cf885872/lean/MCore/Real/P01RecursiveFiniteControlFrontier.lean`:43 | fechado |
| `MCore.Real.P01RecursiveFiniteControlFrontier.frame_protocol_source_closed` | `imports/pnp/cf885872/lean/MCore/Real/P01RecursiveFiniteControlFrontier.lean`:51 | fechado |
| `MCore.Real.P01RecursiveFiniteControlFrontier.p01_frontier_implies_target` | `imports/pnp/cf885872/lean/MCore/Real/P01RecursiveFiniteControlFrontier.lean`:84 | fechado |
| `MCore.Real.P01RecursiveFiniteControlFrontier.p01_promotion_requires_canonical_closure` | `imports/pnp/cf885872/lean/MCore/Real/P01RecursiveFiniteControlFrontier.lean`:70 | fechado |
| `MCore.Real.P01RecursiveFiniteControlFrontier.recursive_parser_implies_legacy_parser` | `imports/pnp/cf885872/lean/MCore/Real/P01RecursiveFiniteControlFrontier.lean`:57 | fechado |
