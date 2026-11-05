# M-Core — branch `atk/global-closed-scope-20261007`

Lean sources from the branch `atk/global-closed-scope-20261007` of the private repository `ShantiDraconis/M-Core`, commit `6ac1067111b0779604315fdbc69fede34c6c911c` (2026-10-07T17:24:55+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 13 — closed 3, conditional 0, open 1, proof error 0, not reached 9, no result 0.
* History: 10 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `c3aebafdc358374bc7b867c2a694d27a1122a9529e28e30f12f3613a7b9bf61d`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_global-closed-scope-20261007/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.FinalFail.ClosedScope.certify` | `lean/MCore/FinalFail/GlobalClosedScope.lean`:21 | fechado |
| `MCore.FinalFail.ClosedScope.certify_cons` | `lean/MCore/FinalFail/GlobalClosedScope.lean`:33 | fechado |
| `MCore.FinalFail.ClosedScope.entry_is_closed` | `lean/MCore/FinalFail/GlobalClosedScope.lean`:11 | fechado |
| `MCore.FinalFail.ClosedScope.materializedClosedScope_certified` | `lean/MCore/FinalFail/GlobalClosedScope.lean`:65 | aberto-sorry |
| `MCore.FinalFail.ClosedScope.ymConditionalClosedWitness` | `lean/MCore/FinalFail/GlobalClosedScope.lean`:58 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.declaredSATCorrect_iff_no_semanticMismatch` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:34 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.decode_verify_iff_satBits` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:23 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.integrated_phase_bridge` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:43 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.no_semanticMismatch_iff_match` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:31 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.physical_read_witness_correct` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:37 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.physical_source_end_preserved` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:40 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.verifier_correct` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:17 | nao_alcancado |
| `MCore.FinalFail.RecoveredClosedFragments.witness_guess_phase_polynomial` | `lean/MCore/FinalFail/RecoveredClosedFragments.lean`:14 | nao_alcancado |
