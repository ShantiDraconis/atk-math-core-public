# M-Core — branch `atk/proof-engine-rncb`

Lean sources from the branch `atk/proof-engine-rncb` of the private repository `ShantiDraconis/M-Core`, commit `348d3577de39cfa3688332699256a9f0c4e97ba9` (2026-09-26T09:29:57+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 8 — closed 8, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 29 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `3e820c32698b3d067a26b3b6523fbc8eb701e62dd842cb8baea372355a21d779`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_proof-engine-rncb/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.ProofEngine.Producer.comp_apply` | `lean/MCore/ProofEngine/Composition.lean`:17 | fechado |
| `MCore.ProofEngine.Producer.id_run` | `lean/MCore/ProofEngine/Composition.lean`:14 | fechado |
| `MCore.ProofEngine.conflict_cannot_issue` | `lean/MCore/ProofEngine/ScientificBoundary.lean`:18 | fechado |
| `MCore.ProofEngine.conflict_not_claimable` | `lean/MCore/ProofEngine/Obligation.lean`:27 | fechado |
| `MCore.ProofEngine.fourth_attempt_escalates` | `lean/MCore/ProofEngine/Retry.lean`:5 | fechado |
| `MCore.ProofEngine.no_layer_skip` | `lean/MCore/ProofEngine/Promotion.lean`:25 | fechado |
| `MCore.ProofEngine.unknown_cannot_issue` | `lean/MCore/ProofEngine/ScientificBoundary.lean`:14 | fechado |
| `MCore.ProofEngine.unknown_not_claimable` | `lean/MCore/ProofEngine/Obligation.lean`:23 | fechado |
