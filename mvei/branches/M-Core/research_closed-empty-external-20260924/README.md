# M-Core — branch `research/closed-empty-external-20260924`

Lean sources from the branch `research/closed-empty-external-20260924` of the private repository `ShantiDraconis/M-Core`, commit `4d224f1dc036ec2c617af3b88be0083fee884cbc` (2026-09-24T08:39:27+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 7 — closed 4, conditional 0, open 0, proof error 1, not reached 2, no result 0.
* History: 20 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `46f785648aeccec2b69be8a3ab13325434953be9843cc5493e323ed085ce7d44`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/research_closed-empty-external-20260924/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.Real.E_one` | `lean/MCore/Real/E.lean`:9 | fechado |
| `MCore.Real.RealProducer.closed` | `lean/MCore/Real/RealProducer.lean`:11 | fechado |
| `MCore.Real.RealProducer.hasEvidence` | `lean/MCore/Real/RealProducer.lean`:17 | fechado |
| `MCore.Real.half_bounds` | `lean/MCore/Real/RealProducerWitness.lean`:7 | erro |
| `MCore.Real.indeterminacy_resolved` | `lean/MCore/Real/Resolution.lean`:44 | fechado |
| `MCore.Research.closed_empty_shape` | `lean/MCore/Research/FinalExternalBranch.lean`:29 | nao_alcancado |
| `MCore.Research.endpoint_does_not_issue` | `lean/MCore/Research/FinalExternalBranch.lean`:34 | nao_alcancado |
