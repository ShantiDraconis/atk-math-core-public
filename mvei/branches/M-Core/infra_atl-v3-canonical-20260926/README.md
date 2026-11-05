# M-Core — branch `infra/atl-v3-canonical-20260926`

Lean sources from the branch `infra/atl-v3-canonical-20260926` of the private repository `ShantiDraconis/M-Core`, commit `e543c3c607acdf86497accc66708160ba03249e9` (2026-09-26T11:03:43+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 7 — closed 5, conditional 0, open 1, proof error 1, not reached 0, no result 0.
* History: 17 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `ebdbe1d5d1c256d52a2e9650be6c7a1bb8b1c6d6c4a52b52d8d591052e2065b4`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/infra_atl-v3-canonical-20260926/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.ATL.V3.external_not_attackable` | `lean/MCore/ATL/V3/Core.lean`:73 | fechado |
| `MCore.ATL.V3.fail_closed_without_term` | `lean/MCore/ATL/V3/Master.lean`:7 | aberto-sorry |
| `MCore.ATL.V3.research_not_attackable` | `lean/MCore/ATL/V3/Core.lean`:69 | fechado |
| `MCore.ATL.V3.scientific_implies_semantic` | `lean/MCore/ATL/V3/Promotion.lean`:37 | fechado |
| `MCore.ATL.V3.semantic_implies_kernel` | `lean/MCore/ATL/V3/Promotion.lean`:42 | fechado |
| `MCore.ATL.V3.theorem_without_term_not_proved` | `lean/MCore/ATL/V3/Certificate.lean`:39 | erro |
| `MCore.ATL.V3.unaudited_mining_not_emittable` | `lean/MCore/ATL/V3/Mining.lean`:42 | fechado |
