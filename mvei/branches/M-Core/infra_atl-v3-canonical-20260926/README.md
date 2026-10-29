# M-Core — branch `infra/atl-v3-canonical-20260926`

Lean sources from the branch `infra/atl-v3-canonical-20260926` of the private repository `ShantiDraconis/M-Core`, commit `e543c3c607acdf86497accc66708160ba03249e9` (2026-09-26T11:03:43+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 7 — closed 3, conditional 0, open 0, proof error 2, not reached 2, no result 0.
* History: 17 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `276f5d8b42b53b24602a4d3e8232f5ca7389f4a035ea9710c6cf1e695d999f8f`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/infra_atl-v3-canonical-20260926/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.ATL.V3.external_not_attackable` | `lean/MCore/ATL/V3/Core.lean`:73 | fechado |
| `MCore.ATL.V3.fail_closed_without_term` | `lean/MCore/ATL/V3/Master.lean`:7 | nao_alcancado |
| `MCore.ATL.V3.research_not_attackable` | `lean/MCore/ATL/V3/Core.lean`:69 | fechado |
| `MCore.ATL.V3.scientific_implies_semantic` | `lean/MCore/ATL/V3/Promotion.lean`:37 | erro |
| `MCore.ATL.V3.semantic_implies_kernel` | `lean/MCore/ATL/V3/Promotion.lean`:42 | erro |
| `MCore.ATL.V3.theorem_without_term_not_proved` | `lean/MCore/ATL/V3/Certificate.lean`:39 | nao_alcancado |
| `MCore.ATL.V3.unaudited_mining_not_emittable` | `lean/MCore/ATL/V3/Mining.lean`:42 | fechado |
