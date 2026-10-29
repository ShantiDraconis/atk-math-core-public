# M-Core — branch `atk/fix-problem-signature-v2`

Lean sources from the branch `atk/fix-problem-signature-v2` of the private repository `ShantiDraconis/M-Core`, commit `03cf316766c7105d498aa72fe234c8d198f1896d` (2026-10-11T17:39:33+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 5 — closed 5, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 21 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `48f87b9f9e189e71ceee5b97e92f8f57e9aedb0da5fccf4bdf9adef8240cbec3`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_fix-problem-signature-v2/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.FinalFail.RelationalHardAtom.determinedAt_iff_centerDetermined` | `lean/MCore/FinalFail/RelationalCenterBridge.lean`:31 | fechado |
| `MCore.FinalFail.RelationalHardAtom.determinedAt_not_failAt` | `lean/MCore/FinalFail/RelationalCenterBridge.lean`:54 | fechado |
| `MCore.FinalFail.RelationalHardAtom.failAt_iff_IFail` | `lean/MCore/FinalFail/RelationalCenterBridge.lean`:43 | fechado |
| `MCore.FinalFail.RelationalHardAtom.failAt_iff_fundamentalIndeterminacy` | `lean/MCore/FinalFail/RelationalCenterBridge.lean`:19 | fechado |
| `MCore.FinalFail.RelationalTotality.closedCenterHard_coexists_with_failAt` | `lean/MCore/FinalFail/RelationalClosedCenterBridge.lean`:69 | fechado |
