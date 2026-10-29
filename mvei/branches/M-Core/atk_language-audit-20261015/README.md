# M-Core — branch `atk/language-audit-20261015`

Lean sources from the branch `atk/language-audit-20261015` of the private repository `ShantiDraconis/M-Core`, commit `46f9a43bfa3e4bc6c04c3f71269361c9064040bc` (2026-10-16T00:18:41+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: em andamento (not in the default branch).
* Theorems only on branches, in this branch: 4 — closed 4, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 19 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `a1cb17af1d8e2a5f36e0b81f6d507825f92575dbbe221d3e063edc03fca24451`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_language-audit-20261015/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `ATK.TerminalLanguage.certificate_requires_bridges` | `atk-kernel/ATK/TerminalLanguage.lean`:42 | fechado |
| `ATK.TerminalLanguage.certificate_requires_producers` | `atk-kernel/ATK/TerminalLanguage.lean`:36 | fechado |
| `ATK.TerminalLanguage.faithful_pair_of_certificate` | `atk-kernel/ATK/TerminalLanguage.lean`:30 | fechado |
| `ATK.TerminalLanguage.parameterized_root_of_certificate` | `atk-kernel/ATK/TerminalLanguage.lean`:24 | fechado |
