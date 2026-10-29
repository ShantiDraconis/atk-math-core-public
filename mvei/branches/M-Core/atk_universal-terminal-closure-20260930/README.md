# M-Core — branch `atk/universal-terminal-closure-20260930`

Lean sources from the branch `atk/universal-terminal-closure-20260930` of the private repository `ShantiDraconis/M-Core`, commit `d0ce322c47c96990a90596501bed86699dbbfe95` (2026-10-01T01:46:59+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 19 — closed 7, conditional 0, open 0, proof error 0, not reached 12, no result 0.
* History: 30 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `d8a6c38e7b4a5db1dc4cc3de4c1b75ec6fc5a4e8b10cd6b57d56a23a1ac84d3b`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_universal-terminal-closure-20260930/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.FinalProof.ProducerMap.target_of_inhabited` | `lean/MCore/UniversalTerminalClosure.lean`:106 | fechado |
| `MCore.FinalProof.ProducerReduction.comp_map` | `lean/MCore/ProducerCalculus.lean`:28 | nao_alcancado |
| `MCore.FinalProof.ProducerReduction.id_map` | `lean/MCore/ProducerCalculus.lean`:25 | nao_alcancado |
| `MCore.FinalProof.ProducerReduction.nonempty_forward` | `lean/MCore/ProducerCalculus.lean`:34 | nao_alcancado |
| `MCore.FinalProof.TerminalLane.closed_of_upstream` | `lean/MCore/ProducerCalculus.lean`:89 | nao_alcancado |
| `MCore.FinalProof.TerminalLane.target_of_closed` | `lean/MCore/UniversalTerminalClosure.lean`:23 | fechado |
| `MCore.FinalProof.TerminalLane.target_of_reduction_chain` | `lean/MCore/ProducerCalculus.lean`:98 | nao_alcancado |
| `MCore.FinalProof.conditional_constructor_closes` | `lean/MCore/ProducerCalculus.lean`:139 | nao_alcancado |
| `MCore.FinalProof.equivalentWrapper_nonempty_iff` | `lean/MCore/UniversalTerminalClosure.lean`:68 | fechado |
| `MCore.FinalProof.hypothesisWrapper_nonempty_implies_target` | `lean/MCore/UniversalTerminalClosure.lean`:86 | fechado |
| `MCore.FinalProof.neutralWrapper_nonempty_iff` | `lean/MCore/ProducerCalculus.lean`:63 | nao_alcancado |
| `MCore.FinalProof.no_universal_conditional_promotion` | `lean/MCore/ProducerCalculus.lean`:127 | nao_alcancado |
| `MCore.FinalProof.producerEquiv_nonempty_iff` | `lean/MCore/ProducerCalculus.lean`:48 | nao_alcancado |
| `MCore.FinalProof.product_nonempty_iff` | `lean/MCore/ProducerCalculus.lean`:81 | nao_alcancado |
| `MCore.FinalProof.proposition_equivalence_conserves_wrapper` | `lean/MCore/ProducerCalculus.lean`:148 | nao_alcancado |
| `MCore.FinalProof.universal_closure_from_reductions` | `lean/MCore/ProducerCalculus.lean`:112 | nao_alcancado |
| `MCore.FinalProof.universal_producer_first_closure` | `lean/MCore/UniversalTerminalClosure.lean`:131 | fechado |
| `MCore.FinalProof.universal_terminal_closure` | `lean/MCore/UniversalTerminalClosure.lean`:46 | fechado |
| `MCore.FinalProof.wrapper_conserves_terminal_difficulty` | `lean/MCore/UniversalTerminalClosure.lean`:138 | fechado |
