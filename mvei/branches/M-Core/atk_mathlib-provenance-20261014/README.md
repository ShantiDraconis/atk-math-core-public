# M-Core — branch `atk/mathlib-provenance-20261014`

Lean sources from the branch `atk/mathlib-provenance-20261014` of the private repository `ShantiDraconis/M-Core`, commit `b443d4d1c8a30edf40d650c10254ebfdd88e4bb4` (2026-10-15T03:21:13+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: em andamento (not in the default branch).
* Theorems only on branches, in this branch: 23 — closed 4, conditional 0, open 0, proof error 1, not reached 18, no result 0.
* History: 11 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `b43a2788030ef5322650b6a53d59669488b6f0d21a342de07c74ce5ea4c2ab38`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/M-Core/atk_mathlib-provenance-20261014/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `ATK.MathlibCandidates.exponent_gcd_le_two` | `MATHLIB_CONTRIBUTION/Lean/ConditionalExponentGCD.lean`:14 | fechado |
| `ATK.MathlibCandidates.gram_complete_square` | `MATHLIB_CONTRIBUTION/Lean/GramQuadratic.lean`:19 | fechado |
| `ATK.MathlibCandidates.gram_residual_le` | `MATHLIB_CONTRIBUTION/Lean/GramQuadratic.lean`:34 | erro |
| `ATK.MathlibCandidates.residual_sub_square_div_le` | `MATHLIB_CONTRIBUTION/Lean/ResidualInequalities.lean`:18 | fechado |
| `ATK.MathlibCandidates.residual_tendsto_zero` | `MATHLIB_CONTRIBUTION/Lean/LogResidualConvergence.lean`:14 | fechado |
| `FermatRightTriangle.coprime_of_minimal` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:85 | nao_alcancado |
| `FermatRightTriangle.exists_minimal` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:75 | nao_alcancado |
| `FermatRightTriangle.exists_param_of_odd` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:202 | nao_alcancado |
| `FermatRightTriangle.exists_pos_minimal` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:102 | nao_alcancado |
| `FermatRightTriangle.exists_smaller_of_even` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:224 | nao_alcancado |
| `FermatRightTriangle.exists_smaller_of_mul_eq_sq` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:147 | nao_alcancado |
| `FermatRightTriangle.exists_smaller_of_odd` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:123 | nao_alcancado |
| `FermatRightTriangle.isCoprime_sq_sub_sq_mul` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:113 | nao_alcancado |
| `FermatRightTriangle.ne_zero` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:53 | nao_alcancado |
| `FermatRightTriangle.neg` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:59 | nao_alcancado |
| `FermatRightTriangle.not_minimal` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:269 | nao_alcancado |
| `FermatRightTriangle.of_mul` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:63 | nao_alcancado |
| `Int.fourth_pow_add_sq_ne_fourth_pow` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:295 | nao_alcancado |
| `Int.fourth_pow_sub_fourth_pow_ne_sq` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:288 | nao_alcancado |
| `Int.not_isSquare_sq_add_sq_and_sq_sub_sq` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:322 | nao_alcancado |
| `Int.sq_ne_two_mul_sq` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:301 | nao_alcancado |
| `PythagoreanTriple.mul_ne_two_mul_sq` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:340 | nao_alcancado |
| `Rat.mul_ne_two_of_sq_add_sq_eq_sq` | `MATHLIB_CONTRIBUTION/upstream/01-fermat-right-triangle/FermatRightTriangle.lean`:365 | nao_alcancado |
