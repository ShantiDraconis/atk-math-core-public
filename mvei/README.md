# MVEI kernel check — M-Core

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/M-Core`. The sources are published in [`imports/M-Core/`](../imports/M-Core/).

## What is published

* Source: `ShantiDraconis/M-Core`, commit `05ce1d7c2ffcc6cbca5812850bdc8a2b6bda5e93` (2026-11-05T10:43:51Z). This is newer than the commit MVEI verified (`390e378`); the files added since then are covered in [Added after the verified commit](#added-after-the-verified-commit).
* 604 files: 598 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`), plus 2 license or origin file(s) that third-party code requires (`atk-kernel/ATK/FltRegular/LICENSE`, `atk-kernel/ATK/FltRegular/ORIGEM.md`). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material). The `Contaminated/` folder, which the author quarantined and marked as never evidence, is left out too.
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-11-03T08:19:01+00:00, on commit `390e3781109fa42e977d143caa9204ed94166a7b`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) | Checked file by file: closed / conditional / open / proof error / not reached |
|---|---|---|---:|---:|---:|---|
| `.` | v4.19.0 | OK | 245 | 0 | 0 | 427 / 6 / 11 / 3 / 42 |
| `atk-kernel` | v4.34.1 | OK | 11 236 | 0 | 0 | 36 / 0 / 0 / 0 / 3 |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 11 944 |
| Unique (name + statement) | 11 926 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 9 959 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`. *Checked file by file* covers the files that no build reached: each one went through Lean whole, with a `#print axioms` for each theorem.

| Theorem | Project | State | Axioms beyond the standard three |
|---|---|---|---|
| `ATK.Experimento.rh_e_beal_postulados` | `. (file by file)` | conditional | `ATK.Experimento.S`, `ATK.Experimento.W`, `ATK.Experimento.hS` |
| `ATK.Experimento.rh_e_nao_rh` | `. (file by file)` | conditional | `ATK.Experimento.Wc` |
| `ATK.Experimento.falso` | `. (file by file)` | conditional | `ATK.Experimento.Wc` |
| `ATK.Experimento.rh_por_sorry` | `. (file by file)` | open | `sorryAx` |
| `MCore.Poincare.promote_to_kernel_endpoint` | `. (file by file)` | conditional | `MCore.Poincare.Closed3Manifold`, `MCore.Poincare.Diffeomorphic`, `MCore.Poincare.FiniteTimeExtinction`, `MCore.Poincare.RicciFlowWithSurgery`, `MCore.Poincare.S3`, `MCore.Poincare.SimplyConnected` |
| `MCore.Research.UserProgram.firewall_has_six_entries` | `. (file by file)` | conditional | `Lean.ofReduceBool` |
| `MCore.Research.UserProgram.I3State.index_next` | `. (file by file)` | conditional | `Lean.ofReduceBool` |
| `MCore.Research.UserProgram.commutatorDefect_zero_of_commutes` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.commutes_preserves_rotation_fixed` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.commutes_preserves_constant_sector` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.LinearC3Operator.preserves_sector0` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.LinearC3Operator.preserves_sector1` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.LinearC3Operator.preserves_sector2` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.opDelta_C_zero` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.cycleDefect_zero` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.I3KernelInhabitant_sound` | `. (file by file)` | open | `sorryAx` |
| `MCore.Research.UserProgram.phase_sum_zero` | `. (file by file)` | open | `sorryAx` |

### Declared theorems

The `.lean` files of the verified commit declare 9 572 `theorem`/`lemma` (counting copies). The kernel checked 9 518 of them (9 506 closed, 2 conditional, 10 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. For 54 the kernel has no result:

| Reason | Theorems |
|---|---:|
| checked file by file: Lean did not reach the theorem (missing import, syntax error or timeout) | 45 |
| the project built, but the file is not part of the lakefile target | 4 |
| checked file by file: the written proof does not pass the kernel | 3 |
| the file compiled, but the name did not appear in the kernel (private, mutual or macro-generated) | 2 |

### MVEI corrections

* `correcoes/imports-no-topo.patch` (import fora do início do arquivo, 1 file(s)): applies to the published sources: `git apply -p1 --directory=imports/M-Core mvei/correcoes/imports-no-topo.patch` (in order, after the ones above)
* `correcoes/renomear-imports-mathlib.patch` (import de módulo que não existe na versão do Mathlib do projeto (renomeado ou dividido), 2 file(s)): applies to the published sources: `git apply -p1 --directory=imports/M-Core mvei/correcoes/renomear-imports-mathlib.patch` (in order, after the ones above)
* `correcoes/tatica-encontrada.patch` (prova que não passava (ou axioma) que uma tática padrão fecha no kernel, 2 file(s)): applies to the published sources: `git apply -p1 --directory=imports/M-Core mvei/correcoes/tatica-encontrada.patch` (in order, after the ones above)
* `correcoes/vocabulario-lean4.patch` (grafia que o Lean 4 não lê (nome acentuado, λ/Σ/Π como nome, ∀ x y ∈ s, docstring solta, constant, tática do Mathlib sem import), 493 file(s)): made for the verified commit; it does not apply to the published commit as is
* `correcoes/z-provas-reparadas.patch` (prova que não passava no kernel (o enunciado fica igual), 7 file(s)): applies to the published sources: `git apply -p1 --directory=imports/M-Core mvei/correcoes/z-provas-reparadas.patch` (in order, after the ones above)

## Added after the verified commit

Between the verified commit `390e378` and the published commit `05ce1d7`, 15 `.lean` files were added and 1 changed (`atk-kernel/ATK.lean`, which only adds their imports). No other published file changed. The MVEI tables above do not cover these files. Their 182 theorems were checked by the Lean kernel outside MVEI:

* **M-Core CI** (private repository), job "Lean 4 + Mathlib — compilação e auditoria de axiomas":
  * run 41828386817 on commit `a777620` (first 8 files, 106 theorems): T1 GREEN, 8 665/8 665 theorems of `atk-kernel` with only the standard axioms (`sources_sha256 f844898a…a797`);
  * run 41917163252 on commit `14cb7fc` (next 7 files, 76 theorems): T6 GREEN, 8 741/8 741 theorems with only the standard axioms (`sources_sha256 1f002f59…989e`). The Lean and Lake files of `14cb7fc` and of the published `05ce1d7` (the merge of M-Core PR #181) are identical.
* **Local build**: `lake build` of the 15 modules with Lean v4.34.1 (the `atk-kernel` toolchain) and `#print axioms` for each theorem. All 182 depend only on `propext`, `Classical.choice` and `Quot.sound` (a few on a subset of them). None uses `sorry`, `admit`, `native_decide` or a declared `axiom`.

| File | Theorems | Content |
|---|---:|---|
| `atk-kernel/ATK/ZeroClasses/PontesRH.lean` | 33 | Six proposed "bridges" to RH. Each one turns out to be a theorem, equivalent to RH, or ill-posed: `c ≤ ½` is RH, the induction step `RHAte T → RHAte (T + δ)` is RH, and Hilbert–Pólya (eigenvalue form) implies RH. |
| `atk-kernel/ATK/ZeroClasses/PontesRHAbscissa.lean` | 4 | The same `c` as the abscissa of `Σ μ(n)n^{−s}`. |
| `atk-kernel/ATK/FracoesChi.lean` | 22 | `χ = 1/p + 1/q + 1/r − 1`: trichotomy, the gap `1/42` at `(2,3,7)`, orders of the polyhedral groups, Hurwitz's bound `84(g − 1)`, Euler `V − E + F = 2`, Beal exponents and `χ`. |
| `atk-kernel/ATK/FracoesBernoulli.lean` | 20 | `ζ(−1) = −1/12`, `ζ(−3) = 1/120`, `ζ(−5)`, `ζ(−7)`, `ζ(−9)` from Bernoulli numbers; von Staudt–Clausen for small indices. |
| `atk-kernel/ATK/FracoesGama.lean` | 13 | Continued fractions with a rational tail for the ordinates of zeros of `ζ`, from rational balls taken as hypotheses. |
| `atk-kernel/ATK/FracoesEscala.lean` | 8 | Scaling law `∫‖k^a f(k·)‖^q = k^{aq−d}∫‖f‖^q`; criticality of Navier–Stokes and Yang–Mills. |
| `atk-kernel/ATK/FracoesSAT.lean` | 5 | The `7/8` clause average for 3-SAT and the binomial identity behind Schöning's walk. |
| `atk-kernel/ATK/FracoesGamaZeros.lean` | 1 | The continued fractions above for three certified zeros. |
| `atk-kernel/ATK/FracoesParRecorde.lean` | 16 | The closest pair of zeros in the certified data (12 363 187 982 787/788), from its two Arb balls taken as hypotheses: continued fractions of both fractional parts with a rational tail, the simplest fraction in each ball (minimal by Farey neighbours), the gap and `−Δγ²/2` in exact rationals, and `3/2000 < s < 1/600 < 1/400 < s` of the previous record pair. |
| `atk-kernel/ATK/FracoesSATMedia.lean` | 8 | Every 3-CNF formula with distinct variables per clause: the average number of satisfied clauses is exactly `7m/8`, and some assignment satisfies at least `7m/8` (Johnson). |
| `atk-kernel/ATK/OSLacuna.lean`, `OSTransferencia.lean`, `OSProcesso.lean`, `OSSimetria.lean`, `OSExemplo.lean` | 52 | Osterwalder–Schrader reconstruction in time: Hilbert space from a reflection-positive stationary measure, transfer matrix `e^{−tH}`, spectral gap from exponential clustering, symmetries as isometries, an example in `ℂ²` where the bound is attained. Published before as branch-only theorems (`branches/M-Core/atk_rh-rho-independent/`); now in the default branch. |

None of these theorems proves the Riemann hypothesis or any other open problem. Several are equivalences with RH, which stays open. Each theorem with its file, line and axioms is in [`AFTER_VERIFIED_COMMIT.csv`](AFTER_VERIFIED_COMMIT.csv).

## Files in this folder

* `AFTER_VERIFIED_COMMIT.csv` — the 182 theorems of the files added after the verified commit: file, line, name, axioms, state
* `VERIFICACAO.json` — each Lean project of this repository, each theorem the kernel read, its statement, its axioms and its state (`fechado` closed, `condicional` conditional, `aberto-sorry` open)
* `TEOREMAS.csv` — each declared `theorem`/`lemma`: file, line, state in the kernel (`nao_checado` = not checked) and, if not checked, why (in Portuguese)
* `BUILD_LOG.txt` — one block per project: Lean version, result, errors
* `SOURCE.json` — source commit, verified commit and dates, machine-readable
* `SOURCES.sha256` — SHA-256 of every published file

## Reproduce

```
cd imports/M-Core/<project>   # a project folder from the table above ('.' is imports/M-Core)
lake exe cache get           # only for projects that require Mathlib
lake build
```

Each project uses the Lean version in its own `lean-toolchain`, which elan installs. The MVEI pipeline that produced these results is in the author's repository and is not public.
