# MVEI kernel check — M-Core

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/M-Core`. The sources are published in [`imports/M-Core/`](../imports/M-Core/).

## What is published

* Source: `ShantiDraconis/M-Core`, commit `390e3781109fa42e977d143caa9204ed94166a7b` (2026-10-27T20:01:22Z).
* 589 files: 583 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`), plus 2 license or origin file(s) that third-party code requires (`atk-kernel/ATK/FltRegular/LICENSE`, `atk-kernel/ATK/FltRegular/ORIGEM.md`). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material). The `Contaminated/` folder, which the author quarantined and marked as never evidence, is left out too.
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-10-29T01:06:09+00:00, on commit `390e3781109fa42e977d143caa9204ed94166a7b`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) | Checked file by file: closed / conditional / open / proof error / not reached |
|---|---|---|---:|---:|---:|---|
| `.` | v4.19.0 | OK | 245 | 0 | 0 | 117 / 3 / 8 / 25 / 336 |
| `atk-kernel` | v4.34.1 | OK | 11 236 | 0 | 0 | 36 / 0 / 0 / 0 / 3 |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 11 634 |
| Unique (name + statement) | 11 630 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 9 665 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`. *Checked file by file* covers the files that no build reached: each one went through Lean whole, with a `#print axioms` for each theorem.

| Theorem | Project | State | Axioms beyond the standard three |
|---|---|---|---|
| `ATK.Experimento.rh_e_beal_postulados` | `. (file by file)` | conditional | `ATK.Experimento.S`, `ATK.Experimento.W`, `ATK.Experimento.hS` |
| `ATK.Experimento.rh_e_nao_rh` | `. (file by file)` | conditional | `ATK.Experimento.Wc` |
| `ATK.Experimento.falso` | `. (file by file)` | conditional | `ATK.Experimento.Wc` |
| `ATK.Experimento.rh_por_sorry` | `. (file by file)` | open | `sorryAx` |
| `MCore.Poincare.promote_to_kernel_endpoint` | `. (file by file)` | open | `sorryAx` |
| `MCore.IBoundary.approach_states_distinct` | `. (file by file)` | open | `sorryAx` |
| `MCore.IBoundary.terminal_projection_not_injective` | `. (file by file)` | open | `sorryAx` |
| `MCore.IBoundary.StructuralBoundaryInformationLoss` | `. (file by file)` | open | `sorryAx` |
| `MCore.IBoundary.approach_states_distinct` | `. (file by file)` | open | `sorryAx` |
| `MCore.IBoundary.terminal_projection_not_injective` | `. (file by file)` | open | `sorryAx` |
| `MCore.IBoundary.StructuralBoundaryInformationLoss` | `. (file by file)` | open | `sorryAx` |

### Declared theorems

The `.lean` files of the verified commit declare 9 572 `theorem`/`lemma` (counting copies). The kernel checked 9 202 of them (9 196 closed, 0 conditional, 6 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. For 370 the kernel has no result:

| Reason | Theorems |
|---|---:|
| checked file by file: Lean did not reach the theorem (missing import, syntax error or timeout) | 339 |
| checked file by file: the written proof does not pass the kernel | 25 |
| the project built, but the file is not part of the lakefile target | 4 |
| the file compiled, but the name did not appear in the kernel (private, mutual or macro-generated) | 2 |

### MVEI corrections

* `correcoes/imports-no-topo.patch` (import fora do início do arquivo, 1 file(s)): applies to the published sources: `git apply -p1 --directory=imports/M-Core mvei/correcoes/imports-no-topo.patch` (in order, after the ones above)
* `correcoes/renomear-imports-mathlib.patch` (import de módulo que não existe na versão do Mathlib do projeto (renomeado ou dividido), 2 file(s)): applies to the published sources: `git apply -p1 --directory=imports/M-Core mvei/correcoes/renomear-imports-mathlib.patch` (in order, after the ones above)

## Files in this folder

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
