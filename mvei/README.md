# MVEI kernel check — M-Core

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/M-Core`. The sources are published in [`imports/M-Core/`](../imports/M-Core/).

## What is published

* Source: `ShantiDraconis/M-Core`, commit `390e3781109fa42e977d143caa9204ed94166a7b` (2026-10-27T20:01:22Z).
* 589 files: 583 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`), plus 2 license or origin file(s) that third-party code requires (`atk-kernel/ATK/FltRegular/LICENSE`, `atk-kernel/ATK/FltRegular/ORIGEM.md`). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material). The `Contaminated/` folder, which the author quarantined and marked as never evidence, is left out too.
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-10-28T16:41:02+00:00, on commit `390e3781109fa42e977d143caa9204ed94166a7b`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) | Checked file by file: closed / conditional / open / proof error / not reached |
|---|---|---|---:|---:|---:|---|
| `.` | v4.19.0 | OK | 245 | 0 | 0 | 102 / 0 / 1 / 16 / 370 |
| `atk-kernel` | v4.34.1 | OK | 10 324 | 0 | 0 | — |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 10 671 |
| Unique (name + statement) | 10 671 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 8 740 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`. *Checked file by file* covers the files that no build reached: each one went through Lean whole, with a `#print axioms` for each theorem.

| Theorem | Project | State | Axioms beyond the standard three |
|---|---|---|---|
| `MCore.Poincare.promote_to_kernel_endpoint` | `. (file by file)` | open | `sorryAx` |

### Declared theorems

The `.lean` files of the verified commit declare 9 572 `theorem`/`lemma` (counting copies). The kernel checked 8 267 of them (8 267 closed, 0 conditional, 0 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. For 1 305 the kernel has no result:

| Reason | Theorems |
|---|---:|
| the project built, but the file is not part of the lakefile target | 921 |
| checked file by file: Lean did not reach the theorem (missing import, syntax error or timeout) | 366 |
| checked file by file: the written proof does not pass the kernel | 16 |
| the file compiled, but the name did not appear in the kernel (private, mutual or macro-generated) | 2 |

A new kernel run for this repository is in progress in the MVEI pipeline; this folder will be updated with its result.

### MVEI corrections

* `correcoes/imports-no-topo.patch` (import fora do início do arquivo, 1 file(s)): applies to the published sources: `git apply -p1 --directory=imports/M-Core mvei/correcoes/imports-no-topo.patch`

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
