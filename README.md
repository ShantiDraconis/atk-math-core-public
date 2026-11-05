# ATK MATH-CORE — Formal Research

Research repository maintained by Tiago Paschoalatto Fagliari (ORCID: https://orcid.org/0009-0006-6874-3910).

Status: **research in progress; no unconditional solution or Millennium Prize certification is claimed.**

This repository will preserve source paths, original commit SHAs, authorship, dependencies, and exact Lean verification outcomes. A successful Lean build does not by itself prove an original open problem unless the formalized theorem exactly matches it and all assumptions are discharged.

Related publication: https://doi.org/10.5281/zenodo.15164501 (historical publication; not a proof certificate).

Do not add confidential data or third-party code without checking its license and attribution.

## License

The author's content is licensed under the [PolyForm Noncommercial License 1.0.0](https://polyformproject.org/licenses/noncommercial/1.0.0) (see [`LICENSE`](LICENSE)): free for noncommercial use (study, research, teaching, checking the proofs) with the Required Notice; commercial use needs a separate license from the author. Third-party code (for example `ATK/FltRegular/`), Lean and Mathlib keep their own licenses. Cite with [`CITATION.cff`](CITATION.cff).

<!-- mvei:start -->
## Lean sources and kernel check (MVEI)

[`imports/M-Core/`](imports/M-Core/) holds the Lean sources of `ShantiDraconis/M-Core` at commit `390e378` (2026-10-27): 589 files. In the MVEI verification the Lean kernel closed 11 977 theorems here (9 992 unique, without the lemmas Lean generates itself), with 6 conditional and 2 open (`sorry`). A closed theorem proves the statement written in the file; it is not a claim that an open problem is solved. Statements, axioms, the build log and how to reproduce: [`mvei/README.md`](mvei/README.md).
<!-- mvei:end -->

<!-- mvei-branches:start -->
## Theorems found only on branches

58 branch(es) with 3 919 theorems that exist only on branches and that the Lean kernel closed, each with a certificate (commit, date, history, SHA-256): [`branches/README.md`](branches/README.md).
<!-- mvei-branches:end -->

## Riemann bridge archive

The separate recovered bicomplex/Riemann formalization, its application and classical bridge index, status ledger, and Lean workflow are documented at [`research/riemann/bicomplex-riemann-formalization/`](research/riemann/bicomplex-riemann-formalization/README.md). Its algebraic and conditional Lean results are not a proof of the Riemann Hypothesis; the package records open analytic obligations explicitly.

