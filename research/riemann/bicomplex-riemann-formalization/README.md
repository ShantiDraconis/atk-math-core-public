# Bicomplex and Riemann bridge archive

This package preserves the recovered bicomplex-coordinate formalization and separates its algebraic results from proposed application analogies and unfinished analytic routes.

## Scope

The Lean sources encode elementary bicomplex algebra, integer-coordinate arithmetic, generic componentwise statements, and conditional bridge contracts. They do not formalize analytic continuation of ζ, establish application-specific physical or social models, or prove the classical Riemann Hypothesis.

The identity `(1+k)(1-k)=0` follows algebraically from `k²=1`; it is a zero-divisor identity, not a physical cancellation law. The shift `sigma-b=0.7` when `sigma=0.5` and `b=-0.2` is coordinate arithmetic, not evidence for a zeta zero off the critical line.

## Navigation

- [Applied systems analysis](CROSS_DOMAIN_ANALYSIS.md), [source materials](SOURCE_MATERIALS.md), and [validation protocols](VALIDATION_PROTOCOLS.md): domain laws, cross-domain methods, authors/data producers, and falsifiable criteria, separate from RH claims.
- [Applied bridge index](PUBLIC_BRIDGE_INDEX.md): maps items 7–15 to equations, methods, sources, and validation tasks.
- [Scaling analogy audit](SCALING_ANALOGY_AUDIT.md): derives the proposed (x^{0.2}) bridge and audits physical examples, evidence, and limits.
- [RH conditional and spectral bridges](RH_CONDITIONAL_SPECTRAL_BRIDGES.md): states conditional RH consequences, the exact bicomplex implication, zero symmetries, Euler-product limits, and Hilbert–Pólya proof obligations.
- [Two-locks audit](TWO_LOCKS_AUDIT.md): audits Euler-product claims, the bicomplex zero divisor, numerical points, Mellin integrals, derivative claims, and proposed physical analogies.
- [Off-line zero counts and symmetry](OFF_LINE_ZERO_COUNTS_AND_SYMMETRY.md): records the infinite off-line zero results for Davenport–Heilbronn/Epstein, the symmetry orbit, and why paired-zero averages are not zeros.
- [Unconditional zeta theorem ledger](UNCONDITIONAL_ZETA_THEOREM_LEDGER.md): separates unconditional zeta theorems, RH-conditional consequences, finite-height verification, and countermodels from different functions.
- [Formula catalog](FORMULA_CATALOG.md), [claim ledger](CLAIMS.md), and [formal file guide](FORMAL_FILE_GUIDE.md).
- [Proof status](FORMAL_PROOF_STATUS.md) and [CSV status register](FORMAL_PROOF_STATUS.csv).
- [Open bridge registry](OPEN_BRIDGE_REGISTRY.csv) and [classical RH registry](CLASSICAL_RH_REGISTRY.csv).
- Lean modules live in [`Formal/`](Formal/).

| Bridge family | Lean sources | Established scope |
|---|---|---|
| Bicomplex algebra and component lift | `Formal/BicomplexLift.lean`, `Formal/ComponentLift.lean` | Algebra and generic two-component zero criterion |
| Shift/application coordinates | `Formal/ShiftModel.lean`, `Formal/ApplicationBridges.lean` | Exact coordinate arithmetic only |
| Symmetry/transfer contracts | `Formal/CenteredSymmetry.lean`, `Formal/BridgeContracts.lean`, `Formal/AnalyticBridgeContracts.lean` | Conditional results; no zeta instance |
| Explicit-formula scaling | `Formal/ExplicitFormulaScaling.lean` | Abstract exponent bookkeeping, not the analytic explicit formula |
| Analytic and classical routes | `ANALYTIC_BRIDGES.md`, `CLASSICAL_RH_BRIDGES.md`, `RH_CONDITIONAL_SPECTRAL_BRIDGES.md` | Conditional consequences and open obligations, not a completed RH proof |

A passing [Lean workflow](../../../.github/workflows/riemann-bridge-formalization.yml) can certify the declarations compiled under the pinned toolchain and passed the configured axiom audit. It does not certify unformalized prose, empirical interpretations, or RH. Every entry marked `WRITTEN_UNCHECKED` remains unchecked until a successful run covers the exact commit.


## Reproducibility tests

The [quasi-Riemann test suite](Tests/README.md) separates exact structural checks from floating-point reproductions. Its root checks are exploratory and are not rigorous zero-isolation certificates. See the [test matrix](Tests/TEST_MATRIX.md) for scope, limitations, and references.
