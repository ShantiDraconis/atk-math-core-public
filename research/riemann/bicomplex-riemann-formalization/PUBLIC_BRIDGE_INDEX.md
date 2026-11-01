# Public bridge index

“Bridge” means a proposed correspondence or proof obligation, not a validated transfer theorem.

| Item | Domain analogy | Required bridge | Package references |
|---:|---|---|---|
| 7 | Belousov–Zhabotinsky chemistry | Define a reaction-diffusion model and derive any relation between oscillation/stability and a zeta coordinate. | `APPLICATION_BRIDGES.md`, `FORMULA_CATALOG.md`, `OPEN_BRIDGE_REGISTRY.csv` |
| 8 | SIR epidemic | Specify equations, units, thresholds, and evidence for the proposed `0.3/0.7` coordinates. | Application registry; `Formal/ApplicationBridges.lean` proves arithmetic only. |
| 9 | Room acoustics | Derive modal growth/decay and phase behavior from boundary conditions and geometry. | `APPLICATION_BRIDGES.md`; zero-divisor identity does not prove acoustic cancellation. |
| 10 | Laser mode | Define the cavity operator and derive its threshold; distinguish instability from a zeta zero. | `APPLICATION_BRIDGES.md`; no physical model is formalized. |
| 11 | Seismic fault | Specify PDE/interface conditions and wavenumber convention; prove any connection to bicomplex factors. | `APPLICATION_BRIDGES.md`; no geophysical theorem is asserted. |
| 12 | EEG | Supply a neural model and clinically grounded criteria; spectral coordinates alone cannot diagnose seizure/sleep. | `APPLICATION_BRIDGES.md`; no clinical data/inference is formalized. |
| 13 | Aeroelastic flutter | Derive coupled bending/torsion eigenvalues and instability threshold from a stated model. | `APPLICATION_BRIDGES.md`; no bridge to `(1+k)(1-k)=0` is proved. |
| 14 | Markets/leverage | Define a stochastic/agent model and test leverage claims; “2008 as a 0.7/0.3 rectangle” is unestablished. | `APPLICATION_BRIDGES.md`; no market-data theorem is supplied. |
| 15 | Social spread | Specify transmission dynamics and validate any reproduction-number interpretation with data or simulation. | `APPLICATION_BRIDGES.md`; no platform data are supplied. |

## Additional classical routes

| Route | Files | Status here |
|---|---|---|
| Dirichlet series, Euler product, analytic continuation, functional equation, completed ξ | `CLASSICAL_RH_BRIDGES.md`, `CLASSICAL_RH_REGISTRY.csv` | Open formalization obligations |
| Zero symmetries and four-point orbit | `Formal/CenteredSymmetry.lean`, `Formal/AnalyticBridgeContracts.lean` | Abstract conditional results; no zeta zero set instantiated |
| Hadamard product, mollification, explicit formula, Hilbert–Pólya/Berry–Keating | `ANALYTIC_BRIDGES.md`, `OPEN_BRIDGE_REGISTRY.csv` | Research routes; analytic/spectral steps remain open |
| Riemann–von Mangoldt count, Nyman–Beurling, Li, de Bruijn–Newman, finite certified zero counts, prime-counting equivalences | `CLASSICAL_RH_BRIDGES.md`, `CLASSICAL_RH_REGISTRY.csv` | Listed as obligations, not proofs in this package |

The coordinate pair `sigma+b=0.3`, `sigma-b=0.7` for `sigma=0.5,b=-0.2` does not imply that ζ has a zero at either point. Davenport–Heilbronn concerns a different function. A Lean build checks only the encoded declarations.
