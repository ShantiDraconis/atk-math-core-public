# Claim ledger

| Claim | Status in this bundle | Reason |
|---|---|---|
| `k = ij` has square `+1` when commuting `i,j` each square to `−1` | Lean proof term included; kernel check unavailable here | `(ij)^2 = i²j² = 1` |
| `(1+k)(1−k)=0` with both factors nonzero | Lean proof terms included; kernel check unavailable here | These are zero divisors; neither factor is zero |
| If `y=a+ib` in ordinary `ℂ`, then `−1+iy=−1−b+ia` | Lean proof terms included; kernel check unavailable here | `i²=−1`; for `b=−3`, the real part is `2` |
| If `y=a+jb` with an independent commuting bicomplex `j`, then `i(a+jb)=ia+kb` | Lean proof term included; kernel check unavailable here | The scalar real coefficient stays unchanged; component shifts arise in idempotent coordinates |
| `z=σ+it+kb` has idempotent components `(σ+b)+it` and `(σ−b)+it` | Coordinate identities included; kernel check unavailable here | Use `e±=(1±k)/2`; `ke±=±e±` |
| A zero in one component alone is a zero of the full bicomplex value | False | It is a zero divisor situation; the other component may be nonzero |
| Setting `b=0` sends every off-line component zero to a classical zero on the critical line | Not established; does not follow | The argument changes, and `σ` is not thereby constrained to `1/2` |
| No classical off-line zeta zeros exist because a second coordinate is absent in `ℂ` | Not established | This is the RH assertion, not a consequence of changing number systems |
| In tenths, `5 - (-2) = 7` and the paired coordinates are `(3,7)` | Lean theorem and proof term written in `Formal/ShiftModel.lean`; kernel check pending | Exact integer arithmetic for the proposed coordinate convention |
| Each of the nine application entries maps to `(0.3,0.7)` | Lean theorem and proof term written in `Formal/ApplicationBridges.lean`; kernel check pending | The registry assigns the same numbers by definition; it proves no domain behavior |
| The 0.7/0.3 pair predicts EEG, chemical, acoustic, laser, seismic, aeroelastic, economic, epidemic, or social outcomes | Not established | Domain-specific dynamics, units, parameter estimates, and independent validation are absent |
| `(1+k)(1-k)=0` means physical cancellation in each listed domain | Not established | It is an algebraic zero-divisor identity in the bicomplex model, not a physical law |
| Reflection/conjugation assumptions produce a four-point orbit | Lean theorem and proof term written in `Formal/AnalyticBridgeContracts.lean`; kernel check pending | The theorem is conditional on both closure assumptions for an abstract set |
| Two component real coordinates both equal to 1/2 force the center to 1/2 and shift to 0 | Lean theorem and proof term written in `Formal/AnalyticBridgeContracts.lean`; kernel check pending | Coordinate arithmetic only; no zeta-zero or RH premise is proved |
| There is a last natural number, or a standard natural “after infinity” | Refuted within the standard `Nat` model by `Formal/AfterInfinity.lean` | Every natural has a successor; an adjoined point belongs to a different type |
| Hadamard, mollifier, explicit-formula, Hilbert–Pólya/Berry–Keating, or RH-consequence bridges close the RH proof | Open / not established | Their definitions, analytic estimates, operator construction, or producer proofs are not present |
| Euler product proves zero-freeness for `Re(s)>1` | Established classical result, not formalized here | The convergence and nonvanishing proof is outside this package |
| Nyman–Beurling, Li, de Bruijn–Newman, zero-counting, and prime-error criteria prove RH | Established equivalences or conditional criteria, not formalized here | An equivalent criterion proves RH only after its all-parameter target is proved; finite checks do not suffice |
| RH forces arbitrary bicomplex inputs to have `b=0` | False | Only a full zero of the proposed component lift, with both components classical nontrivial zeros, yields `b=0` under RH; arbitrary inputs are unrestricted. See `RH_CONDITIONAL_SPECTRAL_BRIDGES.md`. |
| The Euler product forces every zeta zero to have real part 1/2 | False | The Euler product proves nonvanishing in its absolute-convergence region `Re(s)>1`; it does not converge as a product in the critical strip. The functional equation supplies symmetry, not pointwise fixation. |
| RH implies a meaningful Hilbert–Pólya operator exists | Not established | RH permits a tautological diagonal operator on zero ordinates, but does not provide an independent arithmetic operator or determinant identity. |
| A self-adjoint operator alone proves RH | False as stated | One also needs an exact, exhaustive zero/spectrum correspondence and a nonvanishing-factor determinant identity. |
| Berry–Keating `xp` already has zeta ordinates as eigenvalues | Not established | The classical Hamiltonian is a heuristic proposal; the standard half-line dilation realization has continuous spectrum, and regularizations need separate proofs. |
| A second Dirichlet L-function changes the local Euler factor of Riemann ζ into exponents 0.8 and 0.4 | False | Davenport–Heilbronn is a different linear combination of Dirichlet L-functions, not a perturbation of ζ's Euler factors. |
| The bicomplex zero divisor `(1+k)(1-k)=0` breaks RH for classical ζ | False | It is an identity in a different algebra; it does not alter the classical zeta function or its zero set. |
| The elementary integrals `∫₀¹x^{-1/2}dx` and `∫₀¹x^{-0.3}dx` evaluate ζ on those lines | False | They are finite power integrals, not the Mellin representation of ζ; the latter integral requires `Re(s)>1`. |
| Davenport–Heilbronn has infinitely many off-line zeros | Classical result for that distinct function | Voronin gives a lower bound \(N_{DH}(\alpha,\beta;T)\gg T\) in fixed strips to the right of its symmetry line; see `OFF_LINE_ZERO_COUNTS_AND_SYMMETRY.md`. |
| Epstein zeta for discriminant \(-20\) and class number 2 has infinitely many off-line zeros | Classical result for that distinct function | The theorem concerns this Epstein zeta, not classical Riemann \(\zeta\). |
| Functional-equation symmetry makes two off-line zeros “average into” a zero on the line | False | The midpoint has real part 1/2 arithmetically; zerohood of the midpoint does not follow. |
| The finite list of computed Davenport–Heilbronn zeros is the complete off-line zero set | False | The set is infinite; a numerical inventory can only be exhaustive up to a certified finite height. |
| Breaking a function's functional equation creates zeros at prescribed real parts | Not established | No zero follows from breaking symmetry alone; any candidate requires a specified function and certified complex zero. |
| A finite prime-counting error at `x=10^12` refutes an RH asymptotic bound | False | A finite value cannot contradict an asymptotic O-bound with an unspecified constant. |
| RH-conditional consequences listed in `RH_CONDITIONAL_SPECTRAL_BRIDGES.md` are formalized in Lean | False | They are classical theorems summarized in documentation; the current Lean package has no analytic definition of `ζ`/`ξ` or these estimates. |
| The current algebraic and conditional theorem terms are kernel-verified | Not verified | Lean/Lake are unavailable in this environment; see `FORMAL_PROOF_STATUS.md` |
| A full bicomplex pair is zero iff both component values are zero | Lean source theorem written, kernel check pending | `Formal/ComponentLift.lean`; generic product-value statement, not an analytic zeta lift |
| One zero component with a nonzero other component is a zero of the full pair | False; the source proves it is not the pair zero | `one_zero_component_not_pair_zero`; zero-divisor terminology is algebraic |
| Reflection in centered coordinates exchanges the 0.7 and 0.3 tenths values | Lean source theorem written, kernel check pending | `Formal/CenteredSymmetry.lean`; coordinate arithmetic only, no existence of zeta zeros |
| An abstract target-axis theorem transfers to source zeros through an exact bridge | Lean source theorem written, kernel check pending | `Formal/BridgeContracts.lean`; requires both zero correspondence and axis correspondence fields |
| `Formal/BridgeContracts.lean` supplies a bridge instance for classical `ζ` or a physical system | False | No concrete bridge instance, analytic continuation, calibrated operator, or empirical model is included |
| Moving the real exponent from 0.5 to 0.7 changes the numerator power by (x^{0.2}) | Exact exponent difference; multiplicative consequence conditional on an abstract exponent law | `Formal/ExplicitFormulaScaling.lean`; the denominator `|ρ|` also changes slightly when the ordinate is fixed and the real part changes |
| The 251 ratio at (x=10^{12}) is the exact total error in (pi(x)-\operatorname{Li}(x)) | False | It is a rounded ratio of individual zero-term amplitude bounds; phases and other zeros affect the full sum, and passage to `π(x)` uses partial summation |
| A Davenport–Heilbronn off-line zero is an off-line zero of Riemann `ζ` | False | It is a zero of a different function and cannot be inserted into Riemann's prime explicit formula |

The modules formalize only finite algebraic identities, conditional symmetry/arithmetic contracts, and the explicitly defined coordinate registry. They contain no definition of `ζ` or analytic continuation. The new Lean source has not been kernel-checked in this environment.
