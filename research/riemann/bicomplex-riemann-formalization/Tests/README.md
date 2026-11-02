# Quasi-Riemann test suite

This suite tests the logical and numerical claims in the comparison between
the classical zeta function and nearby examples. It intentionally separates
exact algebraic tests, floating-point reproductions, and theorem-level facts.

## Run

```sh
python -m pip install -r requirements-tests.txt
python -m unittest -v test_quasi_riemann.py
```

The numerical tests use SciPy double precision and Euler–Maclaurin evaluation.
They are reproducibility checks, not interval certificates and not proofs of
zero existence. The exact statements and the limits of each numerical check
are listed in `TEST_MATRIX.md`.

## Scope

The suite covers:

* the four-point orbit forced by reflection and conjugation, and a symmetric
  entire countermodel with off-line zeros;
* the completed zeta functional equation and conjugation numerically;
* Euler-product convergence in its valid half-plane, `Re(s) > 1`;
* the Davenport–Heilbronn Dirichlet-series model and its known off-line zero;
* the numerical off-line zero of `zeta(s) + zeta(s+1)` and the failure of the
  proposed `1-s` pairing for that sum;
* the class number calculation for discriminant `-20`;
* the bicomplex zero-divisor identity, kept separate from complex zeta zeros.

There is no certified Epstein off-line zero isolator in this suite. The
Epstein theorem is recorded as a literature-level result in the matrix; a
numerical approximation is not substituted for a proof.
