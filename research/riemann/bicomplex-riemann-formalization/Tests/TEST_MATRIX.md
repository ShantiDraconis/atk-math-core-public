# Test matrix and result interpretation

## Exact tests

| ID | Claim under test | Test | Interpretation |
|---|---|---|---|
| E1 | Reflection plus conjugation produces a four-point orbit. | `test_reflection_and_conjugation_give_a_quartet` | Confirms the orbit arithmetic for an off-line point. It does not put the point on the center line. |
| E2 | Symmetry and an entire finite-order factorization do not force centered zeros for arbitrary functions. | `test_entire_symmetric_countermodel_has_off_line_zeros` | The exact polynomial `F(s)=(s-3/10)(s-7/10)` satisfies `F(s)=F(1-s)` and has off-line zeros. It has no Euler product, so it is not a counterexample to RH. |
| E3 | `(1+k)(1-k)=0` in bicomplex arithmetic. | `test_bicomplex_zero_divisor_is_an_algebra_identity` | Confirms the identity for `k^2=1`; ordinary complex arithmetic with `k^2=-1` gives 2. Neither identity is a zeta-zero theorem. |
| E4 | The principal positive forms of discriminant `-20` are exactly `(1,0,5)` and `(2,2,3)`. | `test_discriminant_minus20_has_two_reduced_positive_forms` | Confirms class number two by reduced-form enumeration. It does not calculate an Epstein zero. |

## Numerical tests

| ID | Claim under test | Test | Interpretation |
|---|---|---|---|
| N1 | Completed zeta has reflection and conjugation symmetries. | `test_completed_zeta_reflection_and_conjugation` | Floating-point consistency check at one point, not a proof of the functional equation. |
| N2 | The Euler product reproduces zeta in its absolute-convergence half-plane. | `test_euler_product_matches_zeta_only_in_its_convergence_region` | Finite-prime approximation at `s=2+3i`; it deliberately makes no claim in `0<Re(s)<1`. |
| N3 | Davenport–Heilbronn has a known zero near `0.8085171824566374+85.69934848537759i`. | `test_davenport_heilbronn_off_line_zero_reproduces` | Reproduces the location under several truncations with SciPy double precision. This is not a rigorous zero-isolation certificate. The theorem-level off-line-zero result is established in the cited literature. |
| N4 | The completed Davenport–Heilbronn combination has a Riemann-type functional equation. | `test_davenport_heilbronn_completed_functional_equation` | Numerical consistency check for the specified normalization. |
| N5 | `G(s)=zeta(s)+zeta(s+1)` has a zero near `0.0988845032321+14.153479151268i`. | `test_shifted_zeta_sum_off_line_zero_reproduces` | Numerical root reproduction at multiple truncations. A rigorous claim would still need interval isolation and a zero-count certificate. |
| N6 | The same-height reflection `1-rho` is not generally a zero of this shifted sum. | `test_shifted_sum_does_not_have_the_claimed_reflection_pair` | At the reproduced root, the residual at `1-rho` is nonzero while the conjugate residual is small. No arithmetic mean of unrelated zeros is used. |

## Not certified by this suite

* No test here proves or refutes the classical Riemann Hypothesis.
* No test claims that the Euler product, the functional equation, and the
  bicomplex identity are three sufficient or individually necessary RH
  hypotheses. The examples vary multiple structural features.
* No Epstein off-line zero is numerically isolated here. The class-number
  calculation and the theorem in the literature are kept as separate evidence.
* Floating-point residuals are evidence for reproducibility only. A rigorous
  numerical zero claim needs interval arithmetic, a box, a nonzero derivative
  or argument-principle count, and an independently checkable certificate.

## References

* NIST Digital Library of Mathematical Functions, §25.10, zeta zero symmetries:
  <https://dlmf.nist.gov/25.10>
* Davenport–Heilbronn definition and off-line zeros: Titchmarsh, *The Theory of
  the Riemann Zeta-Function*, §10.25; a summary of the definition and known
  zeros appears at <https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-09.pdf>.
* Voronin's off-line zero-count result for Davenport–Heilbronn is summarized at
  <https://www.mathnet.ru/eng/present13282>.
* Epstein zeta functions with class number greater than one:
  <https://doi.org/10.1515/forum-2012-0057>.
* Nyman–Beurling equivalence as an approximation criterion:
  <https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.1227/>.
