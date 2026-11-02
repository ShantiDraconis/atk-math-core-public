"""Reproducibility tests for quasi-Riemann comparisons.

Numerical root checks use double precision and Euler--Maclaurin summation.
They are not rigorous interval certificates. Exact algebraic countermodels
are tested separately from numerical observations.
"""

from __future__ import annotations

import math
import unittest
from fractions import Fraction

from scipy.optimize import root
from scipy.special import bernoulli, gamma


BERNOULLI = bernoulli(22)
EM_TERMS = 10


def hurwitz_zeta_em(s: complex, a: float, n_terms: int = 300) -> complex:
    """Euler--Maclaurin approximation to Hurwitz zeta, for s != 1."""
    s = complex(s)
    if abs(s - 1) < 1e-14:
        raise ValueError("Euler--Maclaurin formula has a pole at s=1")
    total = sum(complex(n + a) ** (-s) for n in range(n_terms))
    x = n_terms + a
    total += x ** (1 - s) / (s - 1) + 0.5 * x ** (-s)
    rising = s
    for k in range(1, EM_TERMS + 1):
        if k > 1:
            rising *= (s + 2 * k - 3) * (s + 2 * k - 2)
        total += (
            BERNOULLI[2 * k]
            / math.factorial(2 * k)
            * rising
            * x ** (-s - 2 * k + 1)
        )
    return total


def zeta_em(s: complex, n_terms: int = 300) -> complex:
    return hurwitz_zeta_em(s, 1.0, n_terms)


def xi_em(s: complex, n_terms: int = 300) -> complex:
    s = complex(s)
    return (
        0.5
        * s
        * (s - 1)
        * math.pi ** (-s / 2)
        * gamma(s / 2)
        * zeta_em(s, n_terms)
    )


def primes_up_to(limit: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
    return primes


def euler_product(s: complex, prime_limit: int = 20_000) -> complex:
    product = 1 + 0j
    for p in primes_up_to(prime_limit):
        product /= 1 - complex(p) ** (-s)
    return product


# Primitive odd character modulo 5 with chi(2)=i.
CHI_MOD_5 = {1: 1 + 0j, 2: 1j, 3: -1j, 4: -1 + 0j}
KAPPA = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)
DH_C = (1 - 1j * KAPPA) / 2


def dirichlet_l_mod5(s: complex, conjugate: bool = False, n_terms: int = 250) -> complex:
    total = 0j
    for a, value in CHI_MOD_5.items():
        coefficient = value.conjugate() if conjugate else value
        total += coefficient * hurwitz_zeta_em(s, a / 5, n_terms)
    return 5 ** (-complex(s)) * total


def davenport_heilbronn(s: complex, n_terms: int = 250) -> complex:
    return DH_C * dirichlet_l_mod5(s, False, n_terms) + DH_C.conjugate() * dirichlet_l_mod5(
        s, True, n_terms
    )


def completed_davenport_heilbronn(s: complex, n_terms: int = 250) -> complex:
    s = complex(s)
    return (
        (math.pi / 5) ** (-(s + 1) / 2)
        * gamma((s + 1) / 2)
        * davenport_heilbronn(s, n_terms)
    )


def solve_complex_zero(function, initial: complex) -> tuple[complex, float]:
    result = root(
        lambda xy: [
            function(complex(xy[0], xy[1])).real,
            function(complex(xy[0], xy[1])).imag,
        ],
        [initial.real, initial.imag],
        tol=1e-10,
    )
    point = complex(result.x[0], result.x[1])
    return point, abs(function(point))


class ExactStructureTests(unittest.TestCase):
    def test_reflection_and_conjugation_give_a_quartet(self) -> None:
        beta, gamma0 = Fraction(7, 10), Fraction(14, 1)
        orbit = {
            complex(float(beta), float(gamma0)),
            complex(float(1 - beta), float(gamma0)),
            complex(float(beta), float(-gamma0)),
            complex(float(1 - beta), float(-gamma0)),
        }
        self.assertEqual(len(orbit), 4)
        self.assertIn(complex(0.3, 14.0), orbit)
        self.assertIn(complex(0.7, -14.0), orbit)
        self.assertEqual((beta + (1 - beta)) / 2, Fraction(1, 2))
        # The midpoint is an arithmetic midpoint; it is not asserted to be a zero.

    def test_entire_symmetric_countermodel_has_off_line_zeros(self) -> None:
        # F(s)=(s-3/10)(s-7/10)=s^2-s+21/100.
        # F(1-s)=F(s), and the real coefficients give conjugation symmetry.
        a = Fraction(3, 10)
        b = Fraction(7, 10)

        def polynomial(s: complex) -> complex:
            return (s - float(a)) * (s - float(b))

        for point in (complex(float(a), 0), complex(float(b), 0)):
            self.assertAlmostEqual(abs(polynomial(point)), 0.0, places=14)
        probe = 0.23 + 0.7j
        self.assertLess(abs(polynomial(probe) - polynomial(1 - probe)), 1e-14)
        self.assertNotEqual(a, Fraction(1, 2))
        self.assertNotEqual(b, Fraction(1, 2))

    def test_bicomplex_zero_divisor_is_an_algebra_identity(self) -> None:
        # Pair (a,b) represents a+b*k with k^2=+1.
        def multiply(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
            a, b = x
            c, d = y
            return (a * c + b * d, a * d + b * c)

        self.assertEqual(multiply((1, 1), (1, -1)), (0, 0))
        # In ordinary complex arithmetic, k^2=-1, so the same product is 2.
        self.assertEqual((1 + 1j) * (1 - 1j), 2 + 0j)

    def test_discriminant_minus20_has_two_reduced_positive_forms(self) -> None:
        # Reduced positive primitive forms (a,b,c): |b|<=a<=c,
        # b^2-4ac=-20, with b>=0 when |b|=a or a=c.
        forms = []
        D = -20
        for a in range(1, 10):
            for b in range(-a, a + 1):
                numerator = b * b - D
                if numerator % (4 * a):
                    continue
                c = numerator // (4 * a)
                if a <= c and math.gcd(a, math.gcd(abs(b), c)) == 1:
                    if (abs(b) != a and a != c) or b >= 0:
                        forms.append((a, b, c))
        self.assertEqual(set(forms), {(1, 0, 5), (2, 2, 3)})
        self.assertEqual(len(forms), 2)


class NumericalReproductionTests(unittest.TestCase):
    def test_completed_zeta_reflection_and_conjugation(self) -> None:
        s = 0.37 + 6.2j
        xi_s = xi_em(s, 300)
        xi_reflected = xi_em(1 - s, 300)
        xi_conjugate = xi_em(s.conjugate(), 300)
        self.assertLess(abs(xi_s - xi_reflected) / max(1.0, abs(xi_s)), 2e-9)
        self.assertLess(abs(xi_conjugate - xi_s.conjugate()) / max(1.0, abs(xi_s)), 2e-9)

    def test_euler_product_matches_zeta_only_in_its_convergence_region(self) -> None:
        s = 2.0 + 3.0j
        product = euler_product(s, 20_000)
        value = zeta_em(s, 300)
        self.assertLess(abs(product - value) / abs(value), 2e-4)
        self.assertGreater(s.real, 1)

    def test_davenport_heilbronn_off_line_zero_reproduces(self) -> None:
        expected = 0.8085171824566374 + 85.69934848537759j
        roots = []
        for n_terms in (100, 200, 300):
            point, residual = solve_complex_zero(
                lambda s: davenport_heilbronn(s, n_terms), expected
            )
            roots.append(point)
            self.assertLess(residual, 1e-9)
            self.assertLess(abs(point - expected), 2e-8)
            self.assertNotAlmostEqual(point.real, 0.5, delta=1e-3)
        self.assertLess(abs(roots[0] - roots[-1]), 2e-8)

    def test_davenport_heilbronn_completed_functional_equation(self) -> None:
        s = 0.73 + 2.4j
        lhs = completed_davenport_heilbronn(s, 300)
        rhs = completed_davenport_heilbronn(1 - s, 300)
        self.assertLess(abs(lhs - rhs) / max(1.0, abs(lhs)), 2e-9)

    def test_shifted_zeta_sum_off_line_zero_reproduces(self) -> None:
        shifted_sum = lambda s, n: zeta_em(s, n) + zeta_em(s + 1, n)
        expected = 0.0988845032321 + 14.153479151268j
        roots = []
        for n_terms in (200, 400, 600):
            point, residual = solve_complex_zero(
                lambda s: shifted_sum(s, n_terms), expected
            )
            roots.append(point)
            self.assertLess(residual, 1e-8)
            self.assertLess(abs(point - expected), 2e-7)
            self.assertNotAlmostEqual(point.real, 0.5, delta=1e-3)
        self.assertLess(abs(roots[0] - roots[-1]), 2e-7)

    def test_shifted_sum_does_not_have_the_claimed_reflection_pair(self) -> None:
        rho = 0.0988845032321 + 14.153479151268j
        g_rho = zeta_em(rho, 400) + zeta_em(rho + 1, 400)
        g_reflection = zeta_em(1 - rho, 400) + zeta_em(2 - rho, 400)
        g_conjugate = zeta_em(rho.conjugate(), 400) + zeta_em(rho.conjugate() + 1, 400)
        self.assertLess(abs(g_rho), 1e-8)
        self.assertGreater(abs(g_reflection), 0.1)
        self.assertLess(abs(g_conjugate), 1e-8)


if __name__ == "__main__":
    unittest.main(verbosity=2)
