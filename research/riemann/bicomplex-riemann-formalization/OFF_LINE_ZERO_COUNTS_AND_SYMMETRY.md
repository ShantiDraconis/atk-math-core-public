# Off-line zeros in related functions: counts, symmetry, and finite lists

## Scope

This note separates three different claims:

1. Some functions other than Riemann \(\zeta\) have infinitely many zeros off their own functional-equation line.
2. Functional-equation and conjugation symmetries pair such zeros.
3. The midpoint of two paired zeros lies on the symmetry line.

The first two can be theorems under specified hypotheses. The third is elementary arithmetic. None says that the midpoint is itself a zero, and none transfers a zero to Riemann \(\zeta\).

## 1. Davenport–Heilbronn: what the counting results say

Let \(F_{\rm DH}\) denote the standard Davenport–Heilbronn Dirichlet-series combination and let \(1/2<\alpha<\beta<1\) be fixed. Define
\[
N_{\rm DH}(\alpha,\beta;T)
=\#\{\rho:F_{\rm DH}(\rho)=0,\ \alpha<\operatorname{Re}\rho<\beta,\
0<\operatorname{Im}\rho\le T\},
\]
with multiplicities specified by the source convention.

The cited Voronin result gives a positive constant \(c_{\alpha,\beta}\) such that
\[
N_{\rm DH}(\alpha,\beta;T)\ge c_{\alpha,\beta}T
\]
for sufficiently large \(T\) (equivalently, \(N_{\rm DH}(\alpha,\beta;T)\gg T\)). This proves infinitely many zeros in each such fixed strip to the right of the symmetry line. Reflection gives corresponding zeros on the left.

This lower bound is not, by itself, the exact global asymptotic
\(N_{\rm off}(T)\sim cT\). An asymptotic formula requires a precisely defined counting region, normalization, and a cited theorem that actually proves that asymptotic. Nor does a global \(\gg T\) lower bound imply “two new zeros in every height interval of length 100.”

Davenport–Heilbronn also has many zeros on its own symmetry line. The off-line zeros are not its entire zero set.

## 2. Epstein \(Q(x,y)=x^2+5y^2\)

The discriminant is
\[
D=0^2-4(1)(5)=-20,
\]
and the corresponding imaginary quadratic field has class number \(h(-20)=2\). For positive-definite binary quadratic forms with class number greater than one, Davenport–Heilbronn and Voronin proved lower bounds of order \(T\) for zeros in fixed off-line strips; later work gives refined counting results. Thus this Epstein zeta function has infinitely many off-line zeros.

That is a theorem about the Epstein function attached to \(Q\). It is not an off-line zero of Riemann \(\zeta\), and its counting function cannot be substituted into the Riemann prime explicit formula.

## 3. The symmetry orbit and the “average”

For a completed function \(\Xi_F\) with
\[
\Xi_F(s)=\Xi_F(1-s),\qquad
\Xi_F(\bar s)=\overline{\Xi_F(s)},
\]
a zero \(\rho=\beta+i\gamma\) implies the orbit
\[
\rho,\quad \bar\rho=\beta-i\gamma,\quad
1-\rho=1-\beta-i\gamma,\quad
1-\bar\rho=1-\beta+i\gamma,
\]
counted with multiplicity. For \(\beta\ne1/2\) and \(\gamma\ne0\), these are generally four distinct points.

At the same positive ordinate, the partner of \(\beta+i\gamma\) is
\(1-\beta+i\gamma\). Their arithmetic mean is
\[
\frac{(\beta+i\gamma)+(1-\beta+i\gamma)}{2}
=\frac12+i\gamma.
\]
This point lies on the symmetry line. It is **not thereby a zero**. The functional equation asserts that the two endpoints are zeros; it does not assert that their midpoint is a zero or that the two zeros “merge into one.” Averages of roots do not generally preserve the zero equation.

The orbit size also does not force a single fixed \(\gamma\) to have several different real parts such as \(0.8,0.7,0.6\). Those would be separate zero orbits unless a further theorem showed they shared an ordinate.

## 4. Sample computed Davenport–Heilbronn zeros

A published numerical study reports, among others, the following off-line zeros of the Davenport–Heilbronn example:
\[
\begin{aligned}
&0.808517+85.699348\,i,\\
&0.650830+114.163343\,i,\\
&0.574356+166.479306\,i,\\
&0.724258+176.702461\,i.
\end{aligned}
\]
Their reflected same-height partners have approximate real parts
\[
0.191483,\quad 0.349170,\quad 0.425644,\quad 0.275742,
\]
respectively; conjugation supplies the negative ordinates. These are examples, not a finite complete inventory of an infinite set. Decimal listings are numerical evidence; a proof of an individual zero requires a certified computation or an analytic theorem.

A list can be complete **up to a fixed height** only if an exhaustive zero-counting method proves that no zeros were omitted below that height. A finite list can never be the complete list of an infinite set.

## 5. The phrase “only functions without Euler products”

The examples above are functions without the usual single Euler product for Riemann \(\zeta\). That does not prove the universal statement
“off-line zeros occur only when there is no Euler product.” Euler product alone is not a zero-location theorem; the functional equation, normalization, gamma factors, and exact function class matter.

For instance, \(\zeta(2s)\) has an Euler product in its half-plane of convergence, while its zeros are \(s=\tfrac14+i\gamma/2\), inherited from zeros \(1/2+i\gamma\) of \(\zeta\). Relative to the line \(\operatorname{Re}s=1/2\) these are off-line; relative to the naturally rescaled functional equation of \(\zeta(2s)\), the symmetry line is \(\operatorname{Re}s=1/4\). This example shows why “has an Euler product” without specifying the function's own symmetry center is not enough.

The mathematically relevant statements are narrower:

- The classical Riemann hypothesis concerns only the nontrivial zeros of classical \(\zeta(s)\).
- Davenport–Heilbronn and the indicated Epstein functions are distinct examples with functional-equation symmetry and off-line zeros.
- Their behavior neither proves nor refutes RH.
- There is no theorem here that “Euler product present” is equivalent to “all zeros lie on \(\operatorname{Re}s=1/2\).”

## 6. Breaking the functional equation

A function without a reflection symmetry need not have reflected zero pairs, so a real-part average of \(1/2\) need not arise. But breaking a symmetry does not automatically produce any specified zero, much less a zero of Riemann \(\zeta\).

For
\[
G(s)=\zeta(s)+\zeta(s+1),
\]
the displayed sum does not inherit the completed zeta functional equation as written; it has poles at \(s=1\) and \(s=0\), and it is a different meromorphic function. A claimed pair of real parts such as \(0.0988\) and \(0.1422\) is not a reproducible zero specification: a complex zero requires both real and imaginary parts, the exact function/normalization, and a certified zero calculation. Even if such zeros are verified for \(G\), they would not be zeros of \(\zeta\).

The right RH-refutation target remains a certified \(\rho\) for the classical zeta function with
\[
\zeta(\rho)=0,\qquad 0<\operatorname{Re}\rho<1,\qquad
\operatorname{Re}\rho\ne\frac12.
\]

## 7. Source and evidence status

- Davenport–Heilbronn off-line strip lower bounds: **CLASSICAL THEOREM** for its specific function.
- Epstein off-line strip lower bounds for class number \(>1\): **CLASSICAL THEOREM** for the specific quadratic-form Epstein zeta.
- Sample zeros displayed above: **COMPUTED APPROXIMATIONS**, not a complete list and not all individually certified here.
- The four-point orbit: **CONDITIONAL THEOREM** from functional-equation and conjugation symmetry of the specified completed function.
- The midpoint's real part \(1/2\): **EXACT ARITHMETIC**.
- The midpoint itself being a zero: **NOT IMPLIED**.
- Any transfer of these zeros to classical Riemann \(\zeta\): **FALSE** absent an exact zero-preserving map.

## References

- H. Davenport and H. Heilbronn, [On the zeros of certain Dirichlet series](https://doi.org/10.1112/jlms/s1-11.4.307), 1936.
- S. M. Voronin results summarized by S. A. Gritsenko, [On the zeros of the Davenport–Heilbronn function](https://www.mathnet.ru/php/archive.phtml?jrnid=cheb&option_lang=eng&paperid=604), including an off-critical-line strip lower bound proportional to \(T\).
- E. P. Balanzario and J. Sánchez-Ortiz, [Zeros of the Davenport–Heilbronn counterexample](https://doi.org/10.1090/S0025-5718-07-01999-0), *Mathematics of Computation* (2007), numerical zero list.
- A. Laurinčikas, [On the zeros of Epstein zeta functions](https://doi.org/10.1515/forum-2012-0057).
- [NIST DLMF, zeta zeros and symmetries](https://dlmf.nist.gov/25.10).
- Class number of \(\mathbb Q(\sqrt{-5})\) and reduced forms of discriminant \(-20\): [quadratic forms reference](https://kokunoyumeto.github.io/open-math-courses-public/courses/NT-CFT/hilbert-and-ring-class-fields-and-quadratic-prime-forms.html).
