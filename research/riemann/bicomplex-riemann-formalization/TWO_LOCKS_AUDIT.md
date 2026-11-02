# Audit of the “two locks” claims

## Scope

This audit checks whether the proposed “first lock” (Euler product amplitudes), “second lock” (the bicomplex zero divisor), numerical examples, integrals, derivatives, and physical analogies can move a zero of classical Riemann \(\zeta\) away from \(\operatorname{Re}s=1/2\).

The answer is precise: an off-line zero of the classical zeta function would refute RH; changing to a different \(L\)-function or to bicomplex algebra changes the object and does not refute RH. The “two locks” are not two known mechanisms that constrain \(\zeta\)'s zeros.

## 1. “First lock”: what the Euler product says

For \(\operatorname{Re}s>1\),
\[
\zeta(s)=\prod_p(1-p^{-s})^{-1}
\]
converges absolutely and is nonzero. This proves zero-freeness in \(\operatorname{Re}s>1\). The product does not converge as an ordinary Euler product in the critical strip \(0<\operatorname{Re}s<1\). There is no Euler-product argument that fixes every nontrivial zero at \(1/2\).

The equation
\[
|p^{-s}|=p^{-\operatorname{Re}s}
\]
is correct for each prime factor where the expression is used. It does **not** imply that the Euler product “locks” \(\operatorname{Re}s\) at \(1/2\). The functional equation relates completed values at \(s\) and \(1-s\), with gamma and trigonometric factors; it is not a termwise equality \(p^{-\beta}=p^{-(1-\beta)}\). NIST's zero summary states the actual results: no zeros for \(\operatorname{Re}s>1\), symmetry about the critical line, and RH as the still-open assertion that every nontrivial zero is on that line.

### A second \(L\)-function is a different function

The Davenport–Heilbronn example is a linear combination of two Dirichlet \(L\)-functions modulo 5. In a standard normalization,
\[
f(s)=\frac{1-i\kappa}{2}L(s,\chi)
     +\frac{1+i\kappa}{2}L(s,\overline\chi),
\qquad
\kappa=\frac{\sqrt{10-2\sqrt5}-2}{\sqrt5-1}
       \approx0.284079.
\]
It has a Riemann-type functional equation and zeros away from its symmetry line. Its coefficients combine the two Dirichlet series; it is **not** obtained by replacing each prime factor \(p^{-s}\) of \(\zeta\) by two terms \(p^{-s}+i\kappa p^{-s}\), nor by generating local powers \(p^{-0.8}\) and \(p^{-0.4}\). The function is not the classical Riemann zeta function and has no Euler product of the asserted form.

Epstein zeta functions for certain quadratic forms with class number greater than one also have off-line zeros. That is a result about those Epstein functions. It does not alter the Euler product of \(\zeta\) or transfer a zero to \(\zeta\).

Therefore:
- Davenport–Heilbronn/Epstein demonstrate that functional-equation symmetry alone does not force a general Dirichlet series' zeros onto its symmetry line.
- They do not demonstrate an off-line zero of Riemann \(\zeta\).
- The parameter \(\kappa\) is a coefficient in a different function, not an RH-breaking perturbation of a local Euler factor.

## 2. “Second lock”: the bicomplex identity is separate algebra

In the package's bicomplex convention,
\[
i^2=j^2=-1,\quad ij=ji=k,\quad k^2=+1.
\]
Consequently,
\[
(1+k)(1-k)=1-k^2=0.
\]
If instead a symbol \(k\) satisfies \(k^2=-1\), then the same multiplication gives
\[
(1+k)(1-k)=1-k^2=2.
\]
These are two different algebraic assumptions. In the bicomplex construction \(k=ij\) has square \(+1\); one cannot retain that definition and then substitute \(k^2=-1\) to “close” a second lock. The ordinary complex unit \(i\) has square \(-1\), but it is not the bicomplex product \(k=ij\).

The zero-divisor identity belongs to the split-complex/bicomplex algebra. It does not occur as a factor in the classical Euler product or in the analytic continuation of \(\zeta\). Setting \(b=-0.2\) in a chosen coordinate map moves a *coordinate* from \(0.5\) to \(0.7\); setting \(b=-3\) in \(\sigma_{\rm eff}=\sigma-b\) sends \(-1\) to \(2\). Neither operation changes the zero set of classical \(\zeta\).

For the proposed lift
\[
F_f=f(s+b)e_+ + f(s-b)e_-,
\qquad e_\pm=(1\pm k)/2,
\]
the full bicomplex value is zero iff **both** component values vanish. One vanishing component alone produces a nonzero zero divisor. Under RH, if both components are nontrivial zeta/xi zeros, then their real parts both equal \(1/2\), which forces \(b=0\). That is the conditional theorem recorded in [RH conditional and spectral bridges](RH_CONDITIONAL_SPECTRAL_BRIDGES.md); it assumes RH and proves no unconditional zero location.

## 3. Numerical values at the proposed points

A direct Euler–Maclaurin evaluation (12,000-term cutoff and 10 Bernoulli correction terms, ordinary double precision) gives these approximate checks:
\[
\begin{aligned}
\zeta(0.7+14i)&\approx 0.1610564-0.0677053i,\\
\zeta(0.7+14.13i)&\approx 0.1453826+0.0175854i,\\
\zeta(0.7+14.13472514i)&\approx 0.1449767+0.0207464i.
\end{aligned}
\]
The last value is close to the user's \(0.144+0.020i\), but it uses the first zeta-zero ordinate \(\gamma_1\approx14.13472514\), not \(14\) or \(14.13\). These are numerical evaluations, not interval-certified results. They show only that these particular points are not zeros; they do not rule out other off-line zeros.

At the first critical-line zero,
\[
\left|\zeta'\!\left(\tfrac12+i\gamma_1\right)\right|
\approx0.7931604.
\]
At the different, nonzero point \(0.7+i\gamma_1\), the same numerical differentiation gives
\[
|\zeta'(0.7+i\gamma_1)|\approx0.6747233.
\]
Derivative values at two points are not a “lock,” and the second point is not a zero. A derivative magnitude does not by itself establish a zero's location, multiplicity, or stability.

For \(x=10^{12}\), \(\pi(x)=37{,}607{,}912{,}018\). With the offset convention \(\operatorname{Li}(x)=\int_2^x dt/\log t\), the prime-counting difference is approximately \(38{,}261.8\); with \(\operatorname{li}(x)=\operatorname{Ei}(\log x)\), it is approximately \(38{,}262.8\). The convention changes the constant offset by about 1.045.

The rough value \(17.7\) million is the magnitude of a **single hypothetical \(\psi\)-formula term** \(x^{0.7}/|0.7+i\gamma_1|\). It is not a predicted value of \(\pi(x)-\operatorname{Li}(x)\). The zero sum is oscillatory, includes other zeros and limiting/smoothing conventions, and conversion from \(\psi\) to \(\pi\) uses partial summation. A finite observed error at one \(x\) cannot refute an asymptotic \(O\)-bound with an unspecified constant. To refute RH one needs a certified off-line zero of classical \(\zeta\), or a rigorous contradiction to an equivalent universal theorem.

## 4. Integral claims and analytic continuation

The elementary integrals are correct:
\[
\int_0^1 x^{-1/2}\,dx=2,\qquad
\int_0^1 x^{-0.3}\,dx=\frac{1}{0.7}=\frac{10}{7}.
\]
They compare two power functions. They are not the Mellin representation of zeta.

The identity
\[
\Gamma(s)\zeta(s)=\int_0^\infty\frac{x^{s-1}}{e^x-1}\,dx
\]
holds as an ordinary improper integral only for \(\operatorname{Re}s>1\). Near \(x=0\),
\[
\frac{x^{s-1}}{e^x-1}\sim x^{s-2},
\]
so the integral diverges there when \(\operatorname{Re}s\le1\), including \(\sigma=0.5\) and \(0.7\). Analytic continuation or a specified subtraction/regularization is needed; replacing \(x^{-0.5}\) by \(x^{-0.3}\) in the elementary integral does not calculate \(\zeta(0.5+it)\), \(\zeta(0.7+it)\), or their zeros.

Likewise, in the half-plane where the Dirichlet series converges,
\[
\zeta'(s)=-\sum_{n\ge1}(\log n)n^{-s}.
\]
The summand derivative is \(-(\log n)n^{-s}\). Moving the real exponent from \(0.5\) to \(0.7\) changes a summand by a factor \(n^{-0.2}\), but the difference is
\[
-(\log n)n^{-0.7}+(\log n)n^{-0.5}
=(\log n)n^{-0.5}(1-n^{-0.2}),
\]
not simply \((\log n)n^{-0.2}\). The series is not termwise convergent at \(\sigma=0.5\) or \(0.7\); analytic continuation is again essential.

## 5. Physical and philosophical examples

| Example | Established model-level fact | What does not follow |
|---|---|---|
| Lee–Yang | Under specified ferromagnetic Ising hypotheses, partition-function zeros lie on a unit circle in a fugacity variable. | The circle is not the zeta critical line by itself. Antiferromagnetic behavior depends on the model; some antiferromagnetic systems also have circle theorems. No \(k^2=1\) perturbation of \(\zeta\) is established. |
| Belousov–Zhabotinsky chemistry | A driven chemical reaction can oscillate; kinetics can be modeled with nonlinear ODEs. | \(\operatorname{Re}s=0.5\) is not thereby an equilibrium, bromate is not automatically \(b\), and oscillation does not instantiate the bicomplex zero divisor. |
| Tacoma Narrows | A measured wind near 42 mph accompanied the 1940 collapse; aerodynamic and torsional dynamics are the engineering subject. | Wind speed is not \(b=-0.2\), and the bridge's failure does not mean \(k^2=1\) in bicomplex algebra. There is no zeta-zero map. |
| Philosophy / Kabbalah | These can serve as explicitly labeled metaphors. | Without defined structures, operations, and proved maps, “thesis/antithesis,” sefirot, and qelippot are not mathematical bridges or evidence about RH. |

The previous [cross-domain audit](CROSS_DOMAIN_ANALYSIS.md) supplies the domain equations and evidence standards for EEG, aeroelasticity, finance, epidemics, acoustics, optics, seismology, chemistry, and social diffusion.

## 6. What would actually refute RH?

RH is the statement
\[
\forall \rho\quad
\bigl(\xi(\rho)=0\ \land\ 0<\operatorname{Re}\rho<1\bigr)
\Longrightarrow \operatorname{Re}\rho=\frac12.
\]
A valid refutation must give a specific \(\rho=\beta+i\gamma\), prove \(\xi(\rho)=0\) (equivalently certify a nontrivial zero of \(\zeta\)), and prove \(\beta\ne1/2\). A numerical near-zero, a zero of Davenport–Heilbronn/Epstein, a bicomplex zero divisor, a physical instability, or a finite prime-counting discrepancy does not satisfy those obligations.

The following implications are valid:
\[
\text{certified off-line zero of classical }\zeta
\Longrightarrow \neg\mathrm{RH},
\]
\[
\mathrm{RH}
\Longrightarrow \text{its classical equivalent error bounds and listed consequences}.
\]
The following proposed implications are not established:
\[
\text{second }L\text{ exists}\Longrightarrow\neg\mathrm{RH},
\quad
k^2=1\Longrightarrow\neg\mathrm{RH},
\quad
\text{wind/oscillation/long memory}\Longrightarrow\neg\mathrm{RH}.
\]

## References

- NIST DLMF, [zeta definition, Euler product, and analytic continuation](https://dlmf.nist.gov/25.2), [zero distribution](https://dlmf.nist.gov/25.10), and [Mellin integral with domain \(\operatorname{Re}s>1\)](https://dlmf.nist.gov/25.5).
- Davenport–Heilbronn definition and \(\kappa\): [MathNet article](https://m.mathnet.ru/php/archive.phtml?jrnid=cheb&option_lang=eng&paperid=604).
- Lee–Yang circle theorem for specified ferromagnetic models: [original Heisenberg ferromagnet theorem record](https://doi.org/10.1103/PhysRevLett.24.1409); example of an antiferromagnetic setting with a circle theorem: [Chinese Physics Letters paper](https://cpl.iphy.ac.cn/en/article/id/37653?viewType=citedby-info).
- Tacoma Narrows history and measured wind: [Washington State DOT history](https://wsdot.wa.gov/TNBhistory/collapse.htm); engineering context: [American Physical Society account](https://www.aps.org/apsnews/2016/11/collapse-of-the-tacoma-narrows-bridge).
